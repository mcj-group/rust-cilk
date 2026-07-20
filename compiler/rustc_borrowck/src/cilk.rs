//! Borrow-checker support for cilk_spawn / cilk_sync.
//!
//! A borrow created inside a `cilk_spawn` task may still be live in the parent
//! after `Reattach`, until the matching `Sync` synchronizes the task. The MIR
//! CFG itself does not express that — the parent's continuation flows past
//! `Reattach` as if the spawned task had returned — so without help, NLL
//! infers borrow scopes that are too short and misses conflicts between the
//! parent and the spawned task.
//!
//! The fix is to seed region inference with extra constraints. For each task,
//! we synthesize a *continuation region* `'?c` whose live points span the
//! parent CFG from the task's `Reattach` through to its matching `Sync`, then
//! add `'?b: '?c` for every borrow region `'?b` belonging to the task. After
//! propagation, those borrow regions cover the full continuation, so the
//! existing `Borrows` dataflow correctly keeps them in flight.
//!
//! Public entry point: [`extend_cilk_borrow_lifetimes`] runs once during typeck
//! and applies the scheme to every child task in the body.
//!
//! Internals:
//!   * [`continuation_points`]        — for a child task, enumerate the parent
//!     CFG points from its `Reattach` through its matching `Sync`.
//!   * [`borrow_regions_to_extend`]   — for a child task, enumerate the borrow
//!     regions whose lifetime must cover the continuation.
//!   * [`create_continuation_region`] — fresh region var, marked live at a
//!     supplied set of points.
//!   * [`add_extension_constraint`]   — push the `'?b: '?c` outlives edge.

use rustc_data_structures::fx::{FxHashSet, FxIndexSet};
use rustc_data_structures::work_queue::WorkQueue;
use rustc_hir::attrs::OrphaningAttr;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::bug;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{
    BasicBlock, Body, BorrowKind, ConstraintCategory, Local, LocalInfo, Location, TerminatorKind,
};
use rustc_middle::ty::{self, RegionVid, TyCtxt};
use rustc_mir_dataflow::task_info::{Task, TaskInfo};
use rustc_span::Span;

use crate::borrow_set::BorrowSet;
use crate::constraints::OutlivesConstraint;
use crate::renumber::RegionCtxt;
use crate::type_check::{Locations, MirTypeckRegionConstraints};
use crate::{BorrowckInferCtxt, def_use};

/// Returns `true` if `body` contains any cilk_spawn (i.e., any `Detach`
/// terminator). Used to fast-path past the cilk machinery for ordinary code.
pub(crate) fn body_has_cilk_tasks(body: &Body<'_>) -> bool {
    body.basic_blocks
        .iter()
        .any(|bb_data| matches!(bb_data.terminator().kind, TerminatorKind::Detach { .. }))
}

/// Returns the set of [`BasicBlock`]s whose terminator is a [`TerminatorKind::Call`]
/// to an orphaning closure — a closure bearing `#[orphaning]` synthesized during
/// `cilk_spawn` lowering to wrap the spawn body. The corresponding `DefId` of the 
/// closure called is also returned.
///
/// Calling a closure does not produce a `Call` to the closure's own `DefId`.
/// THIR lowering rewrites `closure()` into a call to the `Fn`/`FnMut`/`FnOnce`
/// trait method (`<{closure} as Fn>::call(&closure, ())`), so the callee in the
/// MIR is the *trait method* `FnDef`, whose `DefId` carries no `#[orphaning]`
/// attribute. The closure itself appears as the receiver: the trait-method
/// `FnDef`'s first generic argument is the closure's `Self` type. We recover
/// that type, pull out the closure's `DefId`, and check *its* [`OrphaningAttr`].
fn blocks_calling_orphaning_closure<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> FxIndexSet<(BasicBlock, BasicBlock, DefId)> {
    let mut result = FxIndexSet::default();
    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call { ref func, target: Some(successor), .. } =
            bb_data.terminator().kind
        else {
            continue;
        };
        let func_ty = func.ty(&body.local_decls, tcx);
        let ty::FnDef(fun_id, generic_args) = *func_ty.kind() else {
            continue;
        };
        // The callee must be one of the `Fn`/`FnMut`/`FnOnce` trait methods.
        let Some(trait_id) = tcx.trait_of_assoc(fun_id) else {
            continue;
        };
        if tcx.fn_trait_kind_from_def_id(trait_id).is_none() {
            continue;
        }
        // The receiver (the `Self` type of the `Fn`-family trait) is the closure.
        let ty::Closure(closure_id, _) = *generic_args.type_at(0).peel_refs().kind() else {
            continue;
        };
        if tcx.codegen_fn_attrs(closure_id).orphaning == OrphaningAttr::Hint {
            result.insert((bb, successor, closure_id));
        }
    }
    result
}

/// Apply cilk lifetime extension to every child task in `body`.
///
/// For each child task in the body's [`TaskInfo`], this:
///   1. Enumerates the parent CFG points spanning the task's `Reattach` to the
///      matching `Sync` ([`continuation_points`]).
///   2. Collects the borrow regions that may be in flight concurrently with
///      the task's accesses ([`borrow_regions_to_extend`]).
///   3. Synthesizes a fresh continuation region `'?c` live at those points
///      ([`create_continuation_region`]).
///   4. For each borrow region `'?b`, pushes `'?b: '?c` so propagation will
///      grow `'?b` to cover the continuation ([`add_extension_constraint`]).
///
/// Tasks with an empty continuation point set or an empty region set are
/// skipped — neither piece in isolation produces any constraint to add.
///
/// Run this during typeck, after the regular liveness constraints have been
/// generated and before SCC construction. It writes only to
/// `constraints.liveness_constraints` (seed values for `'?c`) and
/// `constraints.outlives_constraints` (the `'?b: '?c` edges); the rest of the
/// region-inference pipeline absorbs the new constraints unchanged.
pub(crate) fn extend_cilk_borrow_lifetimes<'tcx>(
    body: &Body<'tcx>,
    infcx: &BorrowckInferCtxt<'tcx>,
    constraints: &mut MirTypeckRegionConstraints<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    let task_info = TaskInfo::from_body(body);
    for task in task_info.child_tasks() {
        let reattach_loc = task_info.expect_last_location(task);
        let TerminatorKind::Reattach { sync_region: _, continuation } =
            body.basic_blocks[reattach_loc.block].terminator().kind
        else {
            bug!(
                "expected last_location of task {task:?} to terminate with Reattach, found {:?}",
                body.basic_blocks[reattach_loc.block].terminator().kind,
            );
        };
        let points = continuation_points(body, continuation);
        if points.is_empty() {
            continue;
        }
        let regions = borrow_regions_to_extend(body, &task_info, task, borrow_set);
        if regions.is_empty() {
            continue;
        }
        let span = body.basic_blocks[reattach_loc.block].terminator().source_info.span;
        let c_region = create_continuation_region(infcx, constraints, points);
        for b_region in regions {
            add_extension_constraint(constraints, b_region, c_region, span);
        }
    }

    for (orphaning_call_block, successor, orphaning_closure_id) in
        blocks_calling_orphaning_closure(body, tcx)
    {
        let points = continuation_points(body, successor);
        if points.is_empty() {
            continue;
        }
        let mut regions = FxIndexSet::default();
        for (_, bw) in borrow_set.location_map.iter() {
            if bw.reserve_location.block == orphaning_call_block
                && let BorrowKind::Mut { .. } = bw.kind
            {
                let local_decl = &body.local_decls[bw.borrowed_place.local];

                // Calling a closure that mutably captures a variable introduces a separate mutable
                // borrow of the closure call object itself. This borrow only exists to invoke the
                // closure, and is categorized as `LocalInfo::Boring` with a closure type. Extending
                // this call-site borrow would unnecessarily keep the closure object mutably borrowed
                // until the sync, rather than allowing it to become `StorageDead` immediately after
                // the call. Therefore, skip the closure called by orphaning block's terminator.
                if matches!(local_decl.local_info(), LocalInfo::Boring)
                    && matches!(
                        local_decl.ty.kind(),
                        ty::Closure(closure_id, _) if *closure_id == orphaning_closure_id
                    )
                {
                    continue;
                }

                regions.insert(bw.region);
            }
        }
        if regions.is_empty() {
            continue;
        }
        let span = body.basic_blocks[orphaning_call_block].terminator().source_info.span;
        let c_region = create_continuation_region(infcx, constraints, points);
        for b_region in regions {
            add_extension_constraint(constraints, b_region, c_region, span);
        }
    }
}

/// Enumerate the CFG locations on the parent's continuation flow that span
/// from `task`'s `Reattach` up to (and including the block of) the matching
/// `Sync`. These are the points the task's borrows must extend over to model
/// cilk's "borrow stays live until sync" semantics.
///
/// The walk is a forward BFS in the parent's CFG starting at the block
/// targeted by the `Reattach`, restricted to blocks whose [`Task`] is `task`'s
/// parent. That restriction naturally:
///
/// Boundary terminators include their containing block in the result but do
/// not propagate to successors:
///   * `Sync` — the matching synchronization point.
///   * `Return`, `UnwindResume`, `UnwindTerminate`, `CoroutineDrop` — the
///     function-level implicit sync. Cilk semantics require any pending
///     children to be synchronized before the function returns, so we treat
///     these as a Sync for the purpose of bounding the continuation.
///
/// Cleanup blocks have no [`Task`] assignment in [`TaskInfo`], so they are
/// filtered out before the parent-task check.
pub(crate) fn continuation_points<'tcx>(
    body: &Body<'tcx>,
    start_block: BasicBlock,
) -> Vec<Location> {
    let mut queue = WorkQueue::with_none(body.basic_blocks.len());
    queue.insert(start_block);
    let mut visited = FxHashSet::default();

    let mut points = Vec::new();
    while let Some(bb) = queue.pop() {
        if visited.contains(&bb) {
            continue;
        }
        visited.insert(bb);
        let bb_data = &body.basic_blocks[bb];
        if bb_data.is_cleanup {
            continue;
        }

        for statement_index in 0..=bb_data.statements.len() {
            points.push(Location { block: bb, statement_index });
        }

        match bb_data.terminator().kind {
            TerminatorKind::Sync { .. }
            | TerminatorKind::Return
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::CoroutineDrop => {
                // Boundary; do not cross.
            }
            _ => {
                for succ in bb_data.terminator().successors() {
                    queue.insert(succ);
                }
            }
        }
    }
    points
}

/// Enumerate the borrow regions that need to outlive `task`'s continuation
/// terminator.
///
/// A borrow is extended if and only if both:
///   1. It is issued in `task` (i.e., `bw.reserve_location.block ∈ task`).
///   2. Its `borrowed_place`'s root local is referenced somewhere outside
///      `task` — in the parent's continuation, in a sibling task, or in
///      function-level code. A borrow whose borrowed local is *only* used
///      inside `task` cannot conflict with anything in the parent's
///      continuation, so extending it would only cause spurious conflicts
///      at task-internal storage operations (e.g. the `StorageDead` of a
///      task-private aggregate the borrow points into).
///
/// The "issued in `task`" filter avoids extending parent-side borrows that
/// happen to mention a captured local. The "referenced outside `task`"
/// filter avoids extending purely intra-task short-lived borrows (e.g.
/// formatter argument arrays inside `println!` macro expansions).
///
/// Cleanup blocks are skipped — they have no `Task` assignment in
/// [`TaskInfo`].
pub(crate) fn borrow_regions_to_extend<'tcx>(
    body: &Body<'tcx>,
    task_info: &TaskInfo,
    task: Task,
    borrow_set: &BorrowSet<'tcx>,
) -> FxIndexSet<RegionVid> {
    let externally_referenced = locals_referenced_outside_task(body, task_info, task);

    let mut regions = FxIndexSet::default();
    for (_, bw) in borrow_set.location_map.iter() {
        let issue_block = bw.reserve_location.block;
        if body.basic_blocks[issue_block].is_cleanup {
            continue;
        }
        if task_info.expect_task(issue_block) != task {
            continue;
        }
        if !externally_referenced.contains(&bw.borrowed_place.local) {
            continue;
        }
        regions.insert(bw.region);
    }
    regions
}

/// Walk every non-cleanup block that does NOT belong to `task` and collect
/// the set of `Local`s referenced in a non-storage context. These are the
/// locals that the parent task (or some sibling) may access concurrently
/// with `task`, and hence the locals whose borrows from inside `task` need
/// lifetime extension.
fn locals_referenced_outside_task(
    body: &Body<'_>,
    task_info: &TaskInfo,
    task: Task,
) -> FxIndexSet<Local> {
    let mut visitor = ReferencedLocalsVisitor { locals: FxIndexSet::default() };
    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        if bb_data.is_cleanup {
            continue;
        }
        if task_info.expect_task(bb) == task {
            continue;
        }
        visitor.visit_basic_block_data(bb, bb_data);
    }
    visitor.locals
}

struct ReferencedLocalsVisitor {
    locals: FxIndexSet<Local>,
}

impl<'tcx> Visitor<'tcx> for ReferencedLocalsVisitor {
    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        if def_use::categorize(context).is_some() {
            self.locals.insert(local);
        }
    }
}

/// Create a fresh existential region var and mark it live at every point in
/// `points`. Returns the new region's `RegionVid`.
///
/// This is the `'?c` ("continuation region") in the cilk lifetime-extension
/// scheme: callers pick the points spanning a task's `Reattach`-to-`Sync`
/// continuation, and this function bakes that point-set into the region's
/// initial value via `liveness_constraints`.
pub(crate) fn create_continuation_region<'tcx>(
    infcx: &BorrowckInferCtxt<'tcx>,
    constraints: &mut MirTypeckRegionConstraints<'tcx>,
    points: impl IntoIterator<Item = Location>,
) -> RegionVid {
    let region = infcx
        .next_nll_region_var(NllRegionVariableOrigin::Existential { name: None }, || {
            RegionCtxt::Existential(None)
        })
        .as_var();
    for loc in points {
        constraints.liveness_constraints.add_location(region, loc);
    }
    region
}

/// Push the `borrow_region: continuation_region` outlives constraint that
/// extends a task-internal borrow across its matching `Sync`.
///
/// `span` should point at the cilk_spawn (or, ideally, the borrow site) so
/// that any region error blamed on this constraint surfaces a useful location.
/// Most cilk-driven errors will get blamed on the original borrow constraint
/// instead, since `CilkContinuation` is given a low diagnostic interest.
pub(crate) fn add_extension_constraint<'tcx>(
    constraints: &mut MirTypeckRegionConstraints<'tcx>,
    borrow_region: RegionVid,
    continuation_region: RegionVid,
    span: Span,
) {
    constraints.outlives_constraints.push(OutlivesConstraint {
        sup: borrow_region,
        sub: continuation_region,
        locations: Locations::All(span),
        span,
        category: ConstraintCategory::CilkContinuation,
        variance_info: Default::default(),
        from_closure: false,
    });
}
