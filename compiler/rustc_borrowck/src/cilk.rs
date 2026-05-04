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

use rustc_data_structures::fx::FxIndexSet;
use rustc_data_structures::work_queue::WorkQueue;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::bug;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{Body, ConstraintCategory, Local, Location, TerminatorKind};
use rustc_middle::ty::RegionVid;
use rustc_mir_dataflow::task_info::{Task, TaskInfo};
use rustc_span::Span;

use crate::borrow_set::BorrowSet;
use crate::constraints::OutlivesConstraint;
use crate::def_use;
use crate::renumber::RegionCtxt;
use crate::type_check::{Locations, MirTypeckRegionConstraints};
use crate::BorrowckInferCtxt;

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
) {
    // Fast path: a body with no `Detach` terminator has no spawned tasks, so
    // there is nothing to extend. This also avoids running `TaskInfo`, whose
    // spindle propagation across plain CFG joins (e.g. SwitchInt → Goto →
    // join) is incomplete and would assert-fail on non-cilk bodies.
    if !body
        .basic_blocks
        .iter()
        .any(|bb_data| matches!(bb_data.terminator().kind, TerminatorKind::Detach { .. }))
    {
        return;
    }

    let task_info = TaskInfo::from_body(body);
    for task in task_info.child_tasks() {
        let points = continuation_points(body, &task_info, task);
        if points.is_empty() {
            continue;
        }
        let regions = borrow_regions_to_extend(body, &task_info, task, borrow_set);
        if regions.is_empty() {
            continue;
        }
        let reattach_loc = task_info.expect_last_location(task);
        let span = body.basic_blocks[reattach_loc.block].terminator().source_info.span;
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
///   * skips over nested spawns' bodies (a nested task's blocks belong to a
///     different `Task`), and
///   * excludes the outer task's own blocks (they belong to `task`, not the
///     parent).
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
    task_info: &TaskInfo,
    task: Task,
) -> Vec<Location> {
    let parent = task_info.expect_parent_task(task);
    let reattach_loc = task_info.expect_last_location(task);
    let TerminatorKind::Reattach { continuation } =
        body.basic_blocks[reattach_loc.block].terminator().kind
    else {
        bug!(
            "expected last_location of task {task:?} to terminate with Reattach, found {:?}",
            body.basic_blocks[reattach_loc.block].terminator().kind,
        );
    };

    let mut queue = WorkQueue::with_none(body.basic_blocks.len());
    queue.insert(continuation);

    let mut points = Vec::new();
    while let Some(bb) = queue.pop() {
        let bb_data = &body.basic_blocks[bb];
        if bb_data.is_cleanup {
            continue;
        }
        if task_info.expect_task(bb) != parent {
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
/// region.
///
/// A MIR-only walk (no HIR upvar analysis required): for each [`Local`]
/// referenced in any of `task`'s blocks, look up `borrow_set.local_map[local]`
/// and collect the regions of every borrow whose place starts with that local.
/// The resulting set is exactly the set of borrows that *might* be in flight
/// concurrently with the task's accesses, which is what cilk lifetime
/// extension needs to model.
///
/// The walk uses [`def_use::categorize`] to skip storage marks
/// (`StorageLive` / `StorageDead`) and other non-uses; only true defs, uses,
/// and drops count as references. This matches the granularity of liveness
/// analysis and ensures we don't count purely structural local mentions.
///
/// This is intentionally broader than HIR upvar analysis: it covers both
/// borrows captured from the parent (the upvar case) and borrows issued
/// inside the task body. Both want the same treatment — extend their region
/// to the matching `Sync`.
pub(crate) fn borrow_regions_to_extend<'tcx>(
    body: &Body<'tcx>,
    task_info: &TaskInfo,
    task: Task,
    borrow_set: &BorrowSet<'tcx>,
) -> FxIndexSet<RegionVid> {
    let mut visitor = ReferencedLocalsVisitor { locals: FxIndexSet::default() };
    for bb in task_info.blocks_of(task) {
        visitor.visit_basic_block_data(bb, &body.basic_blocks[bb]);
    }

    let mut regions = FxIndexSet::default();
    for local in visitor.locals {
        let Some(borrows) = borrow_set.local_map.get(&local) else { continue };
        for &bw in borrows {
            regions.insert(borrow_set[bw].region);
        }
    }
    regions
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
        .next_nll_region_var(
            NllRegionVariableOrigin::Existential { name: None },
            || RegionCtxt::Existential(None),
        )
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