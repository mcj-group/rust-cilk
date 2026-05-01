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
//! This module owns the *plumbing* for that scheme:
//!   * [`continuation_points`]        — for a child task, enumerate the parent
//!     CFG points from its `Reattach` through its matching `Sync`.
//!   * [`create_continuation_region`] — fresh region var, marked live at a
//!     supplied set of points.
//!   * [`add_extension_constraint`]   — push the `'?b: '?c` outlives edge.
//!
//! The remaining piece is the upvar-aware enumeration of borrow regions
//! belonging to the task — Q2 in the design notes.

use rustc_data_structures::work_queue::WorkQueue;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::bug;
use rustc_middle::mir::{Body, ConstraintCategory, Location, TerminatorKind};
use rustc_middle::ty::RegionVid;
use rustc_mir_dataflow::task_info::{Task, TaskInfo};
use rustc_span::Span;

use crate::BorrowckInferCtxt;
use crate::constraints::OutlivesConstraint;
use crate::renumber::RegionCtxt;
use crate::type_check::{Locations, MirTypeckRegionConstraints};

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
#[allow(dead_code)] // wired up once Q2 (which-borrows-to-extend) lands.
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

/// Create a fresh existential region var and mark it live at every point in
/// `points`. Returns the new region's `RegionVid`.
///
/// This is the `'?c` ("continuation region") in the cilk lifetime-extension
/// scheme: callers pick the points spanning a task's `Reattach`-to-`Sync`
/// continuation, and this function bakes that point-set into the region's
/// initial value via `liveness_constraints`.
#[allow(dead_code)] // wired up once the Reattach/Sync pairing analysis lands.
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
#[allow(dead_code)] // wired up once the borrow-region collection lands.
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