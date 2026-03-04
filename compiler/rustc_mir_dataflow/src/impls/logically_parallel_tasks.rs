use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir;

use crate::task_info::{Task, TaskInfo};
use crate::{Analysis, Forward, GenKill};

/// An analysis of which tasks are executing logically in parallel at any given program point.
/// The terminators of interest here are Detach, Reattach, and Sync, since no other statement
/// or terminator can create a new task.
///
/// This analysis is notably *not* usable for determining what dataflow state should be merged
/// at a given sync. This is due to a particular case where Task A spawns Task B, which
/// spawns Task C. If Task B then syncs Task C, the dataflow state from Task C should not be
/// merged at a sync in Task A. In general, this analysis includes *all* tasks that may logically
/// be in parallel rather than just those tasks whose dataflow state should be merged at a
/// sync.
///
/// This analysis is also a "may" analysis in that if a task is conditionally spawned, the task
/// is considered to be logically in parallel at program points that are dominated by the condition.
pub struct LogicallyParallelTasks<'task_info> {
    task_info: &'task_info TaskInfo,
}

impl<'tcx, 'task_info> Analysis<'tcx> for LogicallyParallelTasks<'task_info> {
    // No Dual => join operator is union.
    // This makes sense because this is a "may" anaylsis.
    type Domain = DenseBitSet<Task>;
    type Direction = Forward;

    const NAME: &'static str = "logically_parallel_tasks";

    fn bottom_value(&self, _body: &rustc_middle::mir::Body<'tcx>) -> <Self as Analysis<'tcx>>::Domain {
        DenseBitSet::new_empty(self.task_info.num_tasks())
    }

    fn initialize_start_block(
        &self,
        _body: &rustc_middle::mir::Body<'tcx>,
        state: &mut <Self as Analysis<'tcx>>::Domain,
    ) {
        // Task 0 is initially executing at the beginning of the start block.
        state.insert(Task::from_usize(0));
    }

    fn apply_primary_statement_effect(
        &self,
        _state: &mut Self::Domain,
        _statement: &mir::Statement<'tcx>,
        _location: mir::Location,
    ) {
        // Nothing here since no statement affects the currently-parallel task set,
        // only terminators can do that.
    }

    fn apply_call_return_effect(
        &self,
        _trans: &mut <Self as Analysis<'tcx>>::Domain,
        _block: mir::BasicBlock,
        _return_places: mir::CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing here since returning doesn't affect the currently-parallel task set.
        // Terminator handling should still run in addition to this function since this
        // function just corresponds to a successfuly return.
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        state: &mut Self::Domain,
        term: &'mir rustc_middle::mir::Terminator<'tcx>,
        loc: mir::Location,
    ) -> rustc_middle::mir::TerminatorEdges<'mir, 'tcx> {
        // NOTE(jhilton): I think our handling of unwinds (or lack thereof) is fine
        // here since we won't be querying anything in the unwind subgraph.
        let kind = &term.kind;
        if let mir::TerminatorKind::Detach { spawned_task, continuation } = kind {
            // At a detach, both the spawned task and the current task are logically
            // in parallel.
            let spawned_task = self.task_info.expect_task(*spawned_task);
            let continuation_task = self.task_info.expect_task(*continuation);
            state.insert(spawned_task);
            state.insert(continuation_task);
        } else if let mir::TerminatorKind::Reattach { continuation: _ } = kind {
            // All descendants of the spawned task should be logically parallel here
            // since the continuation can be executing in parallel with any point in
            // the spawned task.
            let current_task = self.task_info.expect_task(loc.block);
            state.gen_all(self.task_info.descendants(current_task));
        } else if let mir::TerminatorKind::Sync { target: _ } = kind {
            // Syncs wait for any descendant of the current task, so
            // none of those descendants can be logically in parallel
            // after the sync.
            let current_task = self.task_info.expect_task(loc.block);
            state.kill_all(self.task_info.descendants(current_task));
        }

        term.edges()
    }
}
