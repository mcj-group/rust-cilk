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
//!   * [`create_continuation_region`] — fresh region var, marked live at a
//!     supplied set of points.
//!   * [`add_extension_constraint`]   — push the `'?b: '?c` outlives edge.
//!
//! The two pieces still missing are the task-scope analysis (pair each
//! `Reattach` with its matching `Sync` and enumerate the points between them)
//! and the upvar-aware enumeration of borrow regions belonging to the task.

use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::mir::{ConstraintCategory, Location};
use rustc_middle::ty::RegionVid;
use rustc_span::Span;

use crate::BorrowckInferCtxt;
use crate::constraints::OutlivesConstraint;
use crate::renumber::RegionCtxt;
use crate::type_check::{Locations, MirTypeckRegionConstraints};

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