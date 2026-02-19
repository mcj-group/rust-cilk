use itertools::{Either, Itertools};
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::visit::{TyContext, Visitor};
use rustc_middle::mir::{Body, Local, Location, SourceInfo, Terminator, TerminatorKind};
use rustc_middle::ty::visit::TypeVisitable;
use rustc_middle::ty::{GenericArgsRef, Region, RegionVid, Ty, TyCtxt};
use rustc_mir_dataflow::impls::MaybeInitializedPlaces;
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_mir_dataflow::points::DenseLocationMap;
use rustc_mir_dataflow::ResultsCursor;
use std::rc::Rc;
use smallvec::SmallVec;
use crate::{
    constraints::OutlivesConstraintSet,
    facts::{AllFacts, AllFactsExt},
    location::LocationTable,
    region_infer::values::LivenessValues,
    universal_regions::UniversalRegions,
};

use super::TypeChecker;

mod local_use_map;
mod polonius;
mod trace;

/// Combines liveness analysis with initialization analysis to
/// determine which variables are live at which points, both due to
/// ordinary uses and drops. Returns a set of (ty, location) pairs
/// that indicate which types must be live at which point in the CFG.
/// This vector is consumed by `constraint_generation`.
///
/// N.B., this computation requires normalization; therefore, it must be
/// performed before
pub(super) fn generate<'mir, 'tcx>(
    typeck: &mut TypeChecker<'_, 'tcx>,
    body: &Body<'tcx>,
    elements: &Rc<DenseLocationMap>,
    flow_inits: &mut ResultsCursor<'mir, 'tcx, MaybeInitializedPlaces<'mir, 'tcx>>,
    move_data: &MoveData<'tcx>,
    location_table: &LocationTable,
    use_polonius: bool,
) {
    debug!("hellooo liveness::generate");

    let free_regions = regions_that_outlive_free_regions(
        typeck.infcx.num_region_vars(),
        typeck.borrowck_context.universal_regions,
        &typeck.borrowck_context.constraints.outlives_constraints,
    );
    let (relevant_live_locals, boring_locals) =
        compute_relevant_live_locals(typeck.tcx(), &free_regions, body);
    let facts_enabled = use_polonius || AllFacts::enabled(typeck.tcx());

    let polonius_drop_used = facts_enabled.then(|| {
        let mut drop_used = Vec::new();
        polonius::populate_access_facts(typeck, body, location_table, move_data, &mut drop_used);
        drop_used
    });

    trace::trace(
        typeck,
        body,
        elements,
        flow_inits,
        move_data,
        relevant_live_locals,
        boring_locals,
        polonius_drop_used,
    );

    // Mark regions that should be live where they appear within rvalues or within a call: like
    // args, regions, and types.
    record_regular_live_regions(
        typeck.tcx(),
        &mut typeck.borrowck_context.constraints.liveness_constraints,
        body,
    );
}

// The purpose of `compute_relevant_live_locals` is to define the subset of `Local`
// variables for which we need to do a liveness computation. We only need
// to compute whether a variable `X` is live if that variable contains
// some region `R` in its type where `R` is not known to outlive a free
// region (i.e., where `R` may be valid for just a subset of the fn body).
fn compute_relevant_live_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    free_regions: &FxHashSet<RegionVid>,
    body: &Body<'tcx>,
) -> (Vec<Local>, Vec<Local>) {
    let (boring_locals, relevant_live_locals): (Vec<_>, Vec<_>) =
        body.local_decls.iter_enumerated().partition_map(|(local, local_decl)| {
            if tcx.all_free_regions_meet(&local_decl.ty, |r| free_regions.contains(&r.as_var())) {
                Either::Left(local)
            } else {
                Either::Right(local)
            }
        });

    debug!("{} total variables", body.local_decls.len());
    debug!("{} variables need liveness", relevant_live_locals.len());
    debug!("{} regions outlive free regions", free_regions.len());

    (relevant_live_locals, boring_locals)
}

/// Computes all regions that are (currently) known to outlive free
/// regions. For these regions, we do not need to compute
/// liveness, since the outlives constraints will ensure that they
/// are live over the whole fn body anyhow.
fn regions_that_outlive_free_regions<'tcx>(
    num_region_vars: usize,
    universal_regions: &UniversalRegions<'tcx>,
    constraint_set: &OutlivesConstraintSet<'tcx>,
) -> FxHashSet<RegionVid> {
    // Build a graph of the outlives constraints thus far. This is
    // a reverse graph, so for each constraint `R1: R2` we have an
    // edge `R2 -> R1`. Therefore, if we find all regions
    // reachable from each free region, we will have all the
    // regions that are forced to outlive some free region.
    let rev_constraint_graph = constraint_set.reverse_graph(num_region_vars);
    let fr_static = universal_regions.fr_static;
    let rev_region_graph = rev_constraint_graph.region_graph(constraint_set, fr_static);

    // Stack for the depth-first search. Start out with all the free regions.
    let mut stack: Vec<_> = universal_regions.universal_regions().collect();

    // Set of all free regions, plus anything that outlives them. Initially
    // just contains the free regions.
    let mut outlives_free_region: FxHashSet<_> = stack.iter().cloned().collect();

    // Do the DFS -- for each thing in the stack, find all things
    // that outlive it and add them to the set. If they are not,
    // push them onto the stack for later.
    while let Some(sub_region) = stack.pop() {
        stack.extend(
            rev_region_graph
                .outgoing_regions(sub_region)
                .filter(|&r| outlives_free_region.insert(r)),
        );
    }

    // Return the final set of things we visited.
    outlives_free_region
}

/// Some variables are "regular live" at `location` -- i.e., they may be used later. This means that
/// all regions appearing in their type must be live at `location`.
fn record_regular_live_regions<'tcx>(
    tcx: TyCtxt<'tcx>,
    liveness_constraints: &mut LivenessValues,
    body: &Body<'tcx>,
) {
    let mut sync_location_visitor = SyncLocationVisitor{sync_region_stack: SmallVec::new(), counter: 0, locations: SmallVec::new()};
    sync_location_visitor.visit_body(body);

    let mut visitor = LiveVariablesVisitor { 
        tcx, 
        liveness_constraints, 
        sync_locations: sync_location_visitor.locations,
        sync_region_stack: SmallVec::new(),
        counter: 0, 
    };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        visitor.visit_basic_block_data(bb, data);
    }
}

struct SyncLocationVisitor {
    sync_region_stack: SmallVec<[usize; 1]>,
    counter: usize,
    locations: SmallVec<[Location; 1]>,
}

impl<'tcx> Visitor<'tcx> for SyncLocationVisitor {
    fn visit_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        let Terminator { source_info: _, kind } = terminator;

        match kind {
            TerminatorKind::Detach { spawned_task: _, continuation: _ } => {
                self.sync_region_stack.push(self.counter);
                self.locations.push(location);
                self.counter += 1;
            } 
            TerminatorKind::Sync { .. } => {
                let index = self.sync_region_stack.pop(); // make sure this removes and returns value
                self.locations[index.expect("Expected a detach and sync region value before sync")] = location; 
            } 
            _ => { 
                self.super_terminator(terminator, location);
            }
        }
    }
}

/// Visitor looking for regions that should be live within rvalues or calls.
struct LiveVariablesVisitor<'cx, 'tcx> {
    tcx: TyCtxt<'tcx>,
    liveness_constraints: &'cx mut LivenessValues,
    sync_locations: SmallVec<[Location; 1]>,
    sync_region_stack: SmallVec<[usize; 1]>,
    counter: usize, // initialize this to 0
}

impl<'cx, 'tcx> Visitor<'tcx> for LiveVariablesVisitor<'cx, 'tcx> {
    /// We sometimes have `args` within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_args(&mut self, args: &GenericArgsRef<'tcx>, location: Location) {
        debug!("CAIATHEN LiveVariablesVisitor visit_args");
        self.record_regions_live_at(*args, location);
        self.super_args(args);
    }

    /// We sometimes have `region`s within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_region(&mut self, region: Region<'tcx>, location: Location) {
        debug!("CAIATHEN LiveVariablesVisitor visit_region");
        let sr = self.sync_region_stack.pop();
        if let Some (sr) = sr {
            self.sync_region_stack.push(sr);
            let sync_location = self.sync_locations[sr];
            debug!("CAIATHEN LiveVariablesVisitor visit_region sync_location {:?} location {:?} region {:?}", sync_location, location, region);
            self.record_regions_live_at(region, sync_location);
        }
        self.record_regions_live_at(region, location);
        self.super_region(region);
    }

    /// We sometimes have `ty`s within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_ty(&mut self, ty: Ty<'tcx>, ty_context: TyContext) {
        debug!("CAIATHEN LiveVariablesVisitor visit_ty");
        match ty_context {
            TyContext::ReturnTy(SourceInfo { span, .. })
            | TyContext::YieldTy(SourceInfo { span, .. })
            | TyContext::ResumeTy(SourceInfo { span, .. })
            | TyContext::UserTy(span)
            | TyContext::LocalDecl { source_info: SourceInfo { span, .. }, .. } => {
                span_bug!(span, "should not be visiting outside of the CFG: {:?}", ty_context);
            }
            TyContext::Location(location) => {
                self.record_regions_live_at(ty, location);
            }
        }

        self.super_ty(ty);
    }
    
    fn visit_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        let Terminator { source_info: _, kind } = terminator;

        match kind {
            TerminatorKind::Detach { spawned_task: _, continuation: _ } => {
                self.sync_region_stack.push(self.counter);
                self.counter += 1;
            } 
            TerminatorKind::Sync { .. } => {
                self.sync_region_stack.pop(); // make sure this removes and returns value
            } 
            _ => { 
                self.super_terminator(terminator, location);
            }
        }
    }
}

impl<'cx, 'tcx> LiveVariablesVisitor<'cx, 'tcx> {
    /// Some variable is "regular live" at `location` -- i.e., it may be used later. This means that
    /// all regions appearing in the type of `value` must be live at `location`.
    fn record_regions_live_at<T>(&mut self, value: T, location: Location)
    where
        T: TypeVisitable<TyCtxt<'tcx>>,
    {
        debug!("record_regions_live_at(value={:?}, location={:?})", value, location);
        self.tcx.for_each_free_region(&value, |live_region| {
            let live_region_vid = live_region.as_var();
            self.liveness_constraints.add_location(live_region_vid, location);
        });
    }
}
