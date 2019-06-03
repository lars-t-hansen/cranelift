//! Live range splitting pass (prototype).
//!
//! We split the live ranges of values that are live across function calls so as to avoid the
//! spiller flagging those values as spilled everywhere.
//!
//! We implement splitting by inserting copies of live values into temps before the call and out of
//! temps after the call and updating the SSA form to match (the values are effectively renamed).
//! The existing spiller will then flag the temps as stack-allocated, which is exactly what we want.
//!
//! This is a machine-independent proof of concept primarily for systems without callee-saves
//! registers: we create temps for all values live across calls.

// Overview.
//
// Consider a call and its context.  The `v` are live across the call; the `d` are defined by the
// call, the `u` are used by the call.  (Some of the `u` may be among the `v`.)
//
//    v1, v2, ..., vn = ...
//    ...
//    d1, d2, ..., dk = call F, u1, u2, ..., um
//    ...
//    ... = v1, v2, ..., vn
//
// This is rewritten as the following, where the `s` and `w` are just new values.
//
//    v1, v2, ..., vn = ...
//    ...
//    s1 = copy v1
//    s2 = copy v2
//    ...
//    sn = copy vn
//    d1, d2, ..., dk = call F, u1, u2, ..., um
//    w1 = copy s1
//    w2 = copy s2
//    ...
//    wn = copy sn
//    ...
//    ... = w1, w2, ..., wn
//
// In the case where the `v` is a constant, it is even simpler: we do not introduce an `s` for it,
// but instead create a new `const` instruction for the value it when we create the `w` after the
// call.
//
// In general the introduction of copies like this requires a renaming of values throughout the
// CFG, which may result in the insertion of new phi nodes, see:
//
//   M. Braun, S. Hack: Register Spilling and Live-Range Splitting for SSA-Form Programs, in
//   Compiler Construction 2009, LNCS Volume 5501.  (This references a 1998 paper by Sastry and Ju
//   for an SSA renaming algorithm but Hack's dissertation (below) has the better description.)
//
//   S. Hack: Register Allocation for Programs in SSA Form, PhD Dissertation, University of
//   Karlsruhe, 2006.

use crate::cursor::{Cursor, EncCursor};
use crate::dominator_tree::DominatorTree;
use crate::entity::{SecondaryMap, SparseMap, SparseMapValue};
use crate::flowgraph::ControlFlowGraph;
use crate::ir::{Ebb, Function, Inst, InstBuilder, Value, ValueDef};
use crate::ir::{ExpandedProgramPoint, ProgramOrder};
use crate::isa::TargetIsa;
use crate::regalloc::live_value_tracker::LiveValueTracker;
use crate::regalloc::liveness::Liveness;
use crate::timing;
use crate::topo_order::TopoOrder;
use core::cmp;
use log::debug;
use std::vec::Vec;

/// Tracks a value and its uses, and its new names.
struct SplitValue {
    value: Value,
    new_names: Vec<Value>,
    uses: Vec<Inst>,
}

impl SparseMapValue<Value> for SplitValue {
    fn key(&self) -> Value {
        self.value
    }
}

impl SplitValue {
    fn new(value: Value) -> Self {
        Self {
            value,
            new_names: vec![],
            uses: vec![],
        }
    }
}

/// Persistent data structures for the splitting pass.
pub struct Splitting {
}

/// Context data structure that gets instantiated once per pass.
struct Context<'a> {
    liveness: &'a Liveness,

    // Current instruction as well as reference to function and ISA.
    cur: EncCursor<'a>,

    // References to contextual data structures we need.
    cfg: &'a ControlFlowGraph,
    domtree: &'a DominatorTree,
    topo: &'a mut TopoOrder,
}

type Renamed = SparseMap<Value, SplitValue>;

/// Simple sparse set of Ebb values, currently just a dense vector.  We can do better but we want
/// profiling data.  This is used for Dominance Frontiers, and they are normally quite small.
#[derive(Clone, Debug)]
struct SparseEbbSet {
    dense: Vec<Ebb>
}

impl SparseEbbSet {
    fn new() -> Self {
        Self {
            dense: vec![]
        }
    }

    fn insert(&mut self, key: Ebb) {
        if !self.contains_key(key) {
            self.dense.push(key);
        }
    }

    fn contains_key(&self, key: Ebb) -> bool {
        for x in &self.dense {
            if *x == key {
                return true;
            }
        }
        return false;
    }

    fn iter(&self) -> SparseEbbSetIterator {
        SparseEbbSetIterator {
            dense: &self.dense,
            next: 0
        }
    }
}

impl Default for SparseEbbSet {
    fn default() -> Self {
        SparseEbbSet::new()
    }
}

impl<'a> IntoIterator for &'a SparseEbbSet {
    type Item = Ebb;
    type IntoIter = SparseEbbSetIterator<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

struct SparseEbbSetIterator<'a> {
    dense: &'a Vec<Ebb>,
    next: usize
}

impl<'a> Iterator for SparseEbbSetIterator<'a> {
    type Item = Ebb;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next == self.dense.len() {
            None
        } else {
            let cur = self.next;
            self.next += 1;
            Some(self.dense[cur])
        }
    }
}

type IDF = SparseEbbSet;

impl Splitting {
    /// Create a new splitting data structure.
    pub fn new() -> Self {
        Self {
        }
    }

    /// Clear all data structures in this splitting pass.
    pub fn clear(&mut self) {
    }

    /// Run the splitting algorithm over `func`.
    pub fn split_across_calls(
        &mut self,
        isa: &TargetIsa,
        func: &mut Function,
        cfg: &ControlFlowGraph,
        domtree: &DominatorTree,
        liveness: &Liveness,
        topo: &mut TopoOrder,
    ) {
        let _tt = timing::ra_splitting();
        debug!("Splitting across calls for:\n{}", func.display(isa));
        let mut ctx = Context {
            cur: EncCursor::new(func, isa),
            cfg,
            domtree,
            liveness,
            topo,
        };
        ctx.run()
    }
}

impl<'a> Context<'a> {
    fn run(&mut self) {
        let mut renamed = Renamed::new();

        // Insert copy-to-temp before a call and copy-from-temp after a call, and retain information
        // about the values that were copied and the names created after the call in `renamed`.
        let mut tracker = LiveValueTracker::new();
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.ebb_insert_temps(ebb, &mut renamed, &mut tracker);
        }

        // Collect use information for all variables in `renamed`.  This will include newly inserted
        // copies.
        for ebb in self.cur.func.layout.ebbs().collect::<Vec<Ebb>>() {
            self.ebb_collect_uses(ebb, &mut renamed);
        }

        for renamed in renamed.as_slice() {
            debug!(
                "Renamed {} -> {:?}, {:?}",
                renamed.value, renamed.new_names, renamed.uses
            );
        }

        // We'll need the dominance frontiers for many nodes, so compute for all.  (Technically we
        // need the DF for the nodes containing the old definition of a name and the new
        // definitions, and it's possible we can compute them just for that set.)
        let df = self.compute_df();

        debug!("Dominance frontiers {:?}", df);

        // TODO: This feels deeply wrong
        let mut keys = vec![];
        for renamed in renamed.into_iter() {
            keys.push(renamed.value);
        }

        // Correct the references to renamed variables and insert phis if necessary.
        for key in keys {
            let r = renamed.get_mut(key).unwrap();
            debug!("Renaming {}", r.value);
            let idf = self.compute_idf(&df, r.value, &r.new_names);
            debug!("  IDF {:?}", idf);
            for use_inst in &r.uses {
                if let Some(new_defn) =
                    self.find_redefinition(*use_inst, r.value, &mut r.new_names, &idf)
                {
                    // Found a new definition, rename the first use in use_inst with a reference to
                    // this definition.
                    debug!(
                        "Replace a use of {} with a use of {}",
                        r.value, new_defn
                    );
                    for arg in self.cur.func.dfg.inst_args_mut(*use_inst) {
                        if *arg == r.value {
                            *arg = new_defn;
                        }
                    }
                }
            }
        }
    }

    // Search for a redefinition in each ebb up the dominator tree from the use.  We may reach the
    // top without finding anything.
    //
    // If the target ebb has a redefinition, then pick the latest such definition in the block,
    // except that if the target ebb is the ebb with the use then pick the latest definition that
    // precedes the use.
    //
    // TODO: insert phis where required
    fn find_redefinition(&self, use_inst: Inst, name: Value, new_names: &mut Vec<Value>, idf: &IDF) -> Option<Value> {
        let use_pp = ExpandedProgramPoint::from(use_inst);
        let layout = &self.cur.func.layout;
        let mut target_ebb = layout.inst_ebb(use_inst).expect("not in layout");
        let mut is_use_ebb = true;
        let mut found = None;
        loop {
            let mut max_defn_pp = ExpandedProgramPoint::from(target_ebb);
            for new_defn in new_names.into_iter() {
                let defn_inst = self.cur.func.dfg.value_def(*new_defn).unwrap_inst();
                let defn_ebb = layout.inst_ebb(defn_inst).expect("not in layout");
                let defn_pp = ExpandedProgramPoint::from(defn_inst);
                if defn_ebb == target_ebb
                    && (!is_use_ebb || layout.cmp(defn_pp, use_pp) == cmp::Ordering::Less)
                {
                    if found.is_none() || layout.cmp(max_defn_pp, defn_pp) == cmp::Ordering::Less {
                        found = Some(*new_defn);
                        max_defn_pp = defn_pp;
                    }
                }
            }
            if found.is_some() {
                break;
            }

            // Walk up the dominator tree to target_ebb's dominator.
            //
            // TODO: If we cross the IDF, which is to say, target_ebb is in the IDF set and we
            // succeed in walking up, then we must insert the old target_ebb into the set of Ebbs
            // that needs phis.  For this we also need the original name (whatever we were renamed
            // from).
            //
            // (This is true even if we ultimately do not find a redefinition along the current
            // path; that is a feature of the IDF.)
            //
            // When we create the phi we also create a new name, and that is the name that we must
            // return from this function, and I'm strongly inclined to say that we must insert the
            // name into new_names so that subsequent uses in the same area will find the same
            // definition.  Since we're on the IDF, we don't need to do anything more.
            //
            // How do we track phi insertion?
            //
            //   - we're going to add a new parameter to the ebb, this is a new name `zappa`
            //   - for each of the predecessors' outgoing edges to this block, we're going to
            //     pass a value in the position of `zappa`.  this value is not necessarily the
            //     original name, but the name of the most recent definition in *that* position.
            //     this seems to invoke renaming / phi insertion recursively, and it may mean
            //     that "phi insertion" happens right here, not in a subsequent pass.
            //
            // So:
            // - IDF should be able to test for set/map membership
            // - IDF is probably sparse (a small number of Ebbs per name)
            // - We need a set of (name,Ebbs) that need phis
            // - When we find an Ebb that needs a phi then this new phi will provide the redefinition
            //   name we're looking for and the search will stop here (so we don't walk up after all)

            is_use_ebb = false;
            match self.domtree.idom(target_ebb) {
                Some(idom) => {
                    target_ebb = layout.inst_ebb(idom).expect("idom not in layout");
                }
                None => {
                    break;
                }
            }
        }

        found
    }

    // Compute the Dominance Frontier for all nodes.  See Cooper & Torczon, 1st Ed, 9.3.2.
    fn compute_df(&self) -> SecondaryMap<Ebb, SparseEbbSet> {
        let mut df = SecondaryMap::<Ebb, SparseEbbSet>::new();
        for n in self.cur.func.layout.ebbs() {
            // Ugly hack, we just want the number of predecessors first, and then we can iterate
            // peacefully over the list.  And the pred_iter wraps the ebb in a BasicBlock and here
            // we just strip it again; There Must Be A Better Way.
            let preds: Vec<Ebb> = self.cfg.pred_iter(n).map(|bb| bb.ebb).collect();
            if preds.len() >= 2 {
                let idom_n = self.cur.func.layout.inst_ebb(self.domtree.idom(n).unwrap()).unwrap();
                for p in preds {
                    let mut runner = p;
                    while runner != idom_n {
                        df[runner].insert(n);
                        runner = self.cur.func.layout.inst_ebb(self.domtree.idom(runner).unwrap()).unwrap();
                    }
                }
            }
        }
        df
    }

    // Compute the Iterated Dominance Frontier for the nodes containing the definitions of the name
    // in question.  This is a straightforward worklist algorithm derived from Cytron et al 1991,
    // the central fact is that DF(S) for a set S of nodes is the union of DF(x) across x in S.
    fn compute_idf(&mut self, df:&SecondaryMap<Ebb, SparseEbbSet>, name: Value, new_names: &Vec<Value>) -> IDF {
        let mut worklist = vec![];
        worklist.push(self.defining_ebb(name));
        for n in new_names {
            worklist.push(self.defining_ebb(*n));
        }

        let mut in_worklist = SparseEbbSet::new();
        for block in &worklist {
            in_worklist.insert(*block);
        }

        let mut idf = SparseEbbSet::new();
        while let Some(block) = worklist.pop() {
            for dblock in &df[block] {
                if !idf.contains_key(dblock) {
                    idf.insert(dblock);
                }
                if !in_worklist.contains_key(dblock) {
                    worklist.push(dblock);
                }
            }
        }

        idf
    }

    fn defining_ebb(&self, defn:Value) -> Ebb {
        match self.cur.func.dfg.value_def(defn) {
            ValueDef::Param(defn_ebb, _) => defn_ebb,
            ValueDef::Result(defn_inst, _) => self.cur.func.layout.inst_ebb(defn_inst).unwrap()
        }
    }

    fn ebb_insert_temps(&mut self, ebb: Ebb, renamed: &mut Renamed,
                        tracker: &mut LiveValueTracker) {
        self.cur.goto_top(ebb);
        tracker.ebb_top(
            ebb,
            &self.cur.func.dfg,
            self.liveness,
            &self.cur.func.layout,
            self.domtree,
        );
        tracker.drop_dead_params();

        self.cur.goto_first_inst(ebb);
        while let Some(inst) = self.cur.current_inst() {
            if !self.cur.func.dfg[inst].opcode().is_ghost() {
                // visit_inst() applies the tracker and advances the instruction
                self.inst_insert_temps(inst, ebb, renamed, tracker);
            } else {
                let (_throughs, _kills) = tracker.process_ghost(inst);
                self.cur.next_inst();
            }
            tracker.drop_dead(inst);
        }
    }

    fn inst_insert_temps(&mut self, inst: Inst, ebb: Ebb, renamed: &mut Renamed,
                         tracker: &mut LiveValueTracker)
    {
        debug_assert_eq!(self.cur.current_inst(), Some(inst));
        debug_assert_eq!(self.cur.current_ebb(), Some(ebb));

        self.cur.use_srcloc(inst);

        // Update the live value tracker with this instruction.
        let (throughs, _kills, _defs) =
            tracker.process_inst(inst, &self.cur.func.dfg, self.liveness);

        // If inst is a call, copy all register values that are live across the call into a temp
        // across the call, so that the temps can be spilled but the values themselves can stay in
        // registers.
        //
        // TODO: This is suboptimal if one of those values will be spilled anyway, that's an
        // argument for integrating this splitting into the spilling phase.
        //
        // TODO: This ignores callee-saved registers.
        //
        // TODO: We can avoid saving values that can be rematerialized cheaply, namely, constants
        // and any results of a GlobalValue computation.  In these cases, we must still insert code
        // after the call (to rematerialize) but no code before the call.

        let call_sig = self.cur.func.dfg.call_signature(inst);
        if call_sig.is_some() {
            // Create temps before the instruction
            let mut temps = vec![];
            for lv in throughs {
                if lv.affinity.is_reg() {
                    let temp = self.cur.ins().copy(lv.value);
                    temps.push(temp);
                }
            }
            // Move to next instruction so that we can insert copies after the call
            self.cur.next_inst();
            // Create copies of the temps after the instruction
            let mut i = 0;
            for lv in throughs {
                if lv.affinity.is_reg() {
                    let temp = temps[i];
                    i += 1;
                    let copy = self.cur.ins().copy(temp);
                    //let inst = self.cur.built_inst();
                    if let Some(r) = renamed.get_mut(lv.value) {
                        r.new_names.push(copy);
                    } else {
                        let mut r = SplitValue::new(lv.value);
                        r.new_names.push(copy);
                        renamed.insert(r);
                    }
                }
            }
        } else {
            self.cur.next_inst();
        }
    }

    fn ebb_collect_uses(&mut self, ebb: Ebb, renamed: &mut Renamed) {
        self.cur.goto_top(ebb);
        while let Some(inst) = self.cur.next_inst() {
            // Now inspect all the uses and if one is a Value defined in renamed, record this
            // instruction with that info.
            //
            // TODO: ideally we only record it once, though that requires additional filtering.  As
            // it happens, recording it multiple times is not bad, it means we'll visit the
            // instruction with the use several times but each time we'll replace one use with the
            // new one.  On the other hand, that means multiple searches up the tree.  On the third
            // hand, how often is this an issue?
            for arg in self.cur.func.dfg.inst_args(inst) {
                if let Some(info) = renamed.get_mut(*arg) {
                    info.uses.push(inst);
                }
            }
        }
    }
}
