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
use crate::flowgraph::{BasicBlock, ControlFlowGraph};
use crate::ir::{Ebb, Function, Inst, InstBuilder, Value, ValueDef};
use crate::ir::{ExpandedProgramPoint, ProgramOrder};
use crate::isa::TargetIsa;
use crate::regalloc::live_value_tracker::LiveValueTracker;
use crate::regalloc::liveness::Liveness;
use crate::timing;
use crate::topo_order::TopoOrder;
use core::cmp::Ordering;
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

type Renamed = SparseMap<Value, SplitValue>;

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
type AllDF = SecondaryMap<Ebb, SparseEbbSet>;

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

        self.insert_temps(&mut renamed);
        self.collect_uses(&mut renamed);

        for renamed in renamed.as_slice() {
            debug!(
                "Renamed {} -> {:?}, {:?}",
                renamed.value, renamed.new_names, renamed.uses
            );
        }

        let df = self.compute_dominance_frontiers();

        debug!("Dominance frontiers {:?}", df);

        self.rename_uses(df, renamed);
    }

    fn rename_uses(&mut self, df: AllDF, mut renamed: Renamed) {
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
            let mut worklist = r.uses.clone(); // Really we should be able to just own this...
            let mut i = 0;
            while i < worklist.len() {
                let use_inst = worklist[i];
                i += 1;
                let (found, inserted) =
                    self.find_redefinition(use_inst, r.value, &r.new_names, &idf);
                if let Some(new_defn) = found {
                    // Found a new definition, rename the first use in use_inst with a reference to
                    // this definition.
                    debug!(
                        "Replace a use of {} with a use of {}",
                        r.value, new_defn
                    );
                    for arg in self.cur.func.dfg.inst_args_mut(use_inst) {
                        if *arg == r.value {
                            *arg = new_defn;
                        }
                    }
                }
                if let Some((phi_name, mut new_uses)) = inserted {
                    r.new_names.push(phi_name);
                    worklist.append(&mut new_uses);
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
    // If the target ebb is in the iterated dominance frontier for the original name and does not
    // otherwise have a redefinition, then we insert a phi in the target ebb to act as a
    // redefinition, and we return the name defined by the phi.  Inserting a phi also adds uses of
    // the original name to all predecessor blocks, so they become new uses.
    //
    // Thus we return a triple: the redefinition we've chosen; optionally a new
    // definition; and optionally new uses for the original name in predecessor blocks.

    fn find_redefinition(&mut self, use_inst: Inst, name: Value, new_names: &Vec<Value>, idf: &IDF)
                         -> (Option<Value>, Option<(Value, Vec<Inst>)>) {
        let layout = &self.cur.func.layout;
        let dfg = &mut self.cur.func.dfg;

        let use_pp = ExpandedProgramPoint::from(use_inst);
        let use_ebb = layout.inst_ebb(use_inst).unwrap();

        // EBB NOT OK HERE
        let mut target_ebb = layout.inst_ebb(use_inst).expect("not in layout");
        let mut found = None;
        let mut phi_info = None;

        'find_closest_defn:
        loop {
            // Search target_ebb for the closest preceding definition (if target_ebb == use_ebb), or
            // the last definition (otherwise).

            let mut max_defn_pp = ExpandedProgramPoint::from(target_ebb);
            for new_defn in new_names.into_iter() {
                let (defn_ebb, defn_pp) = match dfg.value_def(*new_defn) {
                    ValueDef::Result(defn_inst, _) =>
                        (layout.inst_ebb(defn_inst).unwrap(),
                         ExpandedProgramPoint::from(defn_inst)),
                    ValueDef::Param(defn_ebb, _) =>
                        (defn_ebb, ExpandedProgramPoint::from(defn_ebb))
                };

                if defn_ebb != target_ebb {
                    continue;
                }

                // EBB NOT OK HERE
                if target_ebb != use_ebb || layout.cmp(defn_pp, use_pp) == Ordering::Less {
                    if found.is_none() || layout.cmp(max_defn_pp, defn_pp) == Ordering::Less {
                        found = Some(*new_defn);
                        max_defn_pp = defn_pp;
                    }
                }
            }

            // If we found a definition we're done.

            if found.is_some() {
                break 'find_closest_defn;
            }

            // The target_ebb had no definition.  If there's a dominator, then either target_ebb is
            // in the IDF of `name` and we must insert a phi (and use this phi as our result), or we
            // walk up to target_ebb's immediate dominator and search there.

            // EBB NOT OK HERE

            match self.domtree.idom(target_ebb) {
                None => {
                    break 'find_closest_defn;
                }
                Some(idom) => {
                    if idf.contains_key(target_ebb) {
                        let phi_name = dfg.append_ebb_param(target_ebb, dfg.value_type(name));
                        let mut new_uses = vec![];
                        for BasicBlock { inst, .. } in self.cfg.pred_iter(target_ebb) {
                            dfg.append_inst_arg(inst, name);
                            new_uses.push(inst);
                        }
                        found = Some(phi_name);
                        phi_info = Some((phi_name, new_uses));
                        break 'find_closest_defn;
                    } else {
                        target_ebb = layout.inst_ebb(idom).expect("idom not in layout");
                    }
                }
            }
        }

        (found, phi_info)
    }

    // Compute the Dominance Frontier for all nodes.  Taken from:
    //
    //   Keith D. Cooper and Linda Torczon, Engineering a Compiler, 1st Ed, sect 9.3.2.
    //
    // FIXME: This may not be correct for EBBs with side exits?

    /*

Here ebb2 is the join point.  Its idom is ebb0.  It has 2 predecessors, ebb3 and ebb5.  But only the
first part of ebb0 is the idom of ebb2, the second part of ebb0 is not.  This is a bit of a mess.

The value returned from the idom() function actually encodes this by representing the idom as
the control flow instruction, that is, the idom of ebb2 is the brz.  Then we make a mistake by
mapping that instruction to its ebb.

In the case of the definition search, there may be a risk that we find a definition that is past the
CFI that terminates the BB.  So that has to be fixed too.

But for the DF computation, we can't use EBBs like we do - it's just wrong.  We need to use BBs somehow.

A BB is thus a linear range of instructions within an ebb, but if the ebb can have multiple side
exits there can be more than two BBs.  It's uncertain what the idom computation does about that; we
need to investigate.  It should return the preceding range in the same ebb.

                                ebb0(v0: i32, v1: i64):
                                    v10 -> v0
@0044 [RexOp1tjccb#74]              brz v0, ebb4
@0048 [Op1call_id#e8]               v12 = call fn0(v1)
@0048 [null#00]                     v5 = ireduce.i32 v12
@004c [RexOp1rr#01]                 v6 = iadd v5, v0
@004d [Op1jmpb#eb]                  jump ebb3(v6)

                                ebb3(v4: i32):
@004e [Op1jmpb#eb]                  jump ebb2(v4)

                                ebb4:
@0055 [RexOp1r_ib#83]               v9 = iadd_imm.i32 v0, 1
@0056 [Op1jmpb#eb]                  jump ebb5(v9)

                                ebb5(v7: i32):
@0057 [Op1jmpb#eb]                  jump ebb2(v7)

                                ebb2(v3: i32):
@005a [RexOp1rr#01]                 v11 = iadd v3, v0
@005b [Op1jmpb#eb]                  jump ebb1(v11)

                                ebb1(v2: i32):
@005b [RexOp1umr#89]                v13 = uextend.i64 v2
@005b [-]                           fallthrough_return v13

     */
    
    //But the tail only has one predecessor.
    //
    // FIXME: does this affect the idom walk when we look for a definition too?

    fn compute_dominance_frontiers(&self) -> AllDF {
        let mut df = AllDF::new();

        // EBB NOT OK HERE

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
    // in question.  This is a straightforward worklist algorithm, the central fact is that DF(S)
    // for a set S of nodes is the union of DF(x) across x in S.  See:
    //
    //   Ron Cytron, Jeanne Ferrante, Barry K Rosen and Mark N Wegman, Efficiently Computing Static
    //   Single Assignment Form and the Control Dependence Graph, ACM TOPLAS vol 13, no 4, Oct 1991.

    fn compute_idf(&mut self, df: &AllDF, name: Value, new_names: &Vec<Value>) -> IDF {
        let mut worklist = vec![];
        let mut in_worklist = SparseEbbSet::new();

        // EBB NOT OK HERE

        {
            let start = self.defining_ebb(name);
            worklist.push(start);
            in_worklist.insert(start);
        }
        for n in new_names {
            debug!("  New name {}", *n);
            let block = self.defining_ebb(*n);
            if !in_worklist.contains_key(block) {
                worklist.push(block);
                in_worklist.insert(block);
            }
        }

        debug!("  Worklist {:?}", worklist);
        let mut idf = IDF::new();
        while let Some(block) = worklist.pop() {
            debug!("  Processing {}", block);
            for dblock in &df[block] {
                if !idf.contains_key(dblock) {
                    idf.insert(dblock);
                }
                if !in_worklist.contains_key(dblock) {
                    worklist.push(dblock);
                    in_worklist.insert(dblock);
                }
            }
        }

        idf
    }

    // EBB NOT OK HERE

    fn defining_ebb(&self, defn:Value) -> Ebb {
        match self.cur.func.dfg.value_def(defn) {
            ValueDef::Param(defn_ebb, _) => defn_ebb,
            ValueDef::Result(defn_inst, _) => self.cur.func.layout.inst_ebb(defn_inst).unwrap()
        }
    }


    // Insert copy-to-temp before a call and copy-from-temp after a call, and retain information
    // about the values that were copied and the names created after the call in `renamed`.

    fn insert_temps(&mut self, renamed: &mut Renamed) {
        // Topo-ordered traversal because we track liveness precisely.
        let mut tracker = LiveValueTracker::new();
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.ebb_insert_temps(ebb, renamed, &mut tracker);
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

    // Collect use information for all variables in `renamed`.  This will include newly inserted
    // copies.

    fn collect_uses(&mut self, renamed: &mut Renamed) {
        for ebb in self.cur.func.layout.ebbs().collect::<Vec<Ebb>>() {
            self.ebb_collect_uses(ebb, renamed);
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
