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
//
// One wrinkle is that many algorithms for SSA munging are expressed in terms of basic blocks and
// not extended basic blocks, and are incorrect if we ignore the distinction.  This is in particular
// true of dominance frontiers.  Hence we have to translate from Ebbs to BBs in this module.

use crate::cursor::{Cursor, EncCursor};
use crate::dominator_tree::DominatorTree;
use crate::entity::{SecondaryMap, SparseMap, SparseMapValue, SparseSet};
use crate::flowgraph::{BasicBlock, ControlFlowGraph};
use crate::ir::{Ebb, Function, Inst, InstBuilder, Opcode, InstructionData, Value, ValueDef};
use crate::ir::{ExpandedProgramPoint, ProgramOrder};
use crate::isa::TargetIsa;
use crate::regalloc::live_value_tracker::LiveValueTracker;
use crate::regalloc::liveness::Liveness;
use crate::timing;
use crate::topo_order::TopoOrder;
use core::cmp::Ordering;
use log::debug;
use std::vec::Vec;

/// Tracks a renamed value, its uses, and its new names.
struct RenamedValue {
    value: Value,
    new_names: Vec<Value>,
    uses: Vec<Inst>,
}

impl SparseMapValue<Value> for RenamedValue {
    fn key(&self) -> Value {
        self.value
    }
}

impl RenamedValue {
    fn new(value: Value) -> Self {
        RenamedValue {
            value,
            new_names: vec![],
            uses: vec![],
        }
    }
}

/// A map from the original names to information about their renamings.
type Renamed = SparseMap<Value, RenamedValue>;

/// Sparse set of BB values.
#[derive(Clone, Debug)]
struct SparseBBSet {
    /// Just a dense vector.  We can do better but we want profiling data.  This is used for
    /// Dominance Frontiers and worklist marking sets, and they are normally quite small.
    dense: Vec<BB>
}

impl SparseBBSet {
    /// Create an empty set.
    fn new() -> Self {
        Self {
            dense: vec![]
        }
    }

    /// Insert the key into the set, does nothing if the key is already present.
    fn insert(&mut self, key: BB) {
        if !self.contains_key(key) {
            self.dense.push(key);
        }
    }

    /// Test whether the key is in the set.
    fn contains_key(&self, key: BB) -> bool {
        for x in &self.dense {
            if *x == key {
                return true;
            }
        }
        return false;
    }

    /// Create an iterator over the set.
    fn iter(&self) -> SparseBBSetIterator {
        SparseBBSetIterator {
            dense: &self.dense,
            next: 0
        }
    }

    fn is_empty(&self) -> bool {
        self.dense.len() == 0
    }
}

impl Default for SparseBBSet {
    fn default() -> Self {
        SparseBBSet::new()
    }
}

impl<'a> IntoIterator for &'a SparseBBSet {
    type Item = BB;
    type IntoIter = SparseBBSetIterator<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

struct SparseBBSetIterator<'a> {
    dense: &'a Vec<BB>,
    next: usize
}

impl<'a> Iterator for SparseBBSetIterator<'a> {
    type Item = BB;
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

/// A basic block (BB) is represented as the control transfer instruction within an Ebb that ends
/// the BB.  Given a BB we can map it to its containing Ebb using layout.inst_ebb(), and then we can
/// find the relative position of the BB within the Ebb by scanning the information associated with
/// the Ebb.
///
/// At the first BB in an Ebb:
/// - the domtree.idom() method is applied to the Ebb and yields the BB that is the idom
/// - the cfg.pred_iter() method is applied to the Ebb and yields the BBs that are the predecessors
///
/// At the non-first BB in an Ebb:
/// - its idom is the preceding BB in the Ebb
/// - its only predecessor is the preceding BB in the Ebb
type BB = Inst;

/// A basic block graph is represented as a map from Ebbs to a list of the BBs that are in the EBB,
/// in order.
#[derive(Debug)]
struct BBGraph {
    info: SecondaryMap<Ebb, Vec<BB>>
}

impl<'a> BBGraph {
    fn new() -> Self {
        Self {
            info: SecondaryMap::new()
        }
    }

}

type IDF = SparseBBSet;
type AllDF = SecondaryMap<BB, SparseBBSet>;

#[derive(Clone)]
struct SpilledValue {
    key: Value,
    spill: Value
}

impl SparseMapValue<Value> for SpilledValue {
    fn key(&self) -> Value {
        self.key
    }
}

impl SpilledValue {
    fn new(key: Value, spill: Value) -> Self {
        Self { key, spill }
    }
}

struct SpillMap {
    key: Option<BB>,
    spills: SparseMap<Value, SpilledValue>
}

impl SparseMapValue<BB> for SpillMap {
    fn key(&self) -> BB {
        self.key.unwrap()
    }
}

impl SpillMap {
    fn new() -> Self {
        Self {
            key: None,
            spills: SparseMap::new()
        }
    }
    fn init_from(&self, other: &SpillMap) -> Self {
        let mut new_map = SparseMap::new();
        for x in other.spills.as_slice() {
            new_map.insert(x.clone());
        }
        Self { key: None, spills: new_map }
    }
    fn get(&self, v:Value) -> Option<&SpilledValue> {
        self.spills.get(v)
    }
    fn insert(&mut self, v:SpilledValue) {
        self.spills.insert(v);
    }
}

// TODO: This is a terrible data structure because the sets of available temps grow ever larger as
// we descend the dominator tree.  We really should implement some kind of sharing.  It need not be
// hard.

struct SpillTracker {
    maps: SparseMap<BB, SpillMap>
}

impl SpillTracker {
    fn new() -> Self {
        Self {
            maps: SparseMap::new()
        }
    }
    fn get(&self, bb: BB) -> Option<&SpillMap> {
        self.maps.get(bb)
    }
    fn insert(&mut self, bb: BB, mut spills: SpillMap) {
        spills.key = Some(bb);
        self.maps.insert(spills);
    }
}

type DefSet = SparseSet<Value>;

/// Persistent data structures for the splitting pass.
pub struct Splitting {
}

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
            bbgraph: BBGraph::new(),
            cur: EncCursor::new(func, isa),
            cfg,
            domtree,
            liveness,
            topo,
        };
        ctx.run()
    }
}

/// Context data structure that gets instantiated once per pass.
struct Context<'a> {
    bbgraph: BBGraph,

    liveness: &'a Liveness,

    // Current instruction as well as reference to function and ISA.
    cur: EncCursor<'a>,

    // References to contextual data structures we need.
    cfg: &'a ControlFlowGraph,
    domtree: &'a DominatorTree,
    topo: &'a mut TopoOrder,
}

impl<'a> Context<'a> {
    fn run(&mut self) {
        let mut renamed = Renamed::new();

        let ebbs = self.cur.func.layout.ebbs().collect::<Vec<Ebb>>();

        let mut new_defs = DefSet::new();

        self.compute_bbgraph(&ebbs);
        self.insert_temps(&mut renamed, &mut new_defs);
        self.collect_uses(&ebbs, &mut renamed);

        debug!("After inserting temps:\n{}", self.cur.func.display(self.cur.isa));

/*
        for renamed in renamed.as_slice() {
            debug!(
                "Renamed\n   {} -> {:?}\n         {:?}",
                renamed.value, renamed.new_names, renamed.uses
            );
        }
*/
        let df = self.compute_dominance_frontiers(&ebbs);
/*
        debug!("Basic blocks and dominance frontiers per ebb");
        for ebb in &ebbs {
            debug!("{}", *ebb);
            for bb in &self.bbgraph.info[*ebb] {
                debug!(" bb -> {:?}", *bb);
                let bb_df = &df[*bb];
                if !bb_df.is_empty() {
                    debug!("      df = {:?}", bb_df.iter().collect::<Vec<BB>>());
                }
            }
        }
*/
        self.rename_uses(df, renamed, &mut new_defs);

        // Here, go through the set of all new definitions and remove all of them from the code -
        // they were never referenced.
        for new_def in new_defs.as_slice() {
            self.cur.goto_inst(self.cur.func.dfg.value_def(*new_def).unwrap_inst());
            self.cur.remove_inst();
        }
    }

    fn rename_uses(&mut self, df: AllDF, mut renamed: Renamed, new_defs: &mut DefSet) {

        // TODO: This feels deeply wrong
        let mut keys = vec![];
        for renamed in renamed.into_iter() {
            keys.push(renamed.value);
        }

        // Whether a name is old or new doesn't matter, what matters is that we must be able to find
        // its definition.
        for key in &keys {
            let r = renamed.get_mut(*key).unwrap();
            r.new_names.push(r.value);
        }

        // Correct the references to renamed variables and insert phis if necessary.
        for key in &keys {
            let r = renamed.get_mut(*key).unwrap();
//            debug!("Renaming for {}", r.value);
            let idf = self.compute_idf(&df, &r.new_names);
//            debug!("  IDF {:?}", idf);
            let mut worklist = r.uses.clone(); // Really we should be able to just own this...
            let mut i = 0;
            while i < worklist.len() {
                let use_inst = worklist[i];
                i += 1;
//                debug!("  Processing {:?}", use_inst);
                let (found, inserted) =
                    self.find_redefinition(use_inst, r.value, &mut r.new_names, &idf);
                if let Some(new_defn) = found {
                    // Found a new definition, rename the first use in use_inst with a reference to
                    // this definition.
//                    debug!(
//                        "Replace a use of {} with a use of {}",
//                        r.value, new_defn
//                    );
                    for arg in self.cur.func.dfg.inst_args_mut(use_inst) {
                        if *arg == r.value {
                            *arg = new_defn;
                            new_defs.remove(new_defn);
                            break;
                        }
                    }
                } else {
//                    debug!("No replacement");
                }
                if let Some((phi_name, mut new_uses)) = inserted {
                    r.new_names.push(phi_name);
                    worklist.append(&mut new_uses);
                }
            }
        }
    }

    // Search for a definition in each ebb up the dominator tree from the use.  We may find the
    // original definition.
    //
    // If the target ebb has a definition, then pick the latest such definition in the block, except
    // that if the target ebb is the ebb with the use then pick the latest definition that precedes
    // the use.
    //
    // If the target ebb is in the iterated dominance frontier for the original name and does not
    // otherwise have a definition, then we insert a phi in the target ebb to act as a redefinition,
    // and we return the name defined by the phi.  Inserting a phi also adds uses of the original
    // name to all predecessor blocks, so they become new uses.
    //
    // Thus we return a triple: the redefinition we've chosen; optionally a new definition; and
    // optionally new uses for the original name in predecessor blocks.

    fn find_redefinition(&mut self, use_inst: Inst, name: Value, defns: &mut Vec<Value>, idf: &IDF)
                         -> (Option<Value>, Option<(Value, Vec<Inst>)>) {
        let use_pp = ExpandedProgramPoint::from(use_inst);
        let use_bb = self.inst_bb(use_inst);

        let mut target_bb = use_bb;

        loop {
            // If we find an existing definition for one of the defns in target_bb we're done,
            // returning the best such definition.

//            debug!("target_bb = {}, use_bb = {}", target_bb, use_bb);
            if let Some(found) =
                self.find_defn_in_bb(defns, target_bb,
                                     if use_bb == target_bb { Some(use_pp) } else { None }) {
                return (Some(found), None);
            }

            // The target_bb had no definition.  Either target_bb is in the IDF of `name` and we
            // must insert a phi (and use this phi as our result and add the CTIs that target the
            // phi as new uses), or we walk up to target_bb's immediate dominator and search there.

            if idf.contains_key(target_bb) {
                let mut new_uses = vec![];

                let target_ebb = self.bb_ebb(target_bb);
                let phi_name = self.cur.func.dfg.append_ebb_param(target_ebb, self.cur.func.dfg.value_type(name));

                // So, the following doesn't work for indirect_jump_table_br-terminated BBs since
                // that can't handle parameters.
                //
                // In that case, target_ebb should only have one predecessor and so should not be in
                // the idf and so this should not be an issue. But generated code for box2d violates
                // this: the default block is jumped to from various other blocks, but also from the
                // jump table.  Search (from the bottom) for jt0, you'll see
                //
                // jt0 = jump_table [ebb90, ebb77, ebb77, ebb77, ebb77, ebb89, ebb77, ebb77, ebb77, ebb88, ebb77, ebb77, ebb87, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb86, ebb77, ebb85, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb84, ebb77, ebb83, ebb77, ebb82, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb81, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb80, ebb77, ebb77, ebb77, ebb77, ebb79, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb77, ebb78]
                //
                // and then eg at the end of ebb90,
                //
                // @625f [Op1jmpb#eb]                  jump ebb77
                //
                // which violates the invariant.  (The invariant is documented various places.)
                //
                // Turns out the invariant is more complicated: critical edges are split during
                // bytecode->ir translation if there are parameters to pass.  This optimization then
                // precludes adding parameters later.  (code_translator.rs ca line 300)
                //
                // To add parameters later, we have to split the critical edges later, or always
                // assume that we may add parameters later.
                //
                // For now, I've "fixed" this in cranelift-wasm by always splitting edges if the
                // option is enabled for live range splitting across calls.  But this will further
                // slow down compilation and may generate worse code.

                for BasicBlock { inst: phi_inst, .. } in self.cfg.pred_iter(target_ebb) {
                    self.cur.func.dfg.append_inst_arg(phi_inst, name);
                    new_uses.push(phi_inst);
                }

                return (Some(phi_name), Some((phi_name, new_uses)));
            }

            target_bb = self.bb_idom(target_bb).unwrap();
        }
    }

    // Search target_ebb for the closest preceding definition (if target_bb == use_bb), or
    // the last definition (otherwise).

    fn find_defn_in_bb(&self, defns: &Vec<Value>, target_bb: BB, use_pp: Option<ExpandedProgramPoint>) -> Option<Value> {
        let layout = &self.cur.func.layout;

        let mut found = None;
        let mut max_defn_pp = None;

        for defn in defns {
            if let Some(defn_pp) = self.find_one_defn_in_bb(*defn, target_bb) {
                if !use_pp.is_some() || layout.cmp(defn_pp, use_pp.unwrap()) == Ordering::Less {
                    if found.is_none() || layout.cmp(max_defn_pp.unwrap(), defn_pp) != Ordering::Greater {
//                        debug!("Updating because better");
                        found = Some(*defn);
                        max_defn_pp = Some(defn_pp);
                    }
                }
            }
        }

        found
    }
        
    fn find_one_defn_in_bb(&self, defn: Value, target_bb: BB) -> Option<ExpandedProgramPoint> {
        let dfg = &self.cur.func.dfg;
//        debug!("Target name = {}", defn);
        let (defn_bb, defn_pp) = match dfg.value_def(defn) {
            ValueDef::Result(defn_inst, _) => {
//                debug!("Defn found as result in {} in {}", defn_inst, self.inst_bb(defn_inst));
                (self.inst_bb(defn_inst),
                 ExpandedProgramPoint::from(defn_inst))
            }
            ValueDef::Param(defn_ebb, _) => {
//                debug!("Defn found as parameter in {} in {}", defn_ebb, self.ebb_bb(defn_ebb));
                (self.ebb_bb(defn_ebb), ExpandedProgramPoint::from(defn_ebb))
            }
        };
        if defn_bb != target_bb {
            None
        } else {
            Some(defn_pp)
        }
    }

    // Compute the Iterated Dominance Frontier for the nodes containing the definitions of the
    // defns.  This is a straightforward worklist algorithm, the central fact is that DF(S) for a
    // set S of nodes is the union of DF(x) across x in S.  See:
    //
    //   Ron Cytron, Jeanne Ferrante, Barry K Rosen and Mark N Wegman, Efficiently Computing Static
    //   Single Assignment Form and the Control Dependence Graph, ACM TOPLAS vol 13, no 4, Oct 1991.

    fn compute_idf(&mut self, df: &AllDF, defns: &Vec<Value>) -> IDF {
        let mut worklist = vec![];
        let mut in_worklist = SparseBBSet::new();

        for n in defns {
            let block = self.defining_bb(*n);
            if !in_worklist.contains_key(block) {
                worklist.push(block);
                in_worklist.insert(block);
            }
        }

        let mut idf = IDF::new();
        while let Some(block) = worklist.pop() {
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

    fn defining_bb(&self, defn: Value) -> BB {
        match self.cur.func.dfg.value_def(defn) {
            ValueDef::Param(defn_ebb, _) => self.ebb_bb(defn_ebb),
            ValueDef::Result(defn_inst, _) => self.inst_bb(defn_inst)
        }
    }

    // Compute the Dominance Frontier for all BB nodes.  Taken from:
    //
    //   Keith D. Cooper and Linda Torczon, Engineering a Compiler, 1st Ed, sect 9.3.2.

    fn compute_dominance_frontiers(&self, ebbs:&Vec<Ebb>) -> AllDF {
        let mut df = AllDF::new();

        // The outer loop can iterate over ebbs because only ebbs can have more than one
        // predecessor.  But the predecessors are the BBs within predecessor EBBs.
        for ebb in ebbs {
            // TODO: Avoid storage allocation here if possible.
            let preds: Vec<BB> = self.cfg.pred_iter(*ebb).map(|bb| bb.inst).collect();
            if preds.len() >= 2 {
                let n = self.ebb_bb(*ebb);
                let idom_n = self.bb_idom(n).unwrap();
                for p in preds {
                    let mut runner = p;
                    while runner != idom_n {
                        df[runner].insert(n);
                        runner = self.bb_idom(runner).unwrap();
                    }
                }
            }
        }

        df
    }

    // Basic blocks.

    /// Compute and record the lists of BBs in the Ebbs.
    fn compute_bbgraph(&mut self, ebbs: &Vec<Ebb>) {
        for ebb in ebbs {
            let mut bbs = vec![];
            self.cur.goto_top(*ebb);
            let mut got_last = false;
            while let Some(inst) = self.cur.next_inst() {
                got_last = false;
                let op = self.cur.func.dfg[inst].opcode();
                if ends_bb(op) {
                    bbs.push(inst);
                    got_last = true;
                }
            }
            debug_assert!(got_last);
            debug_assert!(bbs.len() > 0);
            self.bbgraph.info[*ebb] = bbs;
        }
    }

    /// The idom of the bb, itself a bb, or None if there is no idom.
    fn bb_idom(&self, bb: BB) -> Option<BB> {
        let (ebb, _, pos) = self.inst_info(bb);
        if pos == 0 {
            self.domtree.idom(ebb)
        } else {
            Some(self.bbgraph.info.get(ebb).unwrap()[pos-1])
        }
    }
    
    // fn bb_isfirst(&self, bb: BB) -> bool {
    //     let (_, _, pos) = self.inst_info(bb);
    //     pos == 0
    // }
    
    /// First BB in the Ebb.
    fn ebb_bb(&self, ebb: Ebb) -> BB {
        self.bbgraph.info.get(ebb).unwrap()[0]
    }

    /// The Ebb containing the BB.
    fn bb_ebb(&self, bb: BB) -> Ebb {
        self.cur.func.layout.inst_ebb(bb).unwrap()
    }

    /// The BB containing the instruction.
    fn inst_bb(&self, inst: Inst) -> BB {
        let (_, bb, _) = self.inst_info(inst);
        bb
    }

    fn inst_info(&self, inst: Inst) -> (Ebb, BB, usize) {
        let ebb = self.bb_ebb(inst);
        let info = self.bbgraph.info.get(ebb).unwrap();
        let inst_pp = ExpandedProgramPoint::from(inst);
        for i in 0..info.len() {
            let bb = info[i];
            let bb_pp = ExpandedProgramPoint::from(bb);
            // Remember, bb_pp is at the end of the BB.
            if self.cur.func.layout.cmp(inst_pp, bb_pp) != Ordering::Greater { 
                return (ebb, bb, i);
            }
        }
        panic!("Should not happen");
    }

    // Insert copy-to-temp before a call and copy-from-temp after a call, and retain information
    // about the values that were copied and the names created after the call in `renamed`.

    fn insert_temps(&mut self, renamed: &mut Renamed, new_defs: &mut DefSet) {
        // Topo-ordered traversal because we track liveness precisely.
        let mut tracker = LiveValueTracker::new();
        let mut spill_tracker = SpillTracker::new();
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.ebb_insert_temps(ebb, renamed, new_defs, &mut tracker, &mut spill_tracker);
        }
    }

    fn ebb_insert_temps(&mut self, ebb: Ebb, renamed: &mut Renamed, new_defs: &mut DefSet,
                        tracker: &mut LiveValueTracker, spill_tracker: &mut SpillTracker) {
        self.cur.goto_top(ebb);
        tracker.ebb_top(
            ebb,
            &self.cur.func.dfg,
            self.liveness,
            &self.cur.func.layout,
            self.domtree,
        );
        tracker.drop_dead_params();

        // spills is the spill map for the current BB
        let mut spills = SpillMap::new();
        if let Some(idom) = self.domtree.idom(ebb) {
            if let Some(avail_spills) = spill_tracker.get(idom) {
                spills.init_from(avail_spills);
            }
        }

        self.cur.goto_first_inst(ebb);
        while let Some(inst) = self.cur.current_inst() {
            if !self.cur.func.dfg[inst].opcode().is_ghost() {
                // inst_insert_temps() applies the tracker and advances the instruction
                self.inst_insert_temps(inst, ebb, renamed, new_defs, tracker, &mut spills);
                if ends_bb(self.cur.func.dfg[inst].opcode()) {
                    spill_tracker.insert(inst, SpillMap::new().init_from(&spills));
                }
            } else {
                let (_throughs, _kills) = tracker.process_ghost(inst);
                self.cur.next_inst();
            }

            tracker.drop_dead(inst);
        }
    }

    fn inst_insert_temps(&mut self, inst: Inst, ebb: Ebb, renamed: &mut Renamed, new_defs: &mut DefSet,
                         tracker: &mut LiveValueTracker, spills: &mut SpillMap)
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

        let call_sig = self.cur.func.dfg.call_signature(inst);
        if call_sig.is_some() {

            // Create temps before the instruction
            let mut temps = vec![];
            for lv in throughs {
                if lv.affinity.is_reg() {
                    if self.is_rematerializable_constant(lv.value) {
                        continue;
                    }
                    // If we have a spill slot for this name then don't create a new one, but record
                    // the name of the existing spill slot as the source to use when filling.
                    let temp =
                        if let Some(SpilledValue { spill, .. }) = spills.get(lv.value) {
                            *spill
                        } else {
                            let spill_slot = self.cur.ins().copy(lv.value);
                            spills.insert(SpilledValue::new(lv.value, spill_slot));
                            spill_slot
                        };
                    temps.push(temp);
                }
            }

            println!("Spills: {}", temps.len());

            // Move to next instruction so that we can insert copies after the call
            self.cur.next_inst();

            // Create copies of the temps after the instruction
            let mut i = 0;
            for lv in throughs {
                if lv.affinity.is_reg() {
                    let new_def =
                        if self.is_rematerializable_constant(lv.value) {
                            self.rematerialize_constant(lv.value)
                        } else {
                            let temp = temps[i];
                            i += 1;
                            self.cur.ins().copy(temp)
                        };
                    new_defs.insert(new_def);
                    if let Some(r) = renamed.get_mut(lv.value) {
                        r.new_names.push(new_def);
                    } else {
                        let mut r = RenamedValue::new(lv.value);
                        r.new_names.push(new_def);
                        renamed.insert(r);
                    }
                }
            }
        } else {
            self.cur.next_inst();
        }
    }

    fn is_rematerializable_constant(&self, value:Value) -> bool {
        match self.cur.func.dfg.value_def(value) {
            ValueDef::Result(inst, _) => match self.cur.func.dfg[inst].opcode() {
                Opcode::Iconst | Opcode::F32const | Opcode::F64const | Opcode::Bconst => true,
                _ => false
            },
            _ => false
        }
    }

    fn rematerialize_constant(&mut self, value:Value) -> Value {
        let inst = self.cur.func.dfg.value_def(value).unwrap_inst();
        let id = &self.cur.func.dfg[inst];
        if let InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } = *id {
            let ty = self.cur.func.dfg.ctrl_typevar(inst);
            self.cur.ins().iconst(ty, imm)
        } else if let InstructionData::UnaryIeee32 { opcode: Opcode::F32const, imm } = *id {
            self.cur.ins().f32const(imm)
        } else if let InstructionData::UnaryIeee64 { opcode: Opcode::F64const, imm } = *id {
            self.cur.ins().f64const(imm)
        } else if let InstructionData::UnaryBool { opcode: Opcode::Bconst, imm } = *id {
            let ty = self.cur.func.dfg.ctrl_typevar(inst);
            self.cur.ins().bconst(ty, imm)
        } else {
            unreachable!()
        }
    }

    // Collect use information for all variables in `renamed`.  This will include newly inserted
    // copies.

    fn collect_uses(&mut self, ebbs: &Vec<Ebb>, renamed: &mut Renamed) {
        for ebb in ebbs {
            self.ebb_collect_uses(*ebb, renamed);
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

fn ends_bb(op: Opcode) -> bool {
    op.is_branch() || op.is_terminator()
}
