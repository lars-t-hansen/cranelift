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
//
// Algorithm.
// 
// Step 0: Compute liveness using the standard Cranelift algorithm.
//
// This yields information needed by step 1.
//
//
// Step 1: insert stack-allocated temps and collect information
//
// Using the dominator tree and the live value tracker we can compute live-in sets for EBBs and
// defs, kills, and throughs for each instruction.  We traverse the EBBs in top-down domtree order
// and process instructions in each EBB in top-down order.
//
// REDEFINED = {}  // map from value -> value
// EXITS = {}      // map from instruction -> (map from value -> value)
// For each instruction I in top-down order
//   for each use of a value U in I st. there is U -> X in REDEFINED,
//     replace U by X in the instruction
//   (DEFS, KILLS, THROUGHS) = analyze(I)
//   if I is a call
//     for each V in THROUGHS
//       create a new variable S
//       create a new variable R
//       create a new instruction S <- copy V before the call
//       create a new instruction R <- copy S after the call
//       add V -> R to REDEFINED (this may remove an old mapping of V)
//   if I is a branch or jump
//     Add I -> immutable copy of REDEFINED to EXITS
//
// (This step follows the spilling pass almost exactly, just does more.)
// 
//
// Maybe: Maintain a set `Renamed` of tuples (v, D, U) where v is an original value that was
// renamed and D is the instruction that defines it, and U is the empty set (it is given a
// value in step 2).
//
//
// Step 2: Collect use information
// 
// Collect, for each use of (v, D, U) in Renamed, the set of instructions U that use v (ie
// update the tuple for v in Renamed).
//
// (It's possible we need to collect definitions in an EBB that are not affected by renaming
// but which are live-out.)
//
//
// Step 3: Update SSA form
//
// Hack's dissertation has a plausible algorithm.  The sets of renamings that we have
// provided will be used during the dominator tree search.
//
// For each variable v



// Several passes here, order uncertain:
//
// - compute live-in / live-out set for all the blocks, this is an upward walk of the cfg
//   with a worklist presumably.
//
// - make a pass across the cfg, insert copies at calls.  we need to know, for each call
//   instruction, which values that are last-use in the instruction so that we don't save
//   them; all other values that are in the live set (but are not defined) must be
//   saved/restored.  we can compute last-use locally from the live-out set and a backward
//   scan of the instructions if need be, so we don't need to store it for every instruction,
//   only for calls.
//   It is probably ok to insert copies by walking upward, so long as we remember the
//   renamings we've done (these may turn into chains of renamings?).  We can do blocks in any
//   order.
//
// - if we have some way of recording the information per-call during the liveness analysis (if
//   we reprocess a block then we throw away the information for calls in that block) then
//   we can annotate each call during the liveness analysis, and we can collect the set of all
//   call instructions for later use, so we don't need to re-scan anything.
//
// - since it's ssa form, do we really need to use a worklist?  can we just walk the
// dominator tree bottom-up in one pass?  that would be sweet...

// A central issue is not really finding the calls and inserting the copies, which seems
// easy, but the subsequent renaming, and the needs of that renaming.

//
// - perform ssa renaming (uses liveness in unspecified way, need to look at algorithms)
//
// We can compute liveness (collect uses) and rename in one pass by walking up the tree,
// collecting uses.  Only the last rename in a block need be remembered for the ssa
// renaming, since for all others the renaming is local and we must just do it, ie, if there
// are two calls back-to-back across which we save x, we will rename for the last call
// and remember this renaming, and then as we move up the block we will ...
//
// the problem, moving up the block, is that we must rename locally below each renaming
// until the next one, until the end of the block, or until the value dies.
//
// I think realistically we compute liveness and uses in an up pass and then do another down
// pass for the initial renaming, and then do the ssa fixup.  We need compute uses only for
// values that are live 

use crate::entity::SecondaryMap;
use crate::regalloc::live_value_tracker::LiveValueTracker;
use crate::cursor::{Cursor, EncCursor};
use crate::dominator_tree::DominatorTree;
use crate::ir::{Ebb, Function, Inst, InstBuilder, Value};
use crate::isa::TargetIsa;
use crate::timing;
use crate::regalloc::liveness::Liveness;
use crate::topo_order::TopoOrder;
use std::vec::Vec;
use log::debug;

/// Persistent data structures for the splitting pass.
pub struct Splitting {
    renamed: SecondaryMap<Value, Vec<Value>>,        // Placeholder
}

/// Context data structure that gets instantiated once per pass.
struct Context<'a> {
    liveness: &'a Liveness,

    renamed: &'a mut SecondaryMap<Value, Vec<Value>>,

    // Current instruction as well as reference to function and ISA.
    cur: EncCursor<'a>,

    // References to contextual data structures we need.
    domtree: &'a DominatorTree,
    topo: &'a mut TopoOrder,
}

impl Splitting {
    /// Create a new splitting data structure.
    pub fn new() -> Self {
        Self {
            renamed: SecondaryMap::new(),
        }
    }

    /// Clear all data structures in this splitting pass.
    pub fn clear(&mut self) {
        self.renamed.clear();
    }

    /// Run the splitting algorithm over `func`.
    pub fn split_across_calls(
        &mut self,
        isa: &TargetIsa,
        func: &mut Function,
        domtree: &DominatorTree,
        liveness: &Liveness,
        topo: &mut TopoOrder,
        tracker: &mut LiveValueTracker,
    ) {
        let _tt = timing::ra_splitting();
        debug!("Splitting across calls for:\n{}", func.display(isa));
        let mut ctx = Context {
            cur: EncCursor::new(func, isa),
            renamed: &mut self.renamed,
            domtree,
            liveness,
            topo,
        };
        ctx.run(tracker)
    }
}

impl<'a> Context<'a> {
    fn run(&mut self, tracker: &mut LiveValueTracker) {
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.visit_ebb(ebb, tracker);
        }
        debug!("Renamed {:?}", self.renamed);
    }

    fn visit_ebb(&mut self, ebb: Ebb, tracker: &mut LiveValueTracker) {
        self.cur.goto_top(ebb);
        self.visit_ebb_header(ebb, tracker);
        tracker.drop_dead_params();

        self.cur.goto_first_inst(ebb);
        while let Some(inst) = self.cur.current_inst() {
            if !self.cur.func.dfg[inst].opcode().is_ghost() {
                // visit_inst() advances the instruction
                self.visit_inst(inst, ebb, tracker);
            } else {
                let (_throughs, _kills) = tracker.process_ghost(inst);
                self.cur.next_inst();
            }
            tracker.drop_dead(inst);
        }
    }

    fn visit_ebb_header(&mut self, ebb: Ebb, tracker: &mut LiveValueTracker) {
        tracker.ebb_top(
            ebb,
            &self.cur.func.dfg,
            self.liveness,
            &self.cur.func.layout,
            self.domtree,
        );
    }

    fn visit_inst(&mut self, inst: Inst, ebb: Ebb, tracker: &mut LiveValueTracker) {
        debug!("Inst {}", self.cur.display_inst(inst));
        debug_assert_eq!(self.cur.current_inst(), Some(inst));
        debug_assert_eq!(self.cur.current_ebb(), Some(ebb));

        self.cur.use_srcloc(inst);

        // Update the live value tracker with this instruction.
        let (throughs, _kills, _defs) = tracker.process_inst(inst, &self.cur.func.dfg, self.liveness);

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
                    self.renamed[lv.value].push(copy);
                }
            }
        } else {
            self.cur.next_inst();
        }
    }
}
