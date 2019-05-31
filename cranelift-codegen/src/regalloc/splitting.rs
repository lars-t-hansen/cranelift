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
//   M. Braun, S. Hack: Register Spilling and Live-Range Splitting for SSA-Form Programs, Compiler
//   Conference 2009
//
//   S. Hack: Register Allocation for Programs in SSA Form, PhD Dissertation, 2006
//
//
// Algorithm.
// 
// Step 0: Compute liveness using the standard Cranelift algorithm.
//
// This yields information needed by step 1.
//
//
// Step 1: insert stack-allocated temps, perform local renaming, collect information
//
// Together with the dominator tree and the live value tracker we can compute live-in sets for EBBs
// and defs, kills, and throughs for each instruction.  We traverse the EBBs in top-down domtree
// order and process instructions in each EBB in top-down order.
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

use crate::cursor::{Cursor, EncCursor};
use crate::dominator_tree::DominatorTree;
use crate::flowgraph::ControlFlowGraph;
use crate::ir::{Ebb, Function};
use crate::isa::TargetIsa;
use crate::timing;
use crate::topo_order::TopoOrder;
use log::debug;

/// Persistent data structures for the splitting pass.
pub struct Splitting {
}

/// Context data structure that gets instantiated once per pass.
struct Context<'a> {
    // Current instruction as well as reference to function and ISA.
    cur: EncCursor<'a>,

    // References to contextual data structures we need.
    cfg: &'a ControlFlowGraph,
    domtree: &'a DominatorTree,
    topo: &'a mut TopoOrder,
}

impl Splitting {
    /// Create a new splitting data structure.
    pub fn new() -> Self {
        Self { }
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
        topo: &mut TopoOrder,
    ) {
        let _tt = timing::ra_splitting();
        debug!("Splitting across calls for:\n{}", func.display(isa));
        let mut ctx = Context {
            cur: EncCursor::new(func, isa),
            cfg,
            domtree,
            topo,
        };

        
        ctx.run()
    }
}

impl<'a> Context<'a> {
    fn run(&mut self) {
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.visit_ebb(ebb);
        }
    }

    fn visit_ebb(&mut self, ebb: Ebb) {
    }
}
