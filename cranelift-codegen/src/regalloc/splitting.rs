//! Live range splitting pass.
//!
//! (This is a machine-independent proof of concept for systems without callee-saves registers.)
//!
//! The splitter's function is (currently) to split the live ranges of values across calls, so that
//! the subsequent spilling pass does not assign values to stack slot just because they're live when
//! there's a call.
//!
//! Consider a call and its context.  The `v` are live across the call; the `d` are defined by the
//! call, the `u` are used by the call.  (Some of the `u` may be among the `v`.)
//!
//!    v1, v2, ..., vn = ...
//!    ...
//!    d1, d2, ..., dk = call F, u1, u2, ..., um
//!    ...
//!    ... = v1, v2, ..., vn
//!
//! This is rewritten as the following, where the `s` and `w` are just new values.
//!
//!    v1, v2, ..., vn = ...
//!    ...
//!    s1 = copy v1
//!    s2 = copy v2
//!    ...
//!    sn = copy vn
//!    d1, d2, ..., dk = call F, u1, u2, ..., um
//!    w1 = copy s1
//!    w2 = copy s2
//!    ...
//!    wn = copy sn
//!    ...
//!    ... = w1, w2, ..., wn
//!
//! In the case where the `v` is a constant, it is even simpler: we do not introduce an `s` for it,
//! but instead create a new `const` instruction for the value it when we create the `w` after the
//! call.
//!
//! In general the introduction of copies like this requires a renaming of values throughout the
//! CFG, which may result in the insertion of new phi nodes, see:
//!
//!   Braun & Hack (FIXME)
//!   Sastry & Ju (FIXME)
//!

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
    pub fn clear(&mut self) { }

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

        // Several passes here, order uncertain:
        //
        // - compute live-in / live-out set for all the blocks, this is an upward walk of the
        //   dominator tree with a worklist presumably?
        //
        // - make a pass across the cfg, insert copies.  we need to know, for each instruction,
        //   which values that are last-use in the instruction so that we don't save them; all other
        //   values that are in the live set (but are not defined) must be saved/restored.  we can
        //   compute last-use locally from the live-out set and a backward scan of the instructions
        //   if need be, so we don't need to store it for every instruction.  It is probably ok to
        //   insert copies by walking upward, so long as we remember the renamings we've done (these
        //   may turn into chains of renamings?).  We can do blocks in any order.
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
