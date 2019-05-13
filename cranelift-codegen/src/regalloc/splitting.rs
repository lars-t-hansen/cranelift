//! Splitting pass.
//!
//! The splitting pass is the first to run after the liveness analysis.  [Not actually true.  The
//! CSSA conversion also uses the liveness info.]
//!
//! The splitter's primary function is to ensure that the register pressure never exceeds the number
//! of available registers by splitting the live ranges of values by inserting copies, typically
//! through memory via spills and reloads but in some special cases just register-to-register.
//!
//! Its secondary function is to insert copies so as to honor instruction operand constraints.  Some
//! instruction operand constraints may require additional registers to resolve:
//!
//! 1. A value used by a tied operand must be killed by the instruction. This is resolved by
//!    inserting a copy to a temporary value when necessary.
//! 2. When the same value is used more than once by an instruction, the operand constraints must
//!    be compatible. Otherwise, the value must be copied into a new register for some of the
//!    operands.
//!
//!
//! Register pressure.
//!
//! (General notes)
//! (Something here about register pressure around calls + callee-saves registers.)
//!
//!
//! Live range splitting.
//!
//! The splitter's main strategy for splitting a live range of a value is to spill the value to the
//! stack when the value becomes not needed for some interval, and then later reloading it at the
//! end of that interval.  The register that would have been occupied by the value thus becomes
//! available to other values during the interval.  The value is effectively copied via memory; it
//! is given a new name when it is reloaded; and may be placed in a different register (than the one
//! it was spilled from) when it is reloaded.
//!
//! The splitter can also choose to split a live range by creating a simple copy of a value; this
//! gives the coloring phase an opportunity to insert a move.  It does not reduce pressure per se
//! but may reduce the complexity of the coloring graph.  For example, at a function call boundary
//! the values that are live across the call must either be in callee-saves registers or in stack
//! slots, and parameters must be in parameter registers.  Yet some value may be both a parameter
//! and live across the call.  Thus the value would have an interference with both the argument
//! registers (because they are caller-save and the value is live across the call) and the
//! callee-save registers (because it must be precolored to sit in an argument register).  This will
//! lead to a situation where the value will be spilled across the call and then reloaded for the
//! outgoing argument.  The tension can be resolved by introducing a local copy for the outgoing
//! argument.  (This is subject to the number of live values across the call vs the number of
//! callee-saves registers, as well.)
//!
//! Splitting necessarily affects the live ranges of values: a value's live range ends where it is
//! spilled (the spill consumes the value); a later reload from the spill creates a new value with a
//! new live range.
//!
//!
//! Inserting local copies.
//!
//! A local copy of an SSA value can be inserted by creating a copy under a new name, using that
//! locally, and let the original name be used henceforth; this does not split a live range
//! however:
//!
//! Change:
//!
//! ... = inst v2
//! ... v2 ...
//!
//! Into:
//!
//! v7 = copy v2
//! ... = inst v7
//! ... v2 ...
//!
//! Since the copy does not live until a control transfer its introduction cannot violate CSSA form.
//!
//!
//! Inserting nonlocal copies.
//!
//! A general copy of an SSA value is instead inserted by creating a new name for the copy and
//! then using that in place of the old name throughout the function.  This requires propagating
//! the renaming and may require inserting new phis.
//!
//! ...
//!
//! Question: can the copy violate CSSA form?  Consider a diamond where there's a spill/reload on
//! one branch but not on the other.  The join will get a phi.  The unaffected branch is fine.  The
//! affected branch will introduce a new name for the reloaded value and the spilled value will be
//! dead.  So at the jump to the join the new value (being new) cannot interfere with any of the
//! other ebb parameters.
//!
//!     

use crate::cursor::{Cursor, EncCursor};
use crate::dominator_tree::DominatorTree;
use crate::ir::{ArgumentLoc, Ebb, Function, Inst, InstBuilder, SigRef, Value, ValueLoc};
use crate::isa::registers::{RegClass, RegClassIndex, RegClassMask, RegUnit};
use crate::isa::{ConstraintKind, EncInfo, RecipeConstraints, RegInfo, TargetIsa};
use crate::regalloc::affinity::Affinity;
use crate::regalloc::live_value_tracker::{LiveValue, LiveValueTracker};
use crate::regalloc::liveness::Liveness;
use crate::regalloc::pressure::Pressure;
use crate::regalloc::virtregs::VirtRegs;
use crate::timing;
use crate::topo_order::TopoOrder;
use core::fmt;
use log::debug;
use std::vec::Vec;

/// Persistent data structures for the splitting pass.
pub struct Splitting {
}

/// Context data structure that gets instantiated once per pass.
struct Context<'a> {
    // Current instruction as well as reference to function and ISA.
    cur: EncCursor<'a>,

    // Cached ISA information.
    reginfo: RegInfo,
    encinfo: EncInfo,

    // References to contextual data structures we need.
    domtree: &'a DominatorTree,
    liveness: &'a mut Liveness,
    virtregs: &'a VirtRegs,
    topo: &'a mut TopoOrder,

    // Current register pressure.
    pressure: Pressure,

    // Values spilled for the current instruction. These values have already been removed from the
    // pressure tracker, but they are still present in the live value tracker and their affinity
    // hasn't been changed yet.
//    spills: &'a mut Vec<Value>,

    // Uses of register values in the current instruction.
//    reg_uses: &'a mut Vec<RegUse>,
}

impl Splitting {
    /// Create a new spilling data structure.
    pub fn new() -> Self {
        Self {
        }
    }

    /// Clear all data structures in this spilling pass.
    pub fn clear(&mut self) {
    }

    /// Run the spilling algorithm over `func`.
    pub fn run(
        &mut self,
        isa: &TargetIsa,
        func: &mut Function,
        domtree: &DominatorTree,
        liveness: &mut Liveness,
        virtregs: &VirtRegs,
        topo: &mut TopoOrder,
        tracker: &mut LiveValueTracker,
    ) {
        let _tt = timing::ra_splitting();
        debug!("Splitting for:\n{}", func.display(isa));
        let reginfo = isa.register_info();
        let usable_regs = isa.allocatable_registers(func);
        let mut ctx = Context {
            cur: EncCursor::new(func, isa),
            reginfo: isa.register_info(),
            encinfo: isa.encoding_info(),
            domtree,
            liveness,
            virtregs,
            topo,
            pressure: Pressure::new(&reginfo, &usable_regs),
//            spills: &mut self.spills,
//            reg_uses: &mut self.reg_uses,
        };
        ctx.run(tracker)
    }
}

// PoC v1 outline.
//
// In PoC v1 we split live ranges across function calls in a simple way, only.  We operate only on
// functions that do not require spilling in non-call contexts and that take only integer parameters
// in integer registers (no stack args).  We ignore callee-saves registers.  The PoC as envisioned
// will not work with all wasm code, it is a small-scale experiment.
//
// The point of PoC v1 is twofold: (1) to test the copy-insertion algorithm on the SSA form, and (2)
// to verify that splitting across calls is enough to deal with one huge problem of the old
// spill/reload architecture, wherein every value live across a call is marked as spilled and thus
// results in very pessimal code everywhere.
//
// We will spill live values immediately before the call and fill directly after the call, thus
// splitting the live ranges and requiring correct copy insertion & renaming throughout the
// function:
//
//   call $f (v1, v7, v10 ) // v7 and v10 are live past the call
//   ...
//   ... = inst v7, v10     // used here
//
// becomes
//
//   s7 = spill v7
//   s10 = spill v10
//   call $f (v1, v7, v10)  // live ranges of v1, v7, v10 now end here
//   v7' = reload s7
//   v10' = reload s10
//   ...
//   ... = inst v7', v10'   // uses renamed v7, v10
//
// Parameters that arrive in registers will be copied to vregs on entry.
//
// We will panic if:
// - there are incoming stack args
// - register pressure becomes too large at any time
//
// Since we have enough registers we'll not need to worry about the situation where the ebb takes a
// spill slot argument.
//
// Since we'll spill only across calls for the PoC, all spill slots will be dead after we fill just
// after the call, and we don't care how slots are managed - we can use a stack, say.
//
// Since we shorten live ranges and our liveness system doesn't have a way of incrementally updating
// that, we'll need to recompute all the liveness information following splitting, adding to the
// cost of splitting.
//
//
// Braun & Hack works by computing the distance everywhere first, not sure if this really requires
// liveness info or if it works just bottom-up on local info, anyway this yields a kind of liveness
// structure with block-in block-out data.  Then determination is made at each block boundary (in
// some top-down order) about which block params and live-in values will be in registers and which
// will not, based on info from the predecessors.  Code is inserted to ensure that each predecessor
// sets things up right.  Then MIN is run locally, using local information + global next-use
// information.  This inserts spills and fills *within the block* and creates an outgoing register
// state.  We spill a value only once but if it's evicted more than once we can reload more than
// once.  A fill however becomes an SSA value, each fill is a new one, and until it must be evicted
// we keep using that, again *within the block*.


// Open questions:
//  - let's just hope that incremental update of liveness is not needed along the way...
//    for PoC v1 we insert reloads, defining new names.  But we need to be sure that
//    the old names that we have spilled don't contribute to register pressure along the
//    tails of their live ranges, we need to discount them there.  The spiller probably
//    uses affinity to avoid this (once a value has been spilled it's not an issue).
//
//    Well - is that a red herring?  
//
//  - aliases that point to existing names can be a problem?  who inserts aliases?
//
//
// "Fix later":
//  - spilling as a result of register pressure, generally
//  - moving the fill to the before the next use(s) after a required spill point
//  - managing spill storage properly (reducing stack usage)
//  - handle non-integer args
//  - handle stack args that start out "spilled" in their home locations
//  - handle spill slots at ebb boundaries
//
// "Fix much later":
//  - moving the spill to after the last use(s) before a required spill point
//  - use callee-saves registers
//  - incremental update of liveness information
//
// Here, a "required spill point" is just a call in PoC v1 but of course more general later

impl<'a> Context<'a> {
    fn run(&mut self, tracker: &mut LiveValueTracker) {
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.visit_ebb(ebb, tracker);
        }
    }

    fn visit_ebb(&mut self, ebb: Ebb, tracker: &mut LiveValueTracker) {
        debug!("Splitting {}:", ebb);
        self.cur.goto_top(ebb);
        self.visit_ebb_header(ebb, tracker);
        tracker.drop_dead_params();
//        self.process_spills(tracker);

        while let Some(inst) = self.cur.next_inst() {
            if !self.cur.func.dfg[inst].opcode().is_ghost() {
                self.visit_inst(inst, ebb, tracker);
            } else {
                let (_throughs, kills) = tracker.process_ghost(inst);
                self.free_regs(kills);
            }
            tracker.drop_dead(inst);
//            self.process_spills(tracker);
        }
    }

    fn visit_ebb_header(&mut self, ebb: Ebb, tracker: &mut LiveValueTracker) {
    }

    fn visit_inst(&mut self, inst: Inst, ebb: Ebb, tracker: &mut LiveValueTracker) {
        debug!("Inst {}, {}", self.cur.display_inst(inst), self.pressure);
    }
}
