//! Splitting pass.
//!
//! The splitting pass is the first to run after the liveness analysis.
//!
//! The splitter's primary function is to ensure that the register pressure never exceeds the number
//! of available registers by splitting the live ranges of values, by inserting copies, typically
//! through memory via spills and reloads, or in some special cases register-to-register.
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
//!
//! Inserting nonlocal copies.
//!
//! A general copy of an SSA value is instead inserted by creating a new name for the copy and
//! then using that in place of the old name throughout the function.  This requires propagating
//! the renaming and may require inserting new phis.
//!
//! ...

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

impl<'a> Context<'a> {
    fn run(&mut self, tracker: &mut LiveValueTracker) {
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.visit_ebb(ebb, tracker);
        }
    }

    fn visit_ebb(&mut self, ebb: Ebb, tracker: &mut LiveValueTracker) {
        debug!("Splitting {}:", ebb);
    }
}
