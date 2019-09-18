//! Spilling pass.
//!
//! The spilling pass is the first to run after the liveness analysis. Its primary function is to
//! ensure that the register pressure never exceeds the number of available registers by moving some
//! SSA values to spill slots on the stack. To do this well, it splits live ranges of values that
//! must be spilled by copying the values to and from stack-allocated slots as needed.
//!
//! The final location of a value is encoded in the "affinity" of the value's live range.
//!
//! Some instruction operand constraints may require additional registers to resolve. Since this
//! can cause spilling, the spilling pass is also responsible for resolving those constraints by
//! inserting copies. The extra constraints are:
//!
//! 1. A value used by a tied operand must be killed by the instruction. This is resolved by
//!    inserting a copy to a temporary value when necessary.
//! 2. When the same value is used more than once by an instruction, the operand constraints must
//!    be compatible. Otherwise, the value must be copied into a new register for some of the
//!    operands.
//!
//! Some values are more cheaply recomputed than spilled and restored, and the spilling pass inserts
//! simple recomputations when it can in these cases:
//!
//! 1. TODO. When the value is a known constant that can be regenerated with a `t.const`
//!    instruction.
//!
//! Live range splitting:
//!
//! When a live value has to be moved from a register because either (a) the register is needed for
//! another value or (b) the register is about to be clobbered by a call, we copy the value into a
//! stack location, terminate the live range of the value, and record that the original value now
//! has a new name and is on the stack.  (Incoming stack parameters effectively start in a "spilled"
//! state.)  When the value is subsequently needed to be in a register, we copy it from the stack
//! location, create a new live range for the value, and record that the original value has yet a
//! new name and is in a register.  Subsequent uses of the old name then instead become uses of the
//! new name.  This general scheme ensures that values are in registers as much as possible.
//!
//! At a control flow join we then risk that a value that was previously live-in to the block now
//! has multiple names and locations: the value may have been spilled and possibly restored along
//! some paths into the block, or along all.  In this case, we must ensure that all the paths agree
//! on the location of the value, if necessary by inserting spills or fills along some paths, and
//! the block will have to accept the value as a new ebb parameter.  For the sake of simplicity, we
//! let the first path into a block determine the location of the value (stack or register); other
//! paths must conform.  (There are some complications here with table jumps and certain conditional
//! jumps that can be resolved by splitting edges; see later.)
//! 
//! In the main, this is a two-pass algorithm.  The first pass ("splitting") makes a single RPO
//! descent of the flow graph, inserting spill and fill instructions, and rematerializing constants.
//! The second pass ("rectification") uses a worklist algorithm to insert new ebb parameters and to
//! rename all uses; a worklist is needed to deal with loop back-edges.  After the two passes are
//! finished, liveness information must be recomputed if any values were spilled.
//!
//! Rematerialization:
//!
//! TODO: Not implemented.
//!
//! When we need to spill a value we examine its definition, and if that defines a constant we
//! instead record that the value was a constant, and when we later fill the value we re-introduce
//! the constant under a new name.
//!
//! Rematerialization effectively splits a live range, but we do not want to insert ebb parameters
//! at join points for a constant value, since that hides the fact that the value is a constant and
//! prevents later rematerialization.  Instead, when we merge constants at join points we must
//! effectively forget the incoming values and record that the constant exists so that it can be
//! rematerialized in dominated nodes, as in the simple case.

use crate::cursor::{Cursor, EncCursor};
use crate::dominator_tree::DominatorTree;
use crate::entity::{SecondaryMap, SparseMap, SparseMapValue};
use crate::ir::{ArgumentLoc, Ebb, Function, Inst, InstBuilder, SigRef, StackSlot, Value};
use crate::isa::registers::{RegClass, RegClassIndex, RegClassMask, RegUnit};
use crate::isa::{ConstraintKind, EncInfo, RecipeConstraints, RegInfo, TargetIsa};
use crate::regalloc::affinity::Affinity;
use crate::regalloc::live_value_tracker::{LiveValue, LiveValueTracker};
use crate::regalloc::liveness::Liveness;
use crate::regalloc::pressure::Pressure;
use crate::regalloc::virtregs::{VirtReg,VirtRegs};
use crate::timing;
use crate::topo_order::TopoOrder;
use core::fmt;
use log::debug;
use std::vec::Vec;

/// Return a top-level register class which contains `unit`.
fn toprc_containing_regunit(unit: RegUnit, reginfo: &RegInfo) -> RegClass {
    let bank = reginfo.bank_containing_regunit(unit).unwrap();
    reginfo.classes[bank.first_toprc..(bank.first_toprc + bank.num_toprcs)]
        .iter()
        .find(|&rc| rc.contains(unit))
        .expect("reg unit should be in a toprc")
}

/// The spill state of a single value at EBB entry, see EbbSpillState below.
struct SpillState {
    value: Value,
    affinity: Affinity,         // only Stack or Reg(rci)
}

impl SparseMapValue<Value> for SpillState {
    fn key(&self) -> Value {
        self.value
    }
}

type SpillStateMap = SparseMap<Value, SpillState>;

/// Here we have info about the current incoming spill state of the EBB.  The structure is first
/// created when we first encounter an EBB in the RPO walk, and then updated as we reach the ebb
/// through other paths.  When we process the EBB, we apply the state herein before processing the
/// instructions of the EBB.  We seed this map with info about the entry block.
///
/// The spill state includes both live-in names and parameter names.
struct EbbSpillState {
    key: Ebb,
    ss: SpillStateMap,
}

impl SparseMapValue<Ebb> for EbbSpillState {
    fn key(&self) -> Ebb {
        self.key
    }
}

type EbbSpillStateMap = SparseMap<Ebb, EbbSpillState>;

/// The slot is always the result of the value having been spilled, but it is possible that the
/// value is an incoming stack parameter, hence it's optional.
///
/// The rci is the rci initially assigned to the value:
/// - if it's a result generated into a register then that provides the rci, and we
///   set it here when the value is spilled.
/// - if it's an incoming register parameter then that provides the rci
/// - if it's an incoming stack parameter then we can compute the rci from the abi

struct ValueAndLocations {
    value: VirtReg,
    slot:  Option<StackSlot>,
    rci:   Option<RegClassIndex>
}

impl SparseMapValue<VirtReg> for ValueAndLocations {
    fn key(&self) -> VirtReg {
        self.value
    }
}

struct ValueRepr {
    value: Value,
    repr: Value
}

impl SparseMapValue<Value> for ValueRepr {
    fn key(&self) -> Value {
        self.value
    }
}

/// Persistent data structures for the spilling pass.
pub struct Spilling {
    spills: Vec<Value>,
    reg_uses: Vec<RegUse>,
}

/// Context data structure that gets instantiated once per pass.
struct Context<'a> {
    // Current instruction as well as reference to function and ISA.
    cur: EncCursor<'a>,

    // Cached ISA information.
    reginfo: RegInfo,
    encinfo: EncInfo,
    isa: &'a dyn TargetIsa,

    // References to contextual data structures we need.
    domtree: &'a DominatorTree,
    liveness: &'a mut Liveness,
    virtregs: &'a mut VirtRegs,
    topo: &'a mut TopoOrder,

    // Current register pressure.
    pressure: Pressure,

    // Values spilled for the current instruction. These values have already been removed from the
    // pressure tracker, but they are still present in the live value tracker and their affinity
    // hasn't been changed yet.
    spills: &'a mut Vec<Value>,

    // Uses of register values in the current instruction.
    reg_uses: &'a mut Vec<RegUse>,

    // Set to true if any new names were created in such a way that liveness analysis must be rerun
    // (not all name introductions require this).
    liveness_invalidated: bool,

    // Mapping of live values to our current notion of affinity for the value.
    affinities: SecondaryMap<Value, Affinity>,

    // For each representative value, map the VR of that value to information about storage
    // locations used for the value (register class index and stack slot), in its various
    // manifestations.
    //
    // (Non-representative values do not have VRs and cannot appear here.)
    locations: SparseMap<VirtReg, ValueAndLocations>,

    // For each value introduced by a fill or a spill, map that value to the representative value:
    // the program value whose live range was split.  For program values, this has no entry.
    representative: SparseMap<Value, ValueRepr>,
}

impl Spilling {
    /// Create a new spilling data structure.
    pub fn new() -> Self {
        Self {
            spills: Vec::new(),
            reg_uses: Vec::new(),
        }
    }

    /// Clear all data structures in this spilling pass.
    pub fn clear(&mut self) {
        self.spills.clear();
        self.reg_uses.clear();
    }

    /// Run the spilling algorithm over `func`.
    pub fn run(
        &mut self,
        isa: &dyn TargetIsa,
        func: &mut Function,
        domtree: &DominatorTree,
        liveness: &mut Liveness,
        virtregs: &mut VirtRegs,
        topo: &mut TopoOrder,
        tracker: &mut LiveValueTracker,
    ) -> bool {
        let _tt = timing::ra_spilling();
        debug!("Spilling for:\n{}", func.display(isa));
        let reginfo = isa.register_info();
        let usable_regs = isa.allocatable_registers(func);

        let mut ctx = Context {
            cur: EncCursor::new(func, isa),
            reginfo: isa.register_info(),
            encinfo: isa.encoding_info(),
            isa,
            domtree,
            liveness,
            virtregs,
            topo,
            pressure: Pressure::new(&reginfo, &usable_regs),
            spills: &mut self.spills,
            reg_uses: &mut self.reg_uses,
            liveness_invalidated: false,
            affinities: SecondaryMap::new(),
            locations: SparseMap::new(),
            representative: SparseMap::new(),
        };

        let mut ebb_spill_state: EbbSpillStateMap = SparseMap::new();

        ctx.run(&mut ebb_spill_state, tracker);
        ctx.liveness_invalidated
    }
}

impl<'a> Context<'a> {
    fn run(&mut self, ebb_spill_state: &mut EbbSpillStateMap, tracker: &mut LiveValueTracker) {

        // Create the spill state for the entry block and create ValueAndLocation entries for the
        // incoming parameters.
        self.init_spill_state(ebb_spill_state, tracker);

        // RPO is needed because spill info is flow-sensitive.
        self.topo.reset(self.domtree.cfg_postorder().iter().rev().map(|x| *x));
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.visit_ebb(ebb, ebb_spill_state, tracker);
        }

        // TODO: Rectification pass
    }

    // Seed the spill state with information about the entry block.
    fn init_spill_state(&mut self, ebb_spill_state: &mut EbbSpillStateMap, tracker: &mut LiveValueTracker) {
        let entry = self.cur.func.layout.entry_block().unwrap();
        self.cur.goto_top(entry);
        let (liveins, params) = tracker.ebb_top(
            entry,
            &self.cur.func.dfg,
            self.liveness,
            &self.cur.func.layout,
            self.domtree,
        );

        debug_assert_eq!(liveins.len(), 0);
        debug_assert_eq!(self.cur.func.signature.params.len(), params.len());

        let mut ss = SparseMap::new();
        for (param_idx, param) in params.iter().enumerate() {
            if !param.is_dead {
                let abi = self.cur.func.signature.params[param_idx];
                let affinity = Affinity::abi(&abi, self.isa);
                ss.insert(SpillState { value: param.value,
                                       affinity });
                self.locations.insert(ValueAndLocations { value: self.virtregs.get(param.value).unwrap(),
                                                          slot: None,
                                                          rci: Some(self.cur.isa.regclass_for_abi_type(abi.value_type).into()) });
            }
        };

        ebb_spill_state.insert(EbbSpillState {
            key: entry,
            ss,
        });
    }

    fn visit_ebb(&mut self, ebb: Ebb, ebb_spill_state: &mut EbbSpillStateMap, tracker: &mut LiveValueTracker) {
        debug!("Spilling {}:", ebb);
        self.cur.goto_top(ebb);

        self.apply_spill_state(ebb, ebb_spill_state, tracker);

        self.visit_ebb_header(ebb, tracker);
        tracker.drop_dead_params();
        self.process_spills();

        while let Some(inst) = self.cur.next_inst() {
            if !self.cur.func.dfg[inst].opcode().is_ghost() {
                self.visit_inst(inst, ebb, ebb_spill_state, tracker);
            } else {
                let (_throughs, kills) = tracker.process_ghost(inst);
                self.free_regs(kills);
            }
            tracker.drop_dead(inst);
            self.process_spills();
        }
    }

    fn apply_spill_state(&mut self, ebb: Ebb, ebb_spill_state: &mut EbbSpillStateMap, tracker: &mut LiveValueTracker) {
        // TODO: In debug builds, set all affinities to Unassigned before applying the state.
        let ss = &ebb_spill_state.get(ebb).unwrap().ss;
        for lv in tracker.live() {
            let affinity = ss.get(lv.value).unwrap().affinity;
            self.set_affinity(lv.value, affinity);
        }
    }

    // These abstract away whether we're using a map or an array indexed by value, and what's in the
    // array, and where it might live.
    fn affinity(&self, v: Value) -> Affinity {
        self.affinities[v]
    }

    fn set_affinity(&mut self, v: Value, affinity: Affinity) {
        self.affinities[v] = affinity;
    }

    // Take all live registers in `regs` from the pressure set.
    // This doesn't cause any spilling, it is assumed there are enough registers.
    fn take_live_regs(&mut self, regs: &[LiveValue]) {
        for lv in regs {
            if !lv.is_dead {
                if let Affinity::Reg(rci) = self.affinity(lv.value) {
                    let rc = self.reginfo.rc(rci);
                    self.pressure.take(rc);
                }
            }
        }
    }

    // Free all registers in `kills` from the pressure set.
    fn free_regs(&mut self, kills: &[LiveValue]) {
        for lv in kills {
            if let Affinity::Reg(rci) = self.affinity(lv.value) {
                if !self.spills.contains(&lv.value) {
                    let rc = self.reginfo.rc(rci);
                    self.pressure.free(rc);
                }
            }
        }
    }

    // Free all dead registers in `regs` from the pressure set.
    fn free_dead_regs(&mut self, regs: &[LiveValue]) {
        for lv in regs {
            if lv.is_dead {
                if let Affinity::Reg(rci) = self.affinity(lv.value) {
                    if !self.spills.contains(&lv.value) {
                        let rc = self.reginfo.rc(rci);
                        self.pressure.free(rc);
                    }
                }
            }
        }
    }

    fn visit_ebb_header(&mut self, ebb: Ebb, tracker: &mut LiveValueTracker) {
        let (liveins, params) = tracker.ebb_top(
            ebb,
            &self.cur.func.dfg,
            self.liveness,
            &self.cur.func.layout,
            self.domtree,
        );

        // Count the live-in registers. These should already fit in registers; they did at the
        // dominator.
        self.pressure.reset();
        self.take_live_regs(liveins);

        // Spilling should have been performed along the branches reaching this block (for non-entry
        // blocks) or should not happen (for the entry block).  We just need to take registers for
        // the parameters.
        for lv in params {
            if let Affinity::Reg(rci) = self.affinity(lv.value) {
                if let Err(_) = self.pressure.take_transient(self.reginfo.rc(rci)) {
                    panic!("There should be no spilling here");
                }
            }
        }

        // The transient pressure counts for the EBB arguments are accurate. Just preserve them.
        self.pressure.preserve_transient();
        self.free_dead_regs(params);
    }

    fn visit_inst(&mut self, inst: Inst, ebb: Ebb, ebb_spill_state: &mut EbbSpillStateMap, tracker: &mut LiveValueTracker) {
        debug!("Inst {}, {}", self.cur.display_inst(inst), self.pressure);
        debug_assert_eq!(self.cur.current_inst(), Some(inst));
        debug_assert_eq!(self.cur.current_ebb(), Some(ebb));

        let constraints = self
            .encinfo
            .operand_constraints(self.cur.func.encodings[inst]);

        // We may need to resolve register constraints if there are any noteworthy uses.
        debug_assert!(self.reg_uses.is_empty());
        self.collect_reg_uses(inst, ebb, constraints);

        // Calls usually have fixed register uses.
        let call_sig = self.cur.func.dfg.call_signature(inst);
        if let Some(sig) = call_sig {
            self.collect_abi_reg_uses(inst, sig);
        }

        if !self.reg_uses.is_empty() {
            self.process_reg_uses(inst, ebb_spill_state, tracker);
        }

        // Update the live value tracker with this instruction.
        let (throughs, kills, defs) = tracker.process_inst(inst, &self.cur.func.dfg, self.liveness);

        // Remove kills from the pressure tracker.
        self.free_regs(kills);

        // If inst is a call, spill all register values that are live across the call.
        // This means that we don't currently take advantage of callee-saved registers.
        // TODO: Be more sophisticated.
        if call_sig.is_some() {
            for lv in throughs {
                if self.affinity(lv.value).is_reg() && !self.spills.contains(&lv.value) {
                    self.spill_reg(lv.value);
                }
            }
        }

        // Make sure we have enough registers for the register defs.
        // Dead defs are included here. They need a register too.
        // No need to process call return values, they are in fixed registers.
        if let Some(constraints) = constraints {
            for op in constraints.outs {
                if op.kind != ConstraintKind::Stack {
                    // Add register def to pressure, spill if needed.
                    while let Err(mask) = self.pressure.take_transient(op.regclass) {
                        debug!("Need {} reg from {} throughs", op.regclass, throughs.len());
                        match self.spill_candidate(mask, throughs) {
                            Some(cand) => self.spill_reg(cand),
                            None => panic!(
                                "Ran out of {} registers for {}",
                                op.regclass,
                                self.cur.display_inst(inst)
                            ),
                        }
                    }
                }
            }
            self.pressure.reset_transient();
        }

        // Restore pressure state, compute pressure with affinities from `defs`.
        // Exclude dead defs. Includes call return values.
        // This won't cause spilling.
        self.take_live_regs(defs);
    }

    // Collect register uses that are noteworthy in one of the following ways:
    //
    // 1. It's a fixed register constraint.
    // 2. It's a use of a spilled value.
    // 3. It's a tied register constraint and the value isn't killed.
    //
    // We are assuming here that if a value is used both by a fixed register operand and a register
    // class operand, they two are compatible. We are also assuming that two register class
    // operands are always compatible.
    fn collect_reg_uses(&mut self, inst: Inst, ebb: Ebb, constraints: Option<&RecipeConstraints>) {
        let args = self.cur.func.dfg.inst_args(inst);
        let num_fixed_ins = if let Some(constraints) = constraints {
            for (idx, (op, &arg)) in constraints.ins.iter().zip(args).enumerate() {
                let mut reguse = RegUse::new(arg, idx, op.regclass.into());
                let lr = &self.liveness[arg];
                let ctx = self.liveness.context(&self.cur.func.layout);
                match op.kind {
                    ConstraintKind::Stack => continue,
                    ConstraintKind::FixedReg(_) => reguse.fixed = true,
                    ConstraintKind::Tied(_) => {
                        // A tied operand must kill the used value.
                        reguse.tied = !lr.killed_at(inst, ebb, ctx);
                    }
                    ConstraintKind::FixedTied(_) => {
                        reguse.fixed = true;
                        reguse.tied = !lr.killed_at(inst, ebb, ctx);
                    }
                    ConstraintKind::Reg => {}
                }

                if self.affinity(arg).is_stack() {
                    reguse.spilled = true;
                }

                // Only collect the interesting register uses.
                if reguse.fixed || reguse.tied || reguse.spilled {
                    debug!("  reguse: {}", reguse);
                    self.reg_uses.push(reguse);
                }
            }
            constraints.ins.len()
        } else {
            // A non-ghost instruction with no constraints can't have any
            // fixed operands.
            0
        };

        // Similarly, for return instructions, collect uses of ABI-defined
        // return values.
        if self.cur.func.dfg[inst].opcode().is_return() {
            debug_assert_eq!(
                self.cur.func.dfg.inst_variable_args(inst).len(),
                self.cur.func.signature.returns.len(),
                "The non-fixed arguments in a return should follow the function's signature."
            );
            for (ret_idx, (ret, &arg)) in
                self.cur.func.signature.returns.iter().zip(args).enumerate()
            {
                let idx = num_fixed_ins + ret_idx;
                let unit = match ret.location {
                    ArgumentLoc::Unassigned => {
                        panic!("function return signature should be legalized")
                    }
                    ArgumentLoc::Reg(unit) => unit,
                    ArgumentLoc::Stack(_) => continue,
                };
                let toprc = toprc_containing_regunit(unit, &self.reginfo);
                let mut reguse = RegUse::new(arg, idx, toprc.into());
                reguse.fixed = true;

                debug!("  reguse: {}", reguse);
                self.reg_uses.push(reguse);
            }
        }
    }

    // Collect register uses from the ABI input constraints.
    fn collect_abi_reg_uses(&mut self, inst: Inst, sig: SigRef) {
        let num_fixed_args = self.cur.func.dfg[inst]
            .opcode()
            .constraints()
            .num_fixed_value_arguments();
        let args = self.cur.func.dfg.inst_variable_args(inst);
        for (idx, (abi, &arg)) in self.cur.func.dfg.signatures[sig]
            .params
            .iter()
            .zip(args)
            .enumerate()
        {
            if abi.location.is_reg() {
                let (rci, spilled) = match self.affinity(arg) {
                    Affinity::Reg(rci) => (rci, false),
                    Affinity::Stack => (
                        self.cur.isa.regclass_for_abi_type(abi.value_type).into(),
                        true,
                    ),
                    Affinity::Unassigned => panic!("Missing affinity for {}", arg),
                };
                let mut reguse = RegUse::new(arg, num_fixed_args + idx, rci);
                reguse.fixed = true;
                reguse.spilled = spilled;
                self.reg_uses.push(reguse);
            }
        }
    }

    // Process multiple register uses to resolve potential conflicts.
    //
    // Look for multiple uses of the same value in `self.reg_uses` and insert copies as necessary.
    // Trigger spilling if any of the temporaries cause the register pressure to become too high.
    //
    // Leave `self.reg_uses` empty.

    // TODO: Along a branch we must set up the ebb arguments just so.
    //
    // If we're the first branch to reach a destination (the spill state map has no entry for the
    // target ebb) then we record the current affinities for the values that are live-in to that
    // block and the ebb parameters along the edge in a spill state record for the ebb.  If a value
    // is currently spilled its canonical location will be spilled; if it is in a register it will
    // continue to be in a register.
    //
    // Otherwise, we may have to change the parameters here to conform to the state at the target
    // block: If the target block has a spilled value but the value is in a register then we must
    // spill it; if the target block requires a register value but it is spilled then we must fill
    // it.  We can choose whether to do this only along the edge, or do it in-line and thus also
    // affect the subsequent code in the ebb (soon to be bb, so only an unconditional jump at most).
    //
    // [Solved] There's a risk that conforming to a previous ebb can't happen, if that ebb decided
    // to keep more values in registers than we have register for at the subsequent instruction.
    // This can happen if the original branch did not require any register values but the new branch
    // does, leaving less space for values live-in to the target.  However, it is only an issue with
    // a real register, not a flags register, so I'm not sure how much of an issue it really is...
    // Table branches?  And if it's a problem it can be fixed by introducing an intermediate block:
    // we branch conditionally w/o parameters to another block, and jump unconditional from that one
    // with the necessary parameters in the correct place.
    //
    // Several branch instrs have multiple non-flag non-var register arguments.  eg, br_icmp has
    // two; br_table, brz, brnz all have one.
    // 
    // Also, there's the possibility that we won't be able to make the correct spilling decision yet
    // because we don't yet have the necessary liveness information for the target in terms of value
    // names?  We have the parameters... but the liveins?  We get those from the target's immediate
    // dominator, which *could* be this one ... the algorithm in ebb_top in the tracker can be
    // adapted to compute the target's liveins for us.
    //
    // ---
    //
    // For branches, we care about the varargs first since they may have a predetermined
    // location, and the fixed args second, since they can be placed in other registers.
    //
    // In some sense, then:
    //   - if first time through the target
    //       - we keep the var registers + target live-ins we have and flag them as nonspillable, no code is
    //         generated; what's spilled is flagged as spilled, ditto; we take regs for
    //         these
    //       - but importantly we *can* allow spilling of ebb args here, and we must, since there can be
    //         more ebb args than registers, and the ebb args might fill up the space for nonvar values,
    //         so we may have to account (somehow) for the nonvar pressure first in this case.
    //       - we then ensure that any nonvar values we have are filled and then take regs
    //         for all these values
    //   - else
    //       - any var registers + target live-ins we have that need to be in registers are flagged as
    //         nonspillable
    //       - any var registers + ditto we have that need to be spilled are spilled
    //       - any var registers + ditto we have that need to be filled are filled (and these regs
    //         are nonspillable)
    //       - we then ensure that any nonvar values we have are filled and then take regs
    //         for all these values
    //
    // We should not run out of registers for any of this, ie, all spills are explicit, by policy,
    // not by capacity.  If a capacity spill is necessary then we need a do-over: we need to
    // allocate a block w/o params which jumps w/ params to the target, then the branch branches to
    // the new block w/o params.  We should only do this for branches that take register args,
    // otherwise we should panic.
    //
    // Note that none of the EBB parameters will be among the reg_uses; only the fixed params of a
    // branch has been processed.  (Below, only the fixed params are excluded from being spilled in
    // the original code.)
    //
    // This all suggests that we first do a loop (conditionally) to handle any branch args, and
    // exclude values thus found from further spilling.  Then we do the fixed args, which we handle
    // with the existing logic, except that the candidate set is a little more complex.
    //

    fn process_reg_uses(&mut self, inst: Inst, ebb_spill_state: &mut EbbSpillStateMap, tracker: &LiveValueTracker) {

        // TODO: Note this could be multiple targets for table-jump but they all have no ebb params
        // and the same live-ins.  The problem is that *some* of the blocks may have been reached
        // from elsewhere before.  The ACTUAL problem is that those blocks may not be in sync wrt to
        // their live-in locations.  In that case, fixup blocks must be inserted along the paths
        // that violate the prior assumptions.

        // If is_branch, then either target_state==None and targets is Some(vec), or
        // target_state=Some(..) and targets==None.  Otherwise (false,None,None).
        let (is_branch, target_state, targets) : (bool, Option<Vec<EbbSpillState>>, Option<Ebb>) =
/*
            match self.cur.func.dfg[inst] {
            InstructionData::Branch { destination, .. } |
            InstructionData::BranchFloat { destination, .. } |
            InstructionData::BranchIcmp { destination, .. } |
            InstructionData::BranchInt { destination, .. } |
            InstructionData::Jump { destination, .. } => {
                match ebb_spill_state.get(destination) {
                    Some(target_state) => (true, Some(vec![target_state]), None),
                    None => (true, None, Some(vec![target_state]))
                }
            }
            InstructionData::BranchTable { opcode, .. } |
            InstructionData::BranchTableBase { opcode, .. } |
            InstructionData::BranchTableEntry { opcode, .. } |
            _ => {
                debug_assert!(!self.cur.func.dfg[inst].opcode().is_branch());
                (false, None, None)
            }
        };
             */
            (false, None, None);

        // first_time_through means first time we reach the target block(s)
        if is_branch && target_state.is_some() {
/*
            let target_state = if target_state.unwrap().len() > 1 {
                // branch table, and at least one of the blocks has constraints
                // may need to create uniform constraints
                // may need to insert blocks so that uniform constraints can be set up
                // the cheap fix is that if there's a conflict in constraints we just
                //   insert unconstrained blocks for all of them and rewrite the
                //   branch table (that should be fun).
                // we need to return one uniform target state here
                target_state.unwrap()[0]
            } else {
                target_state
            };
             */
            
            // Conform to already-recorded needs:
            //
            // - for each actual ebb argument or live-in that is in a register but is wanted in the stack
            //     spill it
            //
            // - for each actual ebb argument or live-in that is in a register and is wanted there
            //     mark it as unspillable
            //
            // - for each actual ebb argument or live-in that is in a slot but is wanted in a register
            //     fill it
            //       -- this is a small core of the loop below
            //       -- we exclude any unspillables from the set of candidates
            //       -- filling could fail for same reasons documented below?!
            //     mark the register as unspillable
            //
            // - for each actual ebb argument or live-in that is in a slot and is wanted in a slot
            //     assert that it's in the right slot
        }

        // We're looking for multiple uses of the same value, so start by sorting by value. The
        // secondary `opidx` key makes it possible to use an unstable (non-allocating) sort.
        self.reg_uses.sort_unstable_by_key(|u| (u.value, u.opidx));

        self.cur.use_srcloc(inst);
        for i in 0..self.reg_uses.len() {
            let ru = self.reg_uses[i];

            // Do we need to insert a copy for this use?
            let need_copy = if ru.tied {
                true
            } else if ru.fixed {
                // This is a fixed register use which doesn't necessarily require a copy.
                // Make a copy only if this is not the first use of the value.
                self.reg_uses
                    .get(i.wrapping_sub(1))
                    .map_or(false, |ru2| ru2.value == ru.value)
            } else {
                false
            };

            if need_copy {
                let copy = self.insert_copy(ru.value, ru.rci);
                self.cur.func.dfg.inst_args_mut(inst)[ru.opidx as usize] = copy;
            }

            // Even if we don't insert a copy, we may need to account for register pressure for the
            // reload pass.
            if need_copy || ru.spilled {
                let rc = self.reginfo.rc(ru.rci);
                while let Err(mask) = self.pressure.take_transient(rc) {
                    debug!("Copy of {} reg causes spill", rc);
                    // Spill a live register that is *not* used by the current instruction.
                    // Spilling a use wouldn't help.
                    //
                    // Do allow spilling of EBB arguments on branches to the extent not prevented by
                    // the pre-determined allocation.  This is safe if we're the first edge into a
                    // join because other edges flowing to the same join will conform to the
                    // allocation created here and also spill their values.
                    //
                    // Spilling EBB arguments is also necessary since there can be arbitrarily many
                    // EBB arguments.
                    match {
                        let args = if is_branch {
                            if target_state.is_none() {
                                self.cur.func.dfg.inst_fixed_args(inst)
                            } else {
                                // It is possible to get into this situation eg if the first edge
                                // into a join has passed a number of register values equal to the
                                // number of registers available (via a Jump, say), and then a later
                                // edge has the same number of parameters but needs additional
                                // registers (a Branch of some kind).
                                //
                                // TODO: This should not panic!  On register-poor architectures we
                                // should expect to hit this case frequently. What we really need to
                                // do here is split the edge so that we can do a conditional jump to
                                // a new block w/o parameters, and then do a unconditional jump from
                                // the new block w/ parameters.
                                panic!("Ran out of {} registers when trying to spill already-fixed EBB argument at {}",
                                       rc,
                                       self.cur.display_inst(inst));
                            }
                        } else {
                            self.cur.func.dfg.inst_args(inst)
                        };
                        // TODO: No unspillable args are candidates here!!
                        self.spill_candidate(
                            mask,
                            tracker.live().iter().filter(|lv| !args.contains(&lv.value)),
                        )
                    } {
                        Some(cand) => self.spill_reg(cand),
                        None => panic!(
                            "Ran out of {} registers when inserting copy before {}",
                            rc,
                            self.cur.display_inst(inst)
                        ),
                    }
                }
            }
            
            if ru.spilled {
                let fill = self.cur.ins().fill(ru.value);
                self.liveness_invalidated = true;
                self.record_representative(ru.value, fill);
                let rci = self.locations.get(self.virtregs.get(ru.value).unwrap()).unwrap().rci.unwrap();
                self.set_affinity(fill, Affinity::Reg(rci));
            }
        }

        if is_branch && target_state.is_none() {
            let targets = targets.unwrap();
            // record the state that will be conformed to by other edges reaching the target(s) wrt
            // ebb args and live-ins
        }

        self.pressure.reset_transient();
        self.reg_uses.clear()
    }

    // Find a spill candidate from `candidates` whose top-level register class is in `mask`.
    fn spill_candidate<'ii, II>(&self, mask: RegClassMask, candidates: II) -> Option<Value>
    where
        II: IntoIterator<Item = &'ii LiveValue>,
    {
        // Find the best viable spill candidate.
        //
        // The very simple strategy implemented here is to spill the value with the earliest def in
        // the reverse post-order. This strategy depends on a good reload pass to generate good
        // code.
        //
        // We know that all candidate defs dominate the current instruction, so one of them will
        // dominate the others. That is the earliest def.
        candidates
            .into_iter()
            .filter_map(|lv| {
                // Viable candidates are registers in one of the `mask` classes, and not already in
                // the spill set.
                if let Affinity::Reg(rci) = self.affinity(lv.value) {
                    let rc = self.reginfo.rc(rci);
                    if (mask & (1 << rc.toprc)) != 0 && !self.spills.contains(&lv.value) {
                        // Here, `lv` is a viable spill candidate.
                        return Some(lv.value);
                    }
                }
                None
            })
            .min_by(|&a, &b| {
                // Find the minimum candidate according to the RPO of their defs.
                self.domtree.rpo_cmp(
                    self.cur.func.dfg.value_def(a),
                    self.cur.func.dfg.value_def(b),
                    &self.cur.func.layout,
                )
            })
    }

    /// Spill `value` immediately by
    ///
    /// 1. Changing its affinity to `Stack` which marks the spill.
    /// 2. Removing the value from the pressure tracker.
    /// 3. Adding the value to `self.spills` for later reference by `process_spills`.
    ///
    /// Note that this does not update the cached affinity in the live value tracker. Call
    /// `process_spills` to do that.
    fn spill_reg(&mut self, value: Value) {
        let rci = match self.affinity(value) {
            Affinity::Reg(rci) => rci,
            _ => { panic!("Cannot spill {} that was already on the stack", value); }
        };

        let rc = self.reginfo.rc(rci);
        self.pressure.free(rc);

        // Remember that the value was spilled
        self.spills.push(value);

        // Create a spill instruction with the appropriate slot for the spilled value, and set the
        // affinity for the spilled value.
        let spill = self.cur.ins().spill(value);
        self.liveness_invalidated = true;
        self.record_representative(value, spill);
        let slot = self.get_spill_slot(value, rci);
        self.set_affinity(spill, Affinity::Stack);
    }

    fn get_spill_slot(&mut self, value: Value, rci: RegClassIndex) -> StackSlot {
        debug_assert!(self.get_representative(value) == value);
        let vr = self.virtregs.get(value).unwrap();
        match self.locations.get(vr) {
            Some(ValueAndLocations { slot: Some(slot), .. }) => *slot,
            _ => {
                let slot = self
                    .cur
                    .func
                    .stack_slots
                    .make_spill_slot(self.cur.func.dfg.value_type(value));
                self.locations.insert(ValueAndLocations { value: vr, slot: Some(slot), rci: Some(rci) });
                slot
            }
        }
    }
    
    /// Process any pending spills in the `self.spills` vector.
    ///
    /// It is assumed that spills are removed from the pressure tracker immediately, see
    /// `spill_reg` above.
    ///
    /// We also need to update the live range affinity and remove spilled values from the live
    /// value tracker.
    fn process_spills(&mut self) {
        self.spills.clear()
    }

    /// Insert a `copy value` before the current instruction and give it a live range extending to
    /// the current instruction.
    ///
    /// Returns the new local value created.
    fn insert_copy(&mut self, value: Value, rci: RegClassIndex) -> Value {
        let copy = self.cur.ins().copy(value);
        let inst = self.cur.built_inst();

        // Update live ranges.
        self.liveness.create_dead(copy, inst, Affinity::Reg(rci));
        self.liveness.extend_locally(
            copy,
            self.cur.func.layout.pp_ebb(inst),
            self.cur.current_inst().expect("must be at an instruction"),
            &self.cur.func.layout,
        );

        // New value starts out in a register
        self.set_affinity(copy, Affinity::Reg(rci));

        copy
    }

    // The value "repr" is the program-value that is the canonical representation for the newly
    // introduced value "value".  Typically, "value" is created by a fill or spill.
    fn record_representative(&mut self, repr: Value, value: Value) {
        debug_assert!(self.get_representative(repr) == repr);
        self.representative.insert(ValueRepr { value, repr });
    }

    fn get_representative(&self, value: Value) -> Value {
        match self.representative.get(value) {
            None => value,
            Some(ValueRepr { repr, .. }) => *repr
        }
    }
}

/// Struct representing a register use of a value.
/// Used to detect multiple uses of the same value with incompatible register constraints.
#[derive(Clone, Copy)]
struct RegUse {
    value: Value,
    opidx: u16,

    // Register class required by the use.
    rci: RegClassIndex,

    // A use with a fixed register constraint.
    fixed: bool,

    // A register use of a spilled value.
    spilled: bool,

    // A use with a tied register constraint *and* the used value is not killed.
    tied: bool,
}

impl RegUse {
    fn new(value: Value, idx: usize, rci: RegClassIndex) -> Self {
        Self {
            value,
            opidx: idx as u16,
            rci,
            fixed: false,
            spilled: false,
            tied: false,
        }
    }
}

impl fmt::Display for RegUse {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}@op{}", self.value, self.opidx)?;
        if self.fixed {
            write!(f, "/fixed")?;
        }
        if self.spilled {
            write!(f, "/spilled")?;
        }
        if self.tied {
            write!(f, "/tied")?;
        }
        Ok(())
    }
}
