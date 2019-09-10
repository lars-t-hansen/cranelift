//! Spilling pass.
//!
//! TODO/SPLITTER: Update this comment.
//!
//! The spilling pass is the first to run after the liveness analysis. Its primary function is to
//! ensure that the register pressure never exceeds the number of available registers by moving
//! some SSA values to spill slots on the stack. This is encoded in the affinity of the value's
//! live range.
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

// Really does not seem like there's a tremendously good reason to update the affinities in
// liverange and live value tracker until later -- only code here depends on them, and we might as
// well keep our own information in some kind of value-indexed table so that it's easy to manage,
// since we'll be making several passes (?).  We can slot it into liverange/tracker when we're done.

// There seems to be no good reason not to insert spill and fill instructions here.  When we later
// do the renaming, a search up the tree will see these instructions and we can then check the
// arguments.  The best reason to use something else may be that the "something else" can carry more
// information, for example, the fill can perhaps carry the original value as some kind of a
// comment, or maybe it can carry an index into a table (though the Instr is itself that type of
// index, for a hash).
//
// The basic structure is that we move down the ebb, and we insert a spill when we must, and then
// later a fill when we must, and we propagate the information about what's in registers and on the
// stack along all edges to join points and make sure that paths that flow into a join have the
// correct locations for values, if necessary by inserting fills or spills along edges (often this
// means a dummy block to split the edge).  At a join, we may have to merge divergent information
// along the edges by inserting a phi.
//
// We can rename uses as we go *but* a back-edge can cause the insertion of a phi, in which case we
// may have to process the loop again, and then possibly loop successors too.  (And nested loops
// means we may repeat this.)  This turns into a worklist.  It may be faster to insert spills,
// fills, and phis on a first pass, and then do the renaming in a second pass.  *But* then there's
// more information to maintain, or recompute, for the second pass.  *But* we may have to maintain
// some info at join points anyway so that we can insert the correct ebb arguments at all the blocks
// if there's going to be a phi.  *But* we don't have to do that because when we reach the join
// point the first time, it's either with the original name or a new name.  If it's a new name then
// a phi will be required.  If it's the old name there's no info to report; if we later reach the
// join point with a new name, then either there's a phi already (and all argument names from
// previously reached branches are correct) or there's not, in which case all previously reached
// branches will insert the original name.  We just need to be able to distinguish previously
// reached branches from unprocessed ones.  Note we can't wait until all predecessors have been seen
// because that does not work for loops -- we have to commit, and keep enough info to be
// incremental.  It's not even clear multi-pass would do anything for us.
//
// Anything live into the loop is live throughout the loop (b/c backedges) but we only need new phi
// nodes if the value is spilled, so it's definitely pessimal to preemptively introduce phis for the
// live-ins.

// So at least phi insertion is worklist-style - it must be.  But fill and spill analysis need not
// be that, because phi insertion does not increase the number of names we're going to be caring
// about.  If we spill v then we spill v for all points dominated by the spill point, and we insert
// a phi where v' meets the original v.  It's still the one value everywhere.
//
// So this suggests two passes again.
//
// The first pass is RPO, and inserts spills and fills and propagates information across ebb
// boundaries and makes decisions about what the entry state for each live-in var and ebb param for
// each ebb is; it can do that because we can ignore backedges.  Future ebb params will not change
// that because that's just a renaming from live-in to param.  This pass must/can determine the
// ultimate valuelocs for all the names (and by implication for phi-inserted names inserted by next
// pass).  This pass will insert fills at those join points where phis will be needed; we can do
// this because doing so does not require anything more than the valuelocs at the incoming branches,
// and those are given by the first incoming branch (for now).
//
// The second pass is a worklist algorithm, with blocks initially enumerated RPO probably, which
// inserts phis and renames all uses in all instructions.  We can recompute the live-out info or we
// can store it, but since we're looking at everything to do renaming, it's possible recomputing is
// necessary.  For phi insertion we need to pay attention to the constraints listed above about the
// ordering of predecessors.  Here, when we insert an ebb param, we must know which names to use in
// all the predecessors, which means we must either insert a use of the original name or a use of
// the correct name; we can only know the correct name if we've retained a map from
// original->correct for the exit of each predecessor.  So maybe the nodes we put on the worklist are
// the predecessor nodes.  But how does that work for loops?
//
// For phi-inserted names, we just pick up the valuelocs of the arguments, they will by definition
// all be the same.

// The first pass can mark EBBs that need new phis, this is just a flag that is computed when we
// figure out fills at join points (though the flag has a different meaning than "needs a fill"),
// the flag is attached to the join point.  If there's more than one predecessor and a live-in (not
// ebb param) value has been split along at least one path then a phi will be needed.
// 
// It's not clear whether this flag is useful however.  We can use it to create a worklist of ebbs
// that need new parameters, but to what end?

// Code can be brought over from the reloader and merged.  Since we don't spill function parameters
// that are in registers for their lifetime, but only as needed, there is no special processing for
// the entry block, we just need to ensure we pick up the right initial locations for incoming values.
//
// A copy from a register remains just that -- nothing interesting.
//
// A copy from a stack location whose value is required for a register is a little trickier.
// Notionally this is a fill + a copy but then the original value ends up in a register and we don't
// really need that.  Instead, this is a fill from the stack location of the original but to the
// target of the register location of the copy.  A wrinkle to keep in mind.
// 
// The copy_nop hack might no longer be necessary though it's hard to tell, as this is something
// that triggers at EBB boundaries for various CSSA reasons.  We'll have fewer spilled names for
// sure, so assume for now it's not required.
//
// Register defs and call return values are not spilled as part of handling the instruction (all
// results are in the locations they were delivered to) so that's simpler too.

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
use cranelift_entity::{SparseMap, SparseMapValue};
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
/// TODO/SPLITTER: Might also want information about pressure at this node?  Current
/// visit_ebb_header takes registers and thus recomputes pressure so maybe it gets computed there
/// and that's good enough?
struct EbbSpillState {
    key: Ebb,
    liveins: SpillStateMap,
    params: SpillStateMap,
}

impl SparseMapValue<Ebb> for EbbSpillState {
    fn key(&self) -> Ebb {
        self.key
    }
}

/// Persistent data structures for the spilling pass.
pub struct Spilling {
    spills: Vec<Value>,
    reg_uses: Vec<RegUse>
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
    virtregs: &'a VirtRegs,
    topo: &'a mut TopoOrder,

    // Current register pressure.
    pressure: Pressure,

    // Values spilled for the current instruction. These values have already been removed from the
    // pressure tracker, but they are still present in the live value tracker and their affinity
    // hasn't been changed yet.
    spills: &'a mut Vec<Value>,

    // Uses of register values in the current instruction.
    reg_uses: &'a mut Vec<RegUse>,

    // Set to true if the liveness information was invalidated by live range splitting.
    liveness_invalidated: bool,

    // ...
    ebb_spill_state: SparseMap<Ebb, EbbSpillState>,
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
        virtregs: &VirtRegs,
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
            ebb_spill_state: SparseMap::new(),
        };
        ctx.run(tracker);
        ctx.liveness_invalidated
    }
}

impl<'a> Context<'a> {
    fn run(&mut self, tracker: &mut LiveValueTracker) {

        // Create the spill state for the entry block.
        self.init_spill_state(tracker);

        // Pass: Insert spills and fills and compute locations for all names.  It introduces new
        // names for filled and spilled values.
        //
        // This touches each instruction just once.  Uses RPO traversal because spill info is
        // flow-sensitive; however we don't have to worry about loop back-edges because the first
        // edge to reach an EBB decides what the location state is going to be on entry to the EBB;
        // everyone else conforms.
        self.topo.reset(self.domtree.cfg_postorder().iter().rev().map(|x| *x));
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.visit_ebb(ebb, tracker);
        }

        // TODO/SPLITTER: reset liveness data and live range data to initial state?

        // Pass: Insert ebb parameters/arguments as needed and rename all uses.  This introduces new
        // names but their locations are trivially determined because they all belong to VRs that
        // already have locations (determined by the actual arguments).
        //
        // This is a worklist algorithm, since loop back-edges may require us to revisit EBBs
        // multiple times.
        //
        // TODO/SPLITTER: implement
    }

    // Seed the spill state with information about the entry block.
    fn init_spill_state(&mut self, tracker: &mut LiveValueTracker) {
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

        let mut param_info = SparseMap::new();
        for (param_idx, param) in params.iter().enumerate() {
            if !param.is_dead {
                let abi = self.cur.func.signature.params[param_idx];
                let affinity = Affinity::abi(&abi, self.isa);
                param_info.insert(SpillState { value: param.value, affinity });
            }
        };

        self.ebb_spill_state.insert(EbbSpillState {
            key: entry,
            liveins: SparseMap::new(),
            params: param_info
        });
    }

    fn visit_ebb(&mut self, ebb: Ebb, tracker: &mut LiveValueTracker) {
        debug!("Spilling {}:", ebb);
        self.cur.goto_top(ebb);

        self.apply_spill_state(ebb, tracker);

        self.visit_ebb_header(ebb, tracker);
        tracker.drop_dead_params();
        self.process_spills(tracker);

        while let Some(inst) = self.cur.next_inst() {
            if !self.cur.func.dfg[inst].opcode().is_ghost() {
                self.visit_inst(inst, ebb, tracker);
            } else {
                let (_throughs, kills) = tracker.process_ghost(inst);
                self.free_regs(kills);
            }
            tracker.drop_dead(inst);
            self.process_spills(tracker);
        }
    }

    // Apply information about the ebb, merged from all the predecessors.
    //
    // TODO/SPLITTER: Various considerations, as follows:
    //
    // If the merging can happen on the fly as we process each CTI in the predecessors then we don't
    // have to have a special case for the entry block, that special case can go inside run().
    //
    // After application, the information is in several places and must be synchronized:
    //
    // - in the self.cur.func.locations array
    //    - actually, this is only written, never read, so it may be we can ignore this
    //      until the rectification pass, which would be nice?  On the other hand, it
    //      holds the stack location for a stack variable, which can be handy?
    //
    // - in the live value tracker
    // - in the liveness data structure
    //    - these are the same value, it's just cached both places, which is a pain but
    //      better apis can be had to sync them maybe
    // 
    // On entry, we must have information associated with the ebb that allows that information to
    // be reconstructed.  For each live-in value and ebb parameter, we must know:
    //
    // - its spill state (spilled, not)
    // - possibly its VR
    // - possibly its stack location, if any, though that follows from the VR?
    //
    // It's possible the rectification pass will deal with the VR update and the stack slot, as
    // it does renaming and phi insertion.  But we can assume that the VR update will work out
    // and we can assign a stack slot if a value reaches a join point in its spilled state.
    //
    // The information can be stored packed, though that may be an issue at merge points -- not
    // sure yet.
    fn apply_spill_state(&mut self, ebb: Ebb, tracker: &mut LiveValueTracker) {
        let ss = self.ebb_spill_state.get(ebb).unwrap();

        // This should work because at this point the live value tracker should only be aware of
        // liveins.  The affinities for the params are handled in visit_ebb_header as a result of
        // calling tracker.ebb_top.
        for lv in tracker.live_mut() {
            lv.affinity = ss.liveins.get(lv.value).unwrap().affinity;
        }

        // for liverange, we need a new method to mirror its spill() method, call it set_affinity,
        // to set affinity as expected.  this may not be so easy, there are complications with
        // how we handle abi-related values?  
        // self.liveness ...
    }

    // Take all live registers in `regs` from the pressure set.
    // This doesn't cause any spilling, it is assumed there are enough registers.
    fn take_live_regs(&mut self, regs: &[LiveValue]) {
        for lv in regs {
            if !lv.is_dead {
                if let Affinity::Reg(rci) = lv.affinity {
                    let rc = self.reginfo.rc(rci);
                    self.pressure.take(rc);
                }
            }
        }
    }

    // Free all registers in `kills` from the pressure set.
    fn free_regs(&mut self, kills: &[LiveValue]) {
        for lv in kills {
            if let Affinity::Reg(rci) = lv.affinity {
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
                if let Affinity::Reg(rci) = lv.affinity {
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
        // the parameters that are in registers.
        for lv in params {
            if let Affinity::Reg(rci) = lv.affinity {
                if let Err(_) = self.pressure.take_transient(self.reginfo.rc(rci)) {
                    panic!("There should be no spilling here");
                }
            }
        }

        // The transient pressure counts for the EBB arguments are accurate. Just preserve them.
        self.pressure.preserve_transient();
        self.free_dead_regs(params);
    }

    // Insert spills and fills.
    // TODO/SPLITTER: And maybe phis?

    fn visit_inst(&mut self, inst: Inst, ebb: Ebb, tracker: &mut LiveValueTracker) {
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
            self.process_reg_uses(inst, tracker);
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
                if lv.affinity.is_reg() && !self.spills.contains(&lv.value) {
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
                if lr.affinity.is_stack() {
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
                let (rci, spilled) = match self.liveness[arg].affinity {
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

    // TODO/SPLITTER: This must load values that must be in registers into registers, and if there's
    // a capacity problem it must spill other values to the stack.  So this incorporates pieces of
    // the reloader.  Crucially when something is reloaded its location is changed to be reg, so
    // that the loop below that spills across calls can spill it again if it remains live.  (This is
    // suboptimal, we should reuse the slot if we can; that requires keeping information about both
    // reg and ss for a value, at least in tree-shaped regions this seems possible.)

    fn process_reg_uses(&mut self, inst: Inst, tracker: &LiveValueTracker) {
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

            // TODO/SPLITTER: If ru.spilled we must fill it -- what the reload pass would normally
            // do for us.  We would insert a fill, and update the affinity & location information
            // somehow, and when we get to a join we must merge the info from this path into any
            // other paths that have already reached the join.

            // Even if we don't insert a copy, we may need to account for register pressure for the
            // reload pass.
            if need_copy || ru.spilled {
                let rc = self.reginfo.rc(ru.rci);
                while let Err(mask) = self.pressure.take_transient(rc) {
                    debug!("Copy of {} reg causes spill", rc);
                    // Spill a live register that is *not* used by the current instruction.
                    // Spilling a use wouldn't help.
                    //
                    // Do allow spilling of EBB arguments on branches. This is safe since we spill
                    // the whole virtual register which includes the matching EBB parameter value
                    // at the branch destination. It is also necessary since there can be
                    // arbitrarily many EBB arguments.
                    //
                    // TODO/SPLITTER: For branches: If we're not the first branch to reach the
                    // target, we must conform to the setup created by the target.  This has
                    // multiple aspects.  If there was originally a value v flowing along multiple
                    // edges to a block but we now have v, v' then we need a phi.  (v and v' could
                    // have the same affinity and would still need this.)  If v and v' have
                    // different affinities then they must be made the same, requiring a fill or a
                    // spill in one of the branches.  If there's a phi v''=phi(v,v') then v'' and
                    // the joint affinity of v,v' becomes the new name for v in the target block.
                    
                    match {
                        let args = if self.cur.func.dfg[inst].opcode().is_branch() {
                            self.cur.func.dfg.inst_fixed_args(inst)
                        } else {
                            self.cur.func.dfg.inst_args(inst)
                        };
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
                if let Affinity::Reg(rci) = lv.affinity {
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

    /// Spill `value` (that is to say, split its live range) immediately by
    ///
    /// 1. Changing its affinity to `Stack` which marks the spill.
    /// 2. Removing the value from the pressure tracker.
    /// 3. Adding the value to `self.spills` for later reference by `process_spills`.
    ///
    /// Note that this does not update the cached affinity in the live value tracker. Call
    /// `process_spills` to do that.
    fn spill_reg(&mut self, value: Value) {
        if let Affinity::Reg(rci) = self.liveness.spill(value) {
            let rc = self.reginfo.rc(rci);
            self.pressure.free(rc);
            self.spills.push(value);
            debug!("Spilled {}:{} -> {}", value, rc, self.pressure);
        } else {
            panic!("Cannot spill {} that was already on the stack", value);
        }

        // Assign a spill slot for the whole virtual register.
        //

        // TODO/SPLITTER: When we can spill and re-spill this no longer makes sense, need a better
        // mechanism.
        //
        // If the value is merged into another VR that is also (and already) spilled, then we
        // absolutely should not compute a spill slot here.  Yet given that we start out in CSSA
        // form, there will only ever be a single spill slot for all values derived from some
        // initial v.  Thus we can have a map from v to v's spill slot (if any).  The code here will
        // be almost the same, we just have a level of indirection to get the spill slot, we won't
        // always make one.
        //
        // And then we will update locations[v], probably.

        let ss = self
            .cur
            .func
            .stack_slots
            .make_spill_slot(self.cur.func.dfg.value_type(value));

        // TODO/SPLITTER: This isn't right, the congruence class is not affected by splitting the
        // live range of one of its members.
        //
        // Note this is the only use of virtregs currently.  We probably must have some kind of
        // update to virtregs, but the truth is that coloring does not need virtregs, only the old
        // spill/reload passes did, so maybe we can just no longer compute them?
        //
        // verify_cssa() wants virtregs...  but is that a reason to update them / keep them in sync?
        // maybe do so only under the verification flag?

        for &v in self.virtregs.congruence_class(&value) {
            self.liveness.spill(v);

            // TODO/SPLITTER: Really don't need to update locations now, do that later?

            self.cur.func.locations[v] = ValueLoc::Stack(ss);
        }
    }

    /// Process any pending spills in the `self.spills` vector.
    ///
    /// It is assumed that spills are removed from the pressure tracker immediately, see
    /// `spill_reg` above.
    ///
    /// We also need to update the live range affinity and remove spilled values from the live
    /// value tracker.
    fn process_spills(&mut self, tracker: &mut LiveValueTracker) {
        if !self.spills.is_empty() {
            tracker.process_spills(|v| self.spills.contains(&v));
            self.spills.clear()
        }
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

        copy
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
