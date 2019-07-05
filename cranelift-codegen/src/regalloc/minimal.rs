//! Minimal register allocator.
//!
//! The `minimal` register allocator assigns every Value in the incoming program to a unique stack
//! slot, then moves values into registers only as required by each instruction, and finally moves
//! any values defined by the instruction out of registers directly after the instruction.
//!
//! The values that are in registers are new Value slots, and the instructions are updated to take
//! these new Values as arguments and produce them as results.  Value movement is through fill and
//! spill instructions.
//!
//! The allocator must handle the function ABI and two-address operations (tied registers) and must
//! obey all instruction constraints (eg fixed registers and register classes), but is otherwise the
//! simplest register allocator imaginable for our given IR structure.

// TODO: can we factor more code?
// TODO: can the flags hack be generalized?

use std::vec::Vec;

use crate::cursor::{Cursor, EncCursor};
use crate::dominator_tree::DominatorTree;
use crate::flowgraph::ControlFlowGraph;
use crate::ir::{
    AbiParam, ArgumentLoc, Ebb, Function, Inst, InstBuilder, InstructionData, Opcode,
    StackSlotKind, Type, Value, ValueLoc,
};
use crate::isa::registers::{RegClass, RegUnit};
use crate::isa::{ConstraintKind, EncInfo, TargetIsa};
use crate::regalloc::register_set::RegisterSet;
use crate::topo_order::TopoOrder;

/// Register allocator state.
pub struct Minimal {}

impl Minimal {
    /// Create a new register allocator state.
    pub fn new() -> Self {
        Self {}
    }

    /// Clear the state of the allocator.
    pub fn clear(&mut self) {}

    /// Run register allocation.
    pub fn run(
        &mut self,
        isa: &TargetIsa,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        domtree: &mut DominatorTree,
        topo: &mut TopoOrder,
    ) {
        let mut ctx = Context {
            new_blocks: false,
            usable_regs: isa.allocatable_registers(func),
            cur: EncCursor::new(func, isa),
            encinfo: isa.encoding_info(),
            domtree,
            topo,
            cfg,
        };
        ctx.run()
    }
}

struct Regs {
    registers: RegisterSet,
}

impl Regs {
    fn new(registers: RegisterSet) -> Self {
        Self { registers }
    }

    fn take_specific(&mut self, rc: RegClass, r: RegUnit) {
        self.registers.take(rc, r);
    }

    fn take(&mut self, rc: RegClass) -> Option<RegUnit> {
        // FIXME: This is probably quite slow.
        let mut i = self.registers.iter(rc);
        let r = i.next();
        if r.is_some() {
            self.registers.take(rc, r.unwrap());
        }
        r
    }

    fn free(&mut self, rc: RegClass, r: RegUnit) {
        self.registers.free(rc, r);
    }
}

struct Context<'a> {
    // True if new blocks were inserted
    new_blocks: bool,

    // Set of registers that the allocator can use.
    usable_regs: RegisterSet,

    // Current instruction as well as reference to function and ISA.
    cur: EncCursor<'a>,

    // Cached ISA information.
    // We save it here to avoid frequent virtual function calls on the `TargetIsa` trait object.
    encinfo: EncInfo,

    // References to contextual data structures we need.
    domtree: &'a mut DominatorTree,
    topo: &'a mut TopoOrder,
    cfg: &'a mut ControlFlowGraph,
}

impl<'a> Context<'a> {
    fn run(&mut self) {
        dbg!(&self.cur.func);

        // For the entry block, spill register parameters to the stack while retaining their names.
        self.visit_entry_block(self.cur.func.layout.entry_block().unwrap());

        // For all blocks other than the entry block, assign stack slots to all block parameters so
        // that we can later process control transfer instructions.
        self.visit_other_blocks();

        // Process all instructions in domtree order so that we'll always know the location of a
        // definition when we see its use.  Fill any register args before the instruction and spill
        // any definitions after.
        let mut regs = Regs::new(self.usable_regs.clone());
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.cur.goto_top(ebb);
            while let Some(inst) = self.cur.next_inst() {
                if !self.cur.func.dfg[inst].opcode().is_ghost() {
                    self.visit_inst(inst, &mut regs);
                }
            }
        }

        // If blocks were added the cfg and domtree are inconsistent and must be recomputed.
        if self.new_blocks {
            self.cfg.compute(&self.cur.func);
            self.domtree.compute(&self.cur.func, self.cfg);
        }

        dbg!(&self.cur.func);
        dbg!(&self.cur.func.locations);
    }

    fn visit_entry_block(&mut self, entry: Ebb) {
        let signature_info: Vec<_> = self
            .cur
            .func
            .dfg
            .ebb_params(entry)
            .iter()
            .zip(&self.cur.func.signature.params)
            .map(|(param, abi)| (*param, *abi))
            .collect();

        self.cur.goto_first_inst(entry);
        for (param, abi) in signature_info {
            match abi.location {
                ArgumentLoc::Reg(reg) => {
                    let new_param = self.cur.func.dfg.replace_ebb_param(param, abi.value_type);
                    self.spill_register(reg, new_param, param, abi.value_type);
                }
                ArgumentLoc::Stack(_offset) => {
                    // Incoming stack arguments have sensible pre-initialized locations.
                    debug_assert!(
                        if let ValueLoc::Stack(_ss) = self.cur.func.locations[param] {
                            true
                        } else {
                            false
                        }
                    );
                }
                ArgumentLoc::Unassigned => {
                    panic!("Should not happen");
                }
            }
        }
    }

    fn visit_other_blocks(&mut self) {
        let entry = self.cur.func.layout.entry_block().unwrap();
        self.topo.reset(self.cur.func.layout.ebbs());

        // Skip the entry block.
        let first = self.topo.next(&self.cur.func.layout, self.domtree).unwrap();
        debug_assert!(first == entry);

        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            for param in self.cur.func.dfg.ebb_params(ebb) {
                let ss = self
                    .cur
                    .func
                    .stack_slots
                    .make_spill_slot(self.cur.func.dfg.value_type(*param));
                self.cur.func.locations[*param] = ValueLoc::Stack(ss);
            }
        }
    }

    fn visit_inst(&mut self, inst: Inst, regs: &mut Regs) {
        let opcode = self.cur.func.dfg[inst].opcode();
        if opcode == Opcode::Copy {
            self.visit_copy(inst);
        } else if opcode.is_branch() {
            self.visit_branch(inst, regs, opcode);
        } else if opcode.is_terminator() {
            self.visit_terminator(inst, opcode);
        } else if opcode.is_call() {
            self.visit_call(inst, regs, opcode);
        } else if opcode == Opcode::Spill && self.is_spill_to_outgoing_arg(inst) {
            self.visit_outgoing_arg_spill(inst, regs);
        } else if opcode == Opcode::Spill || opcode == Opcode::Fill {
            // Inserted by the register allocator; ignore them.
        } else {
            // Some opcodes should not be encountered here.
            debug_assert!(
                opcode != Opcode::Regmove
                    && opcode != Opcode::Regfill
                    && opcode != Opcode::Regspill
                    && opcode != Opcode::CopySpecial
            );
            self.visit_plain_inst(inst, regs);
        }
    }

    fn visit_copy(&mut self, inst: Inst) {
        // As the stack slots are immutable, a copy is simply a sharing of location.
        let arg = self.cur.func.dfg.inst_args(inst)[0];
        let dest = self.cur.func.dfg.inst_results(inst)[0];
        self.cur.func.locations[dest] = self.cur.func.locations[arg];
    }

    fn visit_branch(&mut self, inst: Inst, regs: &mut Regs, opcode: Opcode) {
        let (target_info, has_argument) = self.classify_branch(inst, opcode);
        if let Some((target, side_exit)) = target_info {
            // Insert the fill/spill along the taken edge only.  May have to create a new block to
            // hold the fill/spill instructions.

            let mut inst = inst;
            let mut orig_inst = inst;

            let new_block = side_exit && self.cur.func.dfg.ebb_params(target).len() > 0;
            if new_block {
                // Remember the arguments to the side exit.
                let jump_args: Vec<Value> = self
                    .cur
                    .func
                    .dfg
                    .inst_variable_args(inst)
                    .iter()
                    .map(|x| *x)
                    .collect();

                // Create the block the side exit will jump to.
                let new_ebb = self.make_empty_ebb();

                // Remove the arguments from the side exit and make it jump to the new block.
                self.rewrite_side_exit(inst, opcode, new_ebb);

                if has_argument {
                    self.fill_register_args(inst, regs, true);
                    orig_inst = self.cur.current_inst().unwrap();
                }

                // Insert a jump to the original target with the original arguments into the new
                // block.
                self.cur.goto_first_insertion_point(new_ebb);
                self.cur.ins().jump(target, jump_args.as_slice());

                // Make the fill/spill code below target the jump instruction in the new block,
                // otherwise it won't be visited, as it is not in the current topo order.
                self.cur.goto_first_inst(new_ebb);
                inst = self.cur.current_inst().unwrap();
            } else if has_argument {
                self.fill_register_args(inst, regs, true);
            }

            let arginfo: Vec<_> = self
                .cur
                .func
                .dfg
                .ebb_params(target)
                .iter()
                .zip(self.cur.func.dfg.inst_args(inst).iter())
                .map(|(a, b)| (*b, *a))
                .enumerate()
                .collect();

            for (k, (arg, target_arg)) in arginfo {
                let temp = self.cur.ins().fill(arg);
                let dest = self.cur.ins().spill(temp);
                let spill = self.cur.built_inst();
                let enc = self.cur.func.encodings[spill];
                let constraints = self.encinfo.operand_constraints(enc).unwrap();
                let rc = constraints.ins[0].regclass;
                let reg = regs.take(rc).unwrap();
                self.cur.func.locations[temp] = ValueLoc::Reg(reg);
                self.cur.func.dfg.inst_args_mut(inst)[k] = dest;
                regs.free(rc, reg);
                self.cur.func.locations[dest] = self.cur.func.locations[target_arg];
            }

            // Restore the point, so that the iteration will work correctly.
            if new_block {
                self.cur.goto_inst(orig_inst);
            }
        } else if has_argument {
            self.fill_register_args(inst, regs, true);
        }
    }

    fn visit_terminator(&mut self, inst: Inst, opcode: Opcode) {
        // Some terminators are handled as branches and should not be seen here; others are illegal.
        match opcode {
            Opcode::Return | Opcode::FallthroughReturn => {
                let abi_info = self.make_abi_info(
                    self.cur.func.dfg.inst_args(inst),
                    &self.cur.func.signature.returns,
                );
                let to_stack = self.load_abi_registers(inst, &abi_info);
                debug_assert!(!to_stack);
            }
            Opcode::Trap => {}
            _ => unreachable!(),
        }
    }

    fn make_abi_info(&self, vals: &[Value], abi: &[AbiParam]) -> Vec<(usize, (Value, AbiParam))> {
        vals.iter()
            .zip(abi)
            .map(|(val, abi)| (*val, *abi))
            .enumerate()
            .collect()
    }

    fn load_abi_registers(&mut self, inst: Inst, abi_info: &[(usize, (Value, AbiParam))]) -> bool {
        let mut to_stack = false;
        for (k, (val, abi)) in abi_info {
            match abi.location {
                ArgumentLoc::Reg(r) => {
                    let temp = self.cur.ins().fill(*val);
                    self.cur.func.locations[temp] = ValueLoc::Reg(r);
                    self.cur.func.dfg.inst_variable_args_mut(inst)[*k] = temp;
                }
                _ => {
                    to_stack = true;
                }
            }
        }
        to_stack
    }

    fn store_abi_registers(
        &mut self,
        inst: Inst,
        abi_info: &[(usize, (Value, AbiParam))],
    ) -> (bool, Inst) {
        let mut from_stack = false;
        let mut last = inst;
        for (_, (result, abi)) in abi_info {
            match abi.location {
                ArgumentLoc::Reg(reg) => {
                    last = self.spill_result_from_register(*result, reg);
                    self.cur.goto_after_inst(last);
                }
                _ => {
                    from_stack = true;
                }
            }
        }
        (from_stack, last)
    }

    fn visit_outgoing_arg_spill(&mut self, inst: Inst, regs: &mut Regs) {
        debug_assert!(self.cur.func.dfg[inst].opcode() == Opcode::Spill);
        let arg = self.cur.func.dfg.inst_args(inst)[0];
        let temp = self.cur.ins().fill(arg);
        let enc = self.cur.func.encodings[inst];
        let constraints = self.encinfo.operand_constraints(enc).unwrap();
        let rc = constraints.ins[0].regclass;
        let reg = regs.take(rc).unwrap();
        self.cur.func.locations[temp] = ValueLoc::Reg(reg);
        self.cur.func.dfg.inst_args_mut(inst)[0] = temp;
        regs.free(rc, reg);
    }

    fn visit_call(&mut self, inst: Inst, regs: &mut Regs, _opcode: Opcode) {
        let enc = self.cur.func.encodings[inst];
        let constraints = self.encinfo.operand_constraints(enc).unwrap();

        let sig = self.cur.func.dfg.call_signature(inst).unwrap();

        // Setup register arguments
        let arg_info = self.make_abi_info(
            self.cur.func.dfg.inst_variable_args(inst),
            &self.cur.func.dfg.signatures[sig].params,
        );
        self.load_abi_registers(inst, &arg_info);

        // Reserve the ABI registers so we don't reuse them for any fixed args.
        for (k, (val, abi)) in &arg_info {
            if let ArgumentLoc::Reg(r) = abi.location {
                let ty = self.cur.func.dfg.value_type(*val);
                let rc = self.cur.isa.regclass_for_abi_type(ty).into();
                regs.take_specific(rc, r);
            }
        }

        // Load fixed args.
        self.fill_register_args(inst, regs, true);

        // Unreserve the ABI registers.
        for (k, (val, abi)) in &arg_info {
            if let ArgumentLoc::Reg(r) = abi.location {
                let ty = self.cur.func.dfg.value_type(*val);
                let rc = self.cur.isa.regclass_for_abi_type(ty).into();
                regs.free(rc, r);
            }
        }

        // Move past the instruction
        self.cur.goto_after_inst(inst);

        // Capture results
        let result_info = self.make_abi_info(
            self.cur.func.dfg.inst_results(inst),
            &self.cur.func.dfg.signatures[sig].returns,
        );
        let (from_stack, last) = self.store_abi_registers(inst, &result_info);
        debug_assert!(!from_stack);

        self.cur.goto_inst(last);
    }

    fn visit_plain_inst(&mut self, inst: Inst, regs: &mut Regs) {
        let reg_args = self.fill_register_args(inst, regs, false);
        self.spill_register_results(inst, regs, reg_args);
    }

    // This will not free any tied registers it allocates.  It leaves the point at `inst`.  The
    // return value reflects the allocated registers (all of them), some of which may no longer have
    // been taken from regs.
    fn fill_register_args(&mut self, inst: Inst, regs: &mut Regs, fixed: bool) -> Vec<(usize, Value, RegClass, RegUnit, bool)> {
        let constraints = self
            .encinfo
            .operand_constraints(self.cur.func.encodings[inst]);

        // Reserve any fixed input registers.
        if let Some(constraints) = constraints {
            if constraints.fixed_ins {
                for constraint in constraints.ins {
                    match constraint.kind {
                        ConstraintKind::FixedReg(r) => regs.take_specific(constraint.regclass, r),
                        ConstraintKind::FixedTied(r) => regs.take_specific(constraint.regclass, r),
                        _ => {}
                    }
                }
            }
        }

        // Assign all input registers.
        let mut reg_args = vec![];
        for (k, arg) in if fixed { self.cur.func.dfg.inst_fixed_args(inst) } else { self.cur.func.dfg.inst_args(inst) }.iter().enumerate() {
            debug_assert!(
                if let ValueLoc::Stack(_ss) = self.cur.func.locations[*arg] {
                    true
                } else {
                    self.cur.func.dfg.value_type(*arg).is_flags()
                }
            );
            let constraint = &constraints.unwrap().ins[k];
            if constraint.kind == ConstraintKind::Stack {
                continue;
            }
            let rc = constraint.regclass;
            let (reg, is_tied) = match constraint.kind {
                ConstraintKind::FixedReg(r) => (r, false),
                ConstraintKind::FixedTied(r) => (r, true),
                ConstraintKind::Tied(_) => (regs.take(rc).unwrap(), true),
                ConstraintKind::Reg => (regs.take(rc).unwrap(), false),
                ConstraintKind::Stack => unreachable!(),
            };
            reg_args.push((k, *arg, rc, reg, is_tied));
        }

        // Insert fills, assign locations, update the instruction, free registers.
        for (k, arg, rc, reg, is_tied) in &reg_args {
            let value_type = self.cur.func.dfg.value_type(*arg);
            if value_type.is_flags() {
                self.cur.func.locations[*arg] = ValueLoc::Reg(*reg);
            } else {
                let temp = self.cur.ins().fill(*arg);
                self.cur.func.locations[temp] = ValueLoc::Reg(*reg);
                if fixed {
                    self.cur.func.dfg.inst_fixed_args_mut(inst)[*k] = temp;
                } else {
                    self.cur.func.dfg.inst_args_mut(inst)[*k] = temp;
                }
            }
            if !*is_tied {
                regs.free(*rc, *reg);
            }
        }

        reg_args
    }

    // This will assume that tied registers are already allocated.  It leaves the point at the last
    // instruction inserted after `inst`, if any.
    fn spill_register_results(&mut self, inst: Inst, regs: &mut Regs, reg_args: Vec<(usize, Value, RegClass, RegUnit, bool)>) {
        let constraints = self
            .encinfo
            .operand_constraints(self.cur.func.encodings[inst]);

        // Reserve any fixed output registers that are not also tied.
        if let Some(constraints) = constraints {
            if constraints.fixed_outs {
                for constraint in constraints.outs {
                    match constraint.kind {
                        ConstraintKind::FixedReg(r) => regs.take_specific(constraint.regclass, r),
                        _ => {}
                    }
                }
            }
        }

        // Assign the output registers.
        let mut reg_results = vec![];
        for (k, result) in self.cur.func.dfg.inst_results(inst).iter().enumerate() {
            let constraint = &constraints.unwrap().outs[k];
            debug_assert!(constraint.kind != ConstraintKind::Stack);
            let (rc, reg) = match constraint.kind {
                ConstraintKind::FixedTied(r) => (constraint.regclass, r),
                ConstraintKind::FixedReg(r) => (constraint.regclass, r),
                ConstraintKind::Tied(input) => {
                    let hit = *reg_args
                        .iter()
                        .filter(|(input_k, ..)| *input_k == input as usize)
                        .next()
                        .unwrap();
                    debug_assert!(hit.4);
                    (hit.2, hit.3)
                }
                ConstraintKind::Reg => {
                    (constraint.regclass, regs.take(constraint.regclass).unwrap())
                }
                ConstraintKind::Stack => unreachable!(),
            };
            reg_results.push((k, *result, rc, reg));
        }

        // Insert spills, assign locations, update the instruction, free registers.
        let mut last = inst;
        self.cur.goto_after_inst(inst);
        for (_k, result, rc, reg) in reg_results {
            let value_type = self.cur.func.dfg.value_type(result);
            if value_type.is_flags() {
                self.cur.func.locations[result] = ValueLoc::Reg(reg);
            } else {
                last = self.spill_result_from_register(result, reg);
                self.cur.goto_after_inst(last);
            }

            regs.free(rc, reg);
        }
        self.cur.goto_inst(last);
    }

    fn spill_result_from_register(&mut self, result: Value, reg: RegUnit) -> Inst {
        let value_type = self.cur.func.dfg.value_type(result);
        let new_result = self.cur.func.dfg.replace_result(result, value_type);
        self.spill_register(reg, new_result, result, value_type)
    }

    fn spill_register(&mut self, reg: RegUnit, regname: Value, stackname: Value, value_type: Type) -> Inst {
        self.cur.func.locations[regname] = ValueLoc::Reg(reg);
        self.cur.ins().with_result(stackname).spill(regname);
        let spill = self.cur.built_inst();
        let ss = self.cur.func.stack_slots.make_spill_slot(value_type);
        self.cur.func.locations[stackname] = ValueLoc::Stack(ss);
        spill
    }

    fn is_spill_to_outgoing_arg(&self, inst: Inst) -> bool {
        debug_assert!(self.cur.func.dfg[inst].opcode() == Opcode::Spill);
        let result = self.cur.func.dfg.inst_results(inst)[0];
        if let ValueLoc::Stack(ss) = self.cur.func.locations[result] {
            return self.cur.func.stack_slots[ss].kind == StackSlotKind::OutgoingArg;
        }
        false
    }

    // Returns (Option<(target_ebb, side_exit)>, has_argument)
    fn classify_branch(&self, inst: Inst, opcode: Opcode) -> (Option<(Ebb, bool)>, bool) {
        match self.cur.func.dfg[inst] {
            InstructionData::IndirectJump { .. } => {
                debug_assert!(opcode == Opcode::IndirectJumpTableBr);
                (None, true)
            }
            InstructionData::Jump { destination, .. } => {
                // There should be no Opcode::Fallthrough nodes at this stage.
                debug_assert!(opcode == Opcode::Jump);
                (Some((destination, false)), false)
            }
            InstructionData::Branch { destination, .. } => {
                debug_assert!(opcode == Opcode::Brz || opcode == Opcode::Brnz);
                (Some((destination, true)), true)
            }
            InstructionData::BranchIcmp { destination, .. } => {
                debug_assert!(opcode == Opcode::BrIcmp);
                (Some((destination, true)), true)
            }
            InstructionData::BranchInt { destination, .. } => {
                debug_assert!(opcode == Opcode::Brif);
                (Some((destination, true)), true)
            }
            InstructionData::BranchFloat { destination, .. } => {
                debug_assert!(opcode == Opcode::Brff);
                (Some((destination, true)), true)
            }
            _ => {
                panic!("Unexpected instruction in classify_branch");
            }
        }
    }

    // Make `inst`, which must be a side exit branch with operation `opcode`, jump to `new_ebb`
    // without any arguments.
    fn rewrite_side_exit(&mut self, inst: Inst, opcode: Opcode, new_ebb: Ebb) {
        match opcode {
            Opcode::Brz => {
                let val = self.cur.func.dfg.inst_args(inst)[0];
                self.cur.func.dfg.replace(inst).brz(val, new_ebb, &[]);
            }
            Opcode::Brnz => {
                let val = self.cur.func.dfg.inst_args(inst)[0];
                self.cur.func.dfg.replace(inst).brnz(val, new_ebb, &[]);
            }
            Opcode::BrIcmp => {
                if let InstructionData::BranchIcmp { cond, .. } = self.cur.func.dfg[inst] {
                    let x = self.cur.func.dfg.inst_args(inst)[0];
                    let y = self.cur.func.dfg.inst_args(inst)[0];
                    self.cur
                        .func
                        .dfg
                        .replace(inst)
                        .br_icmp(cond, x, y, new_ebb, &[]);
                }
            }
            Opcode::Brif => {
                if let InstructionData::BranchInt { cond, .. } = self.cur.func.dfg[inst] {
                    let val = self.cur.func.dfg.inst_args(inst)[0];
                    self.cur
                        .func
                        .dfg
                        .replace(inst)
                        .brif(cond, val, new_ebb, &[]);
                }
            }
            Opcode::Brff => {
                if let InstructionData::BranchFloat { cond, .. } = self.cur.func.dfg[inst] {
                    let val = self.cur.func.dfg.inst_args(inst)[0];
                    self.cur
                        .func
                        .dfg
                        .replace(inst)
                        .brff(cond, val, new_ebb, &[]);
                }
            }
            _ => {
                panic!("Unhandled side exit type");
            }
        }
        let ok = self.cur.func.update_encoding(inst, self.cur.isa).is_ok();
        debug_assert!(ok);
    }

    // A new ebb must be inserted before the last ebb because the last ebb may have a
    // fallthrough_return and can't have anything after it.
    fn make_empty_ebb(&mut self) -> Ebb {
        let new_ebb = self.cur.func.dfg.make_ebb();
        let last_ebb = self.cur.layout().last_ebb().unwrap();
        self.cur.layout_mut().insert_ebb(new_ebb, last_ebb);
        self.new_blocks = true;
        new_ebb
    }
}
