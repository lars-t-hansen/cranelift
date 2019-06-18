//! Rematerialize constants and simple expressions close to their uses.
//!
//! Rematerialization has the effect of shrinking live ranges of flow-invariant values, and thus it
//! generally reduces register pressure.  But it may also introduce redundancies that would better
//! be avoided.
//!
//! Rematerialization should be done after hoisting / gvn, as those optimizations might otherwise
//! undo the work we do here.
//!
//! Rematerialization should be done before dce, as dce will remove any values that became
//! unreferenced as a result of rematerialization.  We really need to remove dead phi arguments as
//! part of dce for this to be truly effective.

// TODO: I see some fp constants are being lowered to load-integer-bits + move-to-fp-reg but this
// should not be necessary?
//
// TODO: Limitations on which values we accept?
//
// TODO: This may end up moving integer loads into loops, which may not be what we want.
//
// TODO: Can reuse a previous (dominating) constant, if it doesn't lead to spilling...  But this
// gets us further into regalloc territory.

// There are several ways of doing this, but since the values we replace are flow-independent we can
// just look at each instruction in turn and if any of its input values are constants (or other
// simple expressions we can use) we can just create a copy before the instruction and rewrite the
// instruction.
//
// However, if rematerializing the constant has an effect on the flags then we can't do it blindly;
// we must respect the flags.  This is a little tricky, but we can track the state of the flags
// (dead or alive) and insert constants where the flags are dead.

use crate::cursor::{Cursor, EncCursor};
use crate::isa::TargetIsa;
use crate::ir::{Ebb, Function, InstBuilder, Opcode, InstructionData, ValueDef};
use crate::ir::immediates::{Imm64, Ieee32, Ieee64};
use crate::ir::types;
use std::vec::Vec;

enum Const {
    I32(Imm64),
    I64(Imm64),
    F32(Ieee32),
    F64(Ieee64),
    F32Complex(Imm64),
    F64Complex(Imm64)
}

pub fn do_rematerialize(isa: &TargetIsa, func: &mut Function) {
    let mut cur = EncCursor::new(func, isa);
    let ebbs = cur.func.layout.ebbs().collect::<Vec<Ebb>>();

    for ebb in ebbs {
        cur.goto_first_inst(ebb);
        let mut point = cur.current_inst().unwrap();
        let mut flags_are_dead = true;

        cur.goto_top(ebb);
        while let Some(inst) = cur.next_inst() {

            // Compute the effect of the instruction on the flags and move the point if appropriate.
            // There's an assumption here that an instruction that sets the flags does not also read
            // the flags; this may be too restrictive?
            if let Some(constraints) = isa
                .encoding_info()
                .operand_constraints(cur.func.encodings[inst])
            {
                flags_are_dead = constraints.clobbers_flags;
            }
            if flags_are_dead {
                point = inst;
            }
            if cur.func.dfg[inst].opcode().writes_cpu_flags() {
                flags_are_dead = false;
            }

            // Record the argument positions in inst that must change.
            let mut consts = vec![];
            let mut i = 0;
            for arg in cur.func.dfg.inst_args(inst) {
                if let ValueDef::Result(src, _) = cur.func.dfg.value_def(*arg) {
                    let id = &cur.func.dfg[src];
                    if let InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } = *id {
                        if cur.func.dfg.ctrl_typevar(src) == types::I32 {
                            consts.push((i, Const::I32(imm)));
                        } else {
                            consts.push((i, Const::I64(imm)));
                        }
                    } else if let InstructionData::UnaryIeee32 { imm, .. } = *id {
                        consts.push((i, Const::F32(imm)));
                    } else if let InstructionData::UnaryIeee64 { imm, .. } = *id {
                        consts.push((i, Const::F64(imm)));
                    } else if let InstructionData::Unary { opcode: Opcode::Bitcast, arg: unarg } = *id {
                        match cur.func.dfg.ctrl_typevar(src) {
                            types::F32 => {
                                if let ValueDef::Result(unsrc, _) = cur.func.dfg.value_def(unarg) {
                                    let unid = &cur.func.dfg[unsrc];
                                    if let InstructionData::UnaryImm { opcode: Opcode::Iconst, imm: unimm } = *unid {
                                        if cur.func.dfg.ctrl_typevar(unsrc) == types::I32 {
                                            consts.push((i, Const::F32Complex(unimm)));
                                        }
                                    }
                                }
                            }
                            types::F64 => {
                                if let ValueDef::Result(unsrc, _) = cur.func.dfg.value_def(unarg) {
                                    let unid = &cur.func.dfg[unsrc];
                                    if let InstructionData::UnaryImm { opcode: Opcode::Iconst, imm: unimm } = *unid {
                                        if cur.func.dfg.ctrl_typevar(unsrc) == types::I64 {
                                            consts.push((i, Const::F64Complex(unimm)));
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                i += 1;
            }

            // Update inst if necessary.
            if consts.len() > 0 {
                cur.goto_inst(point);

                for (i, imm) in consts {
                    let new_const = match imm {
                        Const::I32(imm_val) => cur.ins().iconst(types::I32, imm_val),
                        Const::I64(imm_val) => cur.ins().iconst(types::I64, imm_val),
                        Const::F32(imm_val) => cur.ins().f32const(imm_val),
                        Const::F64(imm_val) => cur.ins().f64const(imm_val),
                        Const::F32Complex(imm_val) => {
                            let imm = cur.ins().iconst(types::I32, imm_val);
                            cur.ins().bitcast(types::F32, imm)
                        }
                        Const::F64Complex(imm_val) => {
                            let imm = cur.ins().iconst(types::I64, imm_val);
                            cur.ins().bitcast(types::F64, imm)
                        }
                    };
                    cur.func.dfg.inst_args_mut(inst)[i] = new_const;
                }

                cur.goto_inst(inst);
            }
        }
    }
}
