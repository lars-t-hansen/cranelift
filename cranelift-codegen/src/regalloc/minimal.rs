//! Minimal register allocator.
//!
//! This allocator moves values into registers only as required by each instruction, and moves any
//! defined values out of registers directly after the instruction.  It must handle two-address
//! operations and stack arguments and must obey all register constraints, but is otherwise the
//! simplest register allocator imaginable for our given IR structure.


// About stack slots:
//
// The entry ebb must have locations for its incoming parameters that correspond to the ABI
// locations of the function's parameters.  For incoming register args, they are in registers.  For
// incoming stack arguments, they are flagged as being in incoming_arg stack slots.  It's OK for
// them to live in those slots throughout.
//
// On function calls that have stack args, we must spill those arguments immediately before the call
// to stack slots that are marked outoing_arg.
//
// Stack slots for spilled non-incoming non-outgoing values are labeled simply spill_slot.
//
// All stack slots carry offsets (that are interpreted in the context of their type).
//
// Slots are created by make_spill_slot / make_incoming_arg / get_outgoing_arg in ir/stackslot.rs.
// The latter two need to be told the offset that the slot carries.
//
// There are also emergency slots used for emergency spills, see same file.  We may need these once
// we implement parallel assignment, though it's best to avoid them.
//
//
// About function calls:
//
// The register allocator populates outgoing argument registers with normal register moves and
// outgoing stack slots with spills, directly before the call instruction.  The code generator does
// not insert additional code around the call instruction for anything at all.
//
// => How do we obtain and process ABI information?
//
// 
// About two-address instructions:
//
// These are expressed as tied operands to an instruction, I think - output is tied to one of the
// inputs.  This causes us no particular concern since the register is newly live and we will save
// its value immediately after the operation and then kill the register.
//
//
// About constraints:
//
// => Which constraints are there?  eg, byte register / subregister; register hint; register
// requirement (for some instructions); others?


use crate::flowgraph::ControlFlowGraph;
use crate::fx::FxHashMap;
use crate::cursor::{Cursor, EncCursor};
use crate::entity::{SparseMap, SparseMapValue};
use crate::dominator_tree::DominatorTree;
use crate::ir::{ArgumentLoc, Ebb, Function, Inst, InstBuilder, SigRef, Value, ValueLoc, StackSlot};
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
//use std::vec::Vec;

/// Map from a name in the original program to information about where it's spilled.
type SpillMap = SparseMap<Value, SpillInfo>;

/// Represents spilling information for a name.
struct SpillInfo {
    // The name as it is used in the original program
    name: Value,

    // The name under which the spill slot is known in the region dominated by the definition of
    // `name`
    spill_name: Value,

    // The stack slot used for the spill
    slot: StackSlot
}

impl SparseMapValue<Value> for SpillInfo
{
    fn key(&self) -> Value {
        self.name
    }
}

/// Register allocator state.
pub struct Minimal {
    spills: SpillMap
}

impl Minimal {
    /// Create a new register allocator state.
    pub fn new() -> Self {
        Self {
            spills: SpillMap::new()
        }
    }

    /// Clear the state of the allocator.
    pub fn clear(&mut self) {
        self.spills.clear();
    }

    // Minimal register allocator.
    //
    // Here, every value is on the stack always except right before an instruction that uses the
    // value.  This is just an exercise to learn how to process the input and create correct output.
    //
    // on entry
    //   spill all register arguments into the correct stack locations
    //
    // for each ebb
    //   for each instruction in the ebb
    //     before the instruction:
    //       load the uses[*][**] into the correct registers
    //     annotate the instruction with those registers
    //     after the instruction:
    //       spill the definitions into the correct locations
    //
    // [*] CTIs are different wrt uses.  These may pass arguments but those arguments are never
    // placed in registers in v0.  Instead, we copy from the locations of the arguments to the
    // locations of the phi parameters.
    //
    // [**] Calls may be different wrt uses, not sure.
    //
    //
    // Open questions:
    //
    // - I think there should be no fallthrough instructions at this point in the pipeline, we
    //   should assert that.
    //
    // - For calls we have to move register args into abi registers, but what do we do about the
    //   stack args?  do we use stack locations?
    //
    // - How do we annotate the instruction with register names?
    //   here's some code from the coloring pass that is very evocative:
    //       self.cur.func.locations[lv.value] = ValueLoc::Reg(reg);
    //   indeed the code in color_entry_params() seems highly useful.
    //
    // - How do we manage spill locations?  for v0 we can have one location per value, even if this
    //   is pretty insane, but it simplifies everything.
    //
    // - How are the load-from-stack and store-to-stack instructions expressed in the ir?  Really we
    //   probably have RegFill and RegSpill instructions.  See insert_spill in reload.rs, note how
    //   it's used at ebb entry too, called from visit_entry_params().
    
    /// Run register allocation.
    pub fn run(&mut self,
               isa: &TargetIsa,
               func: &mut Function,
               cfg: &ControlFlowGraph,
               domtree: &mut DominatorTree,
               _liveness: &mut Liveness,
               topo: &mut TopoOrder,
               _tracker: &mut LiveValueTracker,
    ) {
        let mut ctx = Context {
            cur: EncCursor::new(func, isa),
            domtree,
            topo,
        };
        ctx.run()
    }
}

struct Context<'a> {
    // Current instruction as well as reference to function and ISA.
    cur: EncCursor<'a>,

    // References to contextual data structures we need.
    domtree: &'a DominatorTree,
    topo: &'a mut TopoOrder,
}

impl<'a> Context<'a> {
    fn run(&mut self) {
        // Define spill slots for all EBB parameters so that we can process control transfers.
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.make_spill_slots_for_ebb_params(ebb);
        }

        // Insert explicit spills for ebb0?
        let entry = self.topo.next(&self.cur.func.layout, self.domtree).unwrap();
        debug_assert!(self.cur.func.layout.entry_block() == Some(entry));
        self.visit_entry_header(entry);

        // Process all instructions.  Fill any register args before the instruction and spill any
        // definitions after.
        self.topo.reset(self.cur.func.layout.ebbs());
        while let Some(ebb) = self.topo.next(&self.cur.func.layout, self.domtree) {
            self.cur.goto_top(ebb);
            while let Some(inst) = self.cur.next_inst() {
                if !self.cur.func.dfg[inst].opcode().is_ghost() {
                    self.visit_inst(inst);
                }
            }
        }
    }

    fn make_spill_slots_for_ebb_params(&mut self, ebb: Ebb) {
/*
        for p in self.cur.func.dfg.ebb_params(ebb) {
            self.make_spill_slot_for_defn(*p)
        }        
*/
    }

    fn make_spill_slot_for_defn(&mut self, value:Value) {
/*
        if Some(slot) = self.slots.get(value) {
            slot
        } else {
            let ty = self.cur.func.dfg.value_type(value);
            let slot = self.cur.func.stack_slots.make_spill_slot(ty);
            self.slots.insert(SpillInfo { name: value, spill_name: slot, ..});
            slot
        }
*/
    }

    // the entry block actually has register inputs, so must be processed specially.
    fn visit_entry_header(&mut self, ebb: Ebb) {
//        for each parameter register, spill it;
//        but how do we remember where it is so that we can later fill it?            
//        
/*
        debug_assert_eq!(self.cur.func.signature.params.len(), args.len());
        self.cur.goto_first_inst(ebb);

        for (arg_idx, arg) in args.iter().enumerate() {
            let abi = self.cur.func.signature.params[arg_idx];
            match abi.location {
                ArgumentLoc::Reg(_) => {
                    if arg.affinity.is_stack() {
                        // An incoming register parameter was spilled. Replace the parameter value
                        // with a temporary register value that is immediately spilled.
                        let reg = self
                            .cur
                            .func
                            .dfg
                            .replace_ebb_param(arg.value, abi.value_type);
                        let affinity = Affinity::abi(&abi, self.cur.isa);
                        self.liveness.create_dead(reg, ebb, affinity);
                        self.insert_spill(ebb, arg.value, reg);
                    }
                }
                ArgumentLoc::Stack(_) => {
                    debug_assert!(arg.affinity.is_stack());
                }
                ArgumentLoc::Unassigned => panic!("Unexpected ABI location"),
            }
        }
*/
    }

    fn visit_inst(&mut self, inst: Inst) {
        // If it's a cti, then 
/*
        let defs = ...;
        for def in defs {
            let ss = self
                .cur
                .func
                .stack_slots
                .make_spill_slot(self.cur.func.dfg.value_type(def));
            self.cur.func.locations[v] = ValueLoc::Stack(ss);
        }
*/
    }

/*
    fn insert_spill(&mut self, ebb: Ebb, stack: Value, reg: Value) {
        self.cur.ins().with_result(stack).spill(reg);
    }

    fn spill_defn(&mut self, value:Value) {
        let ss = self.stack_slot(value);
        self.cur.func.locations[value] = ValueLoc::Stack(ss);
        self.cur.ins().with_result(stack).spill(reg);
    }
    
    fn stack_slot(&mut self, value:Value) -> StackSlot {
        if Some(slot) = self.slots.get(value) {
            slot
        } else {
            let ty = self.cur.func.dfg.value_type(value);
            let slot = self.cur.func.stack_slots.make_spill_slot(ty);
            self.slots.insert(value, slot);
            slot
        }
    }
*/
}

// Notes for later versions.
//
// There is a map from value to its current location  -- reuse ValueLoc
// The current location is a register or a stack slot
// On function entry, we add the incoming arg locs
// We scan the flow graph from the entry node forward, and we can choose how
//   to handle join: whether to go bfs or dfs.  Assume dfs for simplicty's sake.
//   Note, for liveness tracking we need to do the node's idom before the node
// An instruction has uses U1, ..., Uk and definitions D1, .., Dm
// The uses have to be in registers, for now, so we may need to reload
// To reload we may need to spill
// We should not spill anything we need that's in registers
// We should implement optimized shuffling when possible, consider we need v1=EDX and v2=EAX but we have v1=EAX and v2=EDX
// We should probably spill in LRU order (initially) and otherwise spill what's needed again furthest out (needs lookahead or other precomputation),
//   looks like some sort of abstract spill candidate logic
// At the instruction we kill values no longer needed
// We then allocate destinations
// We need to handle two-address operations properly here (tied constraint)
// We need to handle fixed register allocations here
// At joint points the first to get in may get to determine the storage locations, and others have to conform; so we need to store state
//  at the beginning of each Ebb as it is reached; this doubles as the flag maybe
//
// Must use the existing register classes, AvailableRegs, liveness, -- share as much as possible
//
// How do we record the register choices?
