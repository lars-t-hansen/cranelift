//! Minimal register allocator.
//!
//! Every function operates on a set of values, and at run time each value has a single home
//! location for its entire lifetime (a specific hardware register or a specific stack slot).  The
//! job of the register allocator is to compute that home location for every value and record the
//! locations in the function's `locations` array; subsequent machine code encoding will use that
//! array as the source of truth for each value's location when the encoding needs to know it.  In
//! the process, the allocator may create additional temporary values; it must record the locations
//! for those values too.  The register allocator also must allocate any necessary stack slots.
//!
//! The `minimal` allocator assigns every value to a unique stack slot, then moves values into
//! registers only as required by each instruction, and finally moves any defined values out of
//! registers directly after the instruction.  It must handle the function ABI and two-address
//! operations (tied registers) and must obey all instruction constraints (eg fixed registers), but
//! is otherwise the simplest register allocator imaginable for our given IR structure.

// Overview.
//
// A load of value `v` before an instruction is expressed as a fill from the stack slot of `v` into
// a temp `s` that is assigned a register `r`, which then becomes the argument for the instruction.
// In the case where the argument is constrained to be or allowed to be a stack value, we use `v`
// as it is.  In the case of calls, we may have to spill `r` into an outgoing argument slot `a`.
// Note that `r` may be Fixed, Tied, or FixedTied for some of the arguments and that fixed
// constraints must have priority.  If we don't reuse argument registers for multiple uses of the
// same value we can ignore issues of conflicting constraints.
//
// A store of defined value `d` after an instruction is expressed as defining a register temporary
// `t` and a spill of `t` into stack value `d` (after which `t` is dead).  For now we assume all
// result values are in registers.  Note `t` may be Fixed, Tied, or FixedTied, and fixed
// constraints must have priority; and there may be more than one result.
//
// For a control transfer instruction with arguments, the block parameter in the CTI will be
// assigned a stack slot `ss` and the actual value argument will be in a different stack slot `tt`.
// In this case, we fill a temp register `r` from `tt` and then spill `r` to a stack slot `uu`,
// where `uu` is assigned to the same stack slot as `ss`.
//
// A copy instruction is replaced by a fill/spill pair in the same manner as for the CTI.
//
// CPU flags are basically ignored; we must just be sure not to insert instructions that alter the
// flags, or if we do, we must do so outside a region between the flag setter and its uses.
//
// At the start of each instruction, we have a set of available registers for each register class.
// We first process any fixed constraints.  Then we allocate the rest.


// Some notes.
//
// - Since we keep no live values in registers, tied arguments are easy: we don't have to worry
//   about killing anything.
//
// - I think there should be no fallthrough instructions at this point in the pipeline, we
//   should assert that.
    

// ==============================================================================================
// Sundry notes about how things hang together in Cranelift, not specific to this allocator.
// ==============================================================================================
//
// About value locations:
//
// A value can have only one location and this is fixed for the lifetime of the value; if you want
// to give it more locations, you must create new values (ie split the live range or copy-in/copy
// out to temps).
//
// Machine code generation will use the locations array when referencing the value, so you can't lie
// about this.  (You may be able to use the diversions to lie for a short while, because the
// diversions provide the ultimate source of truth for a value's location, but diversions are
// intra-ebb.)
//
// These are *value* locations and not *argument* locations, so arguments are separate.  There is an
// in-system translation from one to the other: ebb0 takes the function's arguments as parameters,
// expressed in terms of values.  One hopes that these values have been set up with the proper value
// locations initially.  In particular, stack args should have ValueLoc::Stack(ss) where the
// StackSlot ss is of an Argument type.
//
// Regalloc does not update the IR nodes, only the locations array.  Regalloc may insert new nodes
// for fills, spills, copies, and moves, but the allocated locations are stored in the locations
// array.
//
//
// About stack slots, function parameters, and spills:
//
// All stack slots carry offsets (that are interpreted in the context of their type).
//
// Slots are created by make_spill_slot / make_incoming_arg / get_outgoing_arg in ir/stackslot.rs.
// The latter two need to be told the offset that the slot carries.
//
// There are also emergency slots used for emergency spills, see same file.  We may need these once
// we implement parallel assignment, though it's best to avoid them.
//
// There are also explicit slots used for stack-allocated data, see same file.  We don't need them
// at the moment.
//
// The entry ebb must have locations for its incoming parameters that correspond to the ABI
// locations of the function's parameters.  For incoming register args, they are in registers.  For
// incoming stack arguments, they are flagged as being in incoming_arg stack slots.  It's OK for
// them to live in those slots throughout.  The incoming_arg slots are created by the legalizer.
//
// On function calls that have stack args, we must spill those arguments immediately before the call
// to stack slots that are marked outgoing_arg.  The outgoing_arg slots are created by the legalizer,
// and the legalizer also creates spill instructions that fill those slots.  Thus the regalloc
// must only worry about generating code to populate the inputs of those spills.
//
// Stack slots for spilled non-incoming non-outgoing values are labeled simply spill_slot.  Those
// spills are created by the register allocator.  We don't need to worry about offsets; those
// are created for us by layout_stack() after the main compilation.  We just need to track the
// slots for possible reuse.
//
// A spill or fill is a node that connects two values: the value on the stack and the value in the
// register.  Both eventually have a location in the location array: one a StackSlot, the other a
// RegUnit.  This way, the spill node itself does not need to carry allocation information.
//
//
// About function calls:
//
// The register allocator populates outgoing argument registers with normal register moves, directly
// before the call instruction.  Spills into outgoing stack args are inserted by the legalizer.  The
// code generator does not insert additional code around the call instruction for anything at all.
//
// => How do we know which register args we need?  Are there argument affinities on the call
//    instruction, indeed, fixed use constraints?
//
// => reload.rs has a lot of relevant code here
//
// 
// About two-address instructions:
//
// These are expressed as tied operands to an instruction, I think - output is tied to one of the
// inputs.  This causes us no particular concern since the register is newly live and we will save
// its value immediately after the operation and then kill the register.  We just need to ensure
// that the input is allocated to the same register as the output, and this may be complicated by
// either of those registers having a fixed assignment.
//
//
// About CPU flags:
//
// Flags may complicate fills and spills -- these must not affect the flags, but is that so?  Since
// we can set and read flags independently, are there limits on how long those flags are good?  I
// expect not...
// 
//
//
// About control flow joins:
//
// For now, we can assign slots to all ebb parameters independently, and so a join will copy from
// whatever slots the values are in into the slots of the target ebb.  This will usually involve
// creating a new ebb along a conditional exit edge from the ebb to hold those copy instructions,
// if the destination ebb has multiple predecessors.  Along the fallthrough edge we can always
// insert copies before the jump / fallthrough.
//
//
// About constraints:
//
// => Which constraints are there?  eg, byte register / subregister; register hint; fixed register
// requirement (for some instructions); others?
//
//
// About ebbs:
//
// At the entry ebb, we spill incoming register arguments (to new slots that we record) and leave
// others in place on the stack.
//
// At non-entry ebbs, we create stack slots for the incoming args but there's nothing to do on
// entry, everything is done in the predecessor, which copies values into the assigned arg slots.
//

use crate::flowgraph::ControlFlowGraph;
use crate::cursor::{Cursor, EncCursor};
use crate::entity::{SparseMap, SparseMapValue};
use crate::dominator_tree::DominatorTree;
use crate::ir::{ArgumentLoc, Ebb, Function, Inst, InstBuilder, SigRef, Value, ValueLoc, StackSlot};
use crate::isa::registers::{RegClass, RegClassIndex, RegClassMask, RegUnit};
use crate::isa::{ConstraintKind, EncInfo, RecipeConstraints, RegInfo, TargetIsa};
use crate::regalloc::live_value_tracker::{LiveValue, LiveValueTracker};
use crate::regalloc::liveness::Liveness;
use crate::topo_order::TopoOrder;

/// Map from a name in the original program to information about where it's spilled.
type SpillMap = SparseMap<Value, SpillInfo>;

/// Represents spilling information for a name.
struct SpillInfo {
    program_name: Value,        // Name in program
    spilled_name: Value         // Name of spill that holds the value
}

impl SparseMapValue<Value> for SpillInfo
{
    fn key(&self) -> Value {
        self.program_name
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

    /// Run register allocation.
    pub fn run(&mut self,
               isa: &TargetIsa,
               func: &mut Function,
               _cfg: &ControlFlowGraph,
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

    // Spill any entry block parameters that are in registers.
    fn visit_entry_params(&mut self, ebb: Ebb) {
        self.cur.goto_first_inst(ebb);
        for (arg, abi) in self.cur.func.dfg.ebb_params(ebb).zip(self.cur.func.signature.params.into_iter()) {
            match abi.location {
                ArgumentLoc::Reg(r) => {
                    // I think this isn't right, we really want to emit spill() operations here.  regspill()
                    // is lower level than we need.  But at the same time, we must have a stack slot for the
                    // location!
                    //
                    // spill_reg in spilling.rs seems pertinent here, together with code in
                    // reload.rs -- the code in spilling.rs creates a spill slot for that spill and
                    // records this in the affinity, and then reload.rs triggers on the affinity and
                    // inserts a spill instruction.
                    //
                    // still not clear to me how that is later acted on, but those spill instructions can
                    // be lowered directly to machine code.
                    let ty = self.cur.func.dfg.value_type(arg);
                    let ss = self.cur.func.stack_slots.make_spill_slot(ty);
                    let spill = self.cur.ins().regspill(arg, r, ss);
                    let spilled_name = self.cur.func.dfg.first_result(spill);
                    self.spills.insert(SpillInfo { program_name: arg, spilled_name });

                    debug_assert!(self.cur.func.locations[spilled_name] == ValueLoc::Unassigned);
                    self.cur.func.locations[spilled_name] = ValueLoc::Stack(ss);
                }
                ArgumentLoc::Stack(_) => {}
                ArgumentLoc::Unassigned => panic!("Unexpected ABI location"),
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
