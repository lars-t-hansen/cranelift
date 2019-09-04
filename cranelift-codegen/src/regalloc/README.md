# Sundry notes about how things hang together in Cranelift, not specific to this allocator.

## About register allocation in Cranelift

Every function operates on a set of values, and at run time each value has a single home
location for its entire lifetime (a specific hardware register or a specific stack slot).  The
job of the register allocator is to compute that home location for every value and record the
locations in the function's `locations` array; subsequent translation of the IR to machine code
will use that array as the source of truth for each value's location.  In the process of
creating the allocation, the allocator may create additional temporary values; it must record
the locations for those values too.  The register allocator also must allocate any necessary
stack slots.


## About value locations

A value can have only one location and this is fixed for the lifetime of the value; if you want
to give it more locations, you must create new values (ie split the live range or copy-in/copy
out to temps).

Machine code generation will use the locations array when referencing the value, so you can't lie
about this.  (You may be able to use the diversions to lie for a short while, because the
diversions provide the ultimate source of truth for a value's location, but diversions are
intra-ebb.)

These are *value* locations and not *argument* locations, so arguments are separate.  There is an
in-system translation from one to the other: ebb0 takes the function's arguments as parameters,
expressed in terms of values.  One hopes that these values have been set up with the proper value
locations initially.  In particular, stack args should have ValueLoc::Stack(ss) where the
StackSlot ss is of an Argument type.

Regalloc does not update the IR nodes, only the locations array.  Regalloc may insert new nodes
for fills, spills, copies, and moves, but the allocated locations are stored in the locations
array.


## About stack slots, function parameters, and spills:

All stack slots carry offsets (that are interpreted in the context of their type).

Slots are created by make_spill_slot / make_incoming_arg / get_outgoing_arg in ir/stackslot.rs.
The latter two need to be told the offset that the slot carries.

There are also emergency slots used for emergency spills, see same file.  We may need these once
we implement parallel assignment, though it's best to avoid them.

There are also explicit slots used for stack-allocated data, see same file.  We don't need them
at the moment.

The entry ebb must have locations for its incoming parameters that correspond to the ABI
locations of the function's parameters.  For incoming register args, they are in registers.  For
incoming stack arguments, they are flagged as being in incoming_arg stack slots.  It's OK for
them to live in those slots throughout.  The incoming_arg slots are created by the legalizer.

On function calls that have stack args, we must spill those arguments immediately before the call
to stack slots that are marked outgoing_arg.  The outgoing_arg slots are created by the legalizer,
and the legalizer also creates spill instructions that fill those slots.  Thus the regalloc
must only worry about generating code to populate the inputs of those spills.

Stack slots for spilled non-incoming non-outgoing values are labeled simply spill_slot.  Those
spills are created by the register allocator.  We don't need to worry about offsets; those
are created for us by layout_stack() after the main compilation.  We just need to track the
slots for possible reuse.

A spill or fill is a node that connects two values: the value on the stack and the value in the
register.  Both eventually have a location in the location array: one a StackSlot, the other a
RegUnit.  This way, the spill node itself does not need to carry allocation information.


## About function calls

The register allocator populates outgoing argument registers with normal register moves, directly
before the call instruction.  Spills into outgoing stack args are inserted by the legalizer.  The
code generator does not insert additional code around the call instruction for anything at all.

* How do we know which register args we need?  Are there argument affinities on the call
  instruction, indeed, fixed use constraints?

* reload.rs has a lot of relevant code here


## About two-address instructions:

These are expressed as tied operands to an instruction, I think - output is tied to one of the
inputs.  This causes us no particular concern since the register is newly live and we will save
its value immediately after the operation and then kill the register.  We just need to ensure
that the input is allocated to the same register as the output, and this may be complicated by
either of those registers having a fixed assignment.


## About CPU flags:

Flags may complicate fills and spills -- these must not affect the flags, but is that so?  Since
we can set and read flags independently, are there limits on how long those flags are good?  I
expect not...


## About control flow joins:

For now, we can assign slots to all ebb parameters independently, and so a join will copy from
whatever slots the values are in into the slots of the target ebb.  This will usually involve
creating a new ebb along a conditional exit edge from the ebb to hold those copy instructions,
if the destination ebb has multiple predecessors.  Along the fallthrough edge we can always
insert copies before the jump / fallthrough.


## About constraints:

Which constraints are there?  eg, byte register / subregister; register hint; fixed register
requirement (for some instructions); others?


## About ebbs:

At the entry ebb, we spill incoming register arguments (to new slots that we record) and leave
others in place on the stack.

At non-entry ebbs, we create stack slots for the incoming args but there's nothing to do on
entry, everything is done in the predecessor, which copies values into the assigned arg slots.


## About registers and allocation:

The register sets are really quite complex.  Some of this complexity deals with overlapping
registers (which are endemic); some deals with asymmetric register sets in some CPUs (eg ARM).

A `register unit` is an allocatable register but also carries information about whether it
overlaps multiple hardware registers.  The units are allocated from disjoint `register banks`,
which provide registers for one or more `register classes`; top-level classes are disjoint (do
they correspond 1:1 to the banks?) but some classes can be nested inside others.

An instruction encoding's operand is allocated with constraints on the encoding, and for an
encoding that requires the operand to be in a register the encoding holds the desired register
class reference (a pointer to static data). Thus the register class is the fundamental token the
register allocator sees when processing the instruction.

The register class carries several indices into the RegInfo table in the ISA.  The field `index`
is the index of the class itself; the field `toprc` the index of the top-level class (different
from `index` if the class is nested).  Possibly these can be used to index into tables that
mirror the RegInfo table.

A `register set` is a set of all available registers, obtained from the ISA.  It has methods for
taking and releasing and querying the availability of *specific* registers in a class, and for
iterating across the available registers of a class.  The iterator does not reference the set,
but copies its contents.

When we allocate a register, we are given a register class (from the encoding's constraint) and
want to get a register of that class from the register set.

Given all this complexity, getting a free register for a class can be fairly expensive, notably
since getting a register of one class may also affect the availability of registers of other
classes.  It may well be true that the common case is that there are no such interferences, but
there still seems to be significant administrative overhead.

The best bet may be this:

* at the outset, enumerate the register classes, and for each class, create an iterator, and
  iterate across all the free registers in the class given the initial set of available registers
  from the isa.  Store these registers in a per-class data structure.
* when allocating a register for a class, consult this data structure: take a value from it,
  test its availability against the register set, and if it is available, obtain it (and remove it
  from the data structure); otherwise move on to the next value in the data structure.
  usually this will succeed on the first try.
* when freeing a register for a class, return it to the register set and to the data structure.
* the we fail to obtain a register we'd like to deprioritize it; so move it elsewhere in the
  data structure, maybe, or use a roving pointer for allocation?

## Sketches for a superlocal register allocator (not coherent)

* There is a map from value to its current location  -- reuse ValueLoc
* The current location is a register or a stack slot
* On function entry, we add the incoming arg locs
* We scan the flow graph from the entry node forward, and we can choose how 
  to handle join: whether to go bfs or dfs.  Assume dfs for simplicty's sake.
  Note, for liveness tracking we need to do the node's idom before the node
* An instruction has uses U1, ..., Uk and definitions D1, .., Dm
* The uses have to be in registers, for now, so we may need to reload
* To reload we may need to spill
* We should not spill anything we need that's in registers
* We should implement optimized shuffling when possible, consider we need v1=EDX and v2=EAX but we have v1=EAX and v2=EDX
* We should probably spill in LRU order (initially) and otherwise spill what's needed again furthest out (needs lookahead or other precomputation),
  looks like some sort of abstract spill candidate logic
* At the instruction we kill values no longer needed
* We then allocate destinations
* We need to handle two-address operations properly here (tied constraint)
* We need to handle fixed register allocations here
* At joint points the first to get in may get to determine the storage locations, and others have to conform; so we need to store state
*  at the beginning of each Ebb as it is reached; this doubles as the flag maybe
* Must use the existing register classes, AvailableRegs, liveness, -- share as much as possible
* How do we record the register choices?

## Sketches for the minimal register allocator (old; consult code instead)

* A load of value `v` before an instruction is expressed as a fill from the stack slot of `v` into
  a temp `s` that is assigned a register `r`, which then becomes the argument for the instruction.
  In the case where the argument is constrained to be or allowed to be a stack value, we use `v`
  as it is.  In the case of calls, we may have to spill `r` into an outgoing argument slot `a`.
  Note that `r` may be Fixed, Tied, or FixedTied for some of the arguments and that fixed
  constraints must have priority.  If we don't reuse argument registers for multiple uses of the
  same value we can ignore issues of conflicting constraints.
* A store of defined value `d` after an instruction is expressed as defining a register temporary
  `t` and a spill of `t` into stack value `d` (after which `t` is dead).  For now we assume all
  result values are in registers.  Note `t` may be Fixed, Tied, or FixedTied, and fixed
  constraints must have priority; and there may be more than one result.
* For a control transfer instruction with arguments, the block parameter in the CTI will be
  assigned a stack slot `ss` and the actual value argument will be in a different stack slot `tt`.
  In this case, we fill a temp register `r` from `tt` and then spill `r` to a stack slot `uu`,
  where `uu` is assigned to the same stack slot as `ss`.
* CPU flags are basically ignored; we must just be sure not to insert instructions that alter the
  flags, or if we do, we must do so outside a region between the flag setter and its uses.
* At the start of each instruction, we have a set of available registers for each register class.
  We first process any fixed constraints.  Then we allocate the rest.
* We do not reuse stack slots (yet).

