There are many ways to do dataflow on binaries and ROSE doesn't have
a prepackaged interprocedural analysis for generating use-def chains,
but it does have all the parts you need to make one. I'll list some
things you might or might not want to use depending on your exact
situation:

* The SymbolicSemantics::SValue::get_defining_instructions is a set of
  instruction addresses that's attached to symbolic values describing
  which instructions helped define the value.

* BaseSemantics::RegisterStateGeneric, which associates values with
  registers, has methods for tracking which instruction wrote to a
  register. This is tracked at the bit level.

* BaseSemantics::MemoryCellList, which associates values with memory
  locations, has methods for tracking which instruction wrote to a
  memory location. This is tracked at the byte level.

[DONE]* You'll need a CFG for dataflow.  The BinaryAnalysis::ControlFlow is
  one way to get a CFG, but the dataflow engine is not particular
  about what type of graph you have (it must use the Boost Graph API)
  or what the vertices represent (instructions, basic blocks, other).
  In fact, since you're doing interprocedural, you may want to build
  your own CFG with some functions inlined, which will give you a
  convenient way to do context-sensitive interprocedural.

* You'll need a state type to create the states that hold information
  about the uses and definitions.  Depending on your exact needs, you
  could either create your own state (perhaps using existing parts
  like RegisterStateGeneric and MemoryCellList already mentioned), or
  maybe inherit from BaseSemantics::State.

* Your state type will need a merge() operation for merging one state
  into another when control flow comes back together at some CFG
  vertex.  Depending on your semantic domain (concrete, symbolic, etc)
  this can be a simple operation or as complex and precise as you're
  willing to pay.

* You'll need a transfer function, which takes an initial state and a
  CFG vertex and produces a new state.  Usually, if your CFG vertices
  are instructions or basic blocks and your states have (or contain)
  BaseSemantics::State, then the trasfer function just calls
  RiscOperators::processInstruction for each instruction in the
  vertex.  But since you can define any state type you want, any merge
  operation you want, any CFG you want, your transfer function can be
  anything you want.

* You can use the BinaryAnalysis::DataFlow::Engine for the actual
  dataflow. This is a class template that takes your CFG, state, and
  transfer function and runs them one step at a time or until a fixed
  point is reached.

* Within your state, you'll have to think about how to define the
  transfer and merge functions so the dataflow reaches a fixed
  point.  For instance, you can't just keep creating new memory
  locations if the specimen function has a loop that's iterating over
  an array.

Examples (data-flow in general, not just use-def):

1. tests/roseTests/binaryTests/taintedFlow.C

   This is only intra-procedural and it uses
   BinaryAnalysis::TaintedFlow for much of it's work, but you can look
   at the TaintedFlow implementation.   It computes a list of memory
   locations up front so the states are a fixed size during the
   dataflow. It also uses a custom transfer function to speed up the
   analysis since symbolic semantics can be slow.

2. src/frontend/Partitioner2/DataFlow.h

   This is a context-sensitive, inter-procedural dataflow operating in
   the symbolic domain using data structures from the new
   partitioner. It demonstrates how one might produce their own CFG:
   this example creates a dataflow CFG from a global CFG by inlining
   certain function calls and making adjustments around function calls
   and returns to make the transfer function simpler.  It also
   demonstrates using the Sawyer Graph API which is easier to use than
   Boost Graph API and is supported by ROSE's dataflow engine
   (because Sawyer Graphs also contain a Boost API).  The dataflow
   state contains a BaseSemantics::State but doesn't attempt to limit
   its size (yet), so it might not always reach a fixed point. (If
   this file isn't in master yet you can find it at
   github.com/matzke1/edg4x-rose on the partitioner2 branch).

3. src/frontend/Partitioner2/StackDeltaAnalysis.C

   Computes the net effect a function has on the stack pointer using
   context-sensitive inter-procedural dataflow. The dataflow CFG is
   computed by Partitioner2::DataFlow from the partitioner's global
   CFG. The state consists of only registers. The transfer function
   uses instruction semantics to update the registers.  The merge
   function always converges to a solution because there are a fixed
   number of registers and the values form an infinite lattice with
   only three levels.  This example uses data structures specific to
   the partitioner, but the concept is general.
