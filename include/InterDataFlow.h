#ifndef ROSE_Partitioner2_InterDataFlow_H
#define ROSE_Partitioner2_InterDataFlow_H


#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif

#include "sage3basic.h"
#include <iostream>
#include <Partitioner2/Partitioner.h>
#include <sawyer/GraphTraversal.h>
#include <boost/optional.hpp>
#include <SymbolicSemantics2.h>
#include "Diagnostics.h"
#include "DataFlowSemantics2.h"
#include <BinaryDataFlow.h>
#include <Partitioner2/BasicBlock.h>
#include <Partitioner2/ControlFlowGraph.h>
#include <Partitioner2/Modules.h>
#include <Partitioner2/Function.h>
#include <Partitioner2/Engine.h>
#include <sawyer/Graph.h>
#include <sawyer/DistinctList.h>
#include <vector>
#include <typeinfo>
#include <BaseSemantics2.h>
#include <DispatcherX86.h>
#include <SymbolicSemantics2.h>
#include <AstSimpleProcessing.h>

using namespace rose::BinaryAnalysis;
using namespace Sawyer::Message::Common;

namespace IS2 = InstructionSemantics2;


struct compare{
	bool operator() (const SgAsmInstruction* insn1,const SgAsmInstruction* insn2){
		return insn1->get_address() < insn2->get_address();
	}
};

namespace rose {
	namespace BinaryAnalysis {
		namespace Partitioner2 {
			/** Dataflow utilities. */
			namespace InterDataFlow {
				using namespace Sawyer::Container::Algorithm;

				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				//                                      Control Flow Graph
				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

				/** CFG vertex for dataflow analysis.
				 *
				 *  @sa DfCfg */
				class DfCfgVertex {
					public:
						/** Vertex type. */
						enum Type {
							BBLOCK,                                         /**< Vertex represents a basic block. */
							FAKED_CALL,                                     /**< Represents a whole called function. */
							FUNCRET,                                        /**< Vertex represents returning to the caller. */
							INDET,                                          /**< Indeterminate basic block where no information is available. */
						};

					private:
						Type type_;
						BasicBlock::Ptr bblock_;                            // attached to BBLOCK vertices
						Function::Ptr callee_;                              // function represented by FAKED_CALL
						rose_addr_t func_addr;								// Address of the function in which this Vertex lies
						const SgAsmInstruction* call_inst_;						// calling instruction for fake calls

					public:
						/** Construct a basic block vertex.  The basic block pointer should not be a null pointer. */
						explicit DfCfgVertex(const BasicBlock::Ptr &bblock): type_(BBLOCK), bblock_(bblock){
							ASSERT_not_null(bblock);
						}

						/** Construct a faked call vertex. The function may be null if indeterminate. */
						explicit DfCfgVertex(const Function::Ptr &function,const SgAsmInstruction* call_inst): 
							type_(FAKED_CALL), callee_(function),call_inst_(call_inst){	}

						/** Construct a vertex of specified type that takes no auxiliary data. */
						explicit DfCfgVertex(Type type): type_(type) {
							ASSERT_require2(BBLOCK!=type && FAKED_CALL!=type, "use a different constructor");
						}
						/** Construct a vertex of specified type that takes no auxiliary data. */
						explicit DfCfgVertex(Type type,const rose_addr_t function_addr): type_(type),func_addr(function_addr) {
							ASSERT_require(FUNCRET==type);
						}

						/** Type of the vertex.
						 *
						 *  Vertex types are immutable, defined when the vertex is created. Every vertex has a type. */
						Type type() const { return type_; }

						/** Basic block.
						 *
						 *  The basic block for a vertex is immutable, defined when the vertex is created.  Only basic block vertices have a basic
						 *  block; other vertex types will return a null pointer. */
						const BasicBlock::Ptr& bblock() const { return bblock_; }

						const SgAsmInstruction* call_instruction() const {return call_inst_; }

						const rose_addr_t func_address() const {return func_addr;}

						/** Function represented by faked call. */
						const Function::Ptr& callee() const { return callee_; }
				};

				/** Control flow graph used by dataflow analysis.
				 *
				 *  The CFG used for dataflow is slightly different than the global CFG maintained by the partitioner. The partitioner's global
				 *  CFG is tuned for discovering basic blocks and deciding which basic blocks are owned by which functions, whereas a
				 *  dataflow's CFG is tuned for performing data flow analysis.  A dataflow CFG is usually constructed from the partitioner's
				 *  global CFG, but differs in the following ways:
				 *
				 *  @li First, dataflow analysis is usually performed on a subset of the partitioner's global CFG. This function uses the @p
				 *      startVertex to select some connected subgraph, such as a subgraph corresponding to a single function definition when
				 *      given the entry block.
				 *
				 *  @li Function return blocks (e.g., RET instructions) are handled differently during dataflow.  In the partitioner's global
				 *      CFG each return block is marked as a function return and has single successor--the indeterminate vertex.  In a dataflow
				 *      CFG the return blocks are not handled specially, but rather all flow into a single special return vertex that has no
				 *      instructions.  This allows data to be merged from all the return points.
				 *
				 *  @li Function call sites are modified.  In the partitioner global CFG a function call (e.g., CALL instruction) has an edge
				 *      (or edges) going to the entry block of the called function(s) and a special call-return edge to the return site if
				 *      there is one (usually the fall-through address). A data-flow analysis often needs to perform some special action for
				 *      the call-return, thus a call-return edge in the global CFG gets transformed to an edge-vertex-edge sequence in the
				 *      dataflow CFG where the middle vertex is a special CALLRET vertex with no instructions. */
				typedef Sawyer::Container::Graph<DfCfgVertex> DfCfg;

				/** Predicate that decides when to use inter-procedural dataflow.
				 *
				 *  The predicate is invoked with the global CFG and a function call edge and should return true if the called function should
				 *  be included into the dataflow graph.  If it returns false then the graph will have a single FAKED_CALL vertex to represent
				 *  the called function. */
				class InterproceduralPredicate {
					public:
						virtual ~InterproceduralPredicate() {}
						virtual bool operator()(const ControlFlowGraph&, const ControlFlowGraph::ConstEdgeIterator&, size_t depth) = 0;
				};

				/** Predicate that always returns false, preventing interprocedural analysis. */
				class NotInterprocedural: public InterproceduralPredicate {
					public:
						bool operator()(const ControlFlowGraph&, const ControlFlowGraph::ConstEdgeIterator&, size_t depth) ROSE_OVERRIDE {
							return false;
						}
				};
				class Interprocedural: public InterproceduralPredicate {
					public:
						bool operator()(const ControlFlowGraph&, const ControlFlowGraph::ConstEdgeIterator&, size_t depth) ROSE_OVERRIDE {
							return true;
						}
				};

				extern NotInterprocedural NOT_INTERPROCEDURAL;
				extern Interprocedural INTERPROCEDURAL;

				// Traversal to find the node - SgAsmPEImportSection
				class Traversal: public AstSimpleProcessing {
					public:
						AddressIntervalSet &idataExtent;
						std::set<rose_addr_t> &newIATAddress;
					public:
						Traversal(AddressIntervalSet &idataExtent_,std::set<rose_addr_t> &newIATAddress_):
							idataExtent(idataExtent_),newIATAddress(newIATAddress_),AstSimpleProcessing(){}
					protected:
						void virtual visit(SgNode *node);
				};

				/** build a cfg useful for dataflow analysis.
				 *
				 *  The returned CFG will be constructed from the global CFG vertices that are reachable from @p startVertex such that the
				 *  reached vertex belongs to the same function as @p startVertex.
				 *
				 *  @sa DfCfg */
				// private class for Building the Inter-Procedural ControlFlowGraph from the default 
				// ControlFlowGraph given by the Rose Framework
				class DfCfgBuilder {
					public:
						const Partitioner &partitioner;								 // Partitioner instance
						const ControlFlowGraph &cfg;                                 // global control flow graph
						DfCfg dfCfg;                                                 // dataflow control flow graph we are building
						InterproceduralPredicate &interproceduralPredicate;          // returns true when a call should be inlined
						AddressIntervalSet idataExtent;								// lower and upper limit of .idata section
						std::set<rose_addr_t> newIATAddress;						// All thunks and instructions which can lead to a call to new library call

						// maps CFG vertex ID to dataflow vertex
						typedef Sawyer::Container::Map<ControlFlowGraph::ConstVertexIterator, DfCfg::VertexIterator> VertexMap;
						VertexMap vmap;

						// maps function address with there return bblock
						typedef Sawyer::Container::Map<rose_addr_t, DfCfg::VertexIterator> RetMap;
						RetMap retMap;

						typedef Sawyer::Container::Map<rose_addr_t,std::set<SgAsmInstruction*,compare> >funcToInst;
						funcToInst functionToInstruction;						//// [[I WANT TO REMOVE IT]]

						// Instructions which are calling "new" library function
						std::set<SgAsmInstruction*> newCallingInstructions;

						// Info about one function call
						struct CallFrame{
							DfCfg::VertexIterator functionReturnVertex;			// Function return Vertex
							bool wasFaked;										// was faked or not
							rose_addr_t funcAddr;								// function address
							const SgAsmInstruction *call_inst;					// instruction which is calling this function and making this call frame
							CallFrame(DfCfg &dfCfg,rose_addr_t addr_): functionReturnVertex(dfCfg.vertices().end()), wasFaked(false),funcAddr(addr_) {}
						};

						typedef std::list<CallFrame> CallStack;             // we use a list since there's no default constructor for an iterator
						CallStack callStack;
						size_t maxCallStackSize;                            // safety to prevent infinite recursion


						explicit DfCfgBuilder(const Partitioner &partitioner,const ControlFlowGraph &cfg_,InterproceduralPredicate &predicate,rose_addr_t max_call_stack)
							: partitioner(partitioner), cfg(cfg_),interproceduralPredicate(predicate),maxCallStackSize(max_call_stack) {}

						typedef DepthFirstForwardGraphTraversal<const ControlFlowGraph> CfgTraversal;

						/*Find vertex from default ControlFlowGraph vertex to DfCfg vertex*/
						virtual DfCfg::VertexIterator findVertex(const ControlFlowGraph::ConstVertexIterator &cfgVertex); 

						/*Check if the vertex is valid or not*/
						virtual bool isValidVertex(const DfCfg::VertexIterator &dfVertex);

						/*Insert vertex into the dfCfg graph */
						virtual DfCfg::VertexIterator insertVertex(const DfCfgVertex &dfVertex,
								const ControlFlowGraph::ConstVertexIterator &cfgVertex);

						virtual DfCfg::VertexIterator insertVertex(const DfCfgVertex &dfVertex) {
							return dfCfg.insertVertex(dfVertex);
						}

						virtual DfCfg::VertexIterator insertVertex(DfCfgVertex::Type type) {
							return insertVertex(DfCfgVertex(type));
						}

						virtual DfCfg::VertexIterator insertVertex(DfCfgVertex::Type type, const ControlFlowGraph::ConstVertexIterator &cfgVertex) {
							return insertVertex(DfCfgVertex(type), cfgVertex);
						}

						// Insert basic block if it hasn't been already
						virtual DfCfg::VertexIterator findOrInsertBasicBlockVertex(const ControlFlowGraph::ConstVertexIterator &cfgVertex);

						// Returns the dfCfg vertex for a CALL return-to vertex, creating it if necessary.  There might be none, in which case the
						// vertex end iterator is returned.
						virtual DfCfg::VertexIterator findOrInsertCallReturnVertex(const ControlFlowGraph::ConstVertexIterator &cfgVertex);

						/* check if the edge is already present or not */
						virtual bool checkRepeat(DfCfg::VertexIterator &src,
								DfCfg::VertexIterator &dest);

						virtual DfCfg::VertexIterator copyFunction(DfCfg::VertexIterator initBBlock,rose_addr_t finalAddr,
								DfCfg::VertexIterator &fromVertex);

						//Fill functionToInstruction
						virtual void fillInstFunc(Partitioner2::BasicBlock::Ptr &blk );

						// top-level build function.
						virtual DfCfg& build(ControlFlowGraph::ConstVertexIterator &startVertex_,DfCfg::VertexIterator &beginVertex,DfCfg::VertexIterator &endVertex);

						// Starting the building of the Inter-Procedural Control Flow Graph
						virtual DfCfg& startBuilding(ControlFlowGraph::ConstVertexIterator &startVertex_);

						// Checks if the particular function is Thunk or not which tell if either that particular function is Library call or not
						virtual bool checkForLibraryFunction(const Partitioner2::BasicBlock::Ptr& blk,SgAsmInstruction *call_inst);

						// Checks if the function is calling a library function or not , by reading the address from IAT
						virtual bool checkForLibraryCall(SgAsmInstruction *insn);

						virtual DfCfg& getdfCfg(){ return dfCfg;}
				};

				class PePrivilege: public BasicBlockCallback {
					public:
						typedef Sawyer::SharedPointer<PePrivilege> Ptr;
					protected:
						PePrivilege(){};
					public:
						static Ptr instance(){ return Ptr(new PePrivilege());}
						// Checks if the instruction is INT 3 and if it is, then it change the CFG accordingly without indeterminate CFG
						virtual bool operator()(bool chain,const Args &args) ROSE_OVERRIDE;
				};

				/** Emit a dataflow CFG as a GraphViz file. */
				void dumpDfCfg(std::ostream&, const DfCfg&);

				ControlFlowGraph::ConstVertexIterator vertexForInstruction(const Partitioner &partitioner, const std::string &nameOrVa);

				/******************************************************************************************************************************
				 *                                      RangeMap set of numeric values
				 ******************************************************************************************************************************/

				/** Scalar value type for a RangeMap.  Values can be merged if they compare equal; splitting a value is done by copying it.
				 *  The removing() and truncate() methods are no-ops.  See the RangeMapVoid class for full documentation. */
				template<class R, class T>
					class RangeMapSet /*final*/ {
						public:
							typedef R Range;
							typedef T Value;

							/** Constructor creates object whose underlying value is zero. */
							RangeMapSet(): value() {}

							/** Constructor creates object with specified value. */
							RangeMapSet(Value v): value(v) {} // implicit

							/** Accessor for the value actually stored here.
							 *  @{ */
							void set(Value v) /*final*/ {
								value = v;
							}
							virtual Value get() const /*final*/ {
								return value;
							}
							/** @} */


							/** Called when this value is being removed from a RangeMap. */
							void removing(const Range &my_range) /*final*/ {
								assert(!my_range.empty());
							}

							/** Called when removing part of a value from a RangeMap. */
							void truncate(const Range &my_range, const typename Range::Value &new_end) /*final*/ {
								assert(new_end>my_range.first() && new_end<=my_range.last());
							}

							/** Called to merge two RangeMap values.  The values can be merged only if they compare equal. */
							bool merge(const Range &my_range, const Range &other_range, RangeMapSet other_value) /*final*/ {
								assert(!my_range.empty() && !other_range.empty());
								return get()==other_value.get();
							}

							/** Split a RangeMap value into two parts. */
							RangeMapSet split(const Range &my_range, typename Range::Value new_end) /*final*/ {
								assert(my_range.contains(Range(new_end)));
								return *this;
							}

							/** Print a RangeMap value.
							 *  @{ */
							void print(std::ostream &o) const /*final*/ {
								//        o <<value;	// NOT REQUIRED
							}
							friend std::ostream& operator<<(std::ostream &o, const RangeMapSet &x) {
								x.print(o);
								return o;
							}
							/** @} */

						public:
							Value value;
					};



				typedef boost::shared_ptr<class RegisterStateGeneric> RegisterStateGenericPtr;


				class RegisterStateGeneric: public BaseSemantics::RegisterStateGeneric {
					public:
						// A mapping from the bits of a register (e.g., 'al' of 'rax') to the set of virtual address of the instruction that last wrote
						// a value to those bits
						typedef RangeMap<Extent, RangeMapSet<Extent, std::set<rose_addr_t> > > writersParts;
						typedef Map<RegStore, writersParts> allWritersMaps;
						allWritersMaps allWriters_;
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Real constructors
					protected:
						explicit RegisterStateGeneric(const BaseSemantics::SValuePtr &protoval, const RegisterDictionary *regdict)
							: BaseSemantics::RegisterStateGeneric(protoval, regdict) {
								allWriters_.clear();
							}
						explicit RegisterStateGeneric(const RegisterStateGeneric &other)
							: BaseSemantics::RegisterStateGeneric(other),allWriters_(other.allWriters_){
							}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Static allocating constructors
					public:
						/** Instantiate a new register state. The @p protoval argument must be a non-null pointer to a semantic value which will be
						 *  used only to create additional instances of the value via its virtual constructors.  The prototypical value is normally
						 *  of the same type for all parts of a semantic analysis: its state and operator classes.
						 *
						 *  The register dictionary, @p regdict, describes the registers that can be stored by this register state, and should be
						 *  compatible with the register dictionary used for other parts of binary analysis. */
						static RegisterStateGenericPtr instance(const rose::BinaryAnalysis::InstructionSemantics2::BaseSemantics::SValuePtr &protoval, const RegisterDictionary *regdict) {
							return RegisterStateGenericPtr(new RegisterStateGeneric(protoval, regdict));
						}
						/** Instantiate a new copy of an existing register state. */
						static RegisterStateGenericPtr instance(const RegisterStateGenericPtr &other) {
							return RegisterStateGenericPtr(new RegisterStateGeneric(*other));
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Virtual constructors
					public:
						virtual BaseSemantics::RegisterStatePtr create(const rose::BinaryAnalysis::InstructionSemantics2::BaseSemantics::SValuePtr &protoval, const RegisterDictionary *regdict) const ROSE_OVERRIDE {
							return instance(protoval, regdict);
						}

						virtual BaseSemantics::RegisterStatePtr clone() const ROSE_OVERRIDE {
							return RegisterStateGenericPtr(new RegisterStateGeneric(*this));
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Dynamic pointer casts
					public:
						/** Run-time promotion of a base register state pointer to a RegisterStateGeneric pointer. This is a checked conversion--it
						 *  will fail if @p from does not point to a RegisterStateGeneric object. */
						static RegisterStateGenericPtr promote(const BaseSemantics::RegisterStatePtr &from) {
							RegisterStateGenericPtr retval = boost::dynamic_pointer_cast<RegisterStateGeneric>(from);
							ASSERT_not_null(retval);
							return retval;
						}

					public:
						/**Setting a set of multiple writter instruction(addresses) to the particular register */
						virtual void setAllWriters(const RegisterDescriptor &desc, std::set<rose_addr_t> &Writers);
						/**Returns a set of multiple writter instruction(addresses) to the particular register */
						virtual std::set<rose_addr_t> allWriters(const RegisterDescriptor &desc) const ;
				};

				/******************************************************************************************************************
				 *                                  Cell List Memory State
				 ******************************************************************************************************************/
				/** Smart pointer to a MemoryCell object.  MemoryCell objects are reference counted and should not be explicitly deleted. */
				typedef boost::shared_ptr<class MemoryCell> MemoryCellPtr;

				/** Represents one location in memory.
				 *
				 *  Each memory cell has an address and a value. MemoryCell objects are used by the MemoryCellList to represent a memory
				 *  state. */
				class MemoryCell: public BaseSemantics::MemoryCell {
					protected:
						/**Set of instruction address which are latest writer to this memorycell*/
						std::set<rose_addr_t> latest_writers;
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Real constructors
					protected:
						MemoryCell(const BaseSemantics::SValuePtr &address, const BaseSemantics::SValuePtr &value)
							: BaseSemantics::MemoryCell(address,value){
							}

						// deep-copy cell list so modifying this new one doesn't alter the existing one
						MemoryCell(const MemoryCell &other)
							: BaseSemantics::MemoryCell(other) {
								latest_writers = other.latest_writers;
							}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Static allocating constructors
					public:
						/** Instantiates a new memory cell object with the specified address and value. */
						static MemoryCellPtr instance(const BaseSemantics::SValuePtr &address, const BaseSemantics::SValuePtr &value) {
							return MemoryCellPtr(new MemoryCell(address, value));
						}
						/** Instantiates a new copy of an existing cell. */
						static MemoryCellPtr instance(const MemoryCellPtr &other) {
							return MemoryCellPtr(new MemoryCell(*other));
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Virtual constructors
					public:
						/** Creates a new memory cell object with the specified address and value. */
						virtual BaseSemantics::MemoryCellPtr create(const BaseSemantics::SValuePtr &address, const BaseSemantics::SValuePtr &value){
							return instance(address, value);
						}

						/** Creates a new deep-copy of this memory cell. */
						virtual BaseSemantics::MemoryCellPtr clone() const {
							return MemoryCellPtr(new MemoryCell(*this));
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Dynamic pointer casts. No-op since this is the base class.
					public:
						static MemoryCellPtr promote(const BaseSemantics::MemoryCellPtr &x) {
							ASSERT_not_null(x);
							MemoryCellPtr retval = boost::dynamic_pointer_cast<MemoryCell>(x);
							return retval;
						}
						/**set latest writer set of this cell*/
						virtual void set_latest_writers(std::set<rose_addr_t> &Writers){ latest_writers = Writers;}
						/**get latest writer set of this cell*/
						virtual std::set<rose_addr_t>& get_latest_writers() { return latest_writers; }
				};

				typedef boost::shared_ptr<class MemoryCellList> MemoryCellListPtr;

				class MemoryCellList: public BaseSemantics::MemoryState {
					public:
						typedef std::list<MemoryCellPtr> CellList;
					protected:
						MemoryCellPtr protocell; // prototypical memory cell used for its virtual constructors
						CellList cells; // list of cells in reverse chronological order
						bool byte_restricted; // are cell values all exactly one byte wide?
						MemoryCellPtr latest_written_cell; // the cell whose value was most recently written to, if any
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Real constructors
					protected:
						explicit MemoryCellList(const MemoryCellPtr &protocell)
							: BaseSemantics::MemoryState(protocell->get_address(), protocell->get_value()),protocell(protocell),byte_restricted(true) {
								ASSERT_not_null(protocell);
								ASSERT_not_null(protocell->get_address());
								ASSERT_not_null(protocell->get_value());
							}
						MemoryCellList(const BaseSemantics::SValuePtr &addrProtoval, const BaseSemantics::SValuePtr &valProtoval)
							: BaseSemantics::MemoryState(addrProtoval, valProtoval),protocell(MemoryCell::instance(addrProtoval, valProtoval)),byte_restricted(true) {
							}
						// deep-copy cell list so that modifying this new state does not modify the existing state
						MemoryCellList(const MemoryCellList &other)
							: BaseSemantics::MemoryState(other), protocell(other.protocell), byte_restricted(other.byte_restricted),latest_written_cell(other.latest_written_cell) {
								for (CellList::const_iterator ci=other.cells.begin(); ci!=other.cells.end(); ++ci)
									cells.push_back(MemoryCell::promote((*ci)->clone()));
							}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Static allocating constructors
					public:
						/** Instantiate a new prototypical memory state. This constructor uses the default type for the cell type (based on the
						 * semantic domain). The prototypical values are usually the same (addresses and stored values are normally the same
						 * type). */
						static MemoryCellListPtr instance(const BaseSemantics::SValuePtr &addrProtoval, const BaseSemantics::SValuePtr &valProtoval) {
							return MemoryCellListPtr(new MemoryCellList(addrProtoval, valProtoval));
						}
						/** Instantiate a new memory state with prototypical memory cell. */
						static MemoryCellListPtr instance(const MemoryCellPtr &protocell) {
							return MemoryCellListPtr(new MemoryCellList(protocell));
						}
						/** Instantiate a new copy of an existing memory state. */
						static MemoryCellListPtr instance(const MemoryCellListPtr &other) {
							return MemoryCellListPtr(new MemoryCellList(*other));
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Virtual constructors
					public:
						virtual BaseSemantics::MemoryStatePtr create(const BaseSemantics::SValuePtr &addrProtoval, const BaseSemantics::SValuePtr &valProtoval) const ROSE_OVERRIDE {
							return instance(addrProtoval, valProtoval);
						}
						/** Virtual allocating constructor. */
						virtual BaseSemantics::MemoryStatePtr create(const MemoryCellPtr &protocell) const {
							return instance(protocell);
						}
						virtual BaseSemantics::MemoryStatePtr clone() const ROSE_OVERRIDE {
							return BaseSemantics::MemoryStatePtr(new MemoryCellList(*this));
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Dynamic pointer casts
					public:
						/** Promote a base memory state pointer to a BaseSemantics::MemoryCellList pointer. The memory state @p m must have
						 * a BaseSemantics::MemoryCellList dynamic type. */
						static MemoryCellListPtr promote(const BaseSemantics::MemoryStatePtr &m) {
							MemoryCellListPtr retval = boost::dynamic_pointer_cast<MemoryCellList>(m);
							ASSERT_not_null(retval);
							return retval;
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Methods we inherited
					public:
						virtual void clear() ROSE_OVERRIDE {
							cells.clear();
							latest_written_cell.reset();
						}
						/** Read a value from memory.
						 *
						 * See BaseSemantics::MemoryState() for requirements. This implementation scans the reverse chronological cell list until
						 * it finds a cell that must alias the specified addresses and value size. Along the way, it accumulates a list of cells
						 * that may alias the specified address. If the accumulated list does not contain exactly one cell, or the scan fell off
						 * the end of the list, then @p dflt becomes the return value, otherwise the return value is the single value on the
						 * accumulated list. If the @p dflt value is returned, then it is also pushed onto the front of the cell list.
						 *
						 * The width of the @p dflt value determines how much data is read. The base implementation assumes that all cells contain
						 * 8-bit values. */
						virtual BaseSemantics::SValuePtr readMemory(const BaseSemantics::SValuePtr &addr, const BaseSemantics::SValuePtr &dflt,
								BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) ROSE_OVERRIDE;
						/** Write a value to memory.
						 *
						 * See BaseSemantics::MemoryState() for requirements. This implementation creates a new memory cell and pushes it onto
						 * the front of the cell list.
						 *
						 * The base implementation assumes that all cells contain 8-bit values. */
						virtual void writeMemory(const BaseSemantics::SValuePtr &addr, const BaseSemantics::SValuePtr &value,
								BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) ROSE_OVERRIDE;
						virtual void print(std::ostream &stream, BaseSemantics::Formatter &fmt) const;

						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Methods first declared at this level of the class hierarchy
					public:
						/** Indicates whether memory cell values are required to be eight bits wide. The default is true since this simplifies the
						 * calculations for whether two memory cells are alias and how to combine the value from two or more aliasing cells. A
						 * memory that contains only eight-bit values requires that the caller concatenate/extract individual bytes when
						 * reading/writing multi-byte values.
						 * @{ */
						virtual bool get_byte_restricted() const { return byte_restricted; }
						virtual void set_byte_restricted(bool b) { byte_restricted = b; }
						/** @} */
						/** Scans the cell list and returns entries that may alias the given address and value size. The scanning starts at the
						 * beginning of the list (which is normally stored in reverse chronological order) and continues until it reaches either
						 * the end, or a cell that must alias the specified address. If the last cell in the returned list must alias the
						 * specified address, then true is returned via @p short_circuited argument. */
						virtual CellList scan(const BaseSemantics::SValuePtr &addr, size_t nbits, BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps,
								bool &short_circuited/*out*/) const ;
						/** Visitor for traversing a cell list. */
						class Visitor {
							public:
								virtual ~Visitor() {}
								virtual void operator()(MemoryCellPtr&) = 0;
						};

						/** Visit each memory cell. */
						void traverse(Visitor &visitor){
							for (CellList::iterator ci=cells.begin(); ci!=cells.end(); ++ci)
								(visitor)(*ci);
						}
						/** Returns the list of all memory cells.
						 * @{ */
						virtual const CellList& get_cells() const { return cells; }
						virtual CellList& get_cells() { return cells; }
						/** @} */
						/** Returns the cell most recently written. */
						virtual MemoryCellPtr get_latest_written_cell() const { return latest_written_cell; }
						/** Returns the union of writer virtual addresses for cells that may alias the given address. */
						virtual std::set<rose_addr_t> get_latest_writers(const BaseSemantics::SValuePtr &addr, size_t nbits,
								BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) const;
						/** Returns the union of writers virtual addresses for cells that may alias the given address. */
						virtual std::set<rose_addr_t> allWriters(const BaseSemantics::SValuePtr &addr, size_t nbits,
								BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) const;
						/** Returns the union of writers virtual addresses for cells that may alias the given address. */
						virtual std::set<rose_addr_t> rangeWriters(const BaseSemantics::SValuePtr &addr, size_t nbits,
								BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) const;
				};

				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				//                                      Dataflow State
				//
				// Any state can be used in the calls to the generic BinaryAnalysis::DataFlow stuff, but we define a state here based on
				// symbolic semantics because that's what's commonly wanted.  Users are free to create their own states either from scratch or
				// by inheriting from the one defined here.
				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

				/** State for dataflow. Mostly the same as a semantic state. */
				class State: public Sawyer::SharedObject {
					public:
						typedef Sawyer::SharedPointer<State> Ptr;

					private:
						BaseSemantics::RiscOperatorsPtr ops_;				/// RiscOperator for this particular State
						BaseSemantics::StatePtr semanticState_;				/// BaseSemantics state pointer for this particualr State

					protected:
						// Real Constructors
						explicit State(const BaseSemantics::RiscOperatorsPtr &ops)
							: ops_(ops) {
								init();
							}

						// Deep copy
						State(const State &other): ops_(other.ops_) {
							semanticState_ = other.semanticState_->clone();
						}


					public:

						//-----------------------------------------------------------------------------------------------------------------------//
						// Allocating constructor
						static Ptr instance(const BaseSemantics::RiscOperatorsPtr &ops) {
							return Ptr(new State(ops));
						}

						// Copy + allocate constructor
						Ptr clone() const {
							return Ptr(new State(*this));
						}

						void clear() {
							semanticState_->clear();
						}

						/**Return semantic state correspoding to this State*/
						const BaseSemantics::StatePtr semanticState() const { return semanticState_; }
						/**Return Riscoperator correspoding to this State*/
						const BaseSemantics::RiscOperatorsPtr ops() const { return ops_;}

					public:
						/** merge other state into this, returning true iff changed
						 * Merges other State with the current State(this)*/
						bool merge(const Ptr &other);
						/** merge defining instructions of two Symbolic Value into this, returning true iff changed*/
						bool mergeDefiners(BaseSemantics::SValuePtr &dstValue /*in,out*/, const BaseSemantics::SValuePtr &srcValue) const;
						/** merge two Symbolic Value into this, returning true iff changed*/
						bool mergeSValues(BaseSemantics::SValuePtr &dstValue /*in,out*/, const BaseSemantics::SValuePtr &srcValue) const;
						/** merge two RegisterState into this, returning true iff changed*/
						bool mergeRegisterStates(const RegisterStateGenericPtr &dstState,
								const RegisterStateGenericPtr &srcState) const;
						/** merge two MemoryState into this, returning true iff changed*/
						bool mergeMemoryStates(const MemoryCellListPtr &dstState,
								const MemoryCellListPtr &srcState) const;

					private:
						void init();
				};


				typedef boost::shared_ptr<class RiscOperators> RiscOperatorsPtr;

				/* RISC Operator for Def-Use chain */
				class RiscOperators: public IS2::SymbolicSemantics::RiscOperators{
					private:
						// list of registers just read
						typedef std::pair<BaseSemantics::SValuePtr,AbstractLocation*> ValueAbstractPair;
						typedef std::vector<ValueAbstractPair*> ValueAbstractPairSet;
					private:
						ValueAbstractPairSet readList,writeList;
						MemoryMap map;

						// Real Constructor
					protected:
						explicit RiscOperators(const BaseSemantics::SValuePtr &protoval,const MemoryMap &map_, SMTSolver *solver=NULL)
							: IS2::SymbolicSemantics::RiscOperators(protoval, solver),map(map_) {
								set_name("use-def");
							}
						explicit RiscOperators(const BaseSemantics::StatePtr &state,const MemoryMap &map_, SMTSolver *solver=NULL)
							: IS2::SymbolicSemantics::RiscOperators(state, solver),map(map_) {
								set_name("use-def");
							};

						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Static allocating constructors
					public:

						static RiscOperatorsPtr instance(const RegisterDictionary *regdict,const MemoryMap &map_ ,SMTSolver *solver=NULL) {
							BaseSemantics::SValuePtr protoval = IS2::SymbolicSemantics::SValue::instance();
							BaseSemantics::RegisterStatePtr registers = RegisterStateGeneric::instance(protoval, regdict);
							BaseSemantics::MemoryStatePtr memory = MemoryCellList::instance(protoval, protoval);
							BaseSemantics::StatePtr state = BaseSemantics::State::instance(registers, memory);
							return RiscOperatorsPtr(new RiscOperators(state,map_,solver));
						}
						/** Instantiates a new RiscOperators object with specified prototypical value. An SMT solver may be specified as the second
						 * argument for convenience. See set_solver() for details. */

						static RiscOperatorsPtr instance(const BaseSemantics::SValuePtr &protoval,const MemoryMap &map_ , SMTSolver *solver=NULL) {
							return RiscOperatorsPtr(new RiscOperators(protoval,map_, solver));
						}
						/** Instantiates a new RiscOperators with specified state. An SMT solver may be specified as the second argument for
						 * convenience. See set_solver() for details. */
						static RiscOperatorsPtr instance(const BaseSemantics::StatePtr &state,const MemoryMap &map_ , SMTSolver *solver=NULL) {
							return RiscOperatorsPtr(new RiscOperators(state,map_, solver));
						}


						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Virtual constructors
					public:
						virtual BaseSemantics::RiscOperatorsPtr create(const BaseSemantics::SValuePtr &protoval,const MemoryMap &map_ ,
								SMTSolver *solver=NULL) const ROSE_OVERRIDE {
							return instance(protoval,map_, solver);
						}
						virtual BaseSemantics::RiscOperatorsPtr create(const BaseSemantics::StatePtr &state,const MemoryMap &map_ ,
								SMTSolver *solver=NULL) const ROSE_OVERRIDE {
							return instance(state,map_, solver);
						}
						// Dynamic pointer casts
					public:
						/** Run-time promotion of a base RiscOperators pointer to interval operators. This is a checked conversion--it
						 * will fail if @p from does not point to a IntervalSemantics::RiscOperators object. */
						static RiscOperatorsPtr promote(const BaseSemantics::RiscOperatorsPtr &x) {
							ASSERT_always_not_null(x);
							assert(x!=NULL);
							RiscOperatorsPtr retval = boost::dynamic_pointer_cast<RiscOperators>(x);
							assert(retval!=NULL);
							return retval;
						}
						// Methods first introduced at this level of the class hierarchy.
					public:
						/* Reset all sets */
						virtual void reset(){
							readList.clear();
							writeList.clear();
						}
						virtual ValueAbstractPairSet& getReadList(){return readList;}
						virtual ValueAbstractPairSet& getWriteList(){return writeList;}

					public:
						// Wrapper functions for readRegister, readMemory,writeMemory and writeRegister
						// Also sets above mentioned sets ReadRegList,WriteRegList,ReadMemList,WriteMemList
						virtual BaseSemantics::SValuePtr readRegister(const RegisterDescriptor &reg) ROSE_OVERRIDE;
						virtual void writeRegister(const RegisterDescriptor &reg, const BaseSemantics::SValuePtr &a_) ROSE_OVERRIDE;
						virtual BaseSemantics::SValuePtr readMemory(const RegisterDescriptor &segreg,
								const BaseSemantics::SValuePtr &address,
								const BaseSemantics::SValuePtr &dflt,
								const BaseSemantics::SValuePtr &condition) ROSE_OVERRIDE;

						virtual void writeMemory(const RegisterDescriptor &segreg,
								const BaseSemantics::SValuePtr &address,
								const BaseSemantics::SValuePtr &value_,
								const BaseSemantics::SValuePtr &condition) ROSE_OVERRIDE;
						virtual void interrupt( int majr,int minr ) ROSE_OVERRIDE{
							mlog[INFO]<<"Interrupt handler called"<<std::endl;
						};
				};

				/** Smart pointer to a RiscOperators object.  RiscOperators objects are reference counted and should not be explicitly
				 *  deleted. */
				template<class CFG, class StatePtr>
					class BuildDependenciesEngine {
						public:
							CFG &cfg_;								// Central/Main control flow graph
							typedef Sawyer::Container::DistinctList<size_t> WorkList;
							WorkList workList_; 							// CFG vertex IDs to be visited, last in first out w/out
							Sawyer::Container::Map<const SgAsmInstruction*,BaseSemantics::SValuePtr> retAddrMap;
							typedef std::vector<StatePtr> VertexStates;		// 
							VertexStates incomingState_; 					// incoming data flow state per CFG vertex ID
							VertexStates outgoingState_; 					// outgoing data flow state per CFG vertex ID
							const Partitioner2::Partitioner &partitioner;
							size_t maxIterations_;                          // max number of iterations to allow
							size_t nIterations_;                            // number of iterations since last reset
							BaseSemantics::DispatcherPtr cpu_;				// Dispatcher for corresponding architechture
							BaseSemantics::SValuePtr callRetAdjustment_;	// Adjustment needs to be done in ESP after FakeCall(currently for x86 linux only)
							RegisterDescriptor esp,eax,eip,ss,ebp; 			// RegisterDescriptor for ESP register
							BaseSemantics::SValuePtr startHeap;				// Starting Heap address
							rose_addr_t ctr;								// No of times fakes calls are called and given an address from heap
							rose_addr_t minHeapAllocSize;					// Minimum Heap allocation size
							rose_addr_t maxIterationsPerVertex;				// Maximum no. of iteration per vertex
							typedef std::pair<BaseSemantics::SValuePtr,AbstractLocation*> ValueAbstractPair;
							typedef std::pair<ValueAbstractPair*,const SgAsmInstruction*> DependPair;
							typedef std::vector<ValueAbstractPair*> ValueAbstractPairSet;
							typedef std::vector<DependPair*> DependPairSet;
							typedef Sawyer::Container::Map<const SgAsmInstruction* , ValueAbstractPairSet* > ReachingMap;
							typedef Sawyer::Container::Map<const SgAsmInstruction* , DependPairSet* > DependingMap;
							ReachingMap useChain,defChain;
							DependingMap depOnChain,depOfChain;
							const RegisterDictionary *regdict;
							typedef std::pair<Function::Ptr,rose_addr_t> functionToThisPtr;
							std::set<functionToThisPtr> functionToThisPtrSet;
							// Instructions which are loading the thisptr of the class instance
							std::set<SgAsmInstruction*> classInstanceStart;
							std::set<int> missMerge;

						public:
							/** Constructor.
							 *
							 *  Constructs a new data flow engine that will operate over the specified control flow graph using the standard
							 *  transfer function. The control flow graph is incorporated into the engine by reference; the transfer functor is
							 *  copied. */
							BuildDependenciesEngine(CFG &cfg,const BaseSemantics::DispatcherPtr &cpu,const Partitioner &partitioner_,rose_addr_t maxIterations,
									rose_addr_t minHeapAllocSize_,rose_addr_t maxIterationsPerVertex_): cfg_(cfg),maxIterations_(maxIterations),partitioner(partitioner_),
							nIterations_(0),cpu_(cpu),ctr(0),minHeapAllocSize(minHeapAllocSize_),maxIterationsPerVertex(maxIterationsPerVertex_) {
								// Defining Standard registers
								esp = cpu_->findRegister("esp");
								eax = cpu_->findRegister("eax");
								eip = cpu_->findRegister("eip");
								ss = cpu_->findRegister("ss");
								ebp = cpu_->findRegister("ebp");
								size_t adjustment = esp.get_nbits() / 8; // sizeof return address on top of stack
								callRetAdjustment_ = cpu->number_(esp.get_nbits(), adjustment);
								RiscOperatorsPtr ops = RiscOperators::promote(cpu_->get_operators());
								//startHeap = ops->undefined_(32);
								startHeap = ops->number_(32,0x8040000);
								regdict = cpu_->get_register_dictionary();
							}

							virtual State::Ptr initialState() const{
								namespace BS = BaseSemantics;
								BS::RiscOperatorsPtr ops = cpu_->get_operators();
								State::Ptr state = State::instance(ops);
								RegisterStateGenericPtr regState = RegisterStateGeneric::promote(state->semanticState()->get_register_state());
								regState->zero();
								// Any register for which we need its initial state must be initialized rather than just sprining into existence. We could
								// initialize all registers, but that makes output a bit verbose--users usually don't want to see values for registers that
								// weren't accessed by the dataflow, and omitting their initialization is one easy way to hide them.
								regState->writeRegister(esp, ops->number_(esp.get_nbits(),0x7fff0000), ops.get());
								return state;
							}

							/** Reset engine to initial state.
							 *
							 *  This happens automatically by methods such as @ref runToFixedPoint. */
							virtual void reset(size_t startVertexId,const StatePtr &initialState) {
								ASSERT_this();
								ASSERT_require(startVertexId < cfg_.nVertices());
								ASSERT_not_null(initialState);
								incomingState_.clear();
								incomingState_.resize(cfg_.nVertices());
								incomingState_[startVertexId] = initialState;
								outgoingState_.clear();
								outgoingState_.resize(cfg_.nVertices());
								workList_.clear();
								workList_.pushBack(startVertexId);
								nIterations_ = 0;
							}

							/** Max number of iterations to allow.
							 *
							 *  Allow N number of calls to runOneIteration.  When the limit is exceeded an std::runtime_error is
							 *  thrown.
							 *
							 * @{ */
							virtual size_t maxIterations() const { return maxIterations_; }
							virtual void maxIterations(size_t n) { maxIterations_ = n; }
							/** @} */

							/** Number of iterations run
							 *
							 *  The number of times runOneIteration was called since the last reset. */
							virtual size_t nIterations() const { return nIterations_; }

							virtual void printReachingMap(std::ostream &out,ValueAbstractPairSet* reachingMap_){
								for(ValueAbstractPairSet::iterator it=reachingMap_->begin();it!=reachingMap_->end();it++){
									ValueAbstractPair *current = (*it);
									if(!current->first->is_number())
										out<<"\t[undefined,";
									else
										out<<"\t["<<StringUtility::intToHex(current->first->get_number())<<",";
									current->second->print(out,partitioner.instructionProvider().registerDictionary());out<<"]\n";
								}
							}

							virtual void printDependingMap(std::ostream &out,DependPairSet* dependingMap_){
								for(DependPairSet::iterator it=dependingMap_->begin();it!=dependingMap_->end();it++){
									DependPair *current = (*it);
									ValueAbstractPair *currentVAPair = current->first;
									if(!currentVAPair->first->is_number())
										out<<"\t[undefined,";
									else
										out<<"\t["<<StringUtility::intToHex(currentVAPair->first->get_number())<<",";
									currentVAPair->second->print(out,partitioner.instructionProvider().registerDictionary());
									out<<","<<StringUtility::intToHex(current->second->get_address())<<"]\n";
								}
							}

							/*Print Def-Use Chain*/
							virtual void print(std::ostream &out){
								AsmUnparser unparser;
								BOOST_FOREACH (const typename CFG::Vertex &vertex, cfg_.vertices()) {
									if (DfCfgVertex::BBLOCK == vertex.value().type()){
										BOOST_FOREACH (SgAsmInstruction *insn, vertex.value().bblock()->instructions()){
											out<<"Reaching definitions for Instruction at :"<<
												StringUtility::intToHex(insn->get_address())<<std::endl;
											unparser.unparse_insn(true,out,insn);
											if(useChain.exists(insn)){
												out<<"\t-->USE("<<StringUtility::numberToString(useChain[insn]->size())<<")"<<std::endl;
												printReachingMap(out,useChain[insn]);
											}
											if(defChain.exists(insn)){
												out<<"\t-->DEF("<<StringUtility::numberToString(defChain[insn]->size())<<")"<<std::endl;
												printReachingMap(out,defChain[insn]);
											}
											if(depOnChain.exists(insn)){
												out<<"\t-->DEPON("<<StringUtility::numberToString(depOnChain[insn]->size())<<")"<<std::endl;
												printDependingMap(out,depOnChain[insn]);
											}
											if(depOfChain.exists(insn)){
												out<<"\t-->DEPOF("<<StringUtility::numberToString(depOfChain[insn]->size())<<")"<<std::endl;
												printDependingMap(out,depOfChain[insn]);
											}
										}
									}
								}
							}

							virtual void insertValueAbstractPair(ValueAbstractPairSet* set,ValueAbstractPair* ValueAP){
								BOOST_FOREACH(ValueAbstractPair* current,*set){
									BaseSemantics::SValuePtr valueCurrent = current->first;
									BaseSemantics::SValuePtr valueToCheck = ValueAP->first;
									AbstractLocation* CurrentAloc = current->second;
									AbstractLocation* toCheckAloc = ValueAP->second;
									if(valueCurrent->get_width()==valueToCheck->get_width() && valueCurrent->must_equal(valueToCheck) && 
											CurrentAloc->mustAlias(*toCheckAloc))
										return;
								}
								set->push_back(ValueAP);
								return ;
							}

							virtual void insertDependPair(DependPairSet* set,ValueAbstractPair* ValueAP,SgAsmInstruction* instr){
								BOOST_FOREACH(DependPair *current,*set){
									BaseSemantics::SValuePtr valueCurrent = current->first->first;
									BaseSemantics::SValuePtr valueToCheck = ValueAP->first;
									AbstractLocation* toCheckAloc = ValueAP->second;
									AbstractLocation* alocCurrent = current->first->second;
									const SgAsmInstruction* insnCurrent = current->second;
									if(valueCurrent->get_width()==valueToCheck->get_width() && valueCurrent->must_equal(valueToCheck) && 
											alocCurrent->mustAlias(*toCheckAloc) && insnCurrent==instr)
										return;
								}
								set->push_back(new DependPair(ValueAP,instr));
								return ;
							}

							virtual bool checkForClassInstance(SgAsmInstruction* insn){
								SgAsmX86Instruction *current = isSgAsmX86Instruction(insn);
								if(current && current->get_kind()==x86_lea)
									return true;
							}

							// HIGHLY DEPENDS ON COMPILER AND COMPILER FLAGS USED [IT'S IMPOSSIBLE TO MAKE ANY GLOBAL]
							// Currently implemented for Opitimsation level - 0
							// Current Problems :-
							// 1. It will detect if-else condition also with just one instructions in them, but thats how constructors are
							//    represented as well. What compiler did here is put an if condition on whether the "new" library call returns
							//    a possible address or not. So its impossible to completely differenciate between them
							//    -[[Possible Solution]] :- Anyway to detect the x86_call instruction just before mov instruction would be able to filter.
							//							 but can't be trusted always(In the case of inlined constructors, it will not work).
							virtual bool checkForConstructorFuckUp(const typename CFG::VertexIterator &vertexBblock ){
								if(vertexBblock->nInEdges()!=2)
									return false;
								bool foundMovZero=false,foundConst=false;
								rose_addr_t addr1=0,addr2=0,addr2_size=0;int skipId;
								BOOST_FOREACH (const typename CFG::EdgeNode &edge, vertexBblock->inEdges()) {
									if(edge.source()->value().type() != DfCfgVertex::BBLOCK ) continue;
									const BasicBlock::Ptr prevbblock = edge.source()->value().bblock();
									int noPrevs = prevbblock->nInstructions();
									if(!foundMovZero && noPrevs==1){

										// With Optimisation O2/X
										// xor     ecx, ecx

										// With Optimisation O0
										// mov     [ebp+var_80], 0
										skipId = edge.source()->id();
										SgAsmX86Instruction *last = isSgAsmX86Instruction(prevbblock->instructions()[0]);
										addr1=last->get_address();
										if(last && (x86_mov == last->get_kind() || x86_xor == last->get_kind()))
											foundMovZero = true;
									}
									else if(!foundConst && noPrevs==2){
										// With Optimisation 02/X
										// mov     dword ptr [ecx], offset off_408A48
										// mov     dword ptr [ecx+4], 22h
										// jmp     short loc_403717

										// With Optimisation O1
										// mov     ecx, eax
										// call    sub_4011FE
										// mov     ecx, eax

										// With Optimisation O0
										// mov     ecx, [ebp+var_78]
										// call    sub_411393

										// mov     [ebp+var_80], eax
										// jmp     short loc_41423C
										SgAsmX86Instruction *insn1 = isSgAsmX86Instruction(prevbblock->instructions()[0]);
										SgAsmX86Instruction *insn2 = isSgAsmX86Instruction(prevbblock->instructions()[1]);
										addr2 = insn2->get_address(); addr2_size = insn2->get_baseSize();
										if(insn1 && insn2 && x86_mov==insn1->get_kind() && x86_jmp == insn2->get_kind() )
											foundConst=true;
									}
									if(foundMovZero && foundConst && addr2_size+addr2==addr1){
										missMerge.insert(skipId);
										return true;
									}
								}
								return false;
							}

							virtual State::Ptr transferFunction(size_t cfgVertexId, const StatePtr &incomingState){

								RiscOperatorsPtr ops = RiscOperators::promote(cpu_->get_operators());
								typename CFG::VertexIterator vertex = cfg_.findVertex(cfgVertexId);
								State::Ptr retval = incomingState->clone();
								ops->set_state(retval->semanticState());
								// if current vertx is a Fake call vertex type
								if (DfCfgVertex::FAKED_CALL == vertex->value().type()) {

									const SgAsmInstruction *call_inst = vertex->value().call_instruction();
									BaseSemantics::SValuePtr oldStack = ops->readRegister(esp);
									BaseSemantics::SValuePtr newStack = ops->add(oldStack, callRetAdjustment_);
									// Set the ESP value back to the returning address
									ops->writeRegister(esp, newStack);
									// reset the ReadReglist,WriteRegList,ReadMemList and WriteMemList
									ops->reset();
									// In x86 returned value is stored in the eax register and we don't know the returned
									// value so we can put anything in EAX register( i'm gonna go with an unknown heap address)
									// but a Symbolic value will also work instead of any real value
									// You have to also set the current calling instruction as the latest writer to the EAX
									if(!retAddrMap.exists(call_inst)){
										retAddrMap.insert(call_inst,ops->add(startHeap,ops->number_(32,ctr*minHeapAllocSize)));ctr++;
									}
									ops->writeRegister(eax,retAddrMap[call_inst]);

									// EIP will also be changed( for each instruction )
									BaseSemantics::SValuePtr new_eip = ops->readMemory(ss,oldStack,ops->undefined_(32),ops->boolean_(true));
									ops->writeRegister(eip,new_eip);
									// Setting the latest writer for EAX nand EIP
									RegisterStateGenericPtr regState = RegisterStateGeneric::promote(retval->semanticState()->get_register_state());
									regState->set_latest_writer(eip,call_inst->get_address());
									regState->set_latest_writer(eax,call_inst->get_address());
									std::set<rose_addr_t> temp,temp1;
									temp.insert(call_inst->get_address());temp1.insert(call_inst->get_address());
									// Setting the allWriters for the EAX and EIP
									regState->setAllWriters(eax,temp);regState->setAllWriters(eip,temp1);

									// Iterating over the WriteList to build the Def-Use chain contributed by this instuction
									ValueAbstractPairSet &writeList = ops->getWriteList();
									// Iterate over all the Write  List
									BOOST_FOREACH(ValueAbstractPair *ValueAP,writeList){
										insertValueAbstractPair(defChain[call_inst],ValueAP);
									}
								} else if (DfCfgVertex::FUNCRET == vertex->value().type()) {
									// Identity semantics; this vertex just merges all the various return blocks in the function.
								} else if (DfCfgVertex::INDET == vertex->value().type()) {
									// We don't know anything about the vertex, therefore we don't know anything about its semantics
									mlog[WARN]<<"INDET"<<std::endl;
									retval->clear();
								} else { // FOR BBLOCK
									// Build a new state using the retval created above, then execute instructions to update it.
									ASSERT_require(vertex->value().type() == DfCfgVertex::BBLOCK);
									ASSERT_not_null(vertex->value().bblock());

									// Iterate over each instruction of the basicBlock
									BOOST_FOREACH (SgAsmInstruction *insn, vertex->value().bblock()->instructions()){
										// reset the ReadReglist,WriteRegList,ReadMemList and WriteMemList
										ops->reset();

										MemoryCellListPtr prevMemoryState = MemoryCellList::promote(retval->semanticState()->get_memory_state()->clone());
										RegisterStateGenericPtr prevRegisterState = RegisterStateGeneric::promote(retval->semanticState()->get_register_state()->clone());
										//Process the current instrcution of the bblock
										try{
											cpu_->processInstruction(insn);
										}catch (const Disassembler::Exception &e) {
											mlog[WARN]<<"Dissassbling error : Skipping instruction : "<<StringUtility::intToHex(insn->get_address())
												<<std::endl;
										}catch(const BaseSemantics::Exception &e){
											mlog[WARN]<<"Skipping instruction : "<<StringUtility::intToHex(insn->get_address())
												<<std::endl;
										}
										checkForClassInstance(insn);
										// Get the ReadReglist,WriteRegList,ReadMemList and WriteMemList
										ValueAbstractPairSet &readList =  ops->getReadList();
										ValueAbstractPairSet &writeList = ops->getWriteList();

										// Defining instruction
										SgAsmInstruction *inst;

										// Iterate over ReadList
										useChain.insertMaybe(insn,new ValueAbstractPairSet());
										defChain.insertMaybe(insn,new ValueAbstractPairSet());
										depOnChain.insertMaybe(insn,new DependPairSet());
										depOfChain.insertMaybe(insn,new DependPairSet());
										BOOST_FOREACH(ValueAbstractPair *ValueAP,readList){
											insertValueAbstractPair(useChain[insn],ValueAP);
											AbstractLocation* aLoc = ValueAP->second;

											// Get allwriters of the current read register and iterate over it to get the Def-Use chain
											if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="ecx"){
												BOOST_FOREACH(rose_addr_t definer,prevRegisterState->allWriters(aLoc->getRegister())){
													inst = partitioner.discoverInstruction(definer);
													insertDependPair(depOnChain[insn],ValueAP,inst);
												}
											}
											if(aLoc->isAddress()){
												BOOST_FOREACH (rose_addr_t definer,prevMemoryState->rangeWriters(aLoc->getAddress(),
															ValueAP->first->get_width(),ops.get(), ops.get())){
													inst = partitioner.discoverInstruction(definer);
													insertDependPair(depOfChain[inst],ValueAP,insn);
												}
											}

										}
										// Iterate over all the Write  List
										BOOST_FOREACH(ValueAbstractPair *ValueAP,writeList){
											AbstractLocation* aLoc = ValueAP->second;
											BaseSemantics::SValuePtr symval = ValueAP->first;
											if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="ecx" && symval->is_number() && checkForClassInstance(insn)){
												Function::Ptr function = partitioner.basicBlockFunctionOwner(partitioner.basicBlockContainingInstruction(insn->get_address()));
												functionToThisPtr toCheck(function,symval->get_number());
												if(functionToThisPtrSet.find(toCheck)==functionToThisPtrSet.end()){
													mlog[INFO]<<"Found new Instruction initiating class instance : "<<StringUtility::intToHex(insn->get_address())
														<<std::endl;
													functionToThisPtrSet.insert(toCheck);
													classInstanceStart.insert(insn);
												}
											}
											insertValueAbstractPair(defChain[insn],ValueAP);
										}
									}
								}
								return retval;
							}

							/** Run data flow until it reaches a fixed point.
							 *
							 *  Run data flow starting at the specified control flow vertex with the specified initial state until the state
							 *  converges to a fixed point no matter how long that takes. */
							virtual void runToFixedPoint(size_t startVertexId,const StatePtr &initialState){

								reset(startVertexId, initialState);						/// Setting the initial State for each vertex
								std::vector<int> count(cfg_.nVertices(),0);				// limit count
								count[startVertexId]++;
								std::vector<bool> DONE(cfg_.nVertices(),false);
								// Loop to run until the state is getting changed Run until we got a Fixed Point
								while (!workList_.isEmpty()){
									if (++nIterations_ > maxIterations_) {
										throw std::runtime_error("dataflow max iterations reached"
												" (max=" + StringUtility::numberToString(maxIterations_) + ")");
									}
									size_t cfgVertexId = workList_.popFront();
									typename CFG::ConstVertexIterator vertex = cfg_.findVertex(cfgVertexId);
									StatePtr state = incomingState_[cfgVertexId];
									ASSERT_not_null(state);

									/* PROCESS EACH INSTRUCTION IN EACH VERTEX*/
									state = outgoingState_[cfgVertexId] = transferFunction(cfgVertexId, state);

									BOOST_FOREACH (const typename CFG::EdgeNode &edge, vertex->outEdges()) {
										size_t nextVertexId = edge.target()->id();
										if(count[nextVertexId]>=maxIterationsPerVertex){
											mlog[INFO]<<"Stopping Further Processing of Vertex with id : "<<
												StringUtility::numberToString(nextVertexId)<<std::endl;
											continue;
										}
										StatePtr targetState = incomingState_[nextVertexId];
										if(!DONE[nextVertexId]){
											checkForConstructorFuckUp(cfg_.findVertex(nextVertexId));
											DONE[nextVertexId]=true;
										}
										if(missMerge.find(cfgVertexId)!=missMerge.end() ){
											mlog[INFO]<<"Skipping the merging of vertex of id "<<StringUtility::numberToString(nextVertexId)<<
												" with Vertex of id "<<StringUtility::numberToString(cfgVertexId)<<std::endl;
										}
										else if (targetState==NULL) {
											incomingState_[nextVertexId] = state->clone(); // copy the state
											workList_.pushBack(nextVertexId);
											count[nextVertexId]++;
										} else if (targetState->merge(state)) {
											mlog[INFO]<<"Merged : "<<StringUtility::numberToString(nextVertexId)<< " with "<<
												StringUtility::numberToString(cfgVertexId)<<std::endl;
											workList_.pushBack(nextVertexId);
											count[nextVertexId]++;
										} else {
											mlog[INFO]<<"No Change in States after Merging : "<<nextVertexId << " with "<<cfgVertexId<<std::endl;
										}
									}
								}
							}

						public:
							virtual ~BuildDependenciesEngine() {}
					};

				/** Dataflow engine. */
				typedef rose::BinaryAnalysis::Partitioner2::InterDataFlow::BuildDependenciesEngine<DfCfg, State::Ptr> Engine;
			} // namespace
		} // namespace
	} // namespace
} // namespace

#endif
