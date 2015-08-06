///
///     Written By: Shubham Bansal (illusionist.neo@gmail.com)
///     Blog :- http://in3o.me
///		Copyright (c) 2015 Shubham Bansal (iN3O)

///		Permission is hereby granted, free of charge, to any person obtaining a copy of 
///		this software and associated documentation files (the "Software"), to deal in the
///		Software without restriction, including without limitation the rights to use, copy,
///		modify, merge, publish, distribute, sublicense, and/or sell copies of the Software,
///		and to permit persons to whom the Software is furnished to do so, subject to the 
///		following conditions:

///		The above copyright notice and this permission notice shall be included in all copies 
///		or substantial portions of the Software.

///		THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, 
///		INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
///		PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE
///		FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR 
///		OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
///

#ifndef ROSE_Partitioner2_ClassSemantics_H
#define ROSE_Partitioner2_ClassSemantics_H


#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif

#include "sage3basic.h"
#include <iostream>
#include <Partitioner2/Partitioner.h>
#include <Sawyer/GraphTraversal.h>
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
#include <Sawyer/Graph.h>
#include <Sawyer/DistinctList.h>
#include <vector>
#include <typeinfo>
#include <BaseSemantics2.h>
#include <DispatcherX86.h>
#include <AstSimpleProcessing.h>
#include <InsnSemanticsExpr.h>
#include <Partitioner2/Config.h>
#include <YicesSolver.h>

using namespace rose::BinaryAnalysis;
using namespace Sawyer::Message::Common;
using namespace Sawyer::Container::Algorithm;
namespace IS2 = InstructionSemantics2;

#define ARBITRARY_PARAM_LIMIT 60

namespace rose {
	namespace BinaryAnalysis {
		namespace Partitioner2 {


			/** A fully symbolic semantic domain.
			 *
			 * This semantic domain can be used to emulate the execution of a single basic block of instructions. It is similar in nature
			 * to SymbolicSemantics, but with a different type of semantics value (SValue): instead of storing defining instruction for each
			 * variable, we are using modifying instruction which only stores the latest instruction which used/wrote that SValue
			 *
			 * A special MemoryState class is made, in which instead of storing a list of memoryCell with there symbolic value, we are storing
			 * them as a Sawyer::Constainer::Map with hash of SymbolicValue as key and SymbolicValue as value. Although, this is not a perfect
			 * MemoryState class and will give wrong result for same address having different expression (Memory aliasing problem) (as there 
			 * hash calculated is different) but it surely works faster and better in our case and doesn't affect our analysis much.
			 *
			 * SValue: the values stored in registers and memory and used for memory addresses.
			 * MemoryCell: an address-expression/value-expression pair for memory. Same as SymobolidSemantics::MemoryCell .
			 * MemoryState: the collection of MemoryCells that form a complete memory state. 
			 * RegisterState: the collection of registers that form a complete register state. Same as SymobolidSemantics::RegisterState .
			 * State: represents the state of the virtual machine&mdash;its registers and memory. Same as SymobolidSemantics::State .
			 * RiscOperators: the low-level operators called by instruction dispatchers (e.g., DispatcherX86). 
			 *
			 * If an SMT solver is supplied a to the RiscOperators then that SMT solver will be used to answer various questions such as
			 * when two memory addresses can alias one another. When an SMT solver is lacking, the questions will be answered by very
			 * naive comparison of the expression trees. */


			namespace ClassSemantics {

				namespace SymbolicSemantics = IS2::SymbolicSemantics;

				// Required Typedefs from other namespaces

				typedef std::set<SgAsmInstruction*> InsnSet;
				typedef InsnSemanticsExpr::LeafNode LeafNode;
				typedef InsnSemanticsExpr::LeafNodePtr LeafNodePtr;
				typedef InsnSemanticsExpr::InternalNode InternalNode;
				typedef InsnSemanticsExpr::InternalNodePtr InternalNodePtr;
				typedef InsnSemanticsExpr::TreeNodePtr TreeNodePtr;
				typedef boost::shared_ptr<class AbstractLocation> AbstractLocationPtr;
				typedef BaseSemantics::MemoryCellPtr MemoryCellPtr;

				// Function returns the address of the function given the name or the address of the function.
				Sawyer::Optional<rose_addr_t> addressForFunction(const Partitioner &partitioner, const std::string &nameOrVa);

				AddressIntervalSet getSectionRangeByName(SgAsmInterpretation *interp,std::string sectionName);


				// checks of the two symbolic values are equal or not. SMT solver can also be used but its default value is
				// considered to be as NULL and can be used without it although if SMT Sover is not used, it may give false negative
				bool checkSValueEqual(const BaseSemantics::SValuePtr &a_,const BaseSemantics::SValuePtr &b_,SMTSolver *solver=NULL);


				/* Function used to detect special case of library call thunks which are used in debug mode Executables of MSVC
				 *
				 * For example :-
				 *				addr1 :    jmp addr2	  // addr1,addr2 lies in .text section
				 *               addr2 :    jmp ds:[addr3] // addr3 is the address from IAT
				 */
				void libraryThunkFixups(const Partitioner &partitioner, SgAsmInterpretation *interp);


				/* A Callback class to detect the Previlaged instruction like intx (interrupt) and fix the control flow graph
				 *  accordingly.
				 *  For example :- 
				 *					int 0x18		// int this case the out Edge of the CFG is considered as indeterminate by the
				 *									// Rose as it assumes that "intx" will lead to a call to interrupt vector handler
				 *									// which is correct but in our analysis we need to get to the next instruction just
				 *									// after "intx". So each time we detect this case ,this callback will make the next
				 *									// basic block which is just after this instruction, as the children of the currect
				 *									// basic block.
				 */
				class PePrivilege: public BasicBlockCallback {
					public:
						typedef Sawyer::SharedPointer<PePrivilege> Ptr;
					protected:
						bool verbose_;
					protected:
						// Real Constructor
						PePrivilege(bool verbose):verbose_(verbose){};

					public:

						// Static Constructor
						static Ptr instance(bool verbose=false){ return Ptr(new PePrivilege(verbose));}

						// Checks if the instruction is INT 3 and if it is, then it change the CFG accordingly without indeterminate CFG
						virtual bool operator()(bool chain,const Args &args) ROSE_OVERRIDE;
				};

				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				// Semantic values
				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

				/** Class Extended from SymbolicSemantics::SValue.
				 *   - Instead of using the defining instructions( which includes all the instruction which has influenced this
				 *     SValue upto this point ), we defined a similar set of instruction called "modifiers" which consits of only
				 *	  those instruction which used/wrote this SValue to Memory or Register last time.
				 *	- This implementation is much more effective as we can use this to build the complete defining instruction
				 *	  set by traveling back and as you can understand the defining instruction can consist of huge set of instruction
				 *	  which definitely lead to a huge memory usage ,slow speed and completely un-necessary here.
				 */

				/** Smart pointer to an SValue object. SValue objects are reference counted and should not be explicitly deleted. */
				typedef Sawyer::SharedPointer<class SValue> SValuePtr;

				class SValue: public SymbolicSemantics::SValue {
					protected:
						/** Instructions last modified this value. Last instruction that saves the value to a register or memory location
						 * adds itself to the saved value. */
						InsnSet modifiers;
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Real constructors
					protected:
						explicit SValue(size_t nbits): SymbolicSemantics::SValue(nbits) {}
						explicit SValue(size_t nbits, uint64_t number): SymbolicSemantics::SValue(nbits,number) {}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Static allocating constructors
					public:
						/** Instantiate a new prototypical value. Prototypical values are only used for their virtual constructors. */
						static SValuePtr instance() {
							return SValuePtr(new SValue(1));
						}
						/** Instantiate a new undefined value of specified width. */
						static SValuePtr instance(size_t nbits) {
							return SValuePtr(new SValue(nbits));
						}
						/** Instantiate a new concrete value. */
						static SValuePtr instance(size_t nbits, uint64_t value) {
							return SValuePtr(new SValue(nbits, value));
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Virtual allocating constructors
					public:
						virtual BaseSemantics::SValuePtr undefined_(size_t nbits) const ROSE_OVERRIDE {
							return instance(nbits);
						}
						virtual BaseSemantics::SValuePtr number_(size_t nbits, uint64_t value) const ROSE_OVERRIDE {
							return instance(nbits, value);
						}
						virtual BaseSemantics::SValuePtr boolean_(bool value) const ROSE_OVERRIDE {
							return number_(1, value?1:0);
						}
						virtual BaseSemantics::SValuePtr copy(size_t new_width=0) const ROSE_OVERRIDE {
							SValuePtr retval(new SValue(*this));
							if (new_width!=0 && new_width!=retval->get_width())
								retval->set_width(new_width);
							return retval;
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Dynamic pointer casts
					public:
						/** Promote a base value to a CallSemantics value. The value @p v must have a CallSemantics::SValue dynamic type. */
						static SValuePtr promote(const BaseSemantics::SValuePtr &v) { // hot
							SValuePtr retval = v.dynamicCast<SValue>();
							ASSERT_not_null(retval);
							return retval;
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Additional methods first declared in this class...
					public:
						virtual void print(std::ostream&, BaseSemantics::Formatter&) const ROSE_OVERRIDE;
						/** Adds instructions to the list of modifying instructions. Adds the specified instruction and defining sets into this
						 * value and returns a reference to this value. See also add_modifying_instructions().
						 * @{ */

						// Here set1 and set2 are the latest and only modifying instructions sets
						virtual void modified_by(const InsnSet &set1, const InsnSet &set2) {
							set_modifying_instructions(set2);
							add_modifying_instructions(set1);
						}

						// Here set1 is the only and latest modifying instruction set
						virtual void modified_by(const InsnSet &set1) {
							set_modifying_instructions(set1);
						}

						// Here only insn is the latest modifying instruction
						virtual void modified_by(SgAsmInstruction *insn) {
							set_modifying_instructions(insn);
						}

						// Return the modifying instructions of this SymbolicValue
						virtual const InsnSet& get_modifying_instructions() const {
							return modifiers;
						}
						/** Returns the set of instructions that defined this value. The return value is a flattened lattice represented as a set.
						 * When analyzing this basic block starting with an initial default state:
						 *
						 * 1: mov eax, 2
						 * 2: add eax, 1
						 * 3: mov ebx, eax;
						 * 4: mov ebx, 3
						 *
						 * the defining set for EAX will be instructions {1, 2} and the defining set for EBX will be {4}.On the other hand the modifying
						 * set of instructions of EAX will be instruction { 2 } and the modifiying set of intructions of EBX will be {4}.Modifying sets 
						 * for other registers are the empty set. */

						/** Adds modifiers to the list of modifying instructions. Returns the number of items added that weren't already in the
						 * list of modifying instructions. @{ */
						virtual size_t add_modifying_instructions(const InsnSet &to_add);
						virtual size_t add_modifying_instructions(const SValuePtr &source) {
							return add_modifying_instructions(source->get_modifying_instructions());
						}
						virtual size_t add_modifying_instructions(SgAsmInstruction *insn);
						/** @} */
						/** Set modifying instructions. This discards the old set of defining instructions and replaces it with the specified set.
						 * @{ */
						virtual void set_modifying_instructions(const InsnSet &new_modifiers) {
							modifiers = new_modifiers;
						}
						virtual void set_modifying_instructions(const SValuePtr &source) {
							set_modifying_instructions(source->get_modifying_instructions());
						}
						virtual void set_modifying_instructions(SgAsmInstruction *insn);

						/* Special function to find the offest between two SValues and return that offset in argument "offset"
						 *  This implementation is a temparory substitute of subtract function in Riscoperator which doesn't work
						 *  properly. Although this function is not compliacted and handles only specific caes but is sufficient 
						 *  for this analysis.
						 *
						 *  This currently handles two Cases :-
						 *					SValue1		SValue2			Result
						 *		Case 1 ->  	var1 		var1 + xx   	xx
						 *		Case 2 -> 	var1 + xx	var1 + yy		yy - xx
						 *
						 */
						virtual bool getOffset(SValuePtr &other,int32_t &offset,SMTSolver *solver);
						/** @} */
				};

				/*	AbstractClass is made specially for Def-Use Analysis data structure.
				 *	It is of the form < V , A > where V -> Symbolic Value and A -> Abstract Location (could be Register
				 *	or Memory address )
				 *	This structure is used to represent the DEF-USE chain in further analysis.
				 */

				typedef boost::shared_ptr<class AbstractAccess> AbstractAccessPtr;

				class AbstractAccess{
					public:
						typedef BaseSemantics::SValuePtr Address; /**< Type of memory address. */
						typedef BaseSemantics::SValuePtr Value; // For the read/Write value
					private:
						Value val_;
						AbstractLocationPtr aloc_;
					public:
						/** Copy constructor. */
						explicit AbstractAccess(const AbstractAccess& other): aloc_(other.aloc_),val_(other.val_){}

						/** Register referent.
						 *
						 * Constructs an abstract accress that refers to a <value,AbstractLocation> pair. */
						explicit AbstractAccess(const Value& val,const RegisterDescriptor &reg): val_(val),aloc_(new AbstractLocation(reg)){}

						/** Memory referent.
						 *
						 * Constructs an abstract access that refers to a <value,AbstractLocation> pair. */
						explicit AbstractAccess(const Value& val,const Address &addr): val_(val),aloc_(new AbstractLocation(addr,val->get_width())){}

						/** AbstractLocation Referent
						 *
						 * Construct an abstract access that refers to a <value,AbstractLocation> pair. */
						explicit AbstractAccess(const Value& val,const AbstractLocationPtr &aloc): val_(val),aloc_(aloc){}

					public:
						// Static Constructors

						static AbstractAccessPtr instance(const AbstractAccess& other){
							return AbstractAccessPtr(new AbstractAccess(other));
						}

						static AbstractAccessPtr instance(const Value& val,const RegisterDescriptor &reg){
							return AbstractAccessPtr(new AbstractAccess(val,reg));
						}

						static AbstractAccessPtr instance(const Value& val,const Address &addr){
							return AbstractAccessPtr(new AbstractAccess(val,addr));
						}

						static AbstractAccessPtr instance(const Value& val,const AbstractLocationPtr &aloc){
							return AbstractAccessPtr(new AbstractAccess(val,aloc));
						}

					public:

						// Return the V from the pair <V,A> 
						virtual const Value& getValue(){ return val_; }

						// returns the A from the pair <V,A>
						virtual const AbstractLocationPtr& getAloc(){ return aloc_; }

						// Prints the <V,A> as an expression using the SymbolicSemantic formatter
						virtual void print(std::ostream &out,const RegisterDictionary *regdict){
							BaseSemantics::Formatter fmt;
							val_->print(out,fmt);out<<",";
							aloc_->print(out,regdict);
						}

						// checks if two <V,A> are equal or not.
						virtual bool checkEqual(const AbstractAccessPtr &other,SMTSolver *solver=NULL){
							if(checkSValueEqual(val_,other->val_,solver) && aloc_->mustAlias(*(other->aloc_),solver) )
								return true;
							return false;
						}

						/** Assignment operator. */
						AbstractAccess& operator=(const AbstractAccess &other) {
							val_ = other.val_;
							aloc_ = other.aloc_;
							return *this;
						}

				};

				// Same register class used. No need to modify
				typedef BaseSemantics::RegisterStateGeneric RegisterState;
				typedef BaseSemantics::RegisterStateGenericPtr RegisterStatePtr;

				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				// Memory state
				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				typedef boost::shared_ptr<class MemoryState> MemoryStatePtr;

				class MemoryState: public SymbolicSemantics::MemoryState {
					public:
						typedef Sawyer::Container::Map<rose_addr_t,MemoryCellPtr> CellMap;
					protected:
						/* This is the new partialy flawed implementation of the memoryState which stores memory as Map intead
						 *  of traditional list of cells.
						 *  In this implementation key of the map is the hash of the symbolic value of address and the value is the
						 *  MemoryCell which contains the SValue stores at that address.
						 */
						CellMap allCells;

						/// Real Constructor
					protected:
						explicit MemoryState(const BaseSemantics::MemoryCellPtr &protocell)
							: SymbolicSemantics::MemoryState(protocell){}
						explicit MemoryState(const BaseSemantics::SValuePtr &addrProtoval, const BaseSemantics::SValuePtr &valProtoval)
							: SymbolicSemantics::MemoryState(addrProtoval,valProtoval){}
						explicit MemoryState(const MemoryState &other)
							: SymbolicSemantics::MemoryState(other){
								BOOST_FOREACH(const CellMap::Node &cnode,other.allCells.nodes()){
									allCells.insert(cnode.key(),cnode.value()->clone());
								}
							}

						// Static allocating constructor
					public:
						static MemoryStatePtr instance(const BaseSemantics::MemoryCellPtr &protocell){
							return MemoryStatePtr(new MemoryState(protocell));
						}
						static MemoryStatePtr instance(const BaseSemantics::SValuePtr &addrProtoval, const BaseSemantics::SValuePtr &valProtoval) {
							return MemoryStatePtr(new MemoryState(addrProtoval, valProtoval));
						}
						static MemoryStatePtr instance(const MemoryStatePtr &other) {
							return MemoryStatePtr(new MemoryState(*other));
						}

						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Virtual constructors
					public:
						/** Virtual constructor. Creates a memory state having specified prototypical value. This constructor uses
						 * BaseSemantics::MemoryCell as the cell type. */
						virtual BaseSemantics::MemoryStatePtr create(const BaseSemantics::SValuePtr &addrProtoval,
								const BaseSemantics::SValuePtr &valProtoval) const ROSE_OVERRIDE {
							return instance(addrProtoval, valProtoval);
						}
						/** Virtual constructor. Creates a new memory state having specified prototypical cells and value. */
						virtual BaseSemantics::MemoryStatePtr create(const BaseSemantics::MemoryCellPtr &protocell) const ROSE_OVERRIDE {
							return instance(protocell);
						}
						/** Virtual copy constructor. Creates a new deep copy of this memory state. */
						virtual BaseSemantics::MemoryStatePtr clone() const ROSE_OVERRIDE {
							return MemoryStatePtr(new MemoryState(*this));
						}

						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Dynamic pointer casts
					public:
						/** Recasts a base pointer to a symbolic memory state. This is a checked cast that will fail if the specified pointer does
						 * not have a run-time type that is a SymbolicSemantics::MemoryState or subclass thereof. */
						static MemoryStatePtr promote(const BaseSemantics::MemoryStatePtr &x) {
							MemoryStatePtr retval = boost::dynamic_pointer_cast<MemoryState>(x);
							ASSERT_not_null(retval);
							return retval;
						}
						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Methods we inherited
					public:
						virtual void clear() ROSE_OVERRIDE {
							allCells.clear();
							latest_written_cell.reset();
						}

						virtual const CellMap getAllCells(){ return allCells; }

						/** Scans the cell list and returns entries that may alias the given address and value size. The scanning starts at the
						 * beginning of the list (which is normally stored in reverse chronological order) and continues until it reaches either
						 * the end, or a cell that must alias the specified address. If the last cell in the returned list must alias the
						 * specified address, then true is returned via @p short_circuited argument. */
						virtual CellList scan(const BaseSemantics::SValuePtr &address, size_t nbits, BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps,
								bool &short_circuited/*out*/) ROSE_OVERRIDE;

						/** Read a byte from memory.
						 *
						 * In order to read a multi-byte value, use RiscOperators::readMemory(). */
						virtual BaseSemantics::SValuePtr readMemory(const BaseSemantics::SValuePtr &addr, const BaseSemantics::SValuePtr &dflt,
								BaseSemantics::RiscOperators *addrOps,
								BaseSemantics::RiscOperators *valOps) ROSE_OVERRIDE;

						/** Write a byte to memory.
						 *
						 * In order to write a multi-byte value, use RiscOperators::writeMemory(). */
						virtual void writeMemory(const BaseSemantics::SValuePtr &addr, const BaseSemantics::SValuePtr &value,
								BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) ROSE_OVERRIDE;
				};

				/** A multi-byte variable that appears on the stack. */
				struct StackVariable {
					rose_addr_t offset; /**< Offset from initial stack pointer. */
					size_t nBytes; /**< Size of variable in bytes. */
					StackVariable(int64_t offset, size_t nBytes): offset(offset), nBytes(nBytes){}
				};
				/** Multiple stack variables. */
				typedef std::vector<StackVariable> StackVariables;

				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				// Complete state
				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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
						// Read Value stored in the register which is stored in the semanticState_
						// It just calls the Riscoperator to do the job
						virtual BaseSemantics::SValuePtr readRegister(const RegisterDescriptor &desc){
							return semanticState_->readRegister(desc,ops_.get());
						}

						// Read Value stored at the memory Address stored in the semanticState_
						// It just calls the Riscoperator to do the job
						virtual BaseSemantics::SValuePtr readMemory(const RegisterDescriptor &segreg,BaseSemantics::SValuePtr &addr,rose_addr_t size){
							ops_->set_state(semanticState_);
							return ops_->readMemory(segreg,addr,ops_->undefined_(size),ops_->boolean_(true));
						}

						/** merge other state into this, returning true iff changed
						 * Merges other State with the current State(this)*/
						virtual bool merge(const Ptr &other);

						/** merge defining instructions of two Symbolic Value into this, returning true iff changed*/
						virtual bool mergeModifiers(BaseSemantics::SValuePtr &dstValue /*in,out*/, const BaseSemantics::SValuePtr &srcValue) const;

						/** merge two Symbolic Value into this, returning true iff changed*/
						virtual bool mergeSValues(BaseSemantics::SValuePtr &dstValue /*in,out*/, const BaseSemantics::SValuePtr &srcValue) const;

						/** merge two RegisterState into this, returning true iff changed*/
						virtual bool mergeRegisterStates(const RegisterStatePtr &dstState,const RegisterStatePtr &srcState) const;

						/** merge two MemoryState into this, returning true iff changed*/
						virtual bool mergeMemoryStates(const MemoryStatePtr &dstState,const MemoryStatePtr &srcState) const;

					private:
						void init();
				};


				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				// RISC operators
				////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				/* Specialy overrided SymbolicSemantics::RiscOperator class
				 * ==> This class adds an abstraction between the SymbolicSemantics::RiscOperator and the Dispatcher, so that we can
				 *   catch all the memory write and read in the combined form (not in the concrete form). Few other modifications are
				 *	made to make it work more properly, like :-
				 *		-> Added read from MemoryMap of the Specimen loaded
				 * 		-> Added protoval for the new Modified SValue class
				 * ==> Each RISC operator should return a newly allocated semantic value so that the caller can adjust definers for the result
				 * without affecting any of the inputs. For example, a no-op that returns its argument should be implemented like this:
				 *
				 * BaseSemantics::SValuePtr noop(const BaseSemantics::SValuePtr &arg) {
				 * 		return arg->copy(); //correct
				 * 		return arg; //incorrect
				 * }
				 */

				typedef boost::shared_ptr<class RiscOperators> RiscOperatorsPtr;

				/* RISC Operator for Def-Use chain */
				class RiscOperators: public SymbolicSemantics::RiscOperators{
					public:
						typedef std::vector<AbstractAccessPtr> AbstractAccessSet;

					private:
						// list of registers/memory address just read/written
						AbstractAccessSet readList_,writeList_;						// list of read and write in the form of <V,A>
						bool compute_useDefChain,compute_latestWriter;				// flags to turn ON def-use chain build
						MemoryMap &map_;											// to read from the actual Specimen
						bool verbose_;												// verbose

						// Real Constructor
					protected:
						explicit RiscOperators(const BaseSemantics::SValuePtr &protoval,MemoryMap &map,SMTSolver *solver=NULL)
							: SymbolicSemantics::RiscOperators(protoval, solver),compute_useDefChain(false),compute_latestWriter(false),map_(map),verbose_(false){
								set_name("CallSemantics");
								(void) SValue::promote(protoval); // make sure its dynamic type is a CallSemantics::SValue
							}
						explicit RiscOperators(const BaseSemantics::StatePtr &state,MemoryMap &map,SMTSolver *solver=NULL)
							: SymbolicSemantics::RiscOperators(state, solver),compute_useDefChain(false),compute_latestWriter(false),map_(map),verbose_(false) {
								set_name("CallSemantics");
								(void) SValue::promote(state->get_protoval()); // make sure its dynamic type is a CallSemantics::SValue
							};

						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Static allocating constructors
					public:

						static RiscOperatorsPtr instance(const RegisterDictionary *regdict,MemoryMap &map,SMTSolver *solver=NULL) {
							BaseSemantics::SValuePtr protoval = SValue::instance();
							BaseSemantics::RegisterStatePtr registers = RegisterState::instance(protoval, regdict);
							BaseSemantics::MemoryStatePtr memory = MemoryState::instance(protoval, protoval);
							BaseSemantics::StatePtr state = BaseSemantics::State::instance(registers, memory);
							return RiscOperatorsPtr(new RiscOperators(state,map,solver));
						}
						/** Instantiates a new RiscOperators object with specified prototypical value. An SMT solver may be specified as the second
						 * argument for convenience. See set_solver() for details. */

						static RiscOperatorsPtr instance(const BaseSemantics::SValuePtr &protoval,MemoryMap &map,SMTSolver *solver=NULL) {
							return RiscOperatorsPtr(new RiscOperators(protoval,map,solver));
						}
						/** Instantiates a new RiscOperators with specified state. An SMT solver may be specified as the second argument for
						 * convenience. See set_solver() for details. */
						static RiscOperatorsPtr instance(const BaseSemantics::StatePtr &state,MemoryMap &map,SMTSolver *solver=NULL) {
							return RiscOperatorsPtr(new RiscOperators(state,map,solver));
						}


						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Virtual constructors
					public:
						virtual BaseSemantics::RiscOperatorsPtr create(const BaseSemantics::SValuePtr &protoval,MemoryMap &map,SMTSolver *solver=NULL) const ROSE_OVERRIDE {
							return instance(protoval,map,solver);
						}
						virtual BaseSemantics::RiscOperatorsPtr create(const BaseSemantics::StatePtr &state,MemoryMap &map,SMTSolver *solver=NULL) const ROSE_OVERRIDE {
							return instance(state,map,solver);
						}

						// Dynamic pointer casts
					public:
						/** Run-time promotion of a base RiscOperators pointer to interval operators. This is a checked conversion--it
						 * will fail if @p from does not point to a IntervalSemantics::RiscOperators object. */
						static RiscOperatorsPtr promote(const BaseSemantics::RiscOperatorsPtr &x) {
							RiscOperatorsPtr retval = boost::dynamic_pointer_cast<RiscOperators>(x);
							ASSERT_not_null(retval);
							return retval;
						}

						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// Inherited methods for constructing values.
					public:
						virtual BaseSemantics::SValuePtr boolean_(bool b) ROSE_OVERRIDE {
							SValuePtr retval = SValue::promote(SymbolicSemantics::RiscOperators::boolean_(b));
							if (compute_useDefChain )
								retval->modified_by(get_insn());
							return retval;
						}
						virtual BaseSemantics::SValuePtr number_(size_t nbits, uint64_t value) ROSE_OVERRIDE {
							SValuePtr retval = SValue::promote(SymbolicSemantics::RiscOperators::number_(nbits,value));
							if (compute_useDefChain )
								retval->modified_by(get_insn());
							return retval;
						}

						////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
						// New methods for constructing values, so we don't have to write so many SValue::promote calls in the RiscOperators
						// implementations.
					protected:
						SValuePtr svalue_expr(const TreeNodePtr &expr,const InsnSet &defs=InsnSet(),const InsnSet &modfs=InsnSet()) ROSE_OVERRIDE {
							SValuePtr retval = SValue::promote(SymbolicSemantics::RiscOperators::svalue_expr(expr,defs));
							retval->set_modifying_instructions(modfs);
							return retval;
						}
						SValuePtr svalue_undefined(size_t nbits) ROSE_OVERRIDE {
							return SValue::promote(SymbolicSemantics::RiscOperators::svalue_undefined(nbits));
						}
						SValuePtr svalue_number(size_t nbits, uint64_t value) ROSE_OVERRIDE {
							return SValue::promote(number_(nbits, value));
						}
						SValuePtr svalue_boolean(bool b) ROSE_OVERRIDE {
							return SValue::promote(boolean_(b));
						}

						// Methods first introduced at this level of the class hierarchy.
					public:

						virtual void setVerbose(bool b=true){ verbose_=b; }

						// Various method to set,unset,clear the compute_useDefChain flag to activate the
						// building of the def-use chain in RISC operator

						virtual void set_compute_useDefChain(bool b=true){ compute_useDefChain=b; }

						virtual void clear_compute_useDefChain(){ set_compute_useDefChain(false); }

						// Get the value of compute_useDefChain flag
						virtual bool get_compute_useDefChain(){ return compute_useDefChain; }

						virtual void set_compute_latestWriter(bool b=true){ compute_latestWriter=b; }

						virtual void clear_compute_latestWriter(){ set_compute_latestWriter(false); }

						virtual bool get_compute_latestWriter(){ return compute_latestWriter; }

						/* Reset all sets */
						virtual void reset(){
							readList_.clear();
							writeList_.clear();
						}

						// Returns the <V,A> set represeting the Value read from the A register
						virtual AbstractAccessSet& getRegsAndMemRead(){ return readList_; }

						// adds <V,A> to readList_ representing the V Value read from the Memory address A, given A
						virtual void addRegsAndMemRead(AbstractAccessPtr &to_add){ readList_.push_back(to_add); }

						// adds <V,A> to readList_ representing the V Value read from the register A, building a from
						// the constructor of AbstractAccess with given registerDescriptor
						virtual void addRegsAndMemRead(const BaseSemantics::SValuePtr &value,const RegisterDescriptor &reg){
							AbstractAccessPtr to_add = AbstractAccess::instance(value,reg);
							addRegsAndMemRead(to_add);
						}

						// adds <V,A> to readList_ representing the V Value read from the memory address A, building a from
						// the constructor of AbstractAccess with given SValue address
						virtual void addRegsAndMemRead(const BaseSemantics::SValuePtr &value,const BaseSemantics::SValuePtr &addr){
							AbstractAccessPtr to_add = AbstractAccess::instance(value,addr);
							addRegsAndMemRead(to_add);
						}

						// returns list of all <V,A> representing all the writes done to state
						virtual AbstractAccessSet& getRegsAndMemWritten(){ return writeList_; }

						// adds <V,A> to writeList_ representing the V Value written to the A(AbstractAccess), given A
						virtual void addRegsAndMemWritten(AbstractAccessPtr &to_add){ writeList_.push_back(to_add); }

						// adds <V,A> to writeList_ representing the V Value written to the address A, building a from
						// the constructor of AbstractAccess with given SValue of address 
						virtual void addRegsAndMemWritten(const BaseSemantics::SValuePtr &value,const BaseSemantics::SValuePtr &addr){
							AbstractAccessPtr to_add = AbstractAccess::instance(value,addr);
							addRegsAndMemWritten(to_add);
						}

						// adds <V,A> to writeList_ representing the V Value written to the registerDescriptor A, building a from
						// the constructor of AbstractAccess with given RegisterDescriptor
						virtual void addRegsAndMemWritten(const BaseSemantics::SValuePtr &value,const RegisterDescriptor &reg){
							AbstractAccessPtr to_add = AbstractAccess::instance(value,reg);
							addRegsAndMemWritten(to_add);
						}

						// adds curn_insn() as the modifier of the SValue value.
						virtual void addModifiers(SValuePtr &value);

						/* Checks for instruction which doesn't really reads the register or memory location.
						 * The problem is that there's the "literal" semantics of an instruction, and then there's effective semantics.  
						 * When you want to test for things like pass-by-register parameters, you don't really want to include the NOPs that aren't 
						 * really dependent on the value of the register. There's a number of "identity" operations that appear to 
						 * read the register, but don't really.
						 *
						 *	For example :-
						 *				xor reg,reg
						 *				sub reg, reg
						 *				mov reg, reg
						 *				and reg, 0xFFFFFFFF
						 *				or reg, 0x00000000
						 * All of these instruction appears to be dependent on the value of reg but they are not "literally" dependent on the
						 * value of the reg. As, the storing value to reg, doesn't really depends on the value of reg. Its constant for any reg value
						 */
						virtual bool checkIdentityInstr(SgAsmInstruction *instr,const RegisterDescriptor &reg);

					public:
						/* Over-rided because extract is used by Basesemantics::readRegister to extract the value of register.
						 *  and to get the correct & complete modifying instructions of the returning SValue, we need to extract
						 *  those properly.
						 */
						virtual BaseSemantics::SValuePtr extract(const BaseSemantics::SValuePtr &a_,
								size_t begin_bit, size_t end_bit) ROSE_OVERRIDE;

						/* Over-rided because concat is used by Basesemantics::readRegister to concat the two value 
						 *  and to get the correct & complete modifying instructions of the returning SValue, we need to combine
						 *  those properly.
						 */
						virtual BaseSemantics::SValuePtr concat(const BaseSemantics::SValuePtr &a_,
								const BaseSemantics::SValuePtr &b_) ROSE_OVERRIDE;

						/* Over-rided to catch and store all the memory and register - read and write.
						 *  Depenind on the value of the flag compute_useDefChain, the <V,A> pair will be stored.
						 */
						virtual BaseSemantics::SValuePtr readRegister(const RegisterDescriptor &reg) ROSE_OVERRIDE;
						virtual void writeRegister(const RegisterDescriptor &reg, const BaseSemantics::SValuePtr &a_) ROSE_OVERRIDE;
						virtual BaseSemantics::SValuePtr readMemory(const RegisterDescriptor &segreg,
								const BaseSemantics::SValuePtr &address,
								const BaseSemantics::SValuePtr &dflt,
								const BaseSemantics::SValuePtr &condition) ROSE_OVERRIDE;

						virtual void writeMemory(const RegisterDescriptor &segreg,
								const BaseSemantics::SValuePtr &address,
								const BaseSemantics::SValuePtr &value,
								const BaseSemantics::SValuePtr &condition) ROSE_OVERRIDE;

						//  Function called whenever an intrrupt instruction is executed
						virtual void interrupt( int majr,int minr ) ROSE_OVERRIDE{
							if(verbose_)
								mlog[INFO]<<"Interrupt handler called"<<std::endl;
						};
				};

				} // namespace
			} // namespace
		} // namespace
	} // namespace

#endif
