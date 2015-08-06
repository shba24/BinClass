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

#ifndef ROSE_Partitioner2_ENGINE_H
#define ROSE_Partitioner2_ENGINE_H


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
#define STACK_PARAM_THRESHOLD  200

struct Settings{
	std::string isaName;                                // instruction set architecture name
	AddressInterval interruptVector;                    // table of interrupt handling functions
	bool allowDiscontiguousBlocks;                      // can basic blocks be discontiguous in memory?
	bool findDeadCode;                                  // do we look for unreachable basic blocks?
	bool useSemantics;                                  // should we use symbolic semantics?
	bool doPostAnalysis;                                // perform post-partitioning analysis phase?
	bool findFunctionPadding;                           // look for pre-entry-point padding?
	bool doListAum;                                     // list the address usage map
	bool doListFunctions;                               // produce a function index
	bool doShowStats;                                   // show some statistics
	bool doShowMap;                                     // show the memory map
	bool verbose;										// Output verbose
	bool intraFunctionCode;                             // suck up unused addresses as intra-function code
	bool intraFunctionData;                             // suck up unused addresses as intra-function data
	bool useSMTSolver;									// Use Satisfiability modulo theory for precise Calculation
	std::vector<std::string> triggers;                  // debugging aids
	bool doOutputDefUse;								// whether to output def-use or not
	bool doOutputObjects;								// whether to output deduced object information or not
	std::string yamlOutputFile;							// name of the yaml output file containing the datastructure extracted
	std::string defUseOutputFile;						// name of the output file containing the def-use built
	std::string gvBaseName;                             // base name for GraphViz files
	std::string configurationName;                      // config file or directory containing such
	bool gvUseFunctionSubgraphs;                        // use subgraphs in GraphViz files?
	bool gvShowInstructions;                            // show disassembled instructions in GraphViz files?
	bool gvShowFunctionReturns;                         // show edges from function return to indeterminate?
	bool gvCallGraph;                                   // produce a function call graph?
	bool gvControlFlowGraph;							// produce Control flow graph?
	rose_addr_t maxIterations;                          // Maximum number of iteration to run dataFlow Analysis to
	rose_addr_t maxIterationsPerVertex;                 // Maximum no. of times each Vertex is analysed - saving from wasting iteration in future
	rose_addr_t maxClassSize;							// Maximum class size
	Settings():
		isaName("i386"),doPostAnalysis(false),doListAum(false),doListFunctions(false),doOutputDefUse(false),
		useSemantics(true),doShowMap(false),maxIterations(10000),doShowStats(false),gvCallGraph(false),defUseOutputFile("output.txt"),
		allowDiscontiguousBlocks(true),maxIterationsPerVertex(1),yamlOutputFile("output.yaml"),findFunctionPadding(true),
		findDeadCode(true),intraFunctionCode(true),intraFunctionData(true),gvUseFunctionSubgraphs(true), gvShowInstructions(true),
		gvShowFunctionReturns(true),gvControlFlowGraph(false),doOutputObjects(true),maxClassSize(0x100),verbose(false),useSMTSolver(false){
			configurationName = boost::filesystem::current_path().string() + std::string("/../data/windowsAPI");
		}
};

namespace rose {
	namespace BinaryAnalysis {
		namespace Partitioner2 {
			namespace ClassSemantics {

				////////////////////////////////////////////////////////////////////////////////////////////////////
				///////////////////////////////////			Function Summary		////////////////////////////////
				////////////////////////////////////////////////////////////////////////////////////////////////////

				typedef boost::shared_ptr<class FunctionSummary> FunctionSummaryPtr;

				class FunctionSummary{
					public:
						typedef Sawyer::Container::Map<rose_addr_t,BaseSemantics::SValuePtr> thisPtrMap;
					protected:
						const Function::Ptr function_;					// function whose function summary is this
						StackVariables stackArgOffset;					// stack arguments offsets
						State::Ptr inputState_,outputState_;			// input and output state
						BaseSemantics::SValuePtr inputESP_,outputEAX_; 	// cached input value of ESP
						std::set<RegisterDescriptor> registerArgs_;		// pass-by-register argument
						std::string callingConv_;						// calling convention followed by the function
						bool returns,returnsECX_;						// to determine if it returns ECX(thisptr) or not
						Sawyer::Cached<BaseSemantics::SValuePtr> thisptr; // will be cached only if the function is following thiscall__
						thisPtrMap usedThisPtr;// all used this-ptr
						bool libraryFunction;							// set true if this is a function summary of library function calls

					public:
						// Real COnstructor
						explicit FunctionSummary(const Function::Ptr &function):returnsECX_(false),function_(function),returns(false),libraryFunction(false){}

					public:
						// Static Constructor
						static FunctionSummaryPtr instance(const Function::Ptr &function){
							return FunctionSummaryPtr(new FunctionSummary(function));
						}

					public:
						// sets the stack delta of the function
						virtual void set_StackDelta(BaseSemantics::SValuePtr &delta){
							function_->stackDelta() = delta;
						}

						// returned the cached stack delta value
						virtual const Sawyer::Cached<BaseSemantics::SValuePtr>& get_StackDelta(){ return function_->stackDelta(); }

						// return the input state of the function
						virtual const State::Ptr& get_inputState(){ return inputState_; }

						// sets the input state of the function
						virtual void set_inputState(State::Ptr& state,RegisterDescriptor &REG_ESP){ 
							inputState_ = state;
							inputESP_ = inputState_->readRegister(REG_ESP);
						}

						// return the output state of the function
						virtual const State::Ptr& get_outputState(){ return outputState_; }

						// sets the output state of the function
						virtual void set_outputState(State::Ptr &state ){ outputState_ = state; }

						// calculates if the return value in EAX is equal to ECX SValue of the input state
						virtual bool calculate_return(const RegisterDescriptor &REG_EAX,const RegisterDescriptor &REG_ECX,SMTSolver *solver=NULL);

						// calculates the number of stack argument
						/** Returns the list of all known stack variables. A stack variable is any memory location whose address is a constant
						 * offset from an initial stack pointer. That is, the address has the form (add SP0 CONSTANT) where SP0 is a variable
						 * supplied as an argument to this function. When CONSTANT is zero the expression is simplified to SP0, so that also is
						 * accepted. Although memory is byte addressable and values are stored as individual bytes in memory, this function
						 * attempts to sew related addresses back together again to produce variables that are multiple bytes. There are many
						 * ways to do this, all of which are heuristic. 
						 * Returns the list of all known function arguments. A function argument is any stack variable whose starting address is
						 * greater than or equal to the specified stack pointer. For the definition of stack variable.
						 */
						virtual void checkStackArg(const BaseSemantics::RiscOperatorsPtr &ops);

						// calculates the stack delta of the function by finding the difference between the ESP value in input state and ESP value of the
						// output state and if that offset value if not a known number than we assume the delta is equal to 0 but it can be improved further
						// by using SMTSolver [[FUTURE WORK]]
						virtual int32_t calculate_StackDelta(const RegisterDescriptor &REG_ESP,const BaseSemantics::RiscOperatorsPtr &ops,SMTSolver *solver);

						// returns if the function returns the value same as input ECX
						virtual bool getReturnECX(){ return returnsECX_; }

						// sets the calling convention of the function
						virtual void setCallingConv(std::string &conv ){ callingConv_ = conv; }

						// return the calling convention of the function
						virtual std::string& getCallingConv(){ return callingConv_; }

						// adds Register as the pass-by-register argument of the function
						virtual void addRegisterArg(const RegisterDescriptor &reg ){ registerArgs_.insert(reg); }

						virtual std::set<RegisterDescriptor>& getRegisterArg(){ return registerArgs_; }

						// deduces the calling convention of the function
						// Currently it checks for 
						//					- thiscall_
						//					- fastcall_1
						//					- fastcall_2
						//					- fastcall_3
						//					- stdcall__
						//					- cdcel
						virtual bool deduceCallingConvention(RegisterDescriptor &REG_ECX,RegisterDescriptor &REG_EDX);

						// returns the cached value of the SValue of the input value of ESP
						virtual const BaseSemantics::SValuePtr& getInputESP(){ return inputESP_; }

						// returns true/false if the function returns or not
						virtual bool getReturns(){ return returns;}

						// sets if the fucntion returns or nots
						virtual void setReturns(bool b=true) { returns=b; }

						// returns the cached thisPtr of function - only set if the function follows thiscall__ calling convention
						virtual const Sawyer::Cached<BaseSemantics::SValuePtr>& get_thisPtr(){ return thisptr; }

						// reads the register value from the input state
						virtual BaseSemantics::SValuePtr getInputRegisterValue(const RegisterDescriptor &reg);

						// reads the stack memory address from the output state - here offset is the offset to positive side of the stack
						// pointer in the output state
						virtual BaseSemantics::SValuePtr getOutputArgValue(const BaseSemantics::RiscOperatorsPtr &ops,int32_t offset,
								size_t size,RegisterDescriptor &segreg);

						// return if the function is an library function or not
						virtual bool isLibraryFunction(){ return libraryFunction; }

						virtual void setLibraryFunction(bool b=true){ libraryFunction = b; }

						// return the list of the stack argument offset
						virtual const StackVariables& getstackArgOffset(){ return stackArgOffset; }

						// returns the return SValue of the function
						virtual const BaseSemantics::SValuePtr& getReturnValue(){ return outputEAX_; }

						/// add all new found this-ptr to the xref function to assemble all this-ptr used in this function
						virtual void addThisPtr(rose_addr_t ptrhash,const BaseSemantics::SValuePtr& to_add);

						virtual thisPtrMap& getUsedThisPtr(){ return usedThisPtr; }
				};

				////////////////////////////////////////////////////////////////////////////////////////////////////
				///////////////////////////////////			ValueAbstractList		////////////////////////////////
				////////////////////////////////////////////////////////////////////////////////////////////////////


				typedef boost::shared_ptr<class ValueAbstractList> ValueAbstractListPtr;

				// Represents the list of <V,A> pair for representing the def-use chain
				class ValueAbstractList{
					protected:
						typedef std::vector<AbstractAccessPtr> AbstractAccessList;
						AbstractAccessList aAcesList_;
					public:
						// Real Constructor
						explicit ValueAbstractList(){}
					public:
						// Static Constructor
						static ValueAbstractListPtr instance(){
							return ValueAbstractListPtr(new ValueAbstractList());
						}

					public:

						virtual void insert(AbstractAccessPtr &aloc,SMTSolver *solver=NULL);

						virtual void print(std::ostream &out,const RegisterDictionary *regdict);

						// returns the abstract access list
						virtual AbstractAccessList& getaAcesList(){ return aAcesList_; }

						virtual rose_addr_t size(){ return aAcesList_.size(); }
				};

				////////////////////////////////////////////////////////////////////////////////////////////////////
				/////////////////////////////////          ValAbstInstList			////////////////////////////////
				////////////////////////////////////////////////////////////////////////////////////////////////////

				typedef boost::shared_ptr<class ValAbstInstList> ValAbstInstListPtr;

				// Represents the list of <V,A,instr> pair for representing the def-use chain dependencies
				class ValAbstInstList{
					public:
						typedef std::pair<AbstractAccessPtr,SgAsmInstruction*> AbstAcesInstPair;
						typedef std::vector<AbstAcesInstPair> AbstAcesInstList ;
					protected:
						AbstAcesInstList aAcesInstList_;

					public:
						// Real Constructor
						explicit ValAbstInstList(){}

					public:
						// Static Constructor
						static ValAbstInstListPtr instance(){
							return ValAbstInstListPtr(new ValAbstInstList());
						}

					public:
						virtual void insert(AbstractAccessPtr &aloc,SgAsmInstruction *insn,SMTSolver *solver=NULL);

						virtual void print(std::ostream &out,const RegisterDictionary *regdict);

						virtual AbstAcesInstList& getAbstAcesInst() { return aAcesInstList_; }

						virtual rose_addr_t size(){ return aAcesInstList_.size(); }

				};

				////////////////////////////////////////////////////////////////////////////////////////////////////
				///////////////////////////////////         Engine					////////////////////////////////
				////////////////////////////////////////////////////////////////////////////////////////////////////

				class Engine{
					public:
						typedef DepthFirstForwardGraphTraversal<const FunctionCallGraph::Graph> cgTraversal;
						typedef FunctionCallGraph::Graph CallGraph;
						typedef Sawyer::Container::Map<SgAsmInstruction* , ValueAbstractListPtr > ReachingMap;
						typedef Sawyer::Container::Map<SgAsmInstruction* , ValAbstInstListPtr > DependingMap;
						typedef std::vector<State::Ptr> VertexStates;
						typedef Sawyer::Container::DistinctList<size_t> WorkList;
						typedef Sawyer::Container::Map<Function::Ptr,FunctionSummaryPtr> summaryMap;	// Mapping of functions with its summaries
						typedef std::vector<rose_addr_t> limitMap;
						typedef Sawyer::Container::Map<SgAsmInstruction*,BaseSemantics::SValuePtr> callToESPMap;

					public:
						const Partitioner2::Partitioner &partitioner_;	// Partitioner
						const BaseSemantics::DispatcherPtr &cpu_;		// Dispatcher for corresponding architechture
						const ControlFlowGraph &cfg_;					// ControlFlowGraph of the main specimens
						const BaseSemantics::RiscOperatorsPtr &ops_;	// Riscoperator
						Settings &settings_;							// all settings
						ReachingMap useChain,defChain;					// def-use chain
						DependingMap depOnChain,depOfChain;				// depOn-depOf chain
						VertexStates incomingState_; 					// incoming data flow state per CFG vertex ID
						VertexStates outgoingState_; 					// outgoing data flow state per CFG vertex ID
						summaryMap functionSummaries;					// Function summary mapped with function Ptr
						WorkList workList_; 							// CFG vertex IDs to be visited, last in first out w/out
						RegisterDescriptor REG_EAX,REG_ESP,REG_EIP,REG_ECX,REG_SS,REG_EDX;	// cached X86 register
						const RegisterDictionary *regdict;				// Register Dictionary
						size_t nIterations_;                            // number of iterations since last reset
						SMTSolver *solver;								// SMTSolver - YicesSolver
						limitMap limits;								// Number of times a Vertex is processed
						callToESPMap callESP;							// Mapping of call instruction with the SValue of ESP at that instruction


					protected:
						const CallGraph &cg_;							// Function call Graph
						const FunctionCallGraph &functionCallGraph_;	// class which have function call graph

					public:
						// Real Constructor
						Engine(const Partitioner2::Partitioner &partitioner,const BaseSemantics::DispatcherPtr &cpu,const FunctionCallGraph &functionCallGraph,
								const BaseSemantics::RiscOperatorsPtr &ops,Settings &settings,SMTSolver *solver_=NULL):partitioner_(partitioner),cpu_(cpu),
						cfg_(partitioner.cfg()),nIterations_(0),functionCallGraph_(functionCallGraph),cg_(functionCallGraph.graph()),ops_(ops),solver(solver_),
						settings_(settings){
							REG_ESP = cpu_->findRegister("esp");
							REG_EAX = cpu_->findRegister("eax");
							REG_EIP = cpu_->findRegister("eip");
							REG_ECX = cpu_->findRegister("ecx");
							REG_SS =cpu_->findRegister("ss");
							REG_EDX = cpu_->findRegister("edx");
							regdict = cpu_->get_register_dictionary();
							BaseSemantics::SValuePtr check = ops_->number_(32,0);
						}

					public:

						// Initial State - initialised new each time a function is started processing
						virtual State::Ptr initialState() const;

						// Returns Maximum number of iterations complete analyis is going to go
						virtual size_t maxIterations() const { return settings_.maxIterations; }

						virtual size_t nIterations() const { return nIterations_; }

						// Prints the Complete def-use chain if asked to print
						virtual void print(std::ostream &out);

						// Main function which starts building def-use chain for each function
						virtual void buildDependencies();

						// handles function which are supposed to be library function calls
						// Rose doesn't have any function to identify if a call is a library function call or not
						// It handles cases like :-
						//			Case 1.		addr1:  jmp addr2
						//						addr2:	jmp ds:[addr3]		// addr2 lies in IAT
						//			Case 2.		addr1:	jmp ds:[addr2]		// addr2 lies in IAT
						//			Case 3.		addr1:	call ds:[addr2]		// addr2 lies in IAT
						virtual void handleLibraryfunction(const Function::Ptr &function);

						// Handles function which are identified as normal function(which are not library function)
						virtual void handleNormalfunction(const Function::Ptr &function);

						// get Vertes ID of the function in function call graph
						virtual rose_addr_t getFunctionVertexId(const Function::Ptr &function);

						// returns the instructions of the basic Block
						virtual const std::vector<SgAsmInstruction*>& getInstructions(BasicBlock::Ptr &bblock);

						// Merges the One state with other state. Merging includes the merging of both MemoryState and RegisterState
						virtual void mergeStates(const ControlFlowGraph::ConstVertexIterator &vertex,const State::Ptr &state);

						// Process a Basic Block - uses symbolicExec to handle each instruction
						virtual State::Ptr processBasicBlock(ControlFlowGraph::ConstVertexIterator &vertex,const State::Ptr &incomingState,FunctionSummaryPtr &funcSummary);

						// Process a function - uses processBasicBlock to process each basic block
						virtual void processFunction(const Function::Ptr &function);

						// returns the list of all modifiers of the SValue
						virtual const InsnSet& getModiferList(const SValuePtr &symval);

						// returns the registerdescriptor or memroyAddress from the AbstractAccess object
						virtual SValuePtr getRegOrMemValue(const AbstractAccessPtr &aloc);

						// insitialised def-use chain - like size and initial vertex id for processing
						virtual void initialiseChain(SgAsmInstruction *instr);

						// process each instruction - have special case handling for call instruction because we need to
						// connect two functions in that like , connecting function argument, stack pointer value , 
						// function return value and building many dependencies
						virtual void symbolicExec(SgAsmInstruction* instr,RiscOperatorsPtr &ops);

						// resets some variable before processing a function
						virtual void functionReset(rose_addr_t startId,const Function::Ptr &function);

						// special function written to handle function call handling connecting of two functions
						// by call instructions like, connecting function argument, stack pointer value , 
						// function return value and building many dependencies
						virtual void handleCallInstruction(SgAsmInstruction* instr,RiscOperatorsPtr &ops);

						// checks if certain function is library call thunk or not
						virtual bool checkForLibraryThunk(const Function::Ptr &function);

						// Combines various output states which are output state of vertex looking like a return vertex
						//			Example :-
						//						Case 1.			pop esi;
						//										pop edi;
						//										pop ebx; 
						//										mov esp,ebp;
						//										pop ebp
						//										retn
						//						Case 2.			pop esi;
						//										pop edi;
						//										pop ebx;
						//										leave
						//										retn
						virtual State::Ptr buildOutputState(const std::vector<rose_addr_t> &returnVertices);

						// resets few variables before building any chain
						virtual void reset();

						/*Very important function in finding all the pass-by register and excluding all the other saved register
						  accross function from them.
						  Algorithm pseduo code:
						  . Instructions that are NOPs do not cause parameters (e.g. mov edi, edi)  [DONE]

						  . Instructions that aren't really dependent on the reg do not cause parameters (e.g. xor reg,reg)[[DONE]]

						  . Only continue for instructions that read the uninitialized register value...[DONE]

						  . Only continue if the register is written to a stack address...[DONE]

						  (in practice this is usually a push but could be a mov as well)[DONE]

						  . If the register being saved on the stack is ESP, don't count that one (e.g. call)[DONE]

						  . This instruction is possibly a "saved register instruction"[DONE] (done in checkForSavedRegister)

						  . From here on the default behavior is to label the register as a parameter.[DONE]

						  . Now we begin looking for the "restored register instruction"[DONE]

						  . For each instruction dependent on the "saved register instruction"[DONE]

						  ... Did it read from the stack address where the register was saved?[DONE]

						  ... If it did not, it's not the "restored register instruction".[DONE]

						  ... Does this instruction write the value back to same register?[DONE]

						  ... If yes, then check if the there is any future use of the register it poped in previously [DONE]( done in checkFutureUse)

						  ... If there is no future use, then it is surely a "restor register instruction" otherwise continue [DONE] (done in checkForSavedRegister )

						  ... If not continue with the next dependent instruction.[DONE]

						  ... Are there any instructions dependent on the restored register instruction?[DONE]

						  ... If not, this is officially a saved & restored register.  All other cases are parameters.[DONE]*/
						virtual void calculateRegArg(const Function::Ptr &function,FunctionSummaryPtr &funcSummary);

						// builds the connection of call instruction with its register arguments
						virtual void buildConnection(const RegisterDescriptor &reg,RiscOperatorsPtr &ops,SgAsmInstruction *instr);

						// checks for identity instruction like , we did in ClassSemantics::Riscoperator class
						virtual bool checkIdentityInstr(SgAsmInstruction *instr);

						// returns target function of the call instruction if there exists a definied function
						// It uses Control Flow Graph to find the target function which is returned in targetFunction argument if found
						virtual Function::Ptr GetTargetFunction(SgAsmInstruction *instr);

						// checks if saveInstr is the "saved register instruction"
						virtual bool checkForSavedRegister(const RegisterDescriptor& reg,SgAsmInstruction* saveInstr,const BaseSemantics::SValuePtr &readVal,
								const BaseSemantics::SValuePtr &writeAddr,FunctionSummaryPtr &funcSummary);
				};

			}	//namespace
		}	//namespace
	}	//namespace
}	//namespace

#endif
