///
///     Written By: Shubham Bansal (illusionist.neo@gmail.com)
///     Copyright(c) Shubham Bansal (iN3O)
///     Blog :- http://in3o.me
///

#include "sage3basic.h"
#include "sageInterfaceAsm.h"
#include <iostream>
#include <rose_strtoull.h>
#include <ClassSemantics.h>
#include <Engine.h>
#include <Partitioner2/Partitioner.h>
#include <Sawyer/GraphTraversal.h>
#include <Sawyer/ProgressBar.h>
#include <boost/optional.hpp>
#include <SymbolicSemantics2.h>
#include "Diagnostics.h"
#include "DataFlowSemantics2.h"
#include <BinaryDataFlow.h>
#include <AstSimpleProcessing.h>
#include <Partitioner2/BasicBlock.h>
#include <Partitioner2/ControlFlowGraph.h>
#include <Partitioner2/ModulesPe.h>
#include <Partitioner2/Modules.h>
#include <Partitioner2/Function.h>
#include <Sawyer/Graph.h>
#include <Sawyer/DistinctList.h>
#include <vector>
#include <typeinfo>
#include <BaseSemantics2.h>
#include <DispatcherX86.h>
#include <stdio.h>
#include <InsnSemanticsExpr.h>
#include <Partitioner2/Config.h>

/* Namespaces */
using namespace Sawyer::Container;
using namespace Sawyer::Container::Algorithm;
using namespace rose::BinaryAnalysis;
using namespace rose::Diagnostics;

namespace P2 = Partitioner2;
namespace IS2 = InstructionSemantics2;


/* Exclusive namepace ClassSemantics for Inter-Procedural DataFlow Analysis */
namespace rose {
	namespace BinaryAnalysis {
		namespace Partitioner2 {
			namespace ClassSemantics {

				//////////////////////////////////////////////////////////////////////////////////////////////////
				/////////////////////// 				FunctionSummary						//////////////////////
				//////////////////////////////////////////////////////////////////////////////////////////////////

				// checks if the function do return or not - 
				// Currently only checking if the register EAX was written during the function or not but its not a sufficient to just check for it.
				// [TO DO] : Check how many times register EAX was read without getting written to in the calling function
				// then it checks for if the return EAX SValue is equal to ECX value of the input state, so that we can check if the function returns
				//  thisPtr in EAX or not for further analysis
				bool 
					FunctionSummary::calculate_return(const RegisterDescriptor &REG_EAX,const RegisterDescriptor &REG_ECX,SMTSolver *solver){
						ASSERT_not_null(inputState_);
						ASSERT_not_null(outputState_);
						outputEAX_ = outputState_->readRegister(REG_EAX);
						SValuePtr eax_value = SValue::promote(outputEAX_);
						if(!eax_value->get_modifying_instructions().empty()){
							returns = true;
							BaseSemantics::SValuePtr inputECX = inputState_->readRegister(REG_ECX);
							returnsECX_ = checkSValueEqual(inputECX,outputEAX_,solver);
						}
						return returnsECX_;
					}

				// Calculates the Stack Delta of the function by calculating the difference between output value of ESP and input value of ESP
				// suppose the output value of ESP is var1 + XX and the input value of ESP is var1. then the stack delta would be. XX - 4
				// Subtraction is done because the return address is also poped of the stack at the end of the function and we don't want to 
				// consider the differnece in stack pointer because of that to be a part of stack delta
				int32_t
					FunctionSummary::calculate_StackDelta(const RegisterDescriptor &REG_ESP,const BaseSemantics::RiscOperatorsPtr &ops,
							SMTSolver *solver){
						ASSERT_not_null(inputState_);
						ASSERT_not_null(outputState_);
						SValuePtr outputESP = SValue::promote(outputState_->readRegister(REG_ESP));
						SValuePtr inputESP = SValue::promote(inputESP_);
						int32_t offset;
						if(outputESP->getOffset(inputESP,offset,solver) && offset>=4){
							BaseSemantics::SValuePtr delta = ops->number_(32,offset-4);
							set_StackDelta(delta);
							return offset-4;
						}else{
							BaseSemantics::SValuePtr delta = ops->number_(32,0);
							set_StackDelta(delta);
							return 0;
						}
					}

				// Calculates all stack variables
				void
					FunctionSummary::checkStackArg(const BaseSemantics::RiscOperatorsPtr &ops){
						ASSERT_not_null(inputESP_);
						SMTSolver *solver = ops->get_solver(); // might be null
						// What is the word size for this architecture ? We'll assume the word size is the same as the width of the stack pointer,
						// whose value we have in inputESP_.
						ASSERT_require2(inputESP_->get_width() % 8 == 0, "stack pointer width is not an integral number of bytes");
						int32_t wordNBytes = inputESP_->get_width() / 8;
						ASSERT_require2(wordNBytes>0, "overflow");
						// Find groups of consecutive addresses that were written to by the same instruction. This is how we coalesce adjacent
						// bytes into larger variables.
						typedef Sawyer::Container::Interval<int32_t> OffsetInterval;
						typedef Sawyer::Container::IntervalMap<OffsetInterval /*stack_offset*/, rose_addr_t /*modifier_addr*/> StackModifiers;
						StackModifiers stackModifiers;
						// output memory state
						MemoryStatePtr memState = MemoryState::promote(outputState_->semanticState()->get_memory_state());
						if(memState->getAllCells().size()>=STACK_PARAM_THRESHOLD){
							// starting offset of function stack argument
							rose_addr_t delta_num = 4;

							// checking for each offset till ARBITRARY_PARAM_LIMIT
							while(delta_num<=ARBITRARY_PARAM_LIMIT){
								BaseSemantics::SValuePtr new_esp = ops->add(inputESP_,ops->number_(inputESP_->get_width(),delta_num));
								bool shortCircuited = false;
								MemoryState::CellList foundCells = memState->scan(new_esp, 8, ops.get(), ops.get(), shortCircuited);
								if(!foundCells.empty()){
									SValuePtr cellValue = SValue::promote(foundCells.back()->get_value());
									ASSERT_require2(0 == cellValue->get_width() % 8, "memory must be byte addressable");
									size_t nBytes = cellValue->get_width() / 8;
									ASSERT_require(nBytes > 0);
									if(!cellValue->get_modifying_instructions().empty()){
										SgAsmInstruction* latestModifier = *(cellValue->get_modifying_instructions().rbegin());
										ASSERT_not_null(latestModifier);
										stackModifiers.insert(OffsetInterval::baseSize(delta_num, nBytes),latestModifier->get_address());
									}
								}
								delta_num++;
							}
						}else{
							/*Above Stack Argument check handles only stack arguments whose offset is <= ARBITRARY_PARAM_LIMIT
							 *  To work with more precise and unlimited length argument, use the following algorithm.
							 *  Only problem with this will be, its comparitively slow.
							 **/
							SValuePtr inputESP = SValue::promote(inputESP_);
							BOOST_FOREACH (const BaseSemantics::MemoryCellPtr &cell, memState->get_cells()){
								SValuePtr addr = SValue::promote(cell->get_address());
								SValuePtr cellValue = SValue::promote(cell->get_value());
								ASSERT_require2(0 == cellValue->get_width() % 8, "memory must be byte addressable");
								size_t nBytes = cellValue->get_width() / 8;
								ASSERT_require(nBytes > 0);
								int32_t stackOffset = 0;
								if (!cellValue->get_modifying_instructions().empty() && addr->getOffset(inputESP,stackOffset,solver)){
									SgAsmInstruction* latestModifier = *(cellValue->get_modifying_instructions().rbegin());
									stackModifiers.insert(OffsetInterval::baseSize(stackOffset, nBytes),latestModifier->get_address());
								}
							}
						}

						// Organize the intervals into a list of stack variables
						BOOST_FOREACH (const OffsetInterval &interval, stackModifiers.intervals()) {
							int32_t offset = interval.least();
							int32_t nRemaining = interval.size();
							ASSERT_require2(nRemaining>0, "overflow");
							while (nRemaining > 0) {
								int32_t nBytes = nRemaining;
								if (offset < 0 && offset + nBytes > 0) {
									// Never create a variable that spans memory below and above (or equal to) the initial stack pointer. The
									// initial stack pointer is generally the boundary between local variables and function arguments (we're
									// considering the call-return address to be an argument on machines that pass it on the stack).
									nBytes = -offset;
								}
								nBytes = std::min(nBytes, wordNBytes);
								ASSERT_require(nBytes>0 && nBytes<=nRemaining);
								if(offset>=4 && nBytes!=0)
									stackArgOffset.push_back(StackVariable(offset-4, nBytes));
								offset += nBytes;
								nRemaining -= nBytes;
							}
						}
					}

				// Deduces the calling convention according to the following rules
				//	Rule 1. only ECX is the register arguments, stack delta is >= 0(callee cleane), then its thiscall__ calling convention
				// 	Rule 4. only ECX and EDX are register arguments,stackdelta is >=0 (caller cleane), then its fastcall calling convention
				//	Rule 5. no register argument, stackdelta >=0 (callee cleane), then its the cdecl calling convention
				// 	Rule 6. by default calling convention is left empty
				bool 
					FunctionSummary::deduceCallingConvention(RegisterDescriptor &REG_ECX,RegisterDescriptor &REG_EDX){
						BaseSemantics::SValuePtr delta;
						if(callingConv_.empty() && get_StackDelta().getOptional().assignTo(delta) && delta->is_number()){
							int32_t stackDelta = delta->get_number();
							bool foundECX = false,foundEDX = false;
							if(registerArgs_.find(REG_ECX)!=registerArgs_.end()) foundECX=true;
							if(registerArgs_.find(REG_EDX)!=registerArgs_.end()) foundEDX=true;
							if(registerArgs_.size()==1 && stackDelta>=0 && foundECX){
								callingConv_ = "thiscall";  // callee cleanee because we are working on windows // for gcc stackdelta==0
								thisptr = inputState_->readRegister(REG_ECX);
							}else if(registerArgs_.size()==2 && stackDelta>=0 && foundECX && foundEDX){
								callingConv_ = "fastcall"; // eax,edx // caller cleane
							}else if(registerArgs_.size()==0 && stackDelta==0 ){
								callingConv_ = "cdecl"; // caller cleane
							}else if(registerArgs_.size()==0 && stackDelta!=0){
								callingConv_ = "stdcall"; // callee cleane
							}else{  // default convention
								callingConv_ = "";
								return false;
							}
							return true;
						}
					}

				BaseSemantics::SValuePtr 
					FunctionSummary::getInputRegisterValue(const RegisterDescriptor &reg){
						return inputState_->readRegister(reg);
					}

				BaseSemantics::SValuePtr 
					FunctionSummary::getOutputArgValue(const BaseSemantics::RiscOperatorsPtr &ops,int32_t offset,
							size_t size,RegisterDescriptor &segreg){
						BaseSemantics::SValuePtr stackArgaddr = ops->add(inputESP_,ops->number_(32,offset+4));
						return outputState_->readMemory(segreg,stackArgaddr,size);
					}

				void
					FunctionSummary::addThisPtr(rose_addr_t ptrhash,const BaseSemantics::SValuePtr& to_add){
						usedThisPtr.insertMaybe(ptrhash,to_add);
					}

				////////////////////////////////////////////////////////////////////////////////////////////////
				/////////////////////				ValueAbstractList						////////////////////
				////////////////////////////////////////////////////////////////////////////////////////////////
				void 
					ValueAbstractList::insert(AbstractAccessPtr &aloc,SMTSolver *solver){
						BOOST_FOREACH(AbstractAccessPtr &current,aAcesList_){
							if(current->checkEqual(aloc,solver))
								return;
						}
						aAcesList_.push_back(aloc);
					}

				void
					ValueAbstractList::print(std::ostream &out,const RegisterDictionary *regdict){
						BOOST_FOREACH(AbstractAccessPtr &current,aAcesList_){
							out<<"\t[";current->print(out,regdict);out<<"]"<<std::endl;
						}
					}

				////////////////////////////////////////////////////////////////////////////////////////////////
				/////////////////////				ValAbstInstList						////////////////////
				////////////////////////////////////////////////////////////////////////////////////////////////

				void
					ValAbstInstList::insert(AbstractAccessPtr &aloc,SgAsmInstruction *insn,SMTSolver *solver){
						BOOST_FOREACH(AbstAcesInstPair &current,aAcesInstList_){
							if(current.first->checkEqual(aloc,solver) && current.second==insn)
								return;
						}
						aAcesInstList_.push_back(AbstAcesInstPair(aloc,insn));
					}

				void
					ValAbstInstList::print(std::ostream &out,const RegisterDictionary *regdict){
						BOOST_FOREACH(AbstAcesInstPair &current,aAcesInstList_){
							out<<"\t[";current.first->print(out,regdict);
							out<<","<<StringUtility::intToHex(current.second->get_address())<<"]"<<std::endl;
						}
					}


				//////////////////////////////////////////////////////////////////////////////////////////////////
				/////////////////////// 						ENGINE						//////////////////////
				//////////////////////////////////////////////////////////////////////////////////////////////////

				// Initial State - initialised new each time a function is started processing
				State::Ptr 
					Engine::initialState() const{
						BaseSemantics::RiscOperatorsPtr ops = cpu_->get_operators();
						State::Ptr state = State::instance(ops);
						RegisterStatePtr regState = RegisterState::promote(state->semanticState()->get_register_state());
						// Any register for which we need its initial state must be initialized rather than just sprining into existence.
						// We need to initialise each large register(32 bits size here)
						regState->initialize_large();
						return state;
					}

				// resets some variable before processing a function
				void
					Engine::functionReset(rose_addr_t startId,const Function::Ptr &function){
						ASSERT_this();
						workList_.clear();
						limits[startId]++;
						workList_.pushBack(startId);
						FunctionSummaryPtr funcSum = FunctionSummary::instance(function);
						incomingState_[startId] = initialState();
						funcSum->set_inputState(incomingState_[startId],REG_ESP);
						functionSummaries.insert(function,funcSum);
						nIterations_ = 0;
					}

				// resets few variables before building any chain
				void
					Engine::reset(){
						ASSERT_this();
						outgoingState_.clear();
						outgoingState_.resize(cfg_.nVertices());
						incomingState_.clear();
						incomingState_.resize(cfg_.nVertices());
						limits.clear();
						limits.resize(cfg_.nVertices());
					}

				// get Vertes ID of the function in function call graph
				rose_addr_t
					Engine::getFunctionVertexId(const Function::Ptr &function){
						return partitioner_.instructionVertex(function->address())->id();
					}

				// Prints the Complete def-use chain if asked to print
				void 
					Engine::print(std::ostream &out){
						AsmUnparser unparser;
						BOOST_FOREACH(SgAsmInstruction* insn,useChain.keys()){
							out<<"Reaching definitions for Instruction at :"<<
								StringUtility::intToHex(insn->get_address())<<std::endl;
							unparser.unparse_insn(true,out,insn);
							out<<"\t-->USE("<<StringUtility::numberToString(useChain[insn]->size())<<")"<<std::endl;
							useChain[insn]->print(out,regdict);
							out<<"\t-->DEF("<<StringUtility::numberToString(defChain[insn]->size())<<")"<<std::endl;
							defChain[insn]->print(out,regdict);
							out<<"\t-->DEPON("<<StringUtility::numberToString(depOnChain[insn]->size())<<")"<<std::endl;
							depOnChain[insn]->print(out,regdict);
							out<<"\t-->DEPOF("<<StringUtility::numberToString(depOfChain[insn]->size())<<")"<<std::endl;
							depOfChain[insn]->print(out,regdict);
						}
					}

				// Merges the One state with other state. Merging includes the merging of both MemoryState and RegisterState
				void
					Engine::mergeStates(const ControlFlowGraph::ConstVertexIterator &vertex,const State::Ptr &state){
						rose_addr_t cfgVertexId = vertex->id();
						rose_addr_t falseVertexId=-1;

						// this checks if there is an je instructio at the end of the basic block so that we can ignore the false side of the jump
						// [FUTURE WORK] : This is not an correct implementation but its part of future development
						if(vertex->value().type()==V_BASIC_BLOCK && !vertex->value().bblock()->instructions().empty()){
							SgAsmInstruction *instr = vertex->value().bblock()->instructions().back();
							SgAsmX86Instruction *last = isSgAsmX86Instruction(instr);
							if(last->get_kind()==x86_je && vertex->nOutEdges()==2){
								rose_addr_t target=0;
								last->getBranchTarget(&target);
								if(target){
									falseVertexId = partitioner_.instructionVertex(target)->id();
								}
							}
						}
						BOOST_FOREACH (const ControlFlowGraph::Edge &edge, vertex->outEdges()) {
							size_t nextVertexId = edge.target()->id();
							if(edge.value().type()==E_FUNCTION_CALL || 						// We don't want to go outside of this function
									falseVertexId==nextVertexId || 								// we don't want to follow falseVertexId
									limits[nextVertexId]>=settings_.maxIterationsPerVertex )	// we don't want to follow the vertex whose limit is reached
								continue;
							State::Ptr targetState = incomingState_[nextVertexId];

							// Target Vertex has no state till now
							if (targetState==NULL) {
								if(settings_.verbose){
									mlog[INFO]<<"Merged : "<<StringUtility::numberToString(nextVertexId)<< " with "<<
										StringUtility::numberToString(cfgVertexId)<<std::endl;
								}
								incomingState_[nextVertexId] = state->clone(); // copy the state
								limits[nextVertexId]++;
								workList_.pushBack(nextVertexId);
							} else if (targetState->merge(state)) {		// target state is merged with already existing state
								if(settings_.verbose){
									mlog[INFO]<<"Merged : "<<StringUtility::numberToString(nextVertexId)<< " with "<<
										StringUtility::numberToString(cfgVertexId)<<std::endl;
								}
								limits[nextVertexId]++;
								workList_.pushBack(nextVertexId);
							} else {
								if(settings_.verbose){
									mlog[INFO]<<"No Change in States after Merging : "<<nextVertexId << " with "<<cfgVertexId<<std::endl;
								}
							}
						}
					}

				// returns the instructions of the basic Block
				const std::vector<SgAsmInstruction*>&
					Engine::getInstructions(BasicBlock::Ptr &bblock){
						return bblock->instructions();
					}

				// returns the list of all modifiers of the SValue
				const InsnSet&
					Engine::getModiferList(const SValuePtr &symval){
						return symval->get_modifying_instructions();
					}

				// returns the registerdescriptor or memroyAddress from the AbstractAccess object
				SValuePtr
					Engine::getRegOrMemValue(const AbstractAccessPtr &aloc){
						return SValue::promote(aloc->getValue());
					}

				// insitialised def-use chain - like size and initial vertex id for processing
				void
					Engine::initialiseChain(SgAsmInstruction *instr){
						useChain.insertMaybe(instr,ValueAbstractList::instance());
						defChain.insertMaybe(instr,ValueAbstractList::instance());
						depOnChain.insertMaybe(instr,ValAbstInstList::instance());
						depOfChain.insertMaybe(instr,ValAbstInstList::instance());
					}

				// checks if certain function is library call thunk or not which are not recognised as thunk by the Rose
				// Currently it checks for only empty basicBlocks/function
				bool
					Engine::checkForLibraryThunk(const Function::Ptr &function){
						if (function->basicBlockAddresses().size()!=1)
							return false; // thunks have only one basic block...
						BasicBlock::Ptr bblock = partitioner_.basicBlockExists(function->address());
						if(bblock->isEmpty())
							return true;
						return false;
					}

				// builds the connection of call instruction with its register arguments - indirectly it creates dependencies
				void
					Engine::buildConnection(const RegisterDescriptor &reg,RiscOperatorsPtr &ops,SgAsmInstruction *instr){
						BaseSemantics::SValuePtr Value = ops->readRegister(reg);
						AbstractAccessPtr aloc = AbstractAccess::instance(Value,reg);
						SValuePtr val = SValue::promote(Value);
						useChain[instr]->insert(aloc);
						BOOST_FOREACH(SgAsmInstruction* definer, getModiferList(val)){
							depOnChain[instr]->insert(aloc,definer);
							depOfChain[definer]->insert(aloc,instr);
						}
					}

				// returns target function of the call instruction if there exists a definied function
				// It uses Control Flow Graph to find the target function which is returned in targetFunction argument if found
				Function::Ptr
					Engine::GetTargetFunction(SgAsmInstruction *instr){
						Function::Ptr retval;
						ControlFlowGraph::ConstVertexIterator vertex = partitioner_.instructionVertex(instr->get_address());
						if(vertex->nOutEdges()==2 && vertex->value().bblock()->instructions().back()==instr ){
							BOOST_FOREACH (const ControlFlowGraph::Edge &edge, vertex->outEdges()) {
								if(edge.value().type() == E_FUNCTION_CALL && edge.target()->value().type() == V_BASIC_BLOCK){
									retval = edge.target()->value().function();
									return retval;
								}
							}
						}
						if(settings_.verbose)
							mlog[WARN]<<"Target function Not found - "<<StringUtility::intToHex(instr->get_address())<<std::endl;
						return retval;
					}

				// special function written to handle function call handling connecting of two functions
				// by call instructions like, connecting function argument, stack pointer value , 
				// function return value and building many dependencies
				void
					Engine::handleCallInstruction(SgAsmInstruction* instr,RiscOperatorsPtr &ops){
						Function::Ptr function = GetTargetFunction(instr);
						if(function && functionSummaries.exists(function)){
							FunctionSummaryPtr &funcSum = functionSummaries[function];
							const State::Ptr& inputState = funcSum->get_inputState();
							const State::Ptr& outputState = funcSum->get_outputState();
							BaseSemantics::SValuePtr old_esp = ops->readRegister(REG_ESP);

							// adding the value of ESP corresponding to the call instruction if not already added
							if(!callESP.exists(instr))
								callESP.insert(instr,old_esp);

							// Handle connection of stack arguments and register arguments
							BOOST_FOREACH(const StackVariable& variable,funcSum->getstackArgOffset()){
								BaseSemantics::SValuePtr stackArgaddr = ops->add(old_esp,ops->number_(old_esp->get_width(),variable.offset));
								SValuePtr stackArg = SValue::promote(ops->readMemory(REG_SS,stackArgaddr,ops->undefined_(variable.nBytes*8),ops->boolean_(true)));
								AbstractAccessPtr aloc = AbstractAccess::instance(stackArg,stackArgaddr);
								useChain[instr]->insert(aloc);
								BOOST_FOREACH(SgAsmInstruction* definer, getModiferList(stackArg)){
									depOnChain[instr]->insert(aloc,definer);
									depOfChain[definer]->insert(aloc,instr);
								}
							}

							// Builds connection for the register arguments
							BOOST_FOREACH(const RegisterDescriptor &reg,funcSum->getRegisterArg())
								buildConnection(reg,ops,instr);
							ops->reset();
							BaseSemantics::SValuePtr delta;
							// sets the appropriate value of ESP according to the delta of the called function
							if(function->stackDelta().getOptional().assignTo(delta)){
								BaseSemantics::SValuePtr new_esp = ops->add(old_esp,delta);
								ops->writeRegister(REG_ESP,new_esp);
							}

							// sets the return value according to the whether the value returned is equal to the value passed in ECX
							if(funcSum->getReturns()){
								BaseSemantics::SValuePtr new_eax = ops->undefined_(32);
								if(funcSum->getReturnECX())
									new_eax = ops->readRegister(REG_ECX);
								SValue::promote(new_eax)->modified_by(instr);
								ops->writeRegister(REG_EAX,new_eax);
							}
						}else {

							// Set the undefined return value if the function summary is yet to be calculated
							BaseSemantics::SValuePtr new_eax = ops->undefined_(32);
							SValue::promote(new_eax)->modified_by(instr);
							ops->writeRegister(REG_EAX,new_eax);
						}
						// Changes the value of EIP to the next follwoing/fallthrough instruction
						BaseSemantics::SValuePtr old_eip = ops->readRegister(REG_EIP);
						BaseSemantics::SValuePtr new_eip = ops->add(old_eip,ops->number_(old_eip->get_width(),instr->get_size()) );
						SValue::promote(new_eip)->modified_by(instr);
						ops->writeRegister(REG_EIP,new_eip);
					}

				// process each instruction - have special case handling for call instruction because we need to
				// connect two functions in that like , connecting function argument, stack pointer value , 
				// function return value and building many dependencies
				void
					Engine::symbolicExec(SgAsmInstruction* instr,RiscOperatorsPtr &ops){
						ops->reset();
						SgAsmX86Instruction *last = isSgAsmX86Instruction(instr);
						if(last){
							// special handling of call instruction
							if(x86_call==last->get_kind() || x86_farcall==last->get_kind() ){
								handleCallInstruction(instr,ops);
							}else{
								try{
									cpu_->processInstruction(instr);
								}catch (const Disassembler::Exception &e) {
									if(settings_.verbose)
										mlog[WARN]<<"Dissassbling error : Skipping instruction : "<<StringUtility::intToHex(instr->get_address())
											<<std::endl;
								}catch(const BaseSemantics::Exception &e){
									if(settings_.verbose)
										mlog[WARN]<<"Skipping instruction : "<<StringUtility::intToHex(instr->get_address())
											<<std::endl;
								}catch(const SMTSolver::Exception &e){
									if(settings_.verbose)
										mlog[WARN]<<"Caught an SMTSolver Exception at "<<StringUtility::intToHex(instr->get_address())
											<<std::endl;
								}catch(...){
									if(settings_.verbose)
										mlog[WARN]<<"Got an unknown Exception"<<std::endl;
								}
							}
						}
					}

				// handles function which are supposed to be library function calls
				// Rose doesn't have any function to identify if a call is a library function call or not
				// It handles cases like :-
				//			Case 1.		addr1:  jmp addr2
				//						addr2:	jmp ds:[addr3]		// addr2 lies in IAT
				//			Case 2.		addr1:	jmp ds:[addr2]		// addr2 lies in IAT
				//			Case 3.		addr1:	call ds:[addr2]		// addr2 lies in IAT
				void
					Engine::handleLibraryfunction(const Function::Ptr &function){
						FunctionSummaryPtr funcSum = FunctionSummary::instance(function);
						const Configuration &config = partitioner_.configuration();
						ASSERT_not_null(ops_);
						BaseSemantics::SValuePtr retval;
						// stack delta is loaded from the JSON files especially built for this analysis containing the stack delta 
						// and the related information about the function
						if (Sawyer::Optional<int64_t> delta = config.functionStackDelta(function)) {
							if(settings_.verbose)
								mlog[INFO]<<"Library function Stack delta for : "<<function->name()<<" delta :"<<(int)(*delta)<<std::endl;
							retval = ops_->number_(32, (int32_t)(*delta));
						}else{
							if(settings_.verbose)
								mlog[WARN]<<"Library function Stack delta for : "<<function->name()<<" - Not Found"<<std::endl;
							retval = ops_->number_(32, 0);
						}
						// setting the stack delta
						funcSum->set_StackDelta(retval);

						// currently we are just assuming that each library function returns but its not correct
						// [FUTURE WORK] : will be corrected in future version
						funcSum->setReturns();

						// currently we are just assuming that each library function follows the stdcall calling convention
						// which is true for most of the Win32 API but still it will result in many error
						// [FUTURE WORK] : will be corrected in future version
						std::string temp = "stdcall";
						funcSum->setCallingConv(temp);

						// setting the library function flag for this function summary
						funcSum->setLibraryFunction();

						// mapping function to its function summary
						functionSummaries.insert(function,funcSum);
					}

				// Merges all the possible States of return vertex of a function
				State::Ptr
					Engine::buildOutputState(const std::vector<rose_addr_t> &returnVertices){
						State::Ptr retval;
						BOOST_FOREACH(rose_addr_t vertexId,returnVertices){
							if(retval==NULL)
								retval = outgoingState_[vertexId]->clone();
							else
								retval->merge(outgoingState_[vertexId]);
						}
						return retval;
					}

				// Process a Basic Block - uses symbolicExec to handle each instruction
				State::Ptr
					Engine::processBasicBlock(ControlFlowGraph::ConstVertexIterator &vertex,const State::Ptr &incomingState,
							FunctionSummaryPtr &funcSummary){
						// Initial Setup and initializations
						RiscOperatorsPtr ops = RiscOperators::promote(cpu_->get_operators());
						State::Ptr retval = incomingState->clone();
						ops->set_state(retval->semanticState());
						// Start Processing BasicBlock
						if(vertex->value().type()==V_BASIC_BLOCK){
							BasicBlock::Ptr bblock = vertex->value().bblock();
							//Processing for each instruction of the function
							BOOST_FOREACH(SgAsmInstruction* instr,getInstructions(bblock)){
								// initialising chain for each instruction before processing
								initialiseChain(instr);

								// Checking if this instruction does have some effects on the semantic state or not
								/*  An instruction has an effect if it does anything other than setting the instruction pointer to a concrete
								 *  value. Instructions that have no effect are called "no-ops".  The x86 NOP instruction is an example of a no-op, but there
								 *  are others also.
								 *
								 *  The following information about x86 no-ops is largely from [Cory Cohen at CMU/SEI]. In the discussion that follows, we are
								 *  careful to distinguish between NOP (the mneumonic for instructions 90, and 0f1f) and "no-op" (any instruction whose only
								 *  effect is to advance the instruction pointer).
								 *
								 *  Opcode bytes         Intel assembly syntax
								 *  -------------------- ---------------------- 
								 *  90                   nop
								 *
								 *  89c0                 mov eax,eax            Intel's old recommended two-byte no-op was to
								 *  89c9                 mov ecx,ecx            move a register to itself...  The second byte of these are mod/rm
								 *  89d2                 mov edx,edx            bytes, and can generally be substituded wherever you see 0xc0 in
								 *  89db                 mov ebx,ebx            subsequent examples.
								 *  89e4                 mov esp,esp
								 *  89ed                 mov ebp,ebp
								 *  89f6                 mov esi,esi
								 *  89ff                 mov edi,edi
								 *
								 *  88c0                 mov al,al              The above are also available in 8-bit form with a leading byte of 0x88
								 *  6689c0               mov ax,ax              and with an operand size prefix (0x66).
								 *
								 *  66666689c0           mov ax,ax              The prefixes can be repeated. One source seemed to imply that up to
								 *                                              three are reliably supported by the actual Intel processors. ROSE supports
								 *                                              any number up to the maximum instruction size (varies by mode).
								 *
								 *  6688c0               mov al,al              The operand size prefix can even be nonsensical.
								 *
								 *  8ac0                 mov al,al              These are also presumabely no-ops.  As with most instructions, these will
								 *  8bc0                 mov eax,eax            accept operand size prefixes as well.
								 *
								 *  f090                 lock nop               Most of these instructions will accept a lock prefix as well, which does
								 *  f0f090               lock nop               not materially affect the result. As before, they can occur repeatedly, and
								 *  f066f090             lock nop               even in wacky combinations.
								 *  f066f06666f0f066f090 lock nop
								 *  
								 *  f290                 repne nop              Cory Cohen strongly suspects that the other instruction prefixes are
								 *  f390                 rep nop                ignored as well, although to be complete, we might want to conduct a few
								 *  2690                 es nop                 tests into the behavior of common processors.
								 *  2e90                 cs nop
								 *  3690                 ss nop
								 *  3e90                 ds nop
								 *  6490                 fs nop
								 *  6590                 gs nop
								 *  6790                 nop
								 *  
								 *  8d00                 lea eax,[eax]          Intel's old recommendation for larger no-ops was to use the LEA
								 *  8d09                 lea ecx,[ecx]          instruction in various dereferencing modes.
								 *  8d12                 lea edx,[edx]
								 *  8d1b                 lea ebx,[ebx]
								 *  8d36                 lea esi,[esi]
								 *  8d3f                 lea edi,[edi]
								 *  
								 *  8d4000               lea eax,[eax+0x0]
								 *  8d4900               lea ecx,[ecx+0x0]
								 *  8d5200               lea edx,[edx+0x0]
								 *  8d5b00               lea ebx,[ebx+0x0]
								 *  8d7600               lea esi,[esi+0x0]
								 *  8d7f00               lea edi,[edi+0x0]
								 *  
								 *  8d8000000000         lea eax,[eax+0x0]      This last block is really the [reg*0x1+0x0] dereferencing mode.
								 *  8d8900000000         lea ecx,[ecx+0x0]
								 *  8d9200000000         lea edx,[edx+0x0]
								 *  8d9b00000000         lea ebx,[ebx+0x0]
								 *  8db600000000         lea esi,[esi+0x0]
								 *  8dbf00000000         lea edi,[edi+0x0]
								 *
								 *  8d0420               lea eax,[eax]          Then there's funky equivalents involving SIB bytes.
								 *  8d0c21               lea ecx,[ecx]
								*  8d1422               lea edx,[edx]
									*  8d1c23               lea ebx,[ebx]
									*  8d2424               lea esp,[esp]
									*  8d3426               lea esi,[esi]
									*  8d3c27               lea edi,[edi]
									*  
									*  8d442000             lea eax,[eax+0x0]
									*  8d4c2100             lea ecx,[ecx+0x0]
									*  8d542200             lea edx,[edx+0x0]
									*  8d5c2300             lea ebx,[ebx+0x0]
									*  8d642400             lea esp,[esp+0x0]
									*  8d742600             lea esi,[esi+0x0]
									*  8d7c2700             lea edi,[edi+0x0]
									*  
									*  8d842000000000       lea eax,[eax+0x0]
									*  8d8c2100000000       lea ecx,[ecx+0x0]
									*  8d942200000000       lea edx,[edx+0x0]
									*  8d9c2300000000       lea ebx,[ebx+0x0]
									*  8da42400000000       lea esp,[esp+0x0]
									*  8db42600000000       lea esi,[esi+0x0]
									*  8dbc2700000000       lea edi,[edi+0x0]
									*  
									*  8d2c2d00000000       lea ebp,[ebp+0x0]      The EBP variants don't exactly follow the pattern above.
									*  8d6c2500             lea ebp,[ebp+0x0]
									*  8dac2500000000       lea ebp,[ebp+0x0]
									*
									*  0f1f00               nop [eax]              P4+ adds the 0f1f instruction. Each of these can be prefixed with the
									*  0f1f4000             nop [eax+0x0]          0x66 operand size prefix. In fact, Intel recommends doing this now for the
									*  0f1f440000           nop [eax+0x0]          optimally efficient 6- and 9-byte sequences.
									*  0f1f8000000000       nop [eax+0x0]
									*  0f1f840000000000     nop [eax+0x0]
									*
									*  0f0dxx               nop [xxx]              The latest version of the manual implies that this sequence is also
									*                                              reserved for NOP, although I can find almost no references to it except									*                                              in the latest instruction manual on page A-13 of volume 2B. It's also mentioned
									*                                              on x86asm.net. [CORY 2010-04]
									*                                              
									*  d9d0                 fnop                   These aren't really no-ops on the chip, but are no-ops from the program's
									*  9b                   wait                   perspective. Most of these instructions are related to improving cache
									*  0f08                 invd                   efficiency and performance, but otherwise do not affect the program
									*  0f09                 wbinvd                 behavior.
									*  0f01c9               mwait
									*  0f0138               invlpg [eax]
									*  0f01bf00000000       invlpg [edi+0x0]       and more...
									*  0f18 /0              prefetchnta [xxx]
									*  0f18 /1              prefetch0 [xxx]
									*  0f18 /2              prefetch1 [xxx]
									*  0f18 /3              prefetch2 [xxx]
									*  0fae /5              lfence [xxx]
									*  0fae /6              mfence [xxx]
									*  0fae /7              sfence [xxx]
									*
									*  0f18xx through 0f1exx                       This opcode rante is officially undefined but is probably reserved for
									*                                              no-ops as well.  Any instructions encountered in this range are probably
									*                                              consequences of bad code and should be ingored.
									*                                              
									*  JMP, Jcc, PUSH/RET, etc.                    Branches are considered no-ops if they can be proven to always branch
									*                                              to the fall-through address.
									*/
								if(!instr->hasEffect()) continue;

								if(settings_.verbose)
									mlog[INFO]<<"Processing instruction : "<<StringUtility::intToHex(instr->get_address())<<std::endl;

								// executing the instruction according to its need, for example call instruction required to be processed manually
								symbolicExec(instr,ops);

								// building the dependency for def-use chain
								BOOST_FOREACH(AbstractAccessPtr &aloc,ops->getRegsAndMemRead()){

									// Ignore creating un-necessary dependencies of registers like EIP and ESP
									if(aloc->getAloc()->isRegister() && (aloc->getAloc()->getRegister()==REG_EIP ||
												aloc->getAloc()->getRegister()==REG_ESP) )
										continue;
									SValuePtr symval = getRegOrMemValue(aloc);
									useChain[instr]->insert(aloc,solver);
									BOOST_FOREACH(SgAsmInstruction* definer, getModiferList(symval)){
										depOnChain[instr]->insert(aloc,definer,solver);
										depOfChain[definer]->insert(aloc,instr,solver);
									}
								}
								BOOST_FOREACH(AbstractAccessPtr &aloc,ops->getRegsAndMemWritten()){
									// Ignore creating un-necessary dependencies of registers like EIP and ESP
									if (aloc->getAloc()->isRegister() && (aloc->getAloc()->getRegister()==REG_EIP ||
												aloc->getAloc()->getRegister()==REG_ESP) )
										continue;
									defChain[instr]->insert(aloc,solver);
								}
							}
						}
						return retval;
					}

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
				bool
					Engine::checkIdentityInstr(SgAsmInstruction *instr){
						SgAsmX86Instruction *current = isSgAsmX86Instruction(instr);
						if(current->get_kind()==x86_xor){ //checking for "XOR" instruction
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmDirectRegisterExpression *Reg2 = isSgAsmDirectRegisterExpression(Args[1]);
								if(Reg1 && Reg2 && Reg1->get_descriptor()==Reg2->get_descriptor())
									return true;
							}
						}else if(current->get_kind()==x86_sub){ //checking for "SUB" instruction
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmDirectRegisterExpression *Reg2 = isSgAsmDirectRegisterExpression(Args[1]);
								if(Reg1 && Reg2 && Reg1->get_descriptor()==Reg2->get_descriptor())
									return true;
							}
						}else if(current->get_kind()==x86_mov){ //checking for "MOV" instruction
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmDirectRegisterExpression *Reg2 = isSgAsmDirectRegisterExpression(Args[1]);
								if(Reg1 && Reg2 && Reg1->get_descriptor()==Reg2->get_descriptor())
									return true;
							}
						}else if(current->get_kind()==x86_and){ //checking for "AND" instruction
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmIntegerValueExpression *argValue = isSgAsmIntegerValueExpression(Args[1]);
								if(Reg1 && argValue && argValue->get_absoluteValue()==0xffffffff)
									return true;
							}
						}else if(current->get_kind()==x86_or){ //checking for "OR" instruction
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmIntegerValueExpression *argValue = isSgAsmIntegerValueExpression(Args[1]);
								if(Reg1 && argValue && argValue->get_absoluteValue()==0x0)
									return true;
							}
						}
						return false;
					}

				/* seraches for the restore instruction which pops the saved-register accross the function.
				 *  For Example :-
				 *				push ecx
				 *				mov ecx, 37
				 *				move eax, ecx
				 *				pop ecx
				 * Here we need to exclude ecx as the pass-by-register parameter because its actually not getting used as a pass-by-register
				 * parameter, its value is saved and poped from the stack without getting used in the middle of the function.
				 * This function helps in excluding these registers.
				 */
				bool
					Engine::checkForSavedRegister(const RegisterDescriptor& reg,SgAsmInstruction* saveInstr,const BaseSemantics::SValuePtr &readVal,
							const BaseSemantics::SValuePtr &writeAddr,FunctionSummaryPtr &funcSummary){
						bool flag=false;
						BOOST_FOREACH(ValAbstInstList::AbstAcesInstPair &currentdepOf,depOfChain[saveInstr]->getAbstAcesInst()){
							SgAsmInstruction *restoreInstr = currentdepOf.second;
							AbstractAccessPtr& aloc = currentdepOf.first;
							const BaseSemantics::SValuePtr& defval = aloc->getValue();
							// checks if the restore instruction is using the same value which was written at save instruction or not
							if(aloc->getAloc()->isAddress() && checkSValueEqual(defval,readVal,solver) ){
								BaseSemantics::SValuePtr readAddr = aloc->getAloc()->getAddress();
								// checks if the value using here at restore instruction is read from the same address where save instruction
								// store it previosuly
								if(checkSValueEqual(readAddr,writeAddr,solver)){
									BOOST_FOREACH(AbstractAccessPtr &currentDef,defChain[restoreInstr]->getaAcesList()){
										const BaseSemantics::SValuePtr& val = currentDef->getValue();
										// checking if the same value is getting written only and only to the same register at restore register or not
										if(checkSValueEqual(val,defval,solver)) {
											if(currentDef->getAloc()->isRegister()){
												const RegisterDescriptor &depreg = currentDef->getAloc()->getRegister();
												if(depreg==reg){
													flag = true;
													// check if the there is any future use of the register it poped in previously
													if(!depOfChain[restoreInstr]->getAbstAcesInst().empty())
														return false; // using it in the future so not a saved register
												}
												else
													return false; // using it for other than restoring to the same register so not a saved reg
											}
											else 
												return false; // using it for other than restoring to the same register so not a saved reg
										}
									}
								}
							}
						}
						return flag;
					}

				/* seraches for the restore instruction which pops the saved-register accross the function.
				 *  For Example :-
				 *				push ecx
				 *				mov ecx, 37
				 *				move eax, ecx
				 *				pop ecx
				 * Here we need to exclude ecx as the pass-by-register parameter because its actually not getting used as a pass-by-register
				 * parameter, its value is saved and poped from the stack without getting used in the middle of the function.
				 * This function helps in excluding these registers.
				 */
				void
					Engine::calculateRegArg(const Function::Ptr &function,FunctionSummaryPtr &funcSummary){

						// set of 32 bit width registers which are already used
						std::set<RegisterDescriptor> usedRegisters;
						// initial value of ESP for this function
						SValuePtr initESP = SValue::promote(funcSummary->getInputESP());

						// iterating over each instruction
						BOOST_FOREACH(rose_addr_t bblockAddr,function->basicBlockAddresses()){
							BasicBlock::Ptr bblock = partitioner_.basicBlockExists(bblockAddr);
							BOOST_FOREACH(SgAsmInstruction *saveInstr,bblock->instructions()){
								// Instructions that are NOPs/np-ops do not cause parameters (e.g. mov edi, edi)
								if(!useChain.exists(saveInstr) || !saveInstr->hasEffect() || checkIdentityInstr(saveInstr)) continue;
								// finding the registers which are used for the first time in the function without previosuly getting written over
								BOOST_FOREACH(AbstractAccessPtr &currentUse,useChain[saveInstr]->getaAcesList()){
									const BaseSemantics::SValuePtr& readVal = currentUse->getValue();
									if(currentUse->getAloc()->isRegister() && getModiferList(SValue::promote(readVal)).empty()){  
										// Only continue for instructions that read the uninitialized register value
										const RegisterDescriptor &reg = currentUse->getAloc()->getRegister();
										// Check for 32 bit width and If the register being saved on the stack is ESP, don't count that one (e.g. call)
										if(reg.get_nbits()==32 && usedRegisters.find(reg)==usedRegisters.end()){
											// updates the current using register to the list of register already used
											usedRegisters.insert(reg);
											BOOST_FOREACH(AbstractAccessPtr &currentdef,defChain[saveInstr]->getaAcesList()){
												const BaseSemantics::SValuePtr& writeVal = currentdef->getValue();
												if(currentdef->getAloc()->isAddress() && checkSValueEqual(writeVal,readVal,solver)){
													SValuePtr writeAddr = SValue::promote(currentdef->getAloc()->getAddress());
													int32_t offset=0;
													// checking if the value is written to the stack address or not
													if(writeAddr->getOffset(initESP,offset,solver) && offset<0 && 
															// finding for any restore instruction if possible to find, if not then it is the pass-by-register parameter
															!checkForSavedRegister(reg,saveInstr,readVal,writeAddr,funcSummary)){
														if(settings_.verbose)
															mlog[INFO]<<StringUtility::intToHex(saveInstr->get_address())<<" -- "<<regdict->lookup(reg)<<std::endl;
														funcSummary->addRegisterArg(reg);
													}
												}
											}
										}// Check for non 32 bit width and gets the large register from the register dictionary of the same type and does the same as above
										else if(reg.get_nbits()!=32){
											RegisterDescriptor largeReg = regdict->findLargestRegister(reg.get_major(),reg.get_minor());
											if(usedRegisters.find(largeReg)==usedRegisters.end()){
												// updates the current using register to the list of register already used
												usedRegisters.insert(largeReg);
												BOOST_FOREACH(AbstractAccessPtr &currentdef,defChain[saveInstr]->getaAcesList()){
													const BaseSemantics::SValuePtr& writeVal = currentdef->getValue();
													if(currentdef->getAloc()->isAddress() && checkSValueEqual(writeVal,readVal,solver)){
														SValuePtr writeAddr = SValue::promote(currentdef->getAloc()->getAddress());
														int32_t offset=0;
														// checking if the value is written to the stack address or not
														if(writeAddr->getOffset(initESP,offset,solver) && offset<0 && 
																// finding for any restore instruction if possible to find, if not then it is the pass-by-register parameter
																!checkForSavedRegister(reg,saveInstr,readVal,writeAddr,funcSummary)){
															if(settings_.verbose)
																mlog[INFO]<<StringUtility::intToHex(saveInstr->get_address())<<" -- "<<regdict->lookup(largeReg)<<std::endl;
															funcSummary->addRegisterArg(largeReg);
														}
													}
												}
											}
										}

										// end
									}
								}
							}
						}
					}

				// Handles function which are identified as normal function(which are not library function)
				void
					Engine::handleNormalfunction(const Function::Ptr &function){
						// starting function id.
						rose_addr_t startId = getFunctionVertexId(function);
						std::vector<rose_addr_t> returnVertices;
						// restting some variables before any analysis for this function is started
						functionReset(startId,function);
						FunctionSummaryPtr &funcSummary = functionSummaries[function];
						// Loop to run until the state is getting changed Run until we got a Fixed Point
						while (!workList_.isEmpty()){
							if (++nIterations_ > settings_.maxIterations) {
								throw std::runtime_error("dataflow max iterations reached"
										" (max=" + StringUtility::numberToString(settings_.maxIterations) + ")");
							}
							size_t cfgVertexId = workList_.popFront();
							ControlFlowGraph::ConstVertexIterator vertex = cfg_.findVertex(cfgVertexId);
							if(vertex->value().type()==V_BASIC_BLOCK){
								State::Ptr state = incomingState_[cfgVertexId];
								if(settings_.verbose)
									mlog[INFO]<<"Analysing : "<<StringUtility::intToHex(vertex->value().bblock()->address())<<std::endl;
								// Process a function vertex and get the output state
								state = outgoingState_[cfgVertexId] = processBasicBlock(vertex, state,funcSummary);
								if(partitioner_.basicBlockIsFunctionReturn(vertex->value().bblock()))
									returnVertices.push_back(cfgVertexId);
								else
									mergeStates(vertex,state);
							}
						}

						// Merging all the Output states of the return vertices found in this function
						State::Ptr outputState = buildOutputState(returnVertices);
						if(outputState){
							funcSummary->set_outputState(outputState);
							calculateRegArg(function,funcSummary);
							funcSummary->checkStackArg(ops_);
							int32_t delta = funcSummary->calculate_StackDelta(REG_ESP,ops_,solver);
							if(settings_.verbose)
								mlog[INFO]<<"Calculated stack delta "<<delta<<" for function : "<<StringUtility::intToHex(function->address())<<std::endl;
							if(funcSummary->deduceCallingConvention(REG_ECX,REG_EDX)){
								if(settings_.verbose)
									mlog[INFO]<<"Deduced calling convention "<<funcSummary->getCallingConv()<<" for function : "<<
										StringUtility::intToHex(function->address())<<std::endl;
							}else {
									mlog[WARN]<<"Not able to deduce Calling convention for function : "<<StringUtility::intToHex(function->address())<<std::endl;
							}
							if(funcSummary->calculate_return(REG_EAX,REG_ECX,solver) && settings_.verbose){
								mlog[INFO]<<"Function at : "<<StringUtility::intToHex(function->address())<<" returns input ECX value"<<std::endl;
							}
						}else{
							mlog[WARN]<<"Not able to analyse : " <<StringUtility::intToHex(function->address())<<std::endl;
						}
					}

				// Process a function - uses processBasicBlock to process each basic block
				void
					Engine::processFunction(const Function::Ptr &function){
						if(partitioner_.functionIsThunk(function) || checkForLibraryThunk(function)){ // checks for library thunk call
							handleLibraryfunction(function);
						}else{
							// handles the analysis of normal function call
							handleNormalfunction(function);
						}
					}

				// Main function which starts building def-use chain for each function
				void 
					Engine::buildDependencies(){
						reset();
						size_t nFunctions = cg_.nVertices();
						std::vector<bool> visited(nFunctions, false);
						Sawyer::ProgressBar<size_t> progress(nFunctions, mlog[MARCH], "stack-delta analysis");
						for (size_t cgVertexId=0; cgVertexId<nFunctions; ++cgVertexId, ++progress) {
							if(!visited[cgVertexId]){
								// Depth First Traveling the Function call graph to build dependencies in Bottom-Up manner
								for (cgTraversal t(cg_, cg_.findVertex(cgVertexId), ENTER_VERTEX|LEAVE_VERTEX); t; ++t) {
									if (t.event() == ENTER_VERTEX) {
										if (visited[t.vertex()->id()])
											t.skipChildren();
									} else if(!visited[t.vertex()->id()]){
										ASSERT_require(t.event() == LEAVE_VERTEX);
										Function::Ptr function = t.vertex()->value();
										if(settings_.verbose)
											mlog[INFO]<<"Starting building Dependencies for Function : "<<
												StringUtility::intToHex(function->address())<<std::endl;
										processFunction(function);
										visited[t.vertex()->id()] = true;
									}
								}
							}
						}
					}


			}	//namespace
		}	// namespcae
	}	//namespace
}	//namespace
