#ifndef THIS_CALL_ANALYSIS_H
#define THIS_CALL_ANALYSIS_H


#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif

#include "sage3basic.h"
#include <iostream>
#include <InterDataFlow.h>
#include <Partitioner2/Partitioner.h>
#include <sawyer/GraphTraversal.h>
#include <sawyer/SharedPointer.h>
#include <boost/optional.hpp>
#include <SymbolicSemantics2.h>
#include "Diagnostics.h"
#include "DataFlowSemantics2.h"
#include <BinaryDataFlow.h>
#include <Partitioner2/BasicBlock.h>
#include <Partitioner2/ControlFlowGraph.h>
#include <Partitioner2/Function.h>
#include <sawyer/Graph.h>
#include <sawyer/DistinctList.h>
#include <vector>
#include <typeinfo>
#include <BaseSemantics2.h>
#include <DispatcherX86.h>
#include <SymbolicSemantics2.h>

using namespace rose::BinaryAnalysis;
using namespace rose::Diagnostics;

namespace P2 = Partitioner2;
namespace IS2 = InstructionSemantics2;
namespace ID = P2::InterDataFlow;

namespace rose {
	namespace BinaryAnalysis {
		namespace Partitioner2 {
			namespace CallSemantics {


				/* Class to Identify function with _thiscall calling convention
				 *Steps Mentioned here are not precise enough to distinguish between _thiscall 
				 and some instances of __fastcall ( A more Complex Algorithm would need to verify that EDX is not
				 being used to pass parameters)
				 *However , this is a cheap way to eliminate many functions that can't be a part of the further analysis
				 thereby improving the overall efficiency of the approach
				 */
				using namespace Sawyer::Container::Algorithm;

				class classDetails: public Sawyer::SharedObject {
					public:
						typedef Sawyer::SharedPointer<classDetails> Ptr;
					public:
						std::set<P2::Function::Ptr> classMethods;
						std::set<rose_addr_t> vtablePtrs;
						rose_addr_t id;
						std::set<Ptr> sureParentClasses;
						std::set<Ptr> mayBeParentClasses;
						std::set<P2::Function::Ptr> sureConstructor;
						std::set<P2::Function::Ptr> maybeConstructor;
						std::set<rose_addr_t> calledVirtualFunctions;
						std::set<rose_addr_t> foundVirtualFunctions;
						std::set<rose_addr_t> instances;
						std::set<BaseSemantics::SValuePtr> thisptrs;
						typedef std::pair<rose_addr_t,rose_addr_t> Member;
						std::set< Member > dataMembers;

					public:
						classDetails(rose_addr_t id_):id(id_){}

						virtual void print(std::ostream &out);
				};

				class thisCallFunctions{
					public:
						const P2::Partitioner &partitioner;
						ID::Engine::ReachingMap &useChain,&defChain;
						ID::Engine::DependingMap &depOnChain,&depOfChain;
						BaseSemantics::DispatcherPtr cpu_;
						ID::RiscOperatorsPtr ops;
						typedef std::pair<P2::Function::Ptr,SgAsmInstruction*> funcToInstPair;
						typedef std::vector<funcToInstPair>funcToInstSet;
						typedef std::pair<rose_addr_t,rose_addr_t> Member;
						typedef std::pair<P2::Function::Ptr,BaseSemantics::SValuePtr> functionThisPtr;
						typedef std::vector<functionThisPtr> functionThisPtrSet;
						funcToInstSet thisCallsFunctions;
						ID::DfCfgBuilder::funcToInst &functionToInstruction;
						Sawyer::Container::Map<P2::Function::Ptr,classDetails::Ptr> classMap;
						Sawyer::Container::Map<P2::Function::Ptr,std::set<P2::Function::Ptr>* > methodToClassConst;
						std::set<P2::Function::Ptr> sureConstructors;
						std::set<P2::Function::Ptr> mayBeConstructors;
						const RegisterDictionary *regdict;
						rose_addr_t totalClasses;
						BaseSemantics::SValuePtr &startHeap;
						RegisterDescriptor &STACK_SEGMENT;

					public:
						thisCallFunctions(const P2::Partitioner &partitioner_,ID::Engine::ReachingMap &useChain_,ID::Engine::ReachingMap &defChain_,
								ID::Engine::DependingMap &depOnChain_,ID::Engine::DependingMap &depOfChain_,BaseSemantics::DispatcherPtr &cpu,
								ID::DfCfgBuilder::funcToInst &functoinst_ ,BaseSemantics::SValuePtr &startHeap_,RegisterDescriptor &STACK_SEGMENT_):
							partitioner(partitioner_),useChain(useChain_),defChain(defChain_),depOnChain(depOnChain_),depOfChain(depOfChain_),
							cpu_(cpu),totalClasses(0),functionToInstruction(functoinst_),startHeap(startHeap_),STACK_SEGMENT(STACK_SEGMENT_){
								ops = ID::RiscOperators::promote(cpu_->get_operators());
								regdict = cpu_->get_register_dictionary();
							}

					public:
						virtual bool checkForEqual(const BaseSemantics::SValuePtr &a,const BaseSemantics::SValuePtr &b);
						// get a set of all instruction from A function::Ptr
						virtual std::set<SgAsmInstruction*,compare>& getInstructions(const P2::Function::Ptr &function);

						// get a set of all instruction from an instruction inside a function
						virtual std::set<SgAsmInstruction*,compare>& getInstructions(const SgAsmInstruction *instruction);

						virtual std::set<SgAsmInstruction*,compare>& getInstructions(rose_addr_t startVa);

						// get the function address from the instruction
						virtual Function::Ptr getFunction(rose_addr_t insn );

						// get the function address from the instruction
						virtual Function::Ptr getFunction(const SgAsmInstruction* insn );

						// Function to find the Functions following __thicall calling convention
						bool analyzeFunction(const P2::Function::Ptr &function);

						// Detect all different calling conventions
						virtual void detectCallingConvention();

						virtual void lookupMayBeConstructors();

						virtual bool checkReturnOfFunction(P2::Function::Ptr &function,std::set<rose_addr_t>& thisptrs);

						virtual void lookupVirtualFunctionsInVtable(const P2::Function::Ptr &constructor ,rose_addr_t vtptr);

						virtual void lookForVirtualFunctionCalls(const P2::Function::Ptr &constructor ,const SgAsmInstruction* insn);

						virtual void findVirtualTable(const P2::Function::Ptr &constructor ,const BaseSemantics::SValuePtr &thisptr);

						virtual void lookupFunctionDataMembers(Function::Ptr &function,SgAsmInstruction* start,BaseSemantics::SValuePtr &thisptr,
								rose_addr_t maxClassSize);

						virtual bool confirmConstructor(P2::Function::Ptr &constructor,BaseSemantics::SValuePtr &thisptr);

						// Returns thisPtr(Symbolic value returned by new) if it is used in the function
						virtual Sawyer::Optional<BaseSemantics::SValuePtr> findReturnValueOfNewConstructor(const SgAsmInstruction *newCaller,
							std::set<rose_addr_t> &NewAddresses,P2::Function::Ptr &constructor,bool &sureFlag);

						virtual Sawyer::Optional<BaseSemantics::SValuePtr> findReturnValueOfLeaConstructor(const SgAsmInstruction *leaInst,
							P2::Function::Ptr &constructor,bool &sureFlag);

						virtual void lookForAllObjectMethods(const SgAsmInstruction *newCaller,const P2::Function::Ptr &constructor,BaseSemantics::SValuePtr &thisPtr,bool &sureFlag);

						// Returns pointer/address to the object methods : set of functions sharing a common thisPtr
						virtual void findObjectMethodsFromNew(const SgAsmInstruction *newCaller,std::set<rose_addr_t> &NewAddresses);

						virtual void findObjectMethodsFromLea(const SgAsmInstruction* leaInst);

						// Returns MemberMap : mapping from function to pairs <offset,size> describing data members
						virtual void findDataMembers(rose_addr_t maxClassSize);

						virtual void lookForThisPtr(rose_addr_t target,functionThisPtrSet &passed);

						virtual void buildMayBeClass(SgAsmInstruction* newCaller,const P2::Function::Ptr &constructor,BaseSemantics::SValuePtr &thisptr);

						// Returns Parents: set of parent/inherited constructors called by Func
						virtual void lookForInheritance(const P2::Function::Ptr &constructor);
				};

			}
		}
	}
}

#endif
