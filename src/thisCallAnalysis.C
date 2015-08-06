#include "sage3basic.h"
#include <iostream>
#include <InterDataFlow.h>
#include <thisCallAnalysis.h>
#include <Partitioner2/Partitioner.h>
#include <sawyer/GraphTraversal.h>
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
#include <Disassembler.h>

using namespace rose; 

using namespace rose::BinaryAnalysis;
using namespace rose::Diagnostics;

namespace P2 = Partitioner2;
namespace IS2 = InstructionSemantics2;
namespace ID = P2::InterDataFlow;

namespace rose {
	namespace BinaryAnalysis {
		namespace Partitioner2 {
			namespace CallSemantics {

				void 
					classDetails::print(std::ostream &out){
						out<<"\n\nInstances started at :"<<std::endl;
						BOOST_FOREACH(const rose_addr_t &instance,instances)
							out<<"\t"<<StringUtility::intToHex(instance)<<std::endl;
						out<<"class_"<<StringUtility::numberToString(id)<<" {"<<std::endl;
						BOOST_FOREACH(rose_addr_t vtablePtr,vtablePtrs){
							out<<"\tVirtual functions from Virtual Functions Table at : "<<StringUtility::intToHex(vtablePtr)<<
								std::endl;
							BOOST_FOREACH(rose_addr_t funcAddr,foundVirtualFunctions){
								out<<"\t\t--"<<StringUtility::intToHex(funcAddr)<<std::endl;
							}
							out<<"\tCalled Virtual Functions : "<<std::endl;
							BOOST_FOREACH(rose_addr_t called, calledVirtualFunctions)
								out<<"\t\t--"<<StringUtility::intToHex(called)<<std::endl;
						}
						BOOST_FOREACH(const P2::Function::Ptr &function,sureConstructor){
							out<<"\tSure Constructor : "<<StringUtility::intToHex(function->address())<<std::endl;
						}
						BOOST_FOREACH(const P2::Function::Ptr &function,maybeConstructor){
							out<<"\tMay Be Constructor : "<<StringUtility::intToHex(function->address())<<std::endl;
						}
						out<<"\tData Members :"<<std::endl;
						BOOST_FOREACH(const Member &data,dataMembers){
							out<<"\t\t"<<"Offset(bits) : "<<StringUtility::numberToString(data.first)<<" Size(bits) :"<<
								StringUtility::numberToString(data.second)<<std::endl;
						}
						out<<"\tClass Methods :"<<std::endl;
						BOOST_FOREACH(const P2::Function::Ptr &methods,classMethods)
							out<<"\t\t--"<<StringUtility::intToHex(methods->address())<<std::endl;
						out<<"\tSure Inherited Classes : ";
						BOOST_FOREACH(const classDetails::Ptr &parent,sureParentClasses)
							out<<" class_"<<StringUtility::numberToString(parent->id);
						out<<std::endl;
						out<<"\tMay Be Inherited Classes : ";
						BOOST_FOREACH(const classDetails::Ptr &parent,mayBeParentClasses)
							out<<" class_"<<StringUtility::numberToString(parent->id);
						out<<std::endl;
						out<<"};"<<std::endl;
					}

				bool
					thisCallFunctions::checkForEqual(const BaseSemantics::SValuePtr &a,const BaseSemantics::SValuePtr &b){
						if(a->get_width()==b->get_width() && a->must_equal(b))
							return true;
						return false;
					}

				std::set<SgAsmInstruction*,compare>& 
					thisCallFunctions::getInstructions(const P2::Function::Ptr &function){
						return functionToInstruction[function->address()];
					}

				std::set<SgAsmInstruction*,compare>& 
					thisCallFunctions::getInstructions(const SgAsmInstruction *instruction){
						P2::BasicBlock::Ptr bblock = partitioner.basicBlockContainingInstruction(instruction->get_address());
						P2::Function::Ptr function = partitioner.basicBlockFunctionOwner(bblock);
						return functionToInstruction[function->address()];
					}

				std::set<SgAsmInstruction*,compare>& 
					thisCallFunctions::getInstructions(rose_addr_t startVa){
						P2::BasicBlock::Ptr bblock = partitioner.basicBlockContainingInstruction(startVa);
						P2::Function::Ptr function = partitioner.basicBlockFunctionOwner(bblock);
						return functionToInstruction[function->address()];
					}

				// get the function address from the instruction
				Function::Ptr
					thisCallFunctions::getFunction(rose_addr_t insn ){
						return partitioner.basicBlockFunctionOwner(partitioner.basicBlockContainingInstruction(insn));
					}

				// get the function address from the instruction
				Function::Ptr
					thisCallFunctions::getFunction(const SgAsmInstruction *insn ){
						return partitioner.basicBlockFunctionOwner(partitioner.basicBlockContainingInstruction(insn->get_address()));
					}

				bool 
					thisCallFunctions::analyzeFunction(const P2::Function::Ptr &function){
						BOOST_FOREACH(SgAsmInstruction *insn,getInstructions(function)){
							BOOST_FOREACH(ID::Engine::DependPair *depPair ,*(depOnChain[insn])){
								Function::Ptr deffunc = getFunction(depPair->second);
								AbstractLocation *aLoc = depPair->first->second;
								if( aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="ecx"){
									if(deffunc!=function){
										thisCallsFunctions.push_back(std::make_pair(function,insn));
										return true;
									}
									else
										return false;
								}
							}
						}
						return false;
					}

				void 
					thisCallFunctions::detectCallingConvention(){
						BOOST_FOREACH(const P2::Function::Ptr &function,partitioner.functions()){
							if(!functionToInstruction.exists(function->address())) continue;
							mlog[INFO]<<"Analyzing function at : "<<StringUtility::intToHex(function->address())<<
								" for calling convention"<<std::endl;
							if(analyzeFunction(function))
								mlog[INFO]<<"Detected thisCall_ calling convention in function at : "<<
									StringUtility::intToHex(function->address())<<std::endl;
						}
					}

				bool 
				thisCallFunctions::checkReturnOfFunction(P2::Function::Ptr &function,std::set<rose_addr_t>& thisptrs){
					bool gotIn=false;
					BOOST_REVERSE_FOREACH(SgAsmInstruction *insn,getInstructions(function)){
						BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*defChain[insn]){
							AbstractLocation *aLoc = vaPair->second;
							if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="eax"){
								gotIn = true;
								BaseSemantics::SValuePtr symval = vaPair->first;
								if(symval->is_number() && thisptrs.find(symval->get_number())!=thisptrs.end()){
									 return true;
								}
							}
						}
						if(gotIn)
							break ;
					}
					return false;
				}

				void
					thisCallFunctions::lookupMayBeConstructors(){
						BOOST_FOREACH(funcToInstPair &function,thisCallsFunctions){
							SgAsmInstruction* firstInsn = function.second;
							std::set<rose_addr_t> thisptrs;
							BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*useChain[firstInsn]){
								AbstractLocation *aLoc = vaPair->second;
								BaseSemantics::SValuePtr symval = vaPair->first;
								if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="ecx" && symval->is_number()){
									thisptrs.insert(symval->get_number());
								}
							}
							if(checkReturnOfFunction(function.first,thisptrs)){
								mlog[INFO]<<"Found a may be Constructor : "<<StringUtility::intToHex(function.first->address())<<
									std::endl;
								mayBeConstructors.insert(function.first);
							}
						}
						return ;
					}

				void
					thisCallFunctions::lookupVirtualFunctionsInVtable(const P2::Function::Ptr &constructor ,rose_addr_t vtptr){
						BaseSemantics::SValuePtr vtableaddr = ops->number_(32,vtptr);
						BaseSemantics::SValuePtr funcPtr = ops->readMemory(STACK_SEGMENT,vtableaddr,ops->undefined_(32),ops->boolean_(true));
						while(funcPtr->is_number() && funcPtr->get_number()!=0){
							mlog[INFO]<<"Found Virtual Function : "<<StringUtility::intToHex(funcPtr->get_number())<<
								" in Virtual Function table "<<std::endl;
							classMap[constructor]->foundVirtualFunctions.insert(funcPtr->get_number());
							vtableaddr = ops->add(vtableaddr,ops->number_(32,4));
							funcPtr = ops->readMemory(STACK_SEGMENT,vtableaddr,ops->undefined_(32),ops->boolean_(true));
						}
					}

				void
					thisCallFunctions::lookForVirtualFunctionCalls(const P2::Function::Ptr &constructor ,const SgAsmInstruction* insn){
						BOOST_FOREACH(SgAsmInstruction *inst,getInstructions(insn)){
							if(inst->get_address()<insn->get_address()) continue;
							SgAsmX86Instruction *last = isSgAsmX86Instruction(inst);
							if(last && x86_call==last->get_kind()){
								BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*useChain[inst]){
									AbstractLocation *aLoc = vaPair->second;
									BaseSemantics::SValuePtr symval = vaPair->first;
									if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="eax" && symval->is_number()){
										mlog[INFO]<<"Found Virtual Function : "<<StringUtility::intToHex(symval->get_number())<<
											" called at : "<<StringUtility::intToHex(inst->get_address())<<std::endl;
										classMap[constructor]->calledVirtualFunctions.insert(symval->get_number());
									}
								}
								return ;
							}
						}
					}

				void
					thisCallFunctions::findVirtualTable(const P2::Function::Ptr &constructor ,const BaseSemantics::SValuePtr &thisptr){
						SgAsmX86Instruction *current;
						BOOST_FOREACH(SgAsmInstruction *insn,getInstructions(constructor)){
							current = isSgAsmX86Instruction(insn);
							if(current && x86_mov==current->get_kind()){
								BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*defChain[insn]){
									AbstractLocation *aLoc = vaPair->second;
									BaseSemantics::SValuePtr symval = vaPair->first;
									if(aLoc->isAddress() && checkForEqual(aLoc->getAddress(),thisptr) && symval->is_number() ){
										mlog[INFO]<<"Analysing Virtual Table Found at : "<<StringUtility::intToHex(symval->get_number())
											<<std::endl;
										lookupVirtualFunctionsInVtable(constructor,symval->get_number());
										classMap[constructor]->vtablePtrs.insert(symval->get_number());
										BOOST_FOREACH(ID::Engine::DependPair *depPair ,*depOfChain[insn])
											lookForVirtualFunctionCalls(constructor,depPair->second);
										return ;
									}
								}
							}
						}
						return ;
					}

				Sawyer::Optional<BaseSemantics::SValuePtr>
					thisCallFunctions::findReturnValueOfNewConstructor(const SgAsmInstruction *newCaller,std::set<rose_addr_t> &NewAddresses,
							P2::Function::Ptr &constructor,bool &sureFlag){
						int found = 0;
						rose_addr_t target;
						BaseSemantics::SValuePtr retval;
						BOOST_FOREACH(SgAsmInstruction *insn,getInstructions(newCaller)){
							if(insn->get_address()<newCaller->get_address()) continue;
							if(found==0){
								if(insn->get_address()!=newCaller->get_address()) 
									return Sawyer::Nothing();
								target = 0;
								SgAsmX86Instruction *last = isSgAsmX86Instruction(insn);
								if(last && (x86_call==last->get_kind() || x86_farcall==last->get_kind()) ){
									last->getBranchTarget(&target);
									if(target && NewAddresses.find(target)!=NewAddresses.end())
										found++;
									else
										return Sawyer::Nothing();
								}else
									return Sawyer::Nothing();
							}
							else if(found==1){
								BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*useChain[insn]){
									AbstractLocation *aLoc = vaPair->second;
									if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="eax"){
										mlog[INFO]<<"Found thisptr corresponding to the Instance : "<<StringUtility::intToHex(newCaller->get_address())
											<<std::endl;
										retval = vaPair->first;
										found++;break;
									}
								}
							}
							else if(found==2){
								target = 0;
								SgAsmX86Instruction *current = isSgAsmX86Instruction(insn);
								if(current && (x86_call==current->get_kind() || x86_farcall==current->get_kind())){
									current->getBranchTarget(&target);
									if(target){
										constructor = partitioner.functionExists(target);
										mlog[INFO]<<"Found constructor : "<<StringUtility::intToHex(target)<<
											"for the instance started at : "<<StringUtility::intToHex(newCaller->get_address())<<std::endl;
										found++;
									}else
										return retval;
								}
							}
							else if(found==3){
								BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*useChain[insn]){
									AbstractLocation *aLoc = vaPair->second;
									BaseSemantics::SValuePtr symval = vaPair->first;
									if( aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="eax"){
										if(checkForEqual(symval,retval)){
											mlog[INFO]<<"[CONFIRMED] Constructor Found at : "<<StringUtility::intToHex(constructor->address())
												<<std::endl;
											sureFlag = true;
											return retval;
										}else{
											mlog[INFO]<<"[NOT CONFIRMED] Constructor Found at : "<<StringUtility::intToHex(constructor->address())
												<<std::endl;
											return retval;
										}
									}
								}
							}
						}
						if(found==2 || found==3)
							return retval;
						return Sawyer::Nothing();
					}

				bool 
					thisCallFunctions::confirmConstructor(P2::Function::Ptr &constructor,BaseSemantics::SValuePtr &thisptr){
						bool gotIn = false;
						BOOST_REVERSE_FOREACH(SgAsmInstruction *insn,getInstructions(constructor)){
							BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*defChain[insn]){
								AbstractLocation *aLoc = vaPair->second;
								if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="eax"){
									gotIn = true;
									BaseSemantics::SValuePtr symval = vaPair->first;
									if(checkForEqual(symval,thisptr))
										return true;
								}
							}
							if(gotIn)
								return false;
						}
						return false;
					}

				Sawyer::Optional<BaseSemantics::SValuePtr>
					thisCallFunctions::findReturnValueOfLeaConstructor(const SgAsmInstruction *leaInst,P2::Function::Ptr &constructor,
							bool &sureFlag){
						bool found = false;
						rose_addr_t target;
						BaseSemantics::SValuePtr retval;
						BOOST_FOREACH(SgAsmInstruction *insn,getInstructions(leaInst)){
							if(insn->get_address()<leaInst->get_address()) continue;
							if(!found){
								if(insn->get_address()!=leaInst->get_address())
									return Sawyer::Nothing();
								BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*defChain[insn]){
									AbstractLocation *aLoc = vaPair->second;
									BaseSemantics::SValuePtr symval = vaPair->first;
									if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="ecx" && symval->is_number()){
										mlog[INFO]<<"Found thisptr corresponding to the Instance : "<<StringUtility::intToHex(leaInst->get_address())
											<<std::endl;
										retval = symval;
										found=true;break;
									}
								}
							}
							else if(found){
								target = 0;
								SgAsmX86Instruction *current = isSgAsmX86Instruction(insn);
								if(current && (x86_call==current->get_kind() || x86_farcall==current->get_kind())){
									current->getBranchTarget(&target);
									if(target){
										constructor = partitioner.functionExists(target);
										if(confirmConstructor(constructor,retval)){
											mlog[INFO]<<"[CONFIRMED] Constructor Found at : "<<StringUtility::intToHex(target)<<
												" for the instance started at : "<<StringUtility::intToHex(leaInst->get_address())<<std::endl;
											sureFlag = true;
										}
										else{
											mlog[INFO]<<"[NOT CONFIRMED] Constructor Found at : "<<StringUtility::intToHex(target)<<
												" for the instance started at : "<<StringUtility::intToHex(leaInst->get_address())<<std::endl;
										}
										return retval;
									}
								}
							}
						}
						return Sawyer::Nothing();
					}

				void
					thisCallFunctions::lookForAllObjectMethods(const SgAsmInstruction *newCaller,const P2::Function::Ptr &constructor,
						BaseSemantics::SValuePtr &thisPtr,bool &sureFlag){
						if(constructor!=NULL && !classMap.exists(constructor) ){
							sureConstructors.insert(constructor);
							classMap.insert(constructor,classDetails::Ptr( new classDetails(totalClasses++)));
						}
						classMap[constructor]->thisptrs.insert(thisPtr);
						if(sureFlag)
							classMap[constructor]->sureConstructor.insert(constructor);
						else
							classMap[constructor]->maybeConstructor.insert(constructor);
						classMap[constructor]->instances.insert(newCaller->get_address());
						BOOST_FOREACH(funcToInstPair &function,thisCallsFunctions){
							BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*useChain[function.second]){
								AbstractLocation *aLoc = vaPair->second;
								BaseSemantics::SValuePtr symval = vaPair->first;
								if( aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="ecx" && checkForEqual(symval,thisPtr)){
									methodToClassConst.insertMaybe(function.first,new std::set<P2::Function::Ptr>());
									methodToClassConst[function.first]->insert(constructor);
									mlog[INFO]<<"Found method for class instance : "<<StringUtility::intToHex(function.first->address())
										<<std::endl;
									classMap[constructor]->classMethods.insert(function.first);
								}
							}
						}
					}

				// Returns pointer/address to the object methods : set of functions sharing a common thisPtr
				void
					thisCallFunctions::findObjectMethodsFromNew(const SgAsmInstruction *newCaller,std::set<rose_addr_t> &NewAddresses){
						P2::Function::Ptr constructor;
						BaseSemantics::SValuePtr thisPtr ;
						bool sureFlag=false;
						mlog[INFO]<<"Analyzing instance started at : "<<StringUtility::intToHex(newCaller->get_address())<<std::endl;
						if(findReturnValueOfNewConstructor(newCaller,NewAddresses,constructor,sureFlag).assignTo(thisPtr)){
							lookForAllObjectMethods(newCaller,constructor,thisPtr,sureFlag);
						}else{
							mlog[INFO]<<"No thisPtr found for instance Started at : "<<StringUtility::intToHex(newCaller->get_address())<<std::endl;
						}
					}

				void
					thisCallFunctions::findObjectMethodsFromLea(const SgAsmInstruction* leaInst){
						P2::Function::Ptr constructor;
						BaseSemantics::SValuePtr thisPtr ;
						bool sureFlag=false;
						mlog[INFO]<<"Analyzing instance started at : "<<StringUtility::intToHex(leaInst->get_address())<<std::endl;
						if(findReturnValueOfLeaConstructor(leaInst,constructor,sureFlag).assignTo(thisPtr)){
							lookForAllObjectMethods(leaInst,constructor,thisPtr,sureFlag);
						}else{
							mlog[INFO]<<"No thisPtr found for instance Started at : "<<StringUtility::intToHex(leaInst->get_address())<<std::endl;
						}
					}

				void
					thisCallFunctions::lookupFunctionDataMembers(Function::Ptr &function,SgAsmInstruction* start,BaseSemantics::SValuePtr &thisptr,
							rose_addr_t maxClassSize){
						BOOST_FOREACH(SgAsmInstruction *insn,getInstructions(function)){
							if(insn->get_address()<=start->get_address()) continue;
							BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*useChain[insn]){
								AbstractLocation *aLoc = vaPair->second;
								BaseSemantics::SValuePtr symval = vaPair->first;
								if(aLoc->isAddress()){
									BaseSemantics::SValuePtr offset = ops->add(aLoc->getAddress(),ops->negate(thisptr));
									if(offset->is_number() && offset->get_number()>=0 && offset->get_number()<maxClassSize){
										rose_addr_t size = symval->get_width();
										mlog[INFO]<<"Found a data member at offset : "<<StringUtility::numberToString(offset->get_number())<<
											" of Size : "<<StringUtility::numberToString(size)<<std::endl;
										BOOST_FOREACH(const P2::Function::Ptr &fun,*methodToClassConst[function])
											classMap[fun]->dataMembers.insert(std::make_pair(offset->get_number(),size));
									}
								}
							}
							BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*defChain[insn]){
								AbstractLocation *aLoc = vaPair->second;
								BaseSemantics::SValuePtr symval = vaPair->first;
								if(aLoc->isAddress()){
									BaseSemantics::SValuePtr offset = ops->add(aLoc->getAddress(),ops->negate(thisptr));
									if(offset->is_number() && offset->get_number()>=0 && offset->get_number()<maxClassSize){
										rose_addr_t size = symval->get_width();
										mlog[INFO]<<"Found a data member at offset : "<<StringUtility::numberToString(offset->get_number())<<
											" of Size : "<<StringUtility::numberToString(size)<<std::endl;
										BOOST_FOREACH(const P2::Function::Ptr &fun,*methodToClassConst[function])
											classMap[fun]->dataMembers.insert(std::make_pair(offset->get_number(),size));
									}
								}
							}
						}
					}

				// Returns MemberMap : mapping from function to pairs <offset,size> describing data members
				void 
					thisCallFunctions::findDataMembers(rose_addr_t maxClassSize){
						BOOST_FOREACH(funcToInstPair &function,thisCallsFunctions){
							if(!methodToClassConst.exists(function.first)) continue;
							mlog[INFO]<<"Analyzing Function at : "<<StringUtility::intToHex(function.first->address())<<std::endl;
							BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*useChain[function.second]){
								AbstractLocation *aLoc = vaPair->second;
								BaseSemantics::SValuePtr thisptr = vaPair->first;
								if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="ecx"){
									lookupFunctionDataMembers(function.first,function.second,thisptr,maxClassSize);
								}
							}
						}
					}

				void
					thisCallFunctions::lookForThisPtr(rose_addr_t target,functionThisPtrSet &passed){
						BOOST_FOREACH(funcToInstPair &function,thisCallsFunctions){
							if(target==function.first->address()){
								BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*useChain[function.second]){
									AbstractLocation *aLoc = vaPair->second;
									BaseSemantics::SValuePtr symval = vaPair->first;
									if(aLoc->isRegister() && regdict->lookup(aLoc->getRegister())=="ecx" && symval->is_number()){
										passed.push_back(std::make_pair(function.first,symval));
									}
								}
								return;
							}
						}
						return;
					}

				void
					thisCallFunctions::buildMayBeClass(SgAsmInstruction* newCaller,const P2::Function::Ptr &constructor,
						BaseSemantics::SValuePtr &thisptr){
						bool sureFlag=true;
						lookForAllObjectMethods(newCaller,constructor,thisptr,sureFlag);
						findVirtualTable(constructor,thisptr);
						lookForInheritance(constructor);
						return ;
					}

				// Returns Parents: set of parent/inherited constructors called by Func
				void 
					thisCallFunctions::lookForInheritance(const P2::Function::Ptr &constructor){
						functionThisPtrSet passed;
						rose_addr_t target;
						Sawyer::Container::Map<rose_addr_t,SgAsmInstruction*> matchFunction;
						BOOST_FOREACH(SgAsmInstruction *insn,getInstructions(constructor)){
							// Find calls to other constructors
							target=0;
							SgAsmX86Instruction *last = isSgAsmX86Instruction(insn);
							if(last && (x86_call==last->get_kind() || x86_farcall==last->get_kind())){
								last->getBranchTarget(&target);
								if(target && ( sureConstructors.find(getFunction(target))!= sureConstructors.end() || 
									mayBeConstructors.find(getFunction(target))!=mayBeConstructors.end()) ){
									// Get ThisPtr passed to each constructors called from the current constructor
									lookForThisPtr(target,passed);
									matchFunction.insert(target,insn);
								}
							}
						}

						// Look for mov instruction that overwrites location of passed ThisPtr
						BOOST_FOREACH(SgAsmInstruction *insn,getInstructions(constructor)){
							SgAsmX86Instruction *last = isSgAsmX86Instruction(insn);
							if(last && (x86_mov==last->get_kind()) ){
								BOOST_FOREACH(ID::Engine::ValueAbstractPair *vaPair,*defChain[insn]){
									AbstractLocation *aLoc = vaPair->second;
									BaseSemantics::SValuePtr symval = vaPair->first;
									if(aLoc->isAddress()){
										BOOST_FOREACH(functionThisPtr &value,passed){
											if(checkForEqual(symval,value.second)){
												if(!classMap.exists(value.first)){
													mayBeConstructors.erase(value.first);sureConstructors.insert(value.first);
													buildMayBeClass(matchFunction[value.first->address()],value.first,symval);
												}
												mlog[INFO]<<"Found a Parent Class with id : "<<StringUtility::numberToString(classMap[value.first]->id)<<
													" with constructor at : "<<StringUtility::intToHex(value.first->address())<<std::endl;
												classMap[constructor]->sureParentClasses.insert(classMap[value.first]);
											}
										}
									}
								}
							}
						}

						// Put the remaining in mayBeParent
						BOOST_FOREACH(functionThisPtr &value,passed){
							if(!classMap.exists(value.first))
								buildMayBeClass(matchFunction[value.first->address()],value.first,value.second);
							classMap[constructor]->mayBeParentClasses.insert(classMap[value.first]);
						}
						return;
					}


			} // namespace
		}	// namespace
	}	// namespace
}	// namespace
