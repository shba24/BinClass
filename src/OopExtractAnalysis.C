///
///     Written By: Shubham Bansal (illusionist.neo@gmail.com)
///     Blog :- http://in3o.me
///
/// The MIT License (MIT)

/// Copyright (c) 2015 Shubham Bansal(iN3O)

/// Permission is hereby granted, free of charge, to any person obtaining a copy
/// of this software and associated documentation files (the "Software"), to deal
/// in the Software without restriction, including without limitation the rights
/// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
/// copies of the Software, and to permit persons to whom the Software is
/// furnished to do so, subject to the following conditions:

/// The above copyright notice and this permission notice shall be included in
/// all copies or substantial portions of the Software.

/// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
/// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
/// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
/// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
/// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
/// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
/// THE SOFTWARE.

#include "sage3basic.h"
#include "sageInterfaceAsm.h"
#include <iostream>
#include <rose_strtoull.h>
#include <ClassSemantics.h>
#include <Engine.h>
#include <OopExtractAnalysis.h>
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
// YAML C++ extension Library
#ifdef ROSE_HAVE_LIBYAML
#include <yaml-cpp/yaml.h>
#endif

/* Namespaces */
using namespace Sawyer::Container;
using namespace Sawyer::Container::Algorithm;
using namespace rose::BinaryAnalysis;
using namespace rose::Diagnostics;

namespace P2 = Partitioner2;
namespace IS2 = InstructionSemantics2;


/* Exclusive namepace InterDataFlow for Inter-Procedural DataFlow Analysis */
namespace rose {
	namespace BinaryAnalysis {
		namespace Partitioner2 {
			namespace ClassSemantics {

				///////////////////////////////////////////////////////////////////////////////////////////
				////////////////////		Class 		Detail 						//////////////////////
				///////////////////////////////////////////////////////////////////////////////////////////

				// prints all the information collected about the class in the YAML format
				void 
					classDetails::print(YAML::Emitter &out,std::set<rose_addr_t>& functions){
						out << YAML::BeginMap;
						out << YAML::Key << "id" << YAML::Value << id_<< YAML::Comment("Unique id of class");
						out << YAML::Key << "Virtual Tables"<< YAML::Value << YAML::BeginSeq ;
						BOOST_FOREACH(rose_addr_t vtablePtr,vtablePtrs)
							out << StringUtility::intToHex(vtablePtr);
						out << YAML::EndSeq << YAML::Comment("Virtual table Pointers");
						out << YAML::Key << "Constructors "<< YAML::Value << YAML::BeginSeq ;
						BOOST_FOREACH(const P2::Function::Ptr &constructor,Constructor){
							out << StringUtility::intToHex(constructor->address());
							functions.insert(constructor->address());
						}
						out << YAML::EndSeq << YAML::Comment("all Constructors found");
						out << YAML::Key << "Virtual Functions "<< YAML::Value << YAML::BeginSeq ;
						BOOST_FOREACH(rose_addr_t vfunctionAddr,virtualFunctions){
							out << StringUtility::intToHex(vfunctionAddr);
							functions.insert(vfunctionAddr);
						}
						out << YAML::EndSeq << YAML::Comment("all Virtual Functions found");
						out << YAML::Key << "Function Members "<< YAML::Value << YAML::BeginSeq ;
						BOOST_FOREACH(const P2::Function::Ptr &method,classMethods){
							out << StringUtility::intToHex(method->address());
							functions.insert(method->address());
						}
						out << YAML::EndSeq << YAML::Comment("all class methods found");
						out << YAML::Key << "Data Members"<< YAML::Value << YAML::BeginSeq;
						BOOST_FOREACH(const Member &data,dataMembers){
							out << YAML::BeginMap;
							out << YAML::Key << "offset"<< YAML::Value << data.first;
							out << YAML::Key << "Size" << YAML::Value << data.second;
							out << YAML::EndMap;
						}
						out << YAML::EndSeq << YAML::Comment("all Data Members found");
						out << YAML::Key << "Sure Parent Class"<< YAML::Value << YAML::BeginSeq;
						BOOST_FOREACH(offsetToParent::Node &parent,sureParentClasses.nodes()){
							out << YAML::BeginMap;
							out << YAML::Key << "offset"<< YAML::Value << parent.key();
							out << YAML::Key << "Parent Id" << YAML::Value << parent.value()->getId();
							out << YAML::EndMap;
						}
						out << YAML::EndSeq << YAML::Comment("all Sure Parent Classes found");
						out << YAML::Key << "MayBe Parent/Embedded Class"<< YAML::Value << YAML::BeginSeq;
						BOOST_FOREACH(offsetToParent::Node &parent,mayBeParentClasses.nodes()){
							out << YAML::BeginMap;
							out << YAML::Key << "offset"<< YAML::Value << parent.key();
							out << YAML::Key << "object Id" << YAML::Value << parent.value()->getId();
							out << YAML::EndMap;
						}
						out << YAML::EndSeq << YAML::Comment("all MayBe Parent/Embedded Classes found");
						out << YAML::Key << "Embeded Objects"<< YAML::Value << YAML::BeginSeq;
						BOOST_FOREACH(offsetToParent::Node &embeded,embededObjects.nodes()){
							out << YAML::BeginMap;
							out << YAML::Key << "offset"<< YAML::Value << embeded.key();
							out << YAML::Key << "object Id" << YAML::Value << embeded.value()->getId();
							out << YAML::EndMap;
						}
						out << YAML::EndSeq << YAML::Comment("all Embedded Objects found");
						out << YAML::Key << "Instances "<< YAML::Value <<YAML::Flow<< YAML::BeginSeq;
						BOOST_FOREACH(SgAsmInstruction *instance,instances)
							out << StringUtility::intToHex(instance->get_address());
						out << YAML::EndSeq << YAML::Comment("all instances found");
						out << YAML::EndMap;
					}

				// adds vtable pointer(lies in .rdata section) to the class and use it to find all the virtual function pointers 
				// which lies in the .text Section of the Code.
				bool 
					classDetails::addVtablePtr(rose_addr_t vtptr){
						if(vtablePtrs.insert(vtptr).second)
							return true;
						return false;
					}

				bool 
					classDetails::addEmbededObjectPointer(rose_addr_t offset,Ptr &other){
						if(!embededObjectsPointer.exists(offset)){
							embededObjectsPointer.insert(offset,other);
							mlog[INFO]<<"Found new embedded Objects Pointer at offset : "<<offset<<std::endl;
							return true;
						}
						return false;
					}

				///////////////////////////////////////////////////////////////////////////////////////////
				////////////////////          OOP Object Extracting 				///////////////////////
				///////////////////////////////////////////////////////////////////////////////////////////

				void 
					ExtractOOP::addVtablePtr(rose_addr_t vtptr,classDetails::Ptr &object){
						// checks if vtable is really inserted or not
						if(object->addVtablePtr(vtptr)){
							if(settings_.verbose)
								mlog[INFO]<<"Found Virtual Table Ptr : "<<StringUtility::intToHex(vtptr)<<std::endl;
							BaseSemantics::SValuePtr vtableaddr = ops_->number_(32,vtptr);
							// reading the function pointer from the vtable pointer
							BaseSemantics::SValuePtr funcPtr = ops_->readMemory(REG_SS,vtableaddr,ops_->undefined_(vtableaddr->get_width()),ops_->boolean_(true));
							// iterating until we find some unknown function pointer 
							while(funcPtr->is_number() && textSectionRange.exists(funcPtr->get_number()) ){
								object->addVirtualFunction(funcPtr->get_number(),settings_.verbose);
								// finding the next vtable address which might have virtual function pointer
								vtableaddr = ops_->add(vtableaddr,ops_->number_(vtableaddr->get_width(),funcPtr->get_width()/8));
								// reading the function pointer from the next vtable address
								funcPtr = ops_->readMemory(REG_SS,vtableaddr,ops_->undefined_(funcPtr->get_width()),ops_->boolean_(true));
							}
						}
					}

				// sets the address range representing the .rdata section in the binary
				// it is used to find if the virtual table pointer lies in the .rdata section or not
				void 
					ExtractOOP::setrdataAddressRange(SgAsmInterpretation* interp){
						virtualTableRange = getSectionRangeByName(interp,".rdata");
					}

				void 
					ExtractOOP::setStaticDataRange(SgAsmInterpretation* interp){
						staticDataRange = getSectionRangeByName(interp,".data");
					}

				void
					ExtractOOP::setTextSectionRange(SgAsmInterpretation* interp){
						textSectionRange = getSectionRangeByName(interp,".text");
					}

				/* Finds all the cross refernce to a function and returns a set of instructions which are refering to the function
				 *	in one way or another (either through jmp or call)
				 */
				std::vector<SgAsmInstruction*> 
					ExtractOOP::findCrossReferences(const P2::Function::Ptr &function ){
						std::vector<SgAsmInstruction*> retval;
						// finding the Function Call Graph vertex representing the function
						ControlFlowGraph::ConstVertexIterator vertex = partitioner_.findPlaceholder(function->address());
						BOOST_FOREACH(const ControlFlowGraph::Edge &edge, vertex->inEdges()){
							// checking for all the edge representing a function call this function
							if(edge.value().type() == E_FUNCTION_CALL && edge.source()->value().type() == V_BASIC_BLOCK){
								const BasicBlock::Ptr &bblock = edge.source()->value().bblock();
								SgAsmInstruction *xref = bblock->instructions().back();
								retval.push_back(xref);
							}
						}
					}

				void
					ExtractOOP::checkForReturnExist(const P2::Function::Ptr function,Sawyer::Container::DistinctList<P2::Function::Ptr>& functionQueue){
						FunctionSummaryPtr &sourceFuncSum = functionSummaries_[function];
						if(sourceFuncSum->getReturns()){
							rose_addr_t returnedHash = SValue::promote(sourceFuncSum->getReturnValue())->get_expression()->hash();
							if(thisPtrToClass.exists(returnedHash)){
								classDetails::Ptr &object = thisPtrToClass[returnedHash];
								ControlFlowGraph::ConstVertexIterator vertex = partitioner_.findPlaceholder(function->address());
								BOOST_FOREACH(const ControlFlowGraph::Edge &edge, vertex->inEdges()){
									if(edge.value().type() == E_FUNCTION_CALL && edge.source()->value().type() == V_BASIC_BLOCK){
										// foreach xref to function:
										SgAsmInstruction *callInstr = edge.source()->value().bblock()->instructions().back();
										P2::Function::Ptr xreffunction = edge.source()->value().function();
										if(!defChain_.exists(callInstr)) continue;
										BOOST_FOREACH(AbstractAccessPtr &def,defChain_[callInstr]->getaAcesList()){
											const BaseSemantics::SValuePtr& defVal = def->getValue();
											if(def->getAloc()->isRegister() && def->getAloc()->getRegister()==REG_EAX){
												rose_addr_t tranferedHash = SValue::promote(defVal)->get_expression()->hash();
												if(!thisPtrToClass.exists(tranferedHash)){
													addThisPtr(defVal,object,xreffunction);
													functionQueue.pushBack(xreffunction);
												}
												// end
											}
											// end
										}
									}
									// end
								}
							}
							// end
						}
						// end
					}

				/* Very important function
				 * Consider a class object1 which is derived from class object2 and class object3.
				 *	--- Object1
				 *	|--- Object2 (at 0 offset)
				 *	||
				 *	|---
				 *	|---- Object 2 (at 4 offset)
				 *	||
				 *	||
				 *	||
				 *	|----
				 *	|
				 *	---
				 * suppose above is the memory representation of the class/object. Suppose if we found some new "thisPtr" of the class/object Object1,
				 * so what this function will do is, it will add "thisPtr+4" as the new this-ptr of the object/class object2 and all the parent classes
				 * of this object Object1 but will not handle the thisPtrs at 0 offset as this will get confused with the current thisPtr of this object.
				 */
				void
					ExtractOOP::addThisPtr(const BaseSemantics::SValuePtr &thisptr,classDetails::Ptr &object,const Partitioner2::Function::Ptr& xreffunction){
						FunctionSummaryPtr &xrefSummary = functionSummaries_[xreffunction];
						// hash of the this-ptr
						rose_addr_t thisHash = SValue::promote(thisptr)->get_expression()->hash();
						xrefSummary->addThisPtr(thisHash,thisptr);

						object->addThisPtr(thisHash,settings_.verbose);
						thisPtrToClass.insert(thisHash,object);

						// iterating over all sure parent object
						BOOST_FOREACH(const classDetails::offsetToParent::Node &node,object->getSureParentClasses().nodes()){
							rose_addr_t offset = node.key();
							// ignoring the parent thisptr at 0 offset
							if(offset==0) continue;
							const classDetails::Ptr &parent = node.value();
							BaseSemantics::SValuePtr newThisPtr = ops_->add(thisptr,ops_->number_(thisptr->get_width(),offset));
							rose_addr_t newThisPtrHash = SValue::promote(newThisPtr)->get_expression()->hash();
							xrefSummary->addThisPtr(newThisPtrHash,newThisPtr);
							// adding new calculated this-ptr hash to class
							parent->addThisPtr(newThisPtrHash,settings_.verbose);
							// adding map of new this-ptr to its class object
							thisPtrToClass.insert(newThisPtrHash,parent);
						}
						//iterating over all may be parent object
						BOOST_FOREACH(const classDetails::offsetToParent::Node &node,object->getMayBeParentClasses().nodes()){
							rose_addr_t offset = node.key();
							// ignoring the parent thisptr at 0 offset
							if(offset==0) continue;
							const classDetails::Ptr &parent = node.value();
							BaseSemantics::SValuePtr newThisPtr = ops_->add(thisptr,ops_->number_(thisptr->get_width(),offset));
							rose_addr_t newThisPtrHash = SValue::promote(newThisPtr)->get_expression()->hash();
							xrefSummary->addThisPtr(newThisPtrHash,newThisPtr);
							// adding new calculated this-ptr hash to class
							parent->addThisPtr(newThisPtrHash,settings_.verbose);
							// adding map of new this-ptr to its class object
							thisPtrToClass.insert(newThisPtrHash,parent);
						}
						//iterating over all embeded object
						BOOST_FOREACH(const classDetails::offsetToParent::Node &node,object->getEmbededClasses().nodes()){
							rose_addr_t offset = node.key();
							// ignoring the embeded thisptr at 0 offset
							if(offset==0) continue;
							const classDetails::Ptr &embeded = node.value();
							BaseSemantics::SValuePtr newThisPtr = ops_->add(thisptr,ops_->number_(thisptr->get_width(),offset));
							rose_addr_t newThisPtrHash = SValue::promote(newThisPtr)->get_expression()->hash();
							xrefSummary->addThisPtr(newThisPtrHash,newThisPtr);
							// adding new calculated this-ptr hash to class
							embeded->addThisPtr(newThisPtrHash,settings_.verbose);
							// adding map of new this-ptr to its class object
							thisPtrToClass.insert(newThisPtrHash,embeded);
						}
					}

				// function to add a set of this-ptr to this class and calls addThisPtr to add each this-ptr
				void
					ExtractOOP::addThisPtrs(std::vector<BaseSemantics::SValuePtr>& to_add,classDetails::Ptr &object,const Partitioner2::Function::Ptr& xreffunction){
						// iterate over each this-ptr to add to the class
						BOOST_FOREACH(BaseSemantics::SValuePtr &val,to_add)
							addThisPtr(val,object,xreffunction);
					}

				bool
					ExtractOOP::isCallInstruction(SgAsmInstruction* insn){
						SgAsmX86Instruction *current = isSgAsmX86Instruction(insn);
						if(current && (x86_call==current->get_kind() || x86_farcall==current->get_kind()))
							return true;
						return false;
					}
				/* Important Algorithm - finds all the class/object methods , following this-ptrs among different function
				 *  and adding the new found this-ptrs to the corresponding class/Object
				 *  Algorithm:
				 *	foreach function in partitioner_.functions():
				 *		foreach instruction in function:
				 *			if instruction.type = "call":
				 *				if instruction is using this-ptr as any of the argument of the call instruction:
				 *					find the argument using that corresponding this-ptr and 
				 *						add the value corresponding to that argument in the called function to the this-ptr of the class and its parent classes
				 *					if the argument is register ECX and the called function is following thiscall__ calling convention then 
				 *							this called function is a part of the corresponding class whose this-ptr it is using in ECX
				 *			repeat the process again.
				 */
				void
				    ExtractOOP::findClassMethods(Sawyer::Container::DistinctList<P2::Function::Ptr>& functionQueue){
					    while(!functionQueue.isEmpty()){
						    P2::Function::Ptr function = functionQueue.popFront();
						    FunctionSummaryPtr& sourceFuncSum = functionSummaries_[function];
						    BOOST_FOREACH(rose_addr_t bblockVa,function->basicBlockAddresses()){
							    BOOST_FOREACH(SgAsmInstruction *insn,partitioner_.basicBlockContainingInstruction(bblockVa)->instructions()){
								    if(isCallInstruction(insn)){
									    P2::Function::Ptr target = engine.GetTargetFunction(insn);
									    if(target && functionSummaries_.exists(target)){
										    FunctionSummaryPtr& targetFuncSum = functionSummaries_[target];
										    if(!useChain_.exists(insn) || !callESP_.exists(insn)) continue;
										    SValuePtr currentESP = SValue::promote(callESP_[insn]);
										    BOOST_FOREACH(AbstractAccessPtr &use,useChain_[insn]->getaAcesList()){
											    const BaseSemantics::SValuePtr& useVal = use->getValue();
											    rose_addr_t hashUsed = SValue::promote(useVal)->get_expression()->hash();
											    // if instruction is using this-ptr as any of the argument of the call instruction:
											    if( thisPtrToClass.exists(hashUsed)){
												    classDetails::Ptr &object = thisPtrToClass[hashUsed];
												    if(use->getAloc()->isRegister() ){
													    // find the argument using that corresponding this-ptr
													    const RegisterDescriptor &reg = use->getAloc()->getRegister();
													    // the value corresponding to that argument in the called function to the this-ptr of the class and its parent classes
													    BaseSemantics::SValuePtr tranferedValue = targetFuncSum->getInputRegisterValue(reg);
													    rose_addr_t tranferedHash = SValue::promote(tranferedValue)->get_expression()->hash();
													    if(!thisPtrToClass.exists(tranferedHash)){
														    // if the argument is register ECX and the called function is following thiscall__ calling 
														    // convention then this called function is a part of the corresponding class whose this-ptr it is using in ECX
														    if(reg==REG_ECX && thisCallsFunctions.find(target)!=thisCallsFunctions.end())
															    object->addClassMethods(target,settings_.verbose);
														    //add the value corresponding to that argument in the called function to the 
														    //this-ptr of the class and its parent classes
														    addThisPtr(tranferedValue,object,target);
														    functionQueue.pushBack(target);
													    }
												    }else if(use->getAloc()->isAddress()){
													    const BaseSemantics::SValuePtr &useAddr = use->getAloc()->getAddress();
													    int32_t offset=0;
													    // find the argument using that corresponding this-ptr
													    if(SValue::promote(useAddr)->getOffset(currentESP,offset,solver_)){
														    // the value corresponding to that argument in the called function to the this-ptr of the class and its parent classes
														    BaseSemantics::SValuePtr tranferedValue = targetFuncSum->getOutputArgValue(ops_,offset,
																    useVal->get_width(),REG_SS);
														    rose_addr_t tranferedHash = SValue::promote(tranferedValue)->get_expression()->hash();
														    // check if new found this-ptr is really a new found this-ptr or not
														    if(!thisPtrToClass.exists(tranferedHash)){
															    //add the value corresponding to that argument in the called function to the 
															    //this-ptr of the class and its parent classes
															    addThisPtr(tranferedValue,object,target);
															    functionQueue.pushBack(target);
														    }
													    }
												    }
												    // end
											    }
											    // end
										    }
									    }
									    // end
								    }else{
								    	if(!useChain_.exists(insn)) continue;
								    	BOOST_FOREACH(AbstractAccessPtr &use,useChain_[insn]->getaAcesList()){
								    		if(use->getAloc()->isAddress()){
								    			const BaseSemantics::SValuePtr &useAddr = use->getAloc()->getAddress();
								    			classDetails::Ptr embededObject;
								    			if(embededObject = checkForEmbeddedPointer(useAddr,sourceFuncSum) ){
								    				const BaseSemantics::SValuePtr& useVal = use->getValue();
								    				addThisPtr(useVal,embededObject,function);
								    			}
								    		}
								    	}
								    }
							    }
						    }
						    checkForReturnExist(function,functionQueue);
					    }
				    }
				/* Very Important Algorithm in Identifying object instances,this-ptrs,methods,constructors and inheritence of the objects
				 *  initiated by the "new" library call (i.e. Heap Objects)
				 *  
				 *  Algorithm :
				 *  foreach function in partitioner_.functions()
				 *		if function.name = "new":
				 *			foreach xref to function:
				 *				Collect all definied value of EAX using defchain
				 *				look for contructor in the same function just after xref
				 *				if constructor found:
				 *					look for the inheritance in the constructor
				 *					add all the this-pointer corresponding to this class and all its parent class
				 *					add xref to the starting instance of this class
				 *					look for all the function methods following all the new this-ptrs found
				 */
				void 
					ExtractOOP::findHeapThisPtr(functionList &functionQueue){
						BOOST_FOREACH(const P2::Function::Ptr &function,partitioner_.functions()){
							// cheking if the name of the library function is "new" or not, here "??2@YAPAXI@Z" represents mangled function
							// name by the MSVC which is a type of encoding which represents the function call type(calling convention),
							// function arguments type
							if(function->name().substr(0,12)=="??2@YAPAXI@Z"){  /// new function
								ControlFlowGraph::ConstVertexIterator vertex = partitioner_.findPlaceholder(function->address());
								BOOST_FOREACH(const ControlFlowGraph::Edge &edge, vertex->inEdges()){
									if(edge.value().type() == E_FUNCTION_CALL && edge.source()->value().type() == V_BASIC_BLOCK){
										// finding all the xref to the "new" library function
										SgAsmInstruction *xref = edge.source()->value().bblock()->instructions().back();
										if(settings_.verbose)
											mlog[INFO]<<"Found 'new' library call xref : "<<StringUtility::intToHex(xref->get_address())<<std::endl;
										if(!defChain_.exists(xref)) continue;
										std::vector<BaseSemantics::SValuePtr> symThisPtrs;
										std::set<rose_addr_t> thisPtrs;
										// Collect all definied value of EAX(which might represent this-ptr in this case) using defchain
										BOOST_FOREACH(AbstractAccessPtr &xrefDef,defChain_[xref]->getaAcesList()){
											const BaseSemantics::SValuePtr& val = xrefDef->getValue();
											if(xrefDef->getAloc()->isRegister() && xrefDef->getAloc()->getRegister()==REG_EAX){
												// collecting all the symbolic value of the this-ptr
												symThisPtrs.push_back(val);
												// collecting all the hash value of this-ptr which will be used in finding the constructor
												thisPtrs.insert(SValue::promote(val)->get_expression()->hash());
											}
										}
										// cross referencing function
										P2::Function::Ptr xreffunction = edge.source()->value().function();
										P2::Function::Ptr constructor;
										// checking if the found this-ptrs does represents this-ptrs which belongs to a class/object or not
										// in function addUniqueClass , we are looking for call instruction which is calling the constructor
										// and using new found this-ptrs as this-ptr to this function call
										if(addUniqueClass(xreffunction,constructor,xref,thisPtrs)){
											// looking for the inheritance in the constructor
											lookForInheritance(constructor);
											classDetails::Ptr &object = ObjectInfo[constructor];
											// adding all the this-pointer corresponding to this class and all its parent class
											addThisPtrs(symThisPtrs,object,xreffunction);
											// adding xref to the starting instance of this class
											object->addInstance(xref,settings_.verbose);
											// look for all the function methods following all the new this-ptrs found
											functionQueue.pushBack(xreffunction);
										}
									}
								}
							}
						}
						// end
					}

				/* Builds the object in bottom-up manner by finding the xreference to the already found function of the object
				 *  Algorithm :-
				 *	foreach xref to function:
				 *		collect all the new found this-ptrs
				 *		find the class methods using the new found this-ptrs
				 */
				void
					ExtractOOP::buildFromFunction(const P2::Function::Ptr &function,classDetails::Ptr &object,functionList &functionQueue){
						ControlFlowGraph::ConstVertexIterator vertex = partitioner_.findPlaceholder(function->address());
						BOOST_FOREACH(const ControlFlowGraph::Edge &edge, vertex->inEdges()){
							if(edge.value().type() == E_FUNCTION_CALL && edge.source()->value().type() == V_BASIC_BLOCK){
								// Cross reference to already found contructors
								SgAsmInstruction *xref = edge.source()->value().bblock()->instructions().back();
								if(!useChain_.exists(xref)) continue;
								std::vector<BaseSemantics::SValuePtr> symThisPtrs;
								// Collect all definied value of ECX using defchain, which are new this-ptrs to the objects represented by contructor
								BOOST_FOREACH(AbstractAccessPtr &xrefUse,useChain_[xref]->getaAcesList()){
									const BaseSemantics::SValuePtr& val = xrefUse->getValue();
									if(xrefUse->getAloc()->isRegister() && xrefUse->getAloc()->getRegister()==REG_ECX && 
											!thisPtrToClass.exists(SValue::promote(val)->get_expression()->hash())){
										symThisPtrs.push_back(val);
									}
								}
								P2::Function::Ptr xreffunction = edge.source()->value().function();
								if(!symThisPtrs.empty()){
									// add all the this-pointer corresponding to this class and all its parent class
									addThisPtrs(symThisPtrs,object,xreffunction);
									// this is another starting instance of the object if the "function" is constructor of the object
									if(object->isConstructor(function)){
										// add xref to the starting instance of this class
										object->addInstance(xref,settings_.verbose);
									}
									// look for all the function methods following all the new this-ptrs found
									functionQueue.pushBack(xreffunction);
								}
							}
						}
					}

				void
					ExtractOOP::followVirtualFunctions(functionList &functionQueue){
						// iterating over each Object found to build the objects in bottom-to-top manner
						BOOST_FOREACH(const P2::Function::Ptr &constructor,ObjectInfo.keys()){
							classDetails::Ptr &object = ObjectInfo[constructor];
							// building from the virtual functions of the object - Analysing virtual functions for the first time
							BOOST_FOREACH(rose_addr_t virtualMethodAddr,object->getVirtualFunctions()){
								P2::Function::Ptr virtualMethod = partitioner_.functionExists(virtualMethodAddr);
								if(!virtualMethod || !functionSummaries_.exists(virtualMethod)) continue;
								FunctionSummaryPtr& virtualFuncSum = functionSummaries_[virtualMethod];
								// Transfered Value of this-ptr in the virtual function
								BaseSemantics::SValuePtr tranferedValue = virtualFuncSum->getInputRegisterValue(REG_ECX);
								rose_addr_t tranferedHash = SValue::promote(tranferedValue)->get_expression()->hash();
								// checking if the symbolic value of this-ptr is already identified as this-ptr or not
								if(!thisPtrToClass.exists(tranferedHash)){
									addThisPtr(tranferedValue,object,virtualMethod);
									// look for all the function methods following all the new this-ptrs found
									functionQueue.pushBack(virtualMethod);
								}
							}
						}
					}

				// built from all the cross references of the already found contructors
				// For example :-
				//  * Suppose a Class named object1 has a constructor [ object1:object() ] which is already identified by
				//    the above findHeapThisPtr.
				//  * This function tries to find all the cross references to the function(object1:object()) and starts 
				//    building from bottom-to-top. Suppose that cross reference is in function main(), then this function
				//    search for the instrcution which is calling the object1 constructor and detect all the new this-ptrs
				//    found in the main function and follow the top-down procedure(as followed by the findHeapThisPtr) from there
				void
					ExtractOOP::buildfromClassMethods(functionList &functionQueue){
						// iterating over each Object found to build the objects in bottom-to-top manner
						BOOST_FOREACH(const P2::Function::Ptr &constructor,ObjectInfo.keys()){
							classDetails::Ptr &object = ObjectInfo[constructor];
							// building from the constructor of the object
							BOOST_FOREACH(const P2::Function::Ptr &constructor,object->getConstructors()){
								buildFromFunction(constructor,object,functionQueue);
							}
							// building from the class method of the object
							BOOST_FOREACH(const P2::Function::Ptr &method,object->getClassMethods()){
								buildFromFunction(method,object,functionQueue);
							}
						}
					}

				/* Post Object extraction fixup
				 *	- removes parent class methods and constructor from child class methods 
				 *	- removes parent class virtual functions from child class virtual functions
				 */
				void
					ExtractOOP::parentMethodFixUp(const classDetails::offsetToParent& parents,classDetails::Ptr &childObject){
						BOOST_FOREACH(const classDetails::offsetToParent::Node &parentNode,parents.nodes()){
							const classDetails::Ptr &parentObject = parentNode.value();
							// iterates over all class methods and checks if that function lies in parent class "class methods"
							// if found, it will be erased from the childObject class methods
							BOOST_FOREACH(const P2::Function::Ptr &function,childObject->getClassMethods()){
								if(parentObject->isConstructor(function) || parentObject->isClassMethod(function))
									childObject->deleteClassMethod(function);
							}
							// iterates over all class virtual functions and checks if that function lies in parent class "virtual functions"
							// if found, it will be erased from the childObject "virtual functions"
							BOOST_FOREACH(rose_addr_t functionAddr,childObject->getVirtualFunctions()){
								if(parentObject->isVirtualMethod(functionAddr))
									childObject->deleteVirtualMethod(functionAddr);
							}
						}
					}

				// this function does all the post object extracting fixing like :
				// - removing parent class methods and constructor from child class methods
				// - removing parent class virtual functions from child class virtual functions
				// - [TO DO] removing parent class data members from the child class data members
				void 
					ExtractOOP::postExtractionFixup(){
						BOOST_FOREACH(const P2::Function::Ptr &constructor , ObjectInfo.keys()){
							classDetails::Ptr &childObject = ObjectInfo[constructor];
							// fixing the childObject class methods from the sure parent classes
							parentMethodFixUp(childObject->getSureParentClasses(),childObject);
							// fixing the childObject class methods from the may be parent classes
							parentMethodFixUp(childObject->getMayBeParentClasses(),childObject);
						}
					}

				/* Checks if the call instruction to constructor is really the constructor to which all the new found this-ptr really belongs to or not
				 *  it checks if the call instruction uses the new found this-ptrs or not in ECX
				 */
				bool
					ExtractOOP::checkForConstructorCall(SgAsmInstruction* insn,const P2::Function::Ptr &constructor,std::set<rose_addr_t>& thisPtrs){
						// starting to find if the function uses this-ptr or not
						BOOST_FOREACH(AbstractAccessPtr &use,useChain_[insn]->getaAcesList()){
							// Constructor also need to use the new found this-ptrs in ECX as its argument
							if(use->getAloc()->isRegister() && use->getAloc()->getRegister()==REG_ECX){
								const BaseSemantics::SValuePtr& val = use->getValue();
								// checking if the value of register ECX exists in the new found this-ptrs or not
								if(thisPtrs.find(SValue::promote(val)->get_expression()->hash())!=thisPtrs.end()){
									if(!ObjectInfo.exists(constructor)){ 
										// if not already existing then make a new instance of class corresponding to that constructor
										classDetails::Ptr object = classDetails::instance(totalClasses++,constructor,settings_.verbose);
										ObjectInfo.insert(constructor,object);
									}
									return true;
								}
							}
						}
						return false;
					}

				/* Find all the Unique and new class contructors using the new -this-ptrs found and follwing this-ptrs
				 * -Constructor is considered as the first function called just after Object memory allocation
				 * -Constructor is also supposed to return the this-ptr corresponding to itself
				 * -Constructor also need to use this-ptr in ECX as its argument
				 * If any of the above condition is not followed than the found function is not a new found constructor and
				 * we ignore any new found this-ptr and return false, which represents "no constructor found"
				 */
				bool
					ExtractOOP::addUniqueClass(const P2::Function::Ptr &xreffunction,P2::Function::Ptr &constructor,SgAsmInstruction* xref,
							std::set<rose_addr_t>& thisPtrs){
						BOOST_FOREACH(rose_addr_t bblockVa,xreffunction->basicBlockAddresses()){
							P2::BasicBlock::Ptr bblock = partitioner_.basicBlockContainingInstruction(bblockVa);
							BOOST_FOREACH(SgAsmInstruction *insn,bblock->instructions()){
								// checking for all the instructions which lies after the cross referencing instruction
								if(insn->get_address()<=xref->get_address()) continue;
								SgAsmX86Instruction *current = isSgAsmX86Instruction(insn);
								// Constructor is considered as the first function called just after Object memory allocation
								// so here we are looking for the call instruction which lies just after the xref instruction
								// if we found the target function of that call instruction as the contructor which also using 
								// same this-ptr then we found a new class/object
								if(current && (x86_call==current->get_kind() || x86_farcall==current->get_kind())){
									// checking if the target function exists or not, also checking if the called function is thiscall_
									// following function or not becuase constructor is considered to be following thiscall_ calling
									// convention, it could also be possible that the constructor is following other calling convention
									// but by default its thiscall_ and fow now we checking for that only, but it can be changed easily
									constructor = engine.GetTargetFunction(insn);
									if(constructor){
										// target function is already found as constructor in previous analysis
										if(ObjectInfo.exists(constructor)){
											// checking if the constructor found is what we were looking for - it checks if the call instruction
											// uses the new found this-ptr or not in ECX
											return checkForConstructorCall(insn,constructor,thisPtrs);
										}else if(functionSummaries_.exists(constructor) && thisCallsFunctions.find(constructor)!=thisCallsFunctions.end()){
											FunctionSummaryPtr& funcSum = functionSummaries_[constructor];
											// Constructor is also supposed to return the this-ptr  corresponding to itself which is passed as input ECX value.
											// But its always possible to make constructor return something else but that is considered as special case
											if(funcSum->getReturns() && funcSum->getReturnECX() && useChain_.exists(insn)){
												// checking if the constructor found is what we were looking for - it checks if the call instruction
												// uses the new found this-ptr or not in ECX
												return checkForConstructorCall(insn,constructor,thisPtrs);
											}
										}
									}
									// If any of the above condition is not followed than the found function is not a new found constructor
									return false;
								}
							}
						}
						// If any of the above condition is not followed than the found function is not a new found constructor
						return false;
					}

				/* checks if the instruction "instr" is the initialisation of the stack object or not*/
				void
					ExtractOOP::checkForStackObject(SgAsmInstruction* instr,SValuePtr& inputESP,const P2::Function::Ptr &function,
							functionList &functionQueue,std::set<rose_addr_t>& usedStkVar){
						std::vector<BaseSemantics::SValuePtr> symThisPtrs;
						std::set<rose_addr_t> thisPtrs;
						SgAsmX86Instruction *current = isSgAsmX86Instruction(instr);
						// looking for instructions like "lea ecx,[ebp+YY]"
						if(current && x86_lea==current->get_kind()){
							if(!defChain_.exists(instr)) return;
							BOOST_FOREACH(AbstractAccessPtr &def,defChain_[instr]->getaAcesList()){
								// checking if the definied register is ECX or not
								if(def->getAloc()->isRegister() && def->getAloc()->getRegister()==REG_ECX){
									const BaseSemantics::SValuePtr& writeVal = def->getValue();
									SValuePtr writeVal_ = SValue::promote(writeVal);
									int32_t offset=0;
									// checking if the written value to ecx is of the form ebp+YY or esp - XX
									if( writeVal_->getOffset(inputESP,offset,solver_) && offset<-4 && usedStkVar.find(offset)==usedStkVar.end() ){
										// storing all found this-ptrs for further analysis.
										symThisPtrs.push_back(writeVal);
										thisPtrs.insert(writeVal_->get_expression()->hash());
										// storing that the stack variable at offset "offset" is used now and all the future refernce to this
										// stack variable will be ignored
										usedStkVar.insert(offset);
									}
								}
							}
						}else if(current && x86_mov==current->get_kind()){
							if(!defChain_.exists(instr)) return;
							BOOST_FOREACH(AbstractAccessPtr &def,defChain_[instr]->getaAcesList()){
								// checking if the definied register is ECX or not
								if(def->getAloc()->isRegister() && def->getAloc()->getRegister()==REG_ECX){
									const BaseSemantics::SValuePtr& writeVal = def->getValue();
									SValuePtr writeVal_ = SValue::promote(writeVal);
									if(writeVal->is_number() && staticDataRange.exists(writeVal->get_number())){
										// storing all found this-ptrs for further analysis.
										symThisPtrs.push_back(writeVal);
										thisPtrs.insert(writeVal_->get_expression()->hash());
									}
								}
							}
						}
						if(!symThisPtrs.empty()){
							if(settings_.verbose)
								mlog[INFO]<<"Found lea instruction : "<<StringUtility::intToHex(instr->get_address())<<std::endl;
							P2::Function::Ptr constructor;
							// checking if the found this-ptrs does represents this-ptrs which belongs to a class/object or not
							// in function addUniqueClass , we are looking for call instruction which is calling the constructor
							// and using new found this-ptrs as this-ptr to this function call
							if(addUniqueClass(function,constructor,instr,thisPtrs)){
								// looking for the inheritance in the constructor
								lookForInheritance(constructor);
								classDetails::Ptr &object = ObjectInfo[constructor];
								// adding all the this-pointer corresponding to this class and all its parent class
								addThisPtrs(symThisPtrs,object,function);
								// adding xref to the starting instance of this class
								object->addInstance(instr,settings_.verbose);
								// look for all the function methods following all the new this-ptrs found
								functionQueue.pushBack(function);
							}
						}
					}

				/* Very Important Algorithm in Identifying object instances,this-ptrs,methods,constructors and inheritence of the objects
				 * initiated by the lea instruction locally in a function (i.e Stack Objects or local Objects )
				 * We find the initialisation of the stack Object at instructions which uses the reference to the stack variable for the first time, 
				 * Generally what happens is that the stack variable Object is used as a reference to the stack variable and mostly this reference 
				 * is calculated using the "lea" instruction of the form "lea ecx,[ebp+YY]" where ebp + YY == esp - XX.
				 *  
				 *  Algorithm :
				 *  foreach function in functions():
				 *		UsedStackVariable = []
				 *		foreach instr in function.instructions():
				 *			if instr referneces unUsed stack variable:
				 *				
				 */
				void
				    ExtractOOP::findStackThisPtr(functionList &functionQueue){
					    // iterating over all functions and checking for local stack object in each function
					    BOOST_FOREACH(const P2::Function::Ptr &function,partitioner_.functions()){
						    // checking if we have function summary for this function or not, although we should have function summaries for
						    // the functions but sometimes function call graph misses some function due to which the function is not analysed
						    // and function summary for that function is not found
						    if(!functionSummaries_.exists(function)) continue;
						    FunctionSummaryPtr &funcSum = functionSummaries_[function];
						    // checking if the function is a library function or not, because dynamic library functions thunks don't have local
						    // varibale or object to analyse
						    if(funcSum->isLibraryFunction()) continue;

						    // input Symbolic Value of ESP for the function
						    SValuePtr inputESP = SValue::promote(funcSum->getInputESP());
						    // set of the offset(XX) of stack variable of the form(ESP-XX) from ESP, representing the local variables which are 
						    // already used by the function.
						    std::set<rose_addr_t> usedStkVar;
						    BOOST_FOREACH(rose_addr_t bblockVa,function->basicBlockAddresses()){
							    P2::BasicBlock::Ptr bblock = partitioner_.basicBlockContainingInstruction(bblockVa);
							    // iterating over each instruction of the function
							    BOOST_FOREACH(SgAsmInstruction *instr,bblock->instructions()){
								    // checking if the instruction "instr" is the initialisation of the stack object or not
								    // if found new classDetail structure corresponding to that stack Object will be made and build
								    checkForStackObject(instr,inputESP,function,functionQueue,usedStkVar);
							    }
						    }
					    }
				    }

				// find all the functions following thisCall__ calling convention using the functionSummaries corresponding to that function
				// which already has callingc convention deduced using the dataFlow analysis
				void
					ExtractOOP::findThisCallFunctions(){
						BOOST_FOREACH(const P2::Function::Ptr &function,partitioner_.functions()){
							// checking if we already have summary for this function or not
							if(functionSummaries_.exists(function)){
								FunctionSummaryPtr &funcSummary = functionSummaries_[function];
								// checking for thisCall calling convention
								if(funcSummary->getCallingConv()=="thiscall"){
									if(settings_.verbose)
										mlog[INFO]<<"Detected thisCall_ calling convention in function at : "<<
											StringUtility::intToHex(function->address())<<std::endl;
									thisCallsFunctions.insert(function);
								}
							}
						}
					}

				// virtual table corresponding to the constructor
				// Look for instructions of the form: "mov [ecx+Y], offset xxx".
				// This latter type of instruction where XXX is a constant address is _very_ likely to be a virtual function table for the class created by
				// the constructor that was being analyzed.  We can use this information to find candidate virtual function tables.
				void 
					ExtractOOP::findVirtualTable(const Partitioner2::Function::Ptr &constructor){
						classDetails::Ptr &object = ObjectInfo[constructor] ;
						FunctionSummaryPtr &funcSum = functionSummaries_[constructor];
						BaseSemantics::SValuePtr thisPtr;
						// get the this-ptr used in constructor
						if(funcSum->get_thisPtr().getOptional().assignTo(thisPtr)){
							BOOST_FOREACH(rose_addr_t bblockVa,constructor->basicBlockAddresses()){
								P2::BasicBlock::Ptr bblock = partitioner_.basicBlockContainingInstruction(bblockVa);
								// iterate over each instruction
								BOOST_FOREACH(SgAsmInstruction *instr,bblock->instructions()){
									SgAsmX86Instruction* current = isSgAsmX86Instruction(instr);
									// Look for instructions of the form: "mov [ecx+Y], offset xxx".
									if(current && x86_mov==current->get_kind() && defChain_.exists(instr)){
										BOOST_FOREACH(AbstractAccessPtr &def,defChain_[instr]->getaAcesList()){
											// checking if write is to this-ptr address
											if(def->getAloc()->isAddress()){
												BaseSemantics::SValuePtr writeAddr = def->getAloc()->getAddress();
												if(checkSValueEqual(writeAddr,thisPtr,solver_)){
													const BaseSemantics::SValuePtr& writeVal = def->getValue();
													// checking if the found vtable pointer is a defined number and lies in .rdata section of the specimen
													if(writeVal->is_number() && virtualTableRange.exists(writeVal->get_number()))
														addVtablePtr(writeVal->get_number(),object);
												}
											}
										}
									}
								}
							}
							// end
						}
						return ;
					}
				/* finding all the memory use of the class/object in the form of data member.
				 *  Algorithm:
				 *	foreach instr in function.instructions():
				 *		if instr is writing to a memory address referenced by the thisPtr+offset(>0) then:
				 *			add the offset and size of that write as the data member of the object
				 *		else if instr is reading from a memory address referenced by the thisPtr+offset(>0) then:
				 *			add the offset and size of that read as the data member of the object
				 *		else
				 *			continue
				 */
				bool
				    ExtractOOP::analyseForDataMembers(const P2::Function::Ptr &method,const BaseSemantics::SValuePtr &thisPtr,rose_addr_t thisPtrHash,
						    rose_addr_t maxClassSize){
					    bool retval = false;
					    classDetails::Ptr& object = thisPtrToClass[thisPtrHash];
					    FunctionSummaryPtr &funcSum = functionSummaries_[method];
					    SValuePtr thisptr = SValue::promote(thisPtr);
					    // iterating over each instruction of the function to find the data member
					    BOOST_FOREACH(rose_addr_t bblockVa,method->basicBlockAddresses()){
						    P2::BasicBlock::Ptr bblock = partitioner_.basicBlockContainingInstruction(bblockVa);
						    BOOST_FOREACH(SgAsmInstruction *instr,bblock->instructions()){
							    if(!defChain_.exists(instr)) continue;
							    BOOST_FOREACH(AbstractAccessPtr &def,defChain_[instr]->getaAcesList()){
								    if(def->getAloc()->isAddress()){
									    BaseSemantics::SValuePtr writeAddr = def->getAloc()->getAddress();
									    int32_t offset=0;
									    // checking if instr is writing to a memory address referenced by the thisPtr+offset(>0)
									    if(SValue::promote(writeAddr)->getOffset(thisptr,offset,solver_) && offset>=0 && offset<=maxClassSize){
										    SValuePtr writeVal = SValue::promote(def->getValue());
										    // adding the offset and size of that write as the data member of the object
										    classDetails::Member dataMember(offset,writeVal->get_width()/8);
										    object->addDataMember(dataMember,settings_.verbose);
										    // check for embeded object pointer
										    if(thisPtrToClass.exists(writeVal->get_expression()->hash())){
											    classDetails::Ptr &embededObject = thisPtrToClass[writeVal->get_expression()->hash()];
											    if(object->addEmbededObjectPointer(offset,embededObject)){
												    retval = true;
											    }
										    }
									    }
								    }
							    }
							    if(!useChain_.exists(instr)) continue;
							    BOOST_FOREACH(AbstractAccessPtr &use,useChain_[instr]->getaAcesList()){
								    if(use->getAloc()->isAddress()){
									    BaseSemantics::SValuePtr readAddr = use->getAloc()->getAddress();
									    int32_t offset=0;
									    // checking if instr is reading from a memory address referenced by the thisPtr+offset(>0)
									    if(SValue::promote(readAddr)->getOffset(thisptr,offset,solver_) && offset>=0 && offset<=maxClassSize ){
										    // adding the offset and size of that read as the data member of the object
										    classDetails::Member dataMember(offset,use->getValue()->get_width()/8);
										    object->addDataMember(dataMember,settings_.verbose);
									    }
								    }
							    }
						    }
					    }
					    return retval;
				    }

				/* checking for data member for each object by analysing the use of this-ptr as variable references in 
				 *  the methods connected to that particular object
				 */
				bool
					ExtractOOP::findAllDataMembers(){
						bool retval = false;
						BOOST_FOREACH(const P2::Function::Ptr &function,partitioner_.functions()){
							if(!functionSummaries_.exists(function)) continue;
							FunctionSummaryPtr &funcSum = functionSummaries_[function];
							BOOST_FOREACH(thisPtrHashMap::Node &node,funcSum->getUsedThisPtr().nodes()){
								const BaseSemantics::SValuePtr& thisptr = node.value();
								if(analyseForDataMembers(function,thisptr,node.key(),settings_.maxClassSize))
									retval = true;
							}
						}
						return retval;
					}

				// finds all the vtable pointers of all the classes found
				void
					ExtractOOP::findAllVtablePtrs(){
						BOOST_FOREACH(const P2::Function::Ptr &constructor , ObjectInfo.keys()){
							if(settings_.verbose)
								mlog[INFO]<<"Analysing class : "<<ObjectInfo[constructor]->getId()<<std::endl;
							findVirtualTable(constructor);
						}
					}

				// helper function
				void
					ExtractOOP::findAllOffestToFunction(SgAsmInstruction* instr,const P2::Function::Ptr &target,SValuePtr& thisptr,
							Sawyer::Container::Map<int32_t,P2::Function::Ptr>& offsetToFunction){
						BOOST_FOREACH(AbstractAccessPtr &use,useChain_[instr]->getaAcesList()){
							int32_t offset=0;
							// find all the function using this-ptr + offset in ECX as argument and 
							// store the offset corresponding to the function called
							if(use->getAloc()->isRegister() && use->getAloc()->getRegister()==REG_ECX && 
									SValue::promote(use->getValue())->getOffset(thisptr,offset,solver_) && offset>=0){
								// Hint for a Constructor
								offsetToFunction.insert(offset,target);
							}
						}
					}

				/* Main Algorithm to find all the inheritance of the object to which this constructor belongs to
				 *	If the child is overwriting the virtual table pointer of the parent class then its for sure that its parent of the child
				 *  otherwise we have to guess if its really the parent or the embeded object
				 * 
				 *  Algorithm:
				 *	foreach instr in function.instructions():
				 *		if instr is "call":
				 *			target = instr.findTargetfunction()
				 *			if target is constructor function:
				 *				add map from offset (of this-ptr+offset which is passed as this-ptr to parent class) to target in offsetToFunction map
				 *		else if instr is "mov [this+offset],XXX" where offset is already found in the offsetToFunction map:
				 *			if XXX is a known .rdata address then:
				 *				add XXX as the vtable-ptr to this object
				 *			add object corresponding to constructor corresponding to offset in offsetToFunction as the sure parent object if not exists 
				 *				then make a new one
				 *			offsetToFunction.erase(offset) // as we have already found constructor for this
				 *	foreach remaining in offsetToFunction:
				 *		Add each remaining constructor as the may be parent class/object // these objects could be either embeded objects or parent objects
				 *			
				 */
				void 
				    ExtractOOP::lookForInheritance(const P2::Function::Ptr &constructor){
					    FunctionSummaryPtr &funcSum = functionSummaries_[constructor];
					    BaseSemantics::SValuePtr inputECX;
					    // checking if we have this-ptr for this function
					    if(!funcSum->get_thisPtr().getOptional().assignTo(inputECX)) return;
					    SValuePtr thisptr = SValue::promote(inputECX);
					    // classDetail structure representing the object of the constructor
					    classDetails::Ptr &object = ObjectInfo[constructor];
					    if(settings_.verbose)
						    mlog[INFO]<<"Analyzing Class with id : "<<object->getId()<<std::endl;
					    // mapping consisting of the all the Constructors(as values) called from this constructor , keyed
					    // with the offset from the this-ptr of this object, which is passes as this-ptr to these parent
					    // class constructor as "this-ptr+offset(>0)"
					    Sawyer::Container::Map<int32_t,P2::Function::Ptr> offsetToFunction;
					    // iterating over all instructions
					    BOOST_FOREACH(rose_addr_t bblockVa,constructor->basicBlockAddresses()){
						    P2::BasicBlock::Ptr bblock = partitioner_.basicBlockContainingInstruction(bblockVa);
						    BOOST_FOREACH(SgAsmInstruction *instr,bblock->instructions()){
							    // Find calls to other constructors
							    SgAsmX86Instruction *current = isSgAsmX86Instruction(instr);
							    if(current && (x86_call==current->get_kind() || x86_farcall==current->get_kind())){
								    P2::Function::Ptr target = engine.GetTargetFunction(instr);
								    // check if the called function already found constructor or new found constructor
								    if( target){
									    // no need to check for contructor if we have already found it as constructor previously
									    if(ObjectInfo.exists(target)){
										    // find the "this-ptr+offset" passed to the target function from this-ptr.
										    findAllOffestToFunction(instr,target,thisptr,offsetToFunction);
									    }else if(functionSummaries_.exists(target) && thisCallsFunctions.find(target)!=thisCallsFunctions.end() ){
										    FunctionSummaryPtr &targetfuncSum = functionSummaries_[target];
										    if(targetfuncSum->getReturnECX() && useChain_.exists(instr))
											    // find the "this-ptr+offset" passed to the target function from this-ptr.
											    findAllOffestToFunction(instr,target,thisptr,offsetToFunction);
									    }
								    }
							    }else if(current && x86_mov==current->get_kind() && defChain_.exists(instr)){
								    // currently we can only say for sure if a particular class is parent class or not
								    // if the child class is overwriting the vtablePtr or not
								    BOOST_FOREACH(AbstractAccessPtr &def,defChain_[instr]->getaAcesList()){
									    if(def->getAloc()->isAddress()){
										    int32_t offset = 0;
										    SValuePtr writeAddr = SValue::promote(def->getAloc()->getAddress());
										    const BaseSemantics::SValuePtr& writeVal = def->getValue();
										    // check if XXX is a known .rdata section address range
										    if(writeAddr->getOffset(thisptr,offset,solver_) && offsetToFunction.exists(offset) &&
												    writeVal->is_number() && virtualTableRange.exists(writeVal->get_number())){
											    // add sureParent class/object to this class
											    P2::Function::Ptr &target = offsetToFunction[offset];
											    // if parent object already exists
											    if(ObjectInfo.exists(target)){
												    classDetails::Ptr &newObject = ObjectInfo[target];
												    // adds this newObject as the parent class of this class/object
												    object->addSureParentClass(offset,newObject,settings_.verbose);
												    // add new found vtable pointer to this class
												    addVtablePtr(writeVal->get_number(),object);
											    }else{
												    classDetails::Ptr newObject = classDetails::instance(totalClasses++,target,settings_.verbose);
												    ObjectInfo.insert(target,newObject);
												    // looking for the inheritance in the constructor
												    lookForInheritance(target);
												    // adds this newObject as the parent class of this class/object
												    object->addSureParentClass(offset,newObject,settings_.verbose);
												    // add new found vtable pointer to this class
												    addVtablePtr(writeVal->get_number(),object);
											    }
											    // as we have already found constructor for this
											    offsetToFunction.erase(offset);
										    }
									    }
								    }
							    }
						    }
					    }

					    // add rest of the class found as the maybe parent because its always possible that parent class
					    // has no virtual table to overwrite. and its difficult to differentiate between embeded object
					    // and real parent object only on the basis of dataflow as at the end it mayt end up as same
					    // on the dataflow level
					    BOOST_FOREACH(int32_t offset,offsetToFunction.keys()){
						    // add all the remaining to the may be Parent list
						    P2::Function::Ptr &target = offsetToFunction[offset];
						    if(ObjectInfo.exists(target)){
							    classDetails::Ptr &newObject = ObjectInfo[target];
							    if(!newObject->hasVtablePtr()){
								    object->addMayBeParentClass(offset,newObject,settings_.verbose);
							    }
							    else{
								    // if child doesn't overwrite the vtable ptr of the parent object which has vtableptr then its for
								    // sure that its an embeded object
								    object->addEmbededObject(offset,newObject,settings_.verbose);
							    }
						    }else{
							    classDetails::Ptr newObject = classDetails::instance(totalClasses++,target,settings_.verbose);
							    ObjectInfo.insert(target,newObject);
							    // looking for the inheritance in the constructor
							    lookForInheritance(target);
							    if(!newObject->hasVtablePtr()){
								    object->addMayBeParentClass(offset,newObject,settings_.verbose);
							    }
							    else{
								    // if child doesn't overwrite the vtable ptr of the parent object which has vtableptr then its for
								    // sure that its an embeded object
								    object->addEmbededObject(offset,newObject,settings_.verbose);
							    }
						    }
					    }
					    return;
				    }

				classDetails::Ptr
					ExtractOOP::checkForEmbeddedPointer(const BaseSemantics::SValuePtr &tocheck,FunctionSummaryPtr &currentSummary){
						classDetails::Ptr retval;
						SValuePtr checkAddr = SValue::promote(tocheck);
						BOOST_FOREACH(thisPtrHashMap::Node &node,currentSummary->getUsedThisPtr().nodes()){
							SValuePtr thisptr = SValue::promote(node.value());
							classDetails::Ptr thisClass = thisPtrToClass[thisptr->get_expression()->hash()];
							int32_t offset=0;
							if(checkAddr->getOffset(thisptr,offset,solver_) && offset>=0 && thisClass->hasEmbededObjectPointer(offset)){
								retval = thisClass->getEmbededObjectPointer(offset);
							}
						}
						return retval;
					}

				void
					ExtractOOP::rigorousClassBuildup(functionList &functionQueue){
						BOOST_FOREACH(const P2::Function::Ptr &function,partitioner_.functions()){
							if(!functionSummaries_.exists(function)) continue;
							FunctionSummaryPtr &funcSum = functionSummaries_[function];
							if(funcSum->isLibraryFunction()) continue;
							functionQueue.pushBack(function);
						}
						findClassMethods(functionQueue);
					}

				void
					ExtractOOP::extractAllObjects(){
						if(settings_.verbose)
							mlog[INFO]<<"Finding the methods following thiscall__ calling convention"<<std::endl;
						findThisCallFunctions();
						if(settings_.verbose)
							mlog[INFO]<<"Finding Object instances,this-ptrs,Methods,Contructors and inheritance "<<std::endl;
						functionList functionQueue;
						findHeapThisPtr(functionQueue);
						findStackThisPtr(functionQueue);
						if(settings_.verbose)
							mlog[INFO]<<"Finding Virtual Functions Tables "<<std::endl;
						findAllVtablePtrs();
						// finding the remainning functions
						followVirtualFunctions(functionQueue);
						buildfromClassMethods(functionQueue);
						findClassMethods(functionQueue);
						// Post Object methods extraction fixup - like remove parent class methods from child class
						postExtractionFixup();
						if(settings_.verbose)
							mlog[INFO]<<"Starting analysis of functions for Data Members"<<std::endl;
						while(findAllDataMembers()){
							rigorousClassBuildup(functionQueue);
						}
					}

				// prints all the classes found in yaml format
				void
					ExtractOOP::print(std::ostream &out){
						std::set<rose_addr_t> functions;
						YAML::Emitter emitter;
						emitter << YAML::BeginSeq;
						BOOST_FOREACH(classDetails::Ptr &object,ObjectInfo.values()){
							object->print(emitter,functions);
						}
						emitter << YAML::EndSeq;
						out<<emitter.c_str()<<std::endl;
						mlog[INFO]<< "Total Classes Found : "<<totalClasses<<" with a total of : "<<functions.size()<<" functions"<<std::endl;
					}

			} // namespace
		} // namespace
	} // namespace
} // namespace
