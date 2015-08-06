///
///     Written By: Shubham Bansal (illusionist.neo@gmail.com)
///     Copyright(c) Shubham Bansal (iN3O)
///     Blog :- http://in3o.me
///

#ifndef ROSE_Partitioner2_OOPEXTRACTANALYSIS_H
#define ROSE_Partitioner2_OOPEXTRACTANALYSIS_H


#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif

// Standard C++ libraries
#include <iostream>
#include <fstream>
#include <stringify.h>

// Standard Rose Library
#include <rose.h>
#include <rosePublicConfig.h>
#include <rose_strtoull.h>

// SAGE 3rd Party Library Library
#include "sage3basic.h"

// YAML C++ extension Library
#ifdef ROSE_HAVE_LIBYAML
#include <yaml-cpp/yaml.h>
#endif

// YICES SMT solver 3rd Party Library
#include <YicesSolver.h>
#include <yices_c.h>

// Rose's Assembly parsing, disassembling libraries
#include <AsmFunctionIndex.h>
#include <AsmUnparser.h>
#include <BinaryControlFlow.h>
#include <BinaryLoader.h>
#include <Disassembler.h>
#include <Diagnostics.h>

// Rose's new frontend library
#include <Partitioner2/GraphViz.h>
#include <Partitioner2/ModulesM68k.h>
#include <Partitioner2/ModulesPe.h>
#include <Partitioner2/Function.h>
#include <Partitioner2/Modules.h>
#include <Partitioner2/Utility.h>
#include <Partitioner2/Engine.h>
#include <Partitioner2/ControlFlowGraph.h>
#include <Partitioner2/Partitioner.h>
#include <Partitioner2/FunctionCallGraph.h>
#include <Partitioner2/Config.h>

// Sawyer 3rd Party library 
// Used instead of Standard C++ Boost Library
// because of better interface and API's required here
#include <Sawyer/GraphTraversal.h>
#include <Sawyer/Assert.h>
#include <Sawyer/CommandLine.h>
#include <Sawyer/ProgressBar.h>
#include <Sawyer/Stopwatch.h>

// Boost 3rd party library
#include <boost/filesystem.hpp>

// Rose's different semantics library
#include <SymbolicSemantics2.h>
#include <InsnSemanticsExpr.h>
#include <BaseSemantics2.h>
#include <TestSemantics2.h>

// Modules Written By me to do dataFlow analysis
// and other stuff to deduce the OOP classes
#include <ClassSemantics.h>
#include <OopExtractAnalysis.h>
#include <Engine.h>

using namespace rose::BinaryAnalysis;
using namespace Sawyer::Message::Common;
using namespace Sawyer::Container::Algorithm;
namespace IS2 = InstructionSemantics2;

#define ARBITRARY_PARAM_LIMIT 60

namespace rose {
	namespace BinaryAnalysis {
		namespace Partitioner2 {
			namespace ClassSemantics {

				/* Main Algorithm to Extract Object Oriented Structure from the calculated def-use chain
				*  
				*  - All the information about the classes/objects are stored in the classDetail structure
				*/
				using namespace Sawyer::Container::Algorithm;

				// Object class representing the information about the class/objects
				class classDetails: public Sawyer::SharedObject {
					public:
						typedef Sawyer::SharedPointer<classDetails> Ptr;
						typedef std::pair<rose_addr_t,rose_addr_t> Member;
						typedef Sawyer::Container::Map<rose_addr_t,Ptr> offsetToParent;
					protected:
						rose_addr_t id_;											// a unique id for each class
						std::set<Partitioner2::Function::Ptr> classMethods;			// set of all class methods
						std::set<rose_addr_t> thisptrs;								// set of hash of all thisPtrs
						std::set<rose_addr_t> vtablePtrs;							// set of all virtual table pointers
						offsetToParent sureParentClasses;							// pointers to all the class which are surely a parent class
						offsetToParent mayBeParentClasses;							// pointers to all the class which are either a parent class or an embeded class
						offsetToParent embededObjects;								// pointers to all the class which are embeded objects for sure
						std::set<Partitioner2::Function::Ptr> Constructor;			// set of all constructors found
						std::set<rose_addr_t> virtualFunctions;						// pointers to all the virtual function found
						std::set<SgAsmInstruction*> instances;						// set of all the instruction where(or very near) all the instances are initialised
						offsetToParent embededObjectsPointer;				// embedded object pointers
						std::set< Member > dataMembers;								/* data members in the form of <offset,size> where offset represent the offset of 
																					 data member from the starting address of the thisPtr. and size represents the size of it*/

					protected:
						// Real Constructor 
						explicit classDetails(rose_addr_t id,const Partitioner2::Function::Ptr &constructor,bool verbose=false):id_(id){
							if(Constructor.insert(constructor).second && verbose){
								mlog[INFO]<<"Found new class with id "<<id_<<" : with constructor at address : "<<
									StringUtility::intToHex(constructor->address())<<std::endl;
							}
						}

					public:
						// Static allocating constructors
						static Ptr instance(rose_addr_t id,const Partitioner2::Function::Ptr &constructor,bool verbose=false){
							return Ptr(new classDetails(id,constructor,verbose));
						}

					public:
						// adds the method "funtion" to this class instance as a class method
						virtual void addClassMethods(const Partitioner2::Function::Ptr &function,bool verbose=false){
							// donot include function as the class method if the function is the constructor of the class
							if(Constructor.find(function)==Constructor.end() && classMethods.insert(function).second){
								if(verbose)
									mlog[INFO]<<"Found new class("<<id_<<") method : "<<StringUtility::intToHex(function->address())<<std::endl;
							}
						}

						// adds this-ptr hash to the class if not already exists
						virtual void addThisPtr(rose_addr_t to_add,bool verbose=false){
							if(thisptrs.insert(to_add).second && verbose)
								mlog[INFO]<<"Found new this-ptr for class : "<<id_<<std::endl;
						}

						// adds virtual function to the class if not already existing
						virtual void addVirtualFunction(rose_addr_t to_add,bool verbose=false){
							if(virtualFunctions.insert(to_add).second){
								if(verbose)
									mlog[INFO]<<"Found Virtual Function : "<<StringUtility::intToHex(to_add)<<" in Virtual Function table "<<std::endl;
							}
						}

						// adds vtable pointer(lies in .rodata section) to the class and use it to find all the virtual function pointers 
						// which lies in the.text Section of the Code.
						virtual bool addVtablePtr(rose_addr_t vtptr);

						// adds contructor to the class if not already exists
						virtual void addConstructor(const Partitioner2::Function::Ptr &function,bool verbose=false){
							if(Constructor.insert(function).second){
								if(verbose)
									mlog[INFO]<<"Got constructor"<<"for class :"<<id_<<" : "<<" at address "<<
										StringUtility::intToHex(function->address())<<std::endl;
							}
						}

						// adds data member to the class
						virtual void addDataMember(Member &data,bool verbose=false){
							// checking if the data member is this-ptr of the parent class or not , if it is then we ignore it
							if(!sureParentClasses.exists(data.first) && !mayBeParentClasses.exists(data.first) && 
								dataMembers.insert(data).second ){
								if(verbose)
									mlog[INFO]<<"Found a data member at offset : "<<StringUtility::numberToString(data.first)<<
										" of Size : "<<StringUtility::numberToString(data.second)<<std::endl;
							}
						}

						// return this pointers of the class
						virtual const std::set<rose_addr_t>& getThisPtrs(){
							return thisptrs;
						}

						// returns set of all function pointers of this class
						virtual const std::set<Partitioner2::Function::Ptr>& getClassMethods(){
							return classMethods;
						}

						// returns all the virtual functions of this class
						virtual const std::set<rose_addr_t>& getVirtualFunctions(){
							return virtualFunctions;
						}

						// returns the contructor of this class
						virtual const std::set<Partitioner2::Function::Ptr>& getConstructors(){
							return Constructor;
						}

						// checks if this function has virtual table or not
						virtual bool hasVtablePtr(){
							return vtablePtrs.size()>0;
						}

						// adds a class as Sure parent class if not already exists
						virtual void addSureParentClass(rose_addr_t offset,Ptr &other,bool verbose=false){
							if(!sureParentClasses.exists(offset)){
								sureParentClasses.insert(offset,other);
								if(verbose)
									mlog[INFO]<<"Found new Sure Parent of class : "<<id_<<" i.e class : "<<other->getId()<<
										" at offset : "<<offset<<std::endl;
							}
						}

						// adds a class as MayBe parent class or embeded class
						virtual void addMayBeParentClass(rose_addr_t offset,Ptr &other,bool verbose=false){
							if(!mayBeParentClasses.exists(offset)){
								mayBeParentClasses.insert(offset,other);
								if(verbose)
									mlog[INFO]<<"Found new MayBe Parent of class : "<<id_<<" i.e class : "<<other->getId()<<
										" at offset : "<<offset<<std::endl;
							}
						}

						// adds embeded object to the class
						virtual void addEmbededObject(rose_addr_t offset,Ptr &other,bool verbose=false){
							if(!embededObjects.exists(offset)){
								embededObjects.insert(offset,other);
								if(verbose)
									mlog[INFO]<<"Found new embeded object in class :"<<id_<<" i.e class : "<<other->getId()<<
										" at offset : "<<offset<<std::endl;
							}
						}

						// returns the id of the class
						virtual rose_addr_t getId(){
							return id_;
						}

						// adds an instance instruction to the class , if not already exists
						virtual void addInstance(SgAsmInstruction* instance,bool verbose=false){
							if(instances.insert(instance).second){
								if(verbose)
									mlog[INFO]<<"Found new instance at : "<<StringUtility::intToHex(instance->get_address())<<std::endl;
							}
						}

						// checks if the function is the constructor of this class/object or not
						virtual bool isConstructor(const Partitioner2::Function::Ptr &function){
							if(Constructor.find(function)!=Constructor.end())
								return true;
							return false;
						}

						// checks if the function is a method of this class/object or not
						virtual bool isClassMethod(const Partitioner2::Function::Ptr &function){
							if(classMethods.find(function)!=classMethods.end())
								return true;
							return false;
						}

						// checks if the function is one of the virtual function of this class/object or not
						virtual bool isVirtualMethod(rose_addr_t functionAddr){
							if(virtualFunctions.find(functionAddr)!=virtualFunctions.end())
								return true;
							return false;
						}

						// deletes a class methods from the set of all the class methods of this class/object
						virtual void deleteClassMethod(const Partitioner2::Function::Ptr &function){
							classMethods.erase(function);
						}

						// deletes a virtual function from the set of all the virtual functions of this class/object
						virtual void deleteVirtualMethod(rose_addr_t functionAddr){
							virtualFunctions.erase(functionAddr);
						}

						// returns the set of all the sure Parent classes of this class/Object
						virtual const offsetToParent& getSureParentClasses(){ return sureParentClasses; }

						// returns the set of all the may be Parent classes of this class/Object
						virtual const offsetToParent& getMayBeParentClasses(){ return mayBeParentClasses; }

						virtual const offsetToParent& getEmbededClasses(){ return embededObjects; }

						virtual bool addEmbededObjectPointer(rose_addr_t offset,Ptr &other);

						virtual bool hasEmbededObjectPointer(rose_addr_t offset){
							if(embededObjectsPointer.exists(offset))
								return true;
							return false;
						}

						virtual Ptr getEmbededObjectPointer(rose_addr_t offset){
							return embededObjectsPointer[offset];
						}

						// prints the output in yaml format
						virtual void print(YAML::Emitter &out,std::set<rose_addr_t>& functions);
				};


				class ExtractOOP{
				public:
					typedef std::set<Partitioner2::Function::Ptr> functionSet;
					typedef Sawyer::Container::Map<Partitioner2::Function::Ptr,classDetails::Ptr> classMap;
					typedef Sawyer::Container::Map<rose_addr_t,classDetails::Ptr> thisPtrMap;
					typedef Sawyer::Container::Map<SgAsmInstruction*,BaseSemantics::SValuePtr> InstToESP;
					typedef Sawyer::Container::DistinctList<Partitioner2::Function::Ptr> functionList;
					typedef Sawyer::Container::Map<rose_addr_t,BaseSemantics::SValuePtr> thisPtrHashMap;
				protected:
					Engine &engine;														// DataFlow dependency builder Engine
					Engine::ReachingMap &useChain_,&defChain_;							// Use chain & Def Chain
					Engine::DependingMap &depOnChain_,&depOfChain_;						// Dependent On and Dependent Of chain
					Engine::summaryMap &functionSummaries_;								// function summaries map keyed with function pointer
					const Partitioner2::Partitioner &partitioner_;						// partitioner
					RegisterDescriptor REG_EAX,REG_ESP,REG_EIP,REG_ECX,REG_SS,REG_EDX;	// cached registers
					const RegisterDictionary *regdict;									// X86 Register Dictionary
					SMTSolver *solver_;													// SMT Solver
					const BaseSemantics::DispatcherPtr &cpu_;							// Dispatcher for corresponding architechture(currently its x86)
					functionSet thisCallsFunctions;										// all the functions following thiscall_ calling convention
					classMap ObjectInfo;												// Class/Object info mapped with the constructor of the correspoding class
					thisPtrMap thisPtrToClass;											// Class/Object info mapped with the hashes of the the correspoding thisPtrs
					rose_addr_t totalClasses;											// total numbers of classes found
					Settings &settings_;												// Settings
					const BaseSemantics::RiscOperatorsPtr &ops_;						// RISC Operator
					const InstToESP& callESP_;											// ESP value corresponding to the call instruction
					AddressIntervalSet virtualTableRange;								// set of address interval where virtual tables is found
					AddressIntervalSet staticDataRange;									// range of address where static object belongs to
					AddressIntervalSet textSectionRange;								// all the functions lies in this address range

				public:
					// Real Constrcutor
					ExtractOOP(const Partitioner2::Partitioner &partitioner,const BaseSemantics::DispatcherPtr &cpu,Engine &engine_,const BaseSemantics::RiscOperatorsPtr &ops,
						Settings &settings,SMTSolver* solver=NULL):useChain_(engine_.useChain),defChain_(engine_.defChain),depOnChain_(engine_.depOfChain),depOfChain_(engine_.depOfChain),
						partitioner_(partitioner),functionSummaries_(engine_.functionSummaries),cpu_(cpu),solver_(solver),totalClasses(0),engine(engine_),ops_(ops),settings_(settings),
						callESP_(engine_.callESP){
							REG_ESP = cpu_->findRegister("esp");
							REG_EAX = cpu_->findRegister("eax");
							REG_EIP = cpu_->findRegister("eip");
							REG_ECX = cpu_->findRegister("ecx");
							REG_SS =cpu_->findRegister("ss");
							REG_EDX = cpu_->findRegister("edx");
							regdict = cpu_->get_register_dictionary();
						}

				public:

					// finds all the instances of each class/object, initiated by the "new" library call
					virtual void findHeapThisPtr(functionList &functionQueue);  // 1st Pass

					// find all the functions following thiscall__ calling convention
					virtual void findThisCallFunctions();

					virtual void addVtablePtr(rose_addr_t vtptr,classDetails::Ptr &object);

					virtual void setStaticDataRange(SgAsmInterpretation* interp);

					virtual void setTextSectionRange(SgAsmInterpretation* interp);

					// find all the cross reference to a particular function
					virtual std::vector<SgAsmInstruction*> findCrossReferences(const Partitioner2::Function::Ptr &function );

					// sets the address range representing the .rdata section in the binary
					// it is used to find if the virtual table pointer lies in the .rdata section or not
					virtual void setrdataAddressRange(SgAsmInterpretation* interp);

					// this function does all the post object extracting fixing like :
					// - removing parent class methods and constructor from child class methods
					// - removing parent class virtual functions from child class virtual functions
					// - [TO DO] removing parent class data members from the child class data members
					virtual void postExtractionFixup();

					// find the contructor and add new class representing that constructor
					virtual bool addUniqueClass(const Partitioner2::Function::Ptr &xreffunction,Partitioner2::Function::Ptr &constructor,SgAsmInstruction* xref,
						std::set<rose_addr_t>& thisPtrs);

					// find all the class method corresponding to all the new this-ptr found
					virtual void findClassMethods(functionList& functionQueue);

					// find all the virtual function table
					virtual void findVirtualTable(const Partitioner2::Function::Ptr &constructor);

					virtual void parentMethodFixUp(const classDetails::offsetToParent& parents,classDetails::Ptr &childObject);

					virtual bool checkForConstructorCall(SgAsmInstruction* insn,const Partitioner2::Function::Ptr &constructor,std::set<rose_addr_t>& thisPtrs);

					virtual void checkForStackObject(SgAsmInstruction* instr,SValuePtr& inputESP,const Partitioner2::Function::Ptr &function,functionList &functionQueue,
							std::set<rose_addr_t>& usedStkVar);

					virtual void findAllOffestToFunction(SgAsmInstruction* instr,const Partitioner2::Function::Ptr &target,SValuePtr& thisptr,
						Sawyer::Container::Map<int32_t,Partitioner2::Function::Ptr>& offsetToFunction);

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
					virtual void addThisPtr(const BaseSemantics::SValuePtr &thisptr,classDetails::Ptr &object,const Partitioner2::Function::Ptr& xreffunction);

					// various methods to add this pointers or this-ptrs hash to the class
					virtual void addThisPtrs(std::vector<BaseSemantics::SValuePtr>& to_add,classDetails::Ptr &object,const Partitioner2::Function::Ptr& xreffunction);

					virtual void checkForReturnExist(const Partitioner2::Function::Ptr function,functionList& functionQueue);

					// return the map representing object information
					virtual const classMap& getObjectInfo(){
						return ObjectInfo;
					}

					virtual void extractAllObjects();

					virtual bool analyseForDataMembers(const Partitioner2::Function::Ptr &method,const BaseSemantics::SValuePtr &thisPtr,rose_addr_t thisPtrHash,
						rose_addr_t maxClassSize);

					virtual void lookForInheritance(const Partitioner2::Function::Ptr &constructor);

					virtual void buildFromFunction(const Partitioner2::Function::Ptr &function,classDetails::Ptr &object,functionList &functionQueue);

					virtual bool isCallInstruction(SgAsmInstruction* insn);

					virtual void buildfromClassMethods(functionList &functionQueue);

					virtual void followVirtualFunctions(functionList &functionQueue);

					virtual bool findAllDataMembers();

					virtual void findAllVtablePtrs();

					virtual void findStackThisPtr(functionList &functionQueue);

					virtual void print(std::ostream &out);

					virtual void rigorousClassBuildup(functionList &functionQueue);

					virtual classDetails::Ptr checkForEmbeddedPointer(const BaseSemantics::SValuePtr &tocheck,FunctionSummaryPtr &currentSummary);
				};

				} // namespace
			} // namespace
		} // namespace
	} // namespace

#endif