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


/* Exclusive namespace InterDataFlow for Inter-Procedural DataFlow Analysis */
namespace rose {
	namespace BinaryAnalysis {
		namespace Partitioner2 {
			namespace ClassSemantics {

				// Return CFG basic block vertex that contains specified instruction address, or the end vertex if none found.
				Sawyer::Optional<rose_addr_t>
					addressForFunction(const Partitioner &partitioner, const std::string &nameOrVa) {
						const char *s = nameOrVa.c_str();
						char *rest;
						errno = 0;
						rose_addr_t va = rose_strtoull(s, &rest, 0);
						if (*rest || errno!=0) {
							size_t nFound = 0;
							BOOST_FOREACH (const Function::Ptr &function, partitioner.functions()) {
								if (function->name() == nameOrVa) {
									va = function->address();
									++nFound;
								}
							}
							if (0==nFound)
								return Sawyer::Nothing();
							if (nFound > 1)
								throw std::runtime_error("vertex \""+StringUtility::cEscape(nameOrVa)+"\" is ambiguous");
						}
						return va;
					}

				// checks for the equality of the two symbolic value and give exception when SMTsolver can't solve the equation
				bool 
					checkSValueEqual(const BaseSemantics::SValuePtr &a_,const BaseSemantics::SValuePtr &b_,SMTSolver *solver){
						try{
							if(a_->get_width()==b_->get_width() && a_->must_equal(b_,solver))
								return true;
						}catch(const SMTSolver::Exception &e){
							mlog[WARN]<<"Got SMTSolver exception - "<<e<<std::endl;
						}
						return false;
					}

				// BBlock building handler - Called each time a new BBlock is detected
				bool
					PePrivilege::operator()(bool chain,const Args &args) {
						SgAsmInstruction *insn = args.bblock->instructions().back();
						SgAsmX86Instruction *intx = isSgAsmX86Instruction(insn);

						// Correcting the CFG after instructions like intx - generally its unknown but we are branching
						// to the next instruction/fall through instruction in continuous
						if(chain && intx && (intx->get_kind()==x86_int3 || intx->get_kind()==x86_int) ){
							if(verbose_)
								mlog[INFO]<<"Changing cfg at : "<<StringUtility::intToHex(args.bblock->address())<<std::endl;
							args.bblock->successors().clear();
							rose_addr_t fallthroughVa = insn->get_address() + insn->get_size();
							args.bblock->insertSuccessor(fallthroughVa,args.partitioner.instructionProvider().instructionPointerRegister().get_nbits());
						}
						return chain;
					}

				// Library Call thunk Fixup handler
				void
					libraryThunkFixups(const Partitioner &partitioner, SgAsmInterpretation *interp){
						if (interp==NULL)
							return;

						std::vector<Function::Ptr> functions = partitioner.functions();

						// Get the addresses for the PE Import Address Tables
						AddressIntervalSet iatExtent;
						BOOST_FOREACH (SgAsmGenericHeader *fileHeader, interp->get_headers()->get_headers()) {
							SgAsmGenericSectionPtrList iatSections = fileHeader->get_sections_by_name("Import Address Table");
							BOOST_FOREACH (SgAsmGenericSection *section, iatSections) {
								if (section->get_id()==-1 && section->is_mapped())
									iatExtent.insert(AddressInterval::baseSize(section->get_mapped_actual_va(), section->get_mapped_size()));
							}
						}

						// Build an index that maps addresses to entries in the import tables. The addresses are the addresses where the imported
						// functions are expected to be mapped.
						ModulesPe::ImportIndex importIndex = ModulesPe::getImportIndex(partitioner, interp);

						// Process each function that's attached to the CFG/AUM
						BOOST_FOREACH (const Function::Ptr &function, functions) {
							if (function->basicBlockAddresses().size()!=1)
								continue; // thunks have only one basic block...

							BasicBlock::Ptr bblock = partitioner.basicBlockExists(function->address());
							ASSERT_not_null(bblock);
							if (bblock->nInstructions()==2){
								SgAsmInstruction *insn1 = bblock->instructions()[0];
								SgAsmInstruction *insn2 = bblock->instructions()[1];
								SgAsmX86Instruction *jmp = isSgAsmX86Instruction(insn1);

								// addr1:  JMP addr2
								if(!jmp || jmp->get_kind()!=x86_jmp)
									continue;
								const SgAsmExpressionPtrList &jmpArgs = jmp->get_operandList()->get_operands();
								if(jmpArgs.size()!=1)
									continue;
								SgAsmConstantExpression *jmpArg0 = isSgAsmConstantExpression(jmpArgs[0]);
								if(!jmpArg0)
									continue;

								// addr2: JMP DS:address3
								SgAsmX86Instruction *jmp_ = isSgAsmX86Instruction(insn2);
								if(!jmp_ || jmp_->get_kind()!=x86_jmp)
									continue;
								const SgAsmExpressionPtrList &jmpArgs_ = jmp_->get_operandList()->get_operands();
								if(jmpArgs_.size()!=1)
									continue;
								SgAsmMemoryReferenceExpression *jmpArg0_ = isSgAsmMemoryReferenceExpression(jmpArgs_[0]);
								SgAsmIntegerValueExpression *argValue = jmpArg0_ ? isSgAsmIntegerValueExpression(jmpArg0_->get_address()) : NULL;

								// checking if address3 lies in IAT address range
								if(!argValue || !iatExtent.contains(argValue->get_absoluteValue()))
									continue;

								// checking if the successor block is Concrete or not
								bool isComplete = true;
								std::vector<rose_addr_t> successors = partitioner.basicBlockConcreteSuccessors(bblock, &isComplete);
								if (!isComplete || successors.size()!=1)
									continue; // ...and the JMP has a single successor that is concrete...
								SgAsmPEImportItem *importItem = NULL;
								if (!importIndex.getOptional(successors.front()).assignTo(importItem))
									continue; 

								// Merge the new name into the function
								if(function->name().empty()){
									std::string importName = importItem->get_name()->get_string();
									SgAsmPEImportDirectory *importDir = SageInterface::getEnclosingNode<SgAsmPEImportDirectory>(importItem);
									if (importDir && !importDir->get_dll_name()->get_string().empty())
										importName += "@" + importDir->get_dll_name()->get_string();
									function->name(importName);
								}
								function->insertReasons(SgAsmFunction::FUNC_THUNK | SgAsmFunction::FUNC_IMPORT);
							}
						}
					}

				AddressIntervalSet
					getSectionRangeByName(SgAsmInterpretation *interp,std::string sectionName){
						AddressIntervalSet retval;
						BOOST_FOREACH (SgAsmGenericHeader *fileHeader, interp->get_headers()->get_headers()){
							SgAsmGenericSectionPtrList querySections = fileHeader->get_sections_by_name(sectionName);
							BOOST_FOREACH (SgAsmGenericSection *section, querySections) {
								if (section->is_mapped() && section->get_short_name()==sectionName)
									retval.insert(AddressInterval::baseSize(section->get_mapped_actual_va(), section->get_mapped_size()));
							}
						}
						return retval;
					}

				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				////////////////////////		CallSemantics::SValue - New Symbolic Value class 						//////////////////////
				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

				size_t
					SValue::add_modifying_instructions(const InsnSet &to_add)
					{
						size_t nadded = 0;
						for (InsnSet::const_iterator i=to_add.begin(); i!=to_add.end(); ++i) {
							std::pair<InsnSet::iterator, bool> inserted = modifiers.insert(*i);
							if (inserted.second)
								++nadded;
						}
						return nadded;
					}

				size_t
					SValue::add_modifying_instructions(SgAsmInstruction *insn)
					{
						InsnSet tmp;
						if (insn)
							tmp.insert(insn);
						return add_modifying_instructions(tmp);
					}

				void
					SValue::set_modifying_instructions(SgAsmInstruction *insn)
					{
						InsnSet tmp;
						if (insn)
							tmp.insert(insn);
						return set_modifying_instructions(tmp);
					}

				// Prints the modifiers of the symbolic value and the expression representing that symbolic value
				void
					SValue::print(std::ostream &stream, BaseSemantics::Formatter &formatter_) const
					{
						SymbolicSemantics::Formatter *formatter = dynamic_cast<SymbolicSemantics::Formatter*>(&formatter_);
						InsnSemanticsExpr::Formatter dflt_expr_formatter;
						InsnSemanticsExpr::Formatter &expr_formatter = formatter ? formatter->expr_formatter : dflt_expr_formatter;
						if (modifiers.empty()) {
							stream <<(*expr + expr_formatter);
						} else {
							stream <<"{modifiers={";
							size_t nmods =0;
							for (InsnSet::const_iterator mi=modifiers.begin(); mi!=modifiers.end(); ++mi, ++nmods) {
								SgAsmInstruction *insn = *mi;
								if (insn!=NULL)
									stream <<(nmods>0?",":"") <<StringUtility::addrToString(insn->get_address());
							}
							stream <<"}, expr="; expr->print(stream,expr_formatter); stream<<"}";
						}
					}

				// especially written function to find the offset between two symbolic value
				// Very poor but doesn't effect much to our analysis
				bool
					SValue::getOffset(SValuePtr &other,int32_t &offset,SMTSolver *solver){
						using namespace InsnSemanticsExpr;
						const TreeNodePtr& baseExpr = other->get_expression();

						// checking for 0 offset
						if(expr->must_equal(baseExpr,solver)){
							offset = 0;
							return true;
						}else{
							//  This currently handles two Cases :-
							//					SValue1		SValue2			Result
							//		Case 1 ->  	var1 		var1 + xx   	xx
							//		Case 2 -> 	var1 + xx	var1 + yy		yy - xx
							InternalNodePtr baseParentNode = baseExpr->isInternalNode();
							LeafNodePtr variable1 = baseExpr->isLeafNode();
							LeafNodePtr constant1 = LeafNode::create_integer(baseExpr->get_nbits(),0);
							// this if condition calculates the base expression
							if(baseParentNode && baseParentNode->nchildren()==2 && baseParentNode->get_operator()==OP_ADD){
								variable1 = baseParentNode->child(0)->isLeafNode();
								constant1 = baseParentNode->child(1)->isLeafNode();
								if(!constant1 || !constant1->is_known())
									std::swap(variable1,constant1);
								if (!constant1 || !constant1->is_known())
									return false;
							}
							// this if condition calculates the offset and return true if found, otherwise false
							// and also return the offset in call-by-reference argument offset
							InternalNodePtr parentNode = expr->isInternalNode();
							if(variable1 && parentNode && parentNode->nchildren()==2 && parentNode->get_operator()==OP_ADD){
								LeafNodePtr variable2 = parentNode->child(0)->isLeafNode();
								LeafNodePtr constant2 = parentNode->child(1)->isLeafNode();
								if(!constant2 || !constant2->is_known())
									std::swap(variable2,constant2);
								if (!constant2 || !constant2->is_known() || !variable1->must_equal(variable2, solver))
									return false;
								offset = (int32_t)constant2->get_value() - (int32_t)constant1->get_value();
								return true;
							}
						}
						return false;
					}
				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				////////////////////////								MemoryState 									//////////////////////
				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

				// reads the memory byte by byte
				BaseSemantics::SValuePtr
					MemoryState::readMemory(const BaseSemantics::SValuePtr &address_, const BaseSemantics::SValuePtr &dflt,
							BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps)
					{
						size_t nbits = dflt->get_width();
						SValuePtr address = SValue::promote(address_);
						ASSERT_require(8==nbits); // SymbolicSemantics::MemoryState assumes that memory cells contain only 8-bit data
						bool short_circuited;
						CellList matches = scan(address, nbits, addrOps, valOps, short_circuited/*out*/);
						// If we fell off the end of the list then the read could be reading from a memory location for which no cell exists.
						if (!short_circuited) {
							BaseSemantics::MemoryCellPtr tmpcell = protocell->create(address, dflt);
							// adds unknown/new found memory address cell to the memory map keyed with the hash of the address expression
							allCells.insert(address->get_expression()->hash(),tmpcell);
							cells.push_back(tmpcell);
							matches.push_back(tmpcell);
						}
						ASSERT_require(dflt->get_width()==nbits);
						BaseSemantics::SValuePtr retval = get_cell_compressor()->operator()(address, dflt, addrOps, valOps, matches);
						ASSERT_require(retval->get_width()==8);
						return retval;
					}

				// writes to memory byte by byte
				void
					MemoryState::writeMemory(const BaseSemantics::SValuePtr &address, const BaseSemantics::SValuePtr &value,
							BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps)
					{
						ASSERT_require(8==value->get_width());
						ASSERT_not_null(address);
						MemoryCellPtr newCell = protocell->create(address, value);
						SValuePtr addr = SValue::promote(address);
						rose_addr_t newHash = addr->get_expression()->hash();
						// Prune away all cells that must-alias this new one since they will be occluded by this new one.
						if (occlusionsErased_) {
							allCells.erase(newHash);
						}
						// Insert the new cell to the memory map keyed with the new hash and valued with the memorycell pointer
						allCells.insert(newHash,newCell);
						cells.push_back(newCell);
						latest_written_cell = newCell;
					}

				// scans for all the MemoryCell which clashes with address range
				MemoryState::CellList
					MemoryState::scan(const BaseSemantics::SValuePtr &addr, size_t nbits, BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps,
							bool &short_circuited/*out*/)
					{
						ASSERT_not_null(addr);
						short_circuited = false;
						CellList retval;
						MemoryCellPtr to_add;
						for (size_t bytenum=0; bytenum<nbits/8; ++bytenum) {
							SValuePtr newAddr = SValue::promote( valOps->add(addr,valOps->number_(addr->get_width(),bytenum) ) );
							if(allCells.getOptional(newAddr->get_expression()->hash()).assignTo(to_add))
								retval.push_back(to_add);
						}
						if(retval.size()==(nbits/8))
							short_circuited = true;
						return retval;
					}

				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
				////////////////////////							RiscOperator 										//////////////////////
				//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

				void
					RiscOperators::addModifiers(SValuePtr &value){
						if(compute_useDefChain && cur_insn)
							value->modified_by(cur_insn);
					}

				BaseSemantics::SValuePtr
					RiscOperators::extract(const BaseSemantics::SValuePtr &a_, size_t begin_bit, size_t end_bit)
					{
						SValuePtr retval = SValue::promote(SymbolicSemantics::RiscOperators::extract(a_,begin_bit,end_bit));
						SValuePtr a = SValue::promote(a_);

						// calculates the modifier instruction if asked for calculating the def-use chain
						if (compute_useDefChain)
							retval->modified_by(a->get_modifying_instructions());
						return retval;
					}

				BaseSemantics::SValuePtr
					RiscOperators::concat(const BaseSemantics::SValuePtr &lo_bits_, const BaseSemantics::SValuePtr &hi_bits_)
					{
						SValuePtr retval = SValue::promote(SymbolicSemantics::RiscOperators::concat(lo_bits_,hi_bits_));
						SValuePtr lo = SValue::promote(lo_bits_);
						SValuePtr hi = SValue::promote(hi_bits_);
						// calculates the modifier instruction if asked for calculating the def-use chain
						if (compute_useDefChain)
							retval->modified_by(lo->get_modifying_instructions(),hi->get_modifying_instructions());
						return retval;
					}

				// Currently checking for some particular identity instructions
				// will add for more check if found
				bool
					RiscOperators::checkIdentityInstr(SgAsmInstruction *instr,const RegisterDescriptor &reg){
						SgAsmX86Instruction *current = isSgAsmX86Instruction(instr);
						if(current->get_kind()==x86_xor){
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmDirectRegisterExpression *Reg2 = isSgAsmDirectRegisterExpression(Args[1]);
								if(Reg1 && Reg2 && Reg1->get_descriptor()==Reg2->get_descriptor() && reg==Reg1->get_descriptor())
									return true;
							}
						}else if(current->get_kind()==x86_sub){
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmDirectRegisterExpression *Reg2 = isSgAsmDirectRegisterExpression(Args[1]);
								if(Reg1 && Reg2 && Reg1->get_descriptor()==Reg2->get_descriptor() && reg==Reg1->get_descriptor() )
									return true;
							}
						}else if(current->get_kind()==x86_mov){
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmDirectRegisterExpression *Reg2 = isSgAsmDirectRegisterExpression(Args[1]);
								if(Reg1 && Reg2 && Reg1->get_descriptor()==Reg2->get_descriptor() && reg==Reg1->get_descriptor())
									return true;
							}
						}else if(current->get_kind()==x86_and){
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmIntegerValueExpression *argValue = isSgAsmIntegerValueExpression(Args[1]);
								if(Reg1 && argValue && argValue->get_absoluteValue()==0xffffffff && reg==Reg1->get_descriptor() )
									return true;
							}
						}else if(current->get_kind()==x86_or){
							const SgAsmExpressionPtrList &Args = current->get_operandList()->get_operands();
							if(Args.size()==2){
								SgAsmDirectRegisterExpression *Reg1 = isSgAsmDirectRegisterExpression(Args[0]);
								SgAsmIntegerValueExpression *argValue = isSgAsmIntegerValueExpression(Args[1]);
								if(Reg1 && argValue && argValue->get_absoluteValue()==0x0 && reg==Reg1->get_descriptor())
									return true;
							}
						}
						return false;
					}

				// Reads Register Value - However, it completely relies on the underlying SymbolicSemantics::RiscOperator to read the register
				// we just catch the value read and from where it was read to build the def-use chain
				BaseSemantics::SValuePtr 
					RiscOperators::readRegister(const RegisterDescriptor &reg) ROSE_OVERRIDE{
						BaseSemantics::SValuePtr retval = SymbolicSemantics::RiscOperators::readRegister(reg);

						// checks for identity instruction to skip instruction which creates un-necessary dependecies in def-use chain
						if(get_insn() && !checkIdentityInstr(get_insn(),reg) && compute_useDefChain)
							addRegsAndMemRead(retval,reg);
						return retval;
					}

				// Writes Values to Register - However, it completely relies on the underlying SymbolicSemantics::RiscOperator to write to the register
				// we just catch the value written and to where it was written to build the def-use chain
				void 
					RiscOperators::writeRegister(const RegisterDescriptor &reg, const BaseSemantics::SValuePtr &a_) ROSE_OVERRIDE{
						SValuePtr a = SValue::promote(a_->copy());
						if(compute_useDefChain)
							addModifiers(a);
						BaseSemantics::RiscOperators::writeRegister(reg, a);
						// Update latest writer info when appropriate and able to do so.
						if(compute_latestWriter){
							if (SgAsmInstruction *insn = get_insn()) {
								RegisterStatePtr regs = boost::dynamic_pointer_cast<RegisterState>(get_state()->get_register_state());
								if (regs!=NULL)
									regs->set_latest_writer(reg, insn->get_address());
							}
						}

						// adds modifier to the written value if asked to calculate the def-use chain
						if(compute_useDefChain)
							addRegsAndMemWritten(a,reg);
					}

				BaseSemantics::SValuePtr 
					RiscOperators::readMemory(const RegisterDescriptor &segreg,
							const BaseSemantics::SValuePtr &address,
							const BaseSemantics::SValuePtr &default_,
							const BaseSemantics::SValuePtr &condition) ROSE_OVERRIDE {
						BaseSemantics::SValuePtr dflt = default_;
						size_t nbits = dflt->get_width();
						ASSERT_require(0 == nbits % 8);
						ASSERT_require(1==condition->get_width()); // FIXME: condition is not used

						// checks if the memory address is a known address and the default value is undefined
						if(address->is_number() && !dflt->is_number()){
							rose_addr_t buf=0;
							size_t sz = map_.readQuick((void *)&buf,address->get_number(),nbits);
							if(sz==nbits){
								dflt = number_(sz,buf);
							}
						}
						if(compute_useDefChain){
							SValuePtr temp = SValue::promote(dflt);
							addModifiers(temp);
						}

						// Read the bytes and concatenate them together. InsnSemanticsExpr will simplify the expression so that reading after
						// writing a multi-byte value will return the original value written rather than a concatenation of byte extractions.
						SValuePtr retval;
						size_t nbytes = nbits/8;
						BaseSemantics::MemoryStatePtr mem = get_state()->get_memory_state();
						for (size_t bytenum=0; bytenum<nbits/8; ++bytenum) {
							size_t byteOffset = ByteOrder::ORDER_MSB==mem->get_byteOrder() ? nbytes-(bytenum+1) : bytenum;
							BaseSemantics::SValuePtr byte_dflt = extract(dflt, 8*byteOffset, 8*byteOffset+8);
							BaseSemantics::SValuePtr byte_addr = add(address, number_(address->get_width(), bytenum));
							SValuePtr byte_value = SValue::promote(state->readMemory(byte_addr, byte_dflt, this, this));
							if (0==bytenum) {
								retval = byte_value;
							} else if (ByteOrder::ORDER_MSB==mem->get_byteOrder()) {
								retval = SValue::promote(concat(byte_value, retval));
							} else {
								retval = SValue::promote(concat(retval, byte_value));
							}
						}
						ASSERT_require(retval!=NULL && retval->get_width()==nbits);

						// adds modifier to the read value if asked to calculate the def-use chain
						if(compute_useDefChain)
							addRegsAndMemRead(retval,address);
						return retval;
					}

				void 
					RiscOperators::writeMemory(const RegisterDescriptor &segreg,
							const BaseSemantics::SValuePtr &address,
							const BaseSemantics::SValuePtr &value_,
							const BaseSemantics::SValuePtr &condition) ROSE_OVERRIDE {
						SValuePtr value = SValue::promote(value_->copy());
						// sets current instruction as the defining instruction to the written value
						if(compute_useDefChain)
							addModifiers(value);
						size_t nbits = value->get_width();
						ASSERT_require(0 == nbits % 8);
						ASSERT_require(1==condition->get_width()); // FIXME: condition is not used
						size_t nbytes = nbits/8;
						BaseSemantics::MemoryStatePtr mem = get_state()->get_memory_state();
						for (size_t bytenum=0; bytenum<nbytes; ++bytenum) {
							size_t byteOffset = ByteOrder::ORDER_MSB==mem->get_byteOrder() ? nbytes-(bytenum+1) : bytenum;
							BaseSemantics::SValuePtr byte_value = extract(value, 8*byteOffset, 8*byteOffset+8);
							BaseSemantics::SValuePtr byte_addr = add(address, number_(address->get_width(), bytenum));
							state->writeMemory(byte_addr, byte_value, this, this);
							// Update the latest writer info if we have a current instruction and the memory state supports it.
							if(compute_memwriters){
								if (SgAsmInstruction *insn = get_insn()) {
									if (BaseSemantics::MemoryCellListPtr cells = boost::dynamic_pointer_cast<BaseSemantics::MemoryCellList>(mem)) {
										BaseSemantics::MemoryCellPtr cell = cells->get_latest_written_cell();
										ASSERT_not_null(cell); // we just wrote to it!
										cell->latestWriter(insn->get_address());
									}
								}
							}
						}

						// adds modifier to the written value if asked to calculate the def-use chain
						if(compute_useDefChain)
							addRegsAndMemWritten(value,address);
					}

				/////////////////////////////////////////////////////////////////////////////////////////////////
				//////////////////////////////		           State 						/////////////////////
				/////////////////////////////////////////////////////////////////////////////////////////////////
				void
					State::init() {
						// clone+clear might be slower than creating a new state from scratch, but its simpler and it makes sure that any other
						// state configuration that might be present (like pointers to memory maps) will be initialized properly regardless of the
						// state subtype.
						semanticState_ = ops_->get_state()->clone();
						semanticState_->clear();
					}

				// required for State Class
				std::ostream&
					operator<<(std::ostream &out, const State &state) {
						out <<*state.semanticState();
						return out;
					}

				// Merges the memoryState and the registerstate and returns if there were any changes made to the state
				bool
					State::merge(const Ptr &other) {
						RegisterStatePtr reg1 = RegisterState::promote(semanticState_->get_register_state());
						RegisterStatePtr reg2 = RegisterState::promote(other->semanticState_->get_register_state());
						bool registersChanged = mergeRegisterStates(reg1, reg2);

						MemoryStatePtr mem1 = MemoryState::promote(semanticState_->get_memory_state());
						MemoryStatePtr mem2 = MemoryState::promote(other->semanticState_->get_memory_state());
						bool memoryChanged = mergeMemoryStates(mem1, mem2);

						return registersChanged || memoryChanged;
					}

				// Merges modifiers of the symbolic value and returns true if there were any changes
				bool
					State::mergeModifiers(BaseSemantics::SValuePtr &dstValueBase /*in,out*/, const BaseSemantics::SValuePtr &srcValueBase) const {
						SValuePtr dstValue = SValue::promote(dstValueBase);
						SValuePtr srcValue = SValue::promote(srcValueBase);
						const InsnSet& dstModifiers = dstValue->get_modifying_instructions();
						const InsnSet& srcModifiers = srcValue->get_modifying_instructions();
						if (dstModifiers.size() == srcModifiers.size() && std::equal(dstModifiers.begin(), dstModifiers.end(), srcModifiers.begin()))
							return false; // no change
						dstValue->add_modifying_instructions(srcModifiers);
						return true;
					}

				// It merges the symbolic values using a particular lattice set
				//               unknown
				//				 /     \
				//			    /       \
				//		 	 tainted   untainted
				//			   \         /
				//				\       /
				//				   both
				bool
					State::mergeSValues(BaseSemantics::SValuePtr &dstValue /*in,out*/, const BaseSemantics::SValuePtr &srcValue) const {
						// The calls to ops->undefined(...) are mostly so that we're simplifying TOP as much as possible. We want each TOP
						// value to be distinct from the others so we don't encounter things like "TOP xor TOP = 0", but we also don't want TOP
						// to be arbitrarily complex since that just makes things slower.
						if (!dstValue && !srcValue) {                       // both are BOTTOM (not calculated)
							return false;
						} else if (!dstValue) {                             // dstValue is BOTTOM, srcValue is not
							ASSERT_not_null(srcValue);                 
							if (srcValue->is_number())                    
								dstValue = srcValue;
							else
								dstValue = ops_->undefined_(srcValue->get_width());
							return true;
						} else if (!srcValue) {                             // srcValue is BOTTOM, dstValue is not
							return false;
						} else if (!dstValue->is_number()) {                // dstValue was already TOP
							BaseSemantics::SValuePtr merged = ops_->undefined_(dstValue->get_width());
							mergeModifiers(merged,dstValue);
							dstValue = merged;
							return mergeModifiers(dstValue,srcValue);
						} else if (dstValue->must_equal(srcValue,ops_->get_solver())) {        // dstValue == srcValue
							return mergeModifiers(dstValue,srcValue);
						}else {                                            // dstValue becomes TOP
							BaseSemantics::SValuePtr merged = ops_->undefined_(dstValue->get_width());
							mergeModifiers(merged,dstValue);
							dstValue = merged;
							mergeModifiers(dstValue,srcValue);
							return true;
						}
					}

				// Merges register state and return true if there is any change in the registerstate
				bool
					State::mergeRegisterStates(const RegisterStatePtr &dstState,const RegisterStatePtr &srcState) const {
						bool changed = false;
						BOOST_FOREACH (const RegisterState::RegPair &reg_val, srcState->get_stored_registers()) {
							const RegisterDescriptor &reg = reg_val.desc;
							const BaseSemantics::SValuePtr &srcValue = reg_val.value;

							// register is partly known to the state
							if (!dstState->is_partly_stored(reg)) {
								changed = true;
								dstState->writeRegister(reg, ops_->undefined_(reg.get_nbits()), ops_.get());
							} else {
								BaseSemantics::SValuePtr dstValue = dstState->readRegister(reg, ops_.get());
								if (mergeSValues(dstValue /*in,out*/, srcValue)) {
									dstState->writeRegister(reg, dstValue, ops_.get());
									changed = true;
								}
							}
						}
						return changed;
					}

				// Merges memory state and return true if there is any change in the meory state
				bool
					State::mergeMemoryStates(const MemoryStatePtr &dstState,const MemoryStatePtr &srcState) const {
						bool changed = false;
						BOOST_REVERSE_FOREACH (const MemoryCellPtr &srcCell, srcState->get_cells()) {
							// Get the source and destination values
							BaseSemantics::SValuePtr srcValue = ops_->undefined_(8);
							srcValue = srcState->readMemory(srcCell->get_address(), srcValue, ops_.get(), ops_.get());
							bool shortCircuited = false;

							// memoryaddress is unknown to the memory state
							if (dstState->scan(srcCell->get_address(), 8, ops_.get(), ops_.get(), shortCircuited /*out*/).empty()) {
								// dstState doesn't even know about this address, so we just consider it as undefined value
								dstState->writeMemory(srcCell->get_address(), ops_->undefined_(8), ops_.get(), ops_.get());
								changed = true;
							} else {
								// dstState has this address, so merge the src and dst values
								BaseSemantics::SValuePtr dstValue = dstState->readMemory(srcCell->get_address(), ops_->undefined_(8), ops_.get(), ops_.get());
								if (mergeSValues(dstValue /*in,out*/, srcValue)) {
									dstState->writeMemory(srcCell->get_address(), dstValue, ops_.get(), ops_.get());
									changed = true;
								}
							}
						}
						return changed;
					}

			} // namespace
		} // namespace
	} // namespace
} // namespace
