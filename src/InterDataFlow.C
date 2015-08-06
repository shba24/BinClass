#include "sage3basic.h"
#include <iostream>
#include <rose_strtoull.h>
#include <InterDataFlow.h>
#include <Partitioner2/Partitioner.h>
#include <sawyer/GraphTraversal.h>
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
#include <sawyer/Graph.h>
#include <sawyer/DistinctList.h>
#include <vector>
#include <typeinfo>
#include <BaseSemantics2.h>
#include <DispatcherX86.h>
#include <SymbolicSemantics2.h>
#include <stdio.h>

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
			namespace InterDataFlow {

				/** Predicate that always returns false, preventing interprocedural analysis. */
				NotInterprocedural NOT_INTERPROCEDURAL;
				/** Predicate that always returns true, allowing interprocedural analysis. */
				Interprocedural INTERPROCEDURAL;


				// Return CFG basic block vertex that contains specified instruction address, or the end vertex if none found.
				ControlFlowGraph::ConstVertexIterator
					vertexForInstruction(const Partitioner &partitioner, const std::string &nameOrVa) {
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
								return partitioner.cfg().vertices().end();
							if (nFound > 1)
								throw std::runtime_error("vertex \""+StringUtility::cEscape(nameOrVa)+"\" is ambiguous");
						}
						return partitioner.instructionVertex(va);
					}

				//////// 			Traversal 					//////////
				////////										//////////
				void Traversal::visit(SgNode *node) {
					// For new - "??2@YAPAXI@Z"
					if(isSgAsmPEImportDirectory(node)){
						SgAsmPEImportDirectory *import_dir = isSgAsmPEImportDirectory(node);
						rose_addr_t low = import_dir->get_iat_rva().get_va();
						rose_addr_t size = import_dir->iat_required_size();
						mlog[INFO]<<"Found another Import directory address Range : "<<StringUtility::intToHex(low)<<
							" to "<<StringUtility::intToHex(low+size)<<std::endl;
						AddressInterval limits = AddressInterval::baseSize(low,size);
						idataExtent.insert(limits);
					}
					else if(isSgAsmPEImportItem(node)){
						SgAsmPEImportItem *import_func = isSgAsmPEImportItem(node);
						rose_addr_t vaAddr = import_func->get_iat_entry_va();
						if(import_func->get_name()->get_string()=="??2@YAPAXI@Z"){
							mlog[INFO]<<"Found 'new' library call thunk address : "<<StringUtility::intToHex(vaAddr)<<std::endl;
							newIATAddress.insert(vaAddr);
						}
					}
				}

				//////// 			DfCfgBuilder 				///////////////
				////////										///////////////

				/*Find vertex from default ControlFlowGraph vertex to DfCfg vertex*/
				DfCfg::VertexIterator 
					DfCfgBuilder::findVertex(const ControlFlowGraph::ConstVertexIterator &cfgVertex) {
						ASSERT_require(!callStack.empty());
						CallFrame &callFrame = callStack.back();
						return vmap.getOrElse(cfgVertex, dfCfg.vertices().end());
					}

				// Checks if the particular vertex is real and valid or not
				bool 
					DfCfgBuilder::isValidVertex(const DfCfg::VertexIterator &dfVertex) {
						return dfVertex != dfCfg.vertices().end();
					}

				// Inserts vertex to the custom new control flow graph for inter-procedural CFG
				DfCfg::VertexIterator 
					DfCfgBuilder::insertVertex(const DfCfgVertex &dfVertex,
							const ControlFlowGraph::ConstVertexIterator &cfgVertex) {
						ASSERT_require(!callStack.empty());
						CallFrame &callFrame = callStack.back();
						ASSERT_require(cfgVertex != cfg.vertices().end());
						ASSERT_require(!vmap.exists(cfgVertex));
						DfCfg::VertexIterator dfVertexIter = dfCfg.insertVertex(dfVertex);
						vmap.insert(cfgVertex, dfVertexIter);
						return dfVertexIter;
					}

				//Fill functionToInstruction
				void 
					DfCfgBuilder::fillInstFunc(Partitioner2::BasicBlock::Ptr &blk ){				/// [[I WANT TO REMOVE IT]]
						if(!functionToInstruction.exists(callStack.back().funcAddr))
							functionToInstruction.insert(callStack.back().funcAddr,std::set<SgAsmInstruction*,compare>());
						BOOST_FOREACH(SgAsmInstruction *insn,blk->instructions())
							functionToInstruction[callStack.back().funcAddr].insert(insn);
					}

				// Insert basic block if it hasn't been already
				DfCfg::VertexIterator 
					DfCfgBuilder::findOrInsertBasicBlockVertex(const ControlFlowGraph::ConstVertexIterator &cfgVertex) {
						ASSERT_require(!callStack.empty());
						CallFrame &callFrame = callStack.back();
						ASSERT_require(cfgVertex != cfg.vertices().end());
						ASSERT_require(cfgVertex->value().type() == V_BASIC_BLOCK);
						DfCfg::VertexIterator retval = dfCfg.vertices().end();
						if (!vmap.getOptional(cfgVertex).assignTo(retval)) {
							BasicBlock::Ptr bblock = cfgVertex->value().bblock();
							ASSERT_not_null(bblock);
							fillInstFunc(bblock);
							mlog[INFO]<<"Inserting the Basic Block Vertex at : "<<StringUtility::intToHex(bblock->address())<<std::endl;
							retval = insertVertex(DfCfgVertex(bblock), cfgVertex);
							// All function return basic blocks will point only to the special FUNCRET vertex.
							if (partitioner.basicBlockIsFunctionReturn(bblock)) {
								if (!isValidVertex(callFrame.functionReturnVertex))
									callFrame.functionReturnVertex = retMap[callFrame.funcAddr];
								mlog[INFO]<<"Inserting the Edge from Basic Block at "<<StringUtility::intToHex(bblock->address())<<
									"of function at : "<<StringUtility::intToHex(callFrame.funcAddr)<<" to Return Vertex"<<std::endl;
								dfCfg.insertEdge(retval, callFrame.functionReturnVertex);
							}
						}
						return retval;
					}

				// Find or Insert Call Return vertex at the end of a particular function call
				DfCfg::VertexIterator 
					DfCfgBuilder::findOrInsertCallReturnVertex(const ControlFlowGraph::ConstVertexIterator &cfgVertex) {
						ASSERT_require(cfgVertex != cfg.vertices().end());
						ASSERT_require(cfgVertex->value().type() == V_BASIC_BLOCK);
						DfCfg::VertexIterator retval = dfCfg.vertices().end();
						BOOST_FOREACH (const ControlFlowGraph::Edge &edge, cfgVertex->outEdges()) {
							if (edge.value().type() == E_CALL_RETURN) {
								ASSERT_require(edge.target()->value().type() == V_BASIC_BLOCK);
								ASSERT_require2(retval == dfCfg.vertices().end(),
										edge.target()->value().bblock()->printableName() + " has multiple call-return edges");
								retval = findOrInsertBasicBlockVertex(edge.target());
							}
						}
						return retval;
					}

				// Checks repeatition of particular edge in the custom CFG
				bool 
					DfCfgBuilder::checkRepeat(DfCfg::VertexIterator &src,
							DfCfg::VertexIterator &dest){
						bool retval = true;
						int source = src->id();
						int destination = dest->id();
						BOOST_FOREACH (const DfCfg::Edge &edge, dfCfg.edges()) {
							if(edge.source()->id()==source && edge.target()->id()==destination){
								retval = false;
							}
						}
						return retval;
					}

				// Copies the complete function CFG and connects it the the fromVetrex and return the return vertex
				DfCfg::VertexIterator 
					DfCfgBuilder::copyFunction(DfCfg::VertexIterator initBBlock,rose_addr_t finalAddr,
							DfCfg::VertexIterator &fromVertex){

						typedef Sawyer::Container::Map<DfCfg::VertexIterator, DfCfg::VertexIterator> newVertexMap;
						newVertexMap vertexMap;
						DfCfg::VertexIterator outVertex,in_vertex,out_vertex,inVertex,retval;
						std::queue<DfCfg::VertexIterator> inProcess;
						std::set<rose_addr_t> completed;
						in_vertex = dfCfg.insertVertex(DfCfgVertex(initBBlock->value().bblock()));
						dfCfg.insertEdge(fromVertex,in_vertex);
						vertexMap.insert(initBBlock,in_vertex);
						inProcess.push(initBBlock);
						while(!inProcess.empty()){
							inVertex = inProcess.front();
							inProcess.pop();
							in_vertex = vertexMap[inVertex];
							//ASSERT_not_null(in_vertex);
							completed.insert(inVertex->id());

							// Function return vertex and its childrens will not be put into the queue
							if(DfCfgVertex::FUNCRET == inVertex->value().type() && inVertex->value().func_address()==finalAddr ){
								retval = in_vertex;
								continue;
							}

							// Iterate over all outEdges to get all childrens which are not completed already
							BOOST_FOREACH (DfCfg::Edge &edge, inVertex->outEdges()){
								outVertex = edge.target();
								if(vertexMap.exists(outVertex)){
									out_vertex=vertexMap[outVertex];
								}
								else if(DfCfgVertex::FAKED_CALL == outVertex->value().type()){
									out_vertex = dfCfg.insertVertex(DfCfgVertex(outVertex->value().callee(),outVertex->value().call_instruction()));
								}
								else if(DfCfgVertex::FUNCRET == outVertex->value().type()){
									out_vertex = insertVertex(DfCfgVertex(DfCfgVertex::FUNCRET,outVertex->value().func_address()));
								}
								else if(DfCfgVertex::INDET == outVertex->value().type()){
									out_vertex = insertVertex(DfCfgVertex::INDET);
								}
								else{
									out_vertex = dfCfg.insertVertex(DfCfgVertex(outVertex->value().bblock()));
								}
								dfCfg.insertEdge(in_vertex,out_vertex);
								if(!vertexMap.exists(outVertex))						// Map if doesn't exist already
									vertexMap.insert(outVertex,out_vertex);
								if(completed.find(outVertex->id())==completed.end())	// not found
									inProcess.push(outVertex);
							}
						}
						return retval;
					}

				// Checks if the particular function is Thunk or not which tell if either that particular function is Library call or not
				bool
					DfCfgBuilder::checkForLibraryFunction(const BasicBlock::Ptr& blk,SgAsmInstruction *call_insn ){
						mlog[INFO]<<"Checking for Library call at : "<<StringUtility::intToHex(call_insn->get_address())<<std::endl;
						Function::Ptr function = partitioner.basicBlockFunctionOwner(blk);
						if(partitioner.functionIsThunk(function))
							return true;
						else{
							// DETECT FOLLOWING SIGNATURE
							// address1:   jmp address2
							// address2:   jmp ds:address3

							if(blk->nInstructions()==2){
								SgAsmInstruction *insn1 = blk->instructions()[0];
								SgAsmInstruction *insn2 = blk->instructions()[1];
								newIATAddress.insert(insn1->get_address());
								newIATAddress.insert(insn2->get_address());
								SgAsmX86Instruction *jmp = isSgAsmX86Instruction(insn1);
								if(!jmp || jmp->get_kind()!=x86_jmp)
									return false;
								const SgAsmExpressionPtrList &jmpArgs = jmp->get_operandList()->get_operands();
								if(jmpArgs.size()!=1)
									return false;
								SgAsmConstantExpression *jmpArg0 = isSgAsmConstantExpression(jmpArgs[0]);
								if(!jmpArg0)
									return false;

								// JMP DS:address2
								SgAsmX86Instruction *jmp_ = isSgAsmX86Instruction(insn2);
								if(!jmp_ || jmp_->get_kind()!=x86_jmp)
									return false;
								const SgAsmExpressionPtrList &jmpArgs_ = jmp_->get_operandList()->get_operands();
								if(jmpArgs_.size()!=1)
									return false;
								SgAsmMemoryReferenceExpression *jmpArg0_ = isSgAsmMemoryReferenceExpression(jmpArgs_[0]);
								if(!jmpArg0_ )
									return false;
								SgAsmIntegerValueExpression *argValue = isSgAsmIntegerValueExpression(jmpArg0_->get_address());
								if(!argValue)
									return false;
								if(!idataExtent.contains(argValue->get_absoluteValue()))
									return false;
								if(newIATAddress.find(argValue->get_absoluteValue())!=newIATAddress.end())
									newCallingInstructions.insert(call_insn);
								return true;
							}
							else
								return false;
						}
					}

				// check if an instruction is a function call directly by reading linked address from the IAT
				bool
					DfCfgBuilder::checkForLibraryCall(SgAsmInstruction *insn){
						mlog[INFO]<<"Checking for Library call at : "<<StringUtility::intToHex(insn->get_address())<<std::endl;
						SgAsmX86Instruction *call = isSgAsmX86Instruction(insn);

						// Detects call ds:[address] type of instruction
						if(!call || call->get_kind()!=x86_call)
							return false;
						const SgAsmExpressionPtrList &callArgs = call->get_operandList()->get_operands();
						if(callArgs.size()!=1)
							return false;
						SgAsmMemoryReferenceExpression *callArg0 = isSgAsmMemoryReferenceExpression(callArgs[0]);
						if(!callArg0)
							return false;
						SgAsmIntegerValueExpression *argValue = isSgAsmIntegerValueExpression(callArg0->get_address());
						if(!argValue)
							return false;
						if(!idataExtent.contains(argValue->get_absoluteValue()))
							return false;
						if(newIATAddress.find(argValue->get_absoluteValue())!=newIATAddress.end())
							newCallingInstructions.insert(insn);
						return true;
					}

				// BBlock building handler - Called each time a new BBlock is detected
				bool
					PePrivilege::operator()(bool chain,const Args &args) {
						SgAsmInstruction *insn = args.bblock->instructions().back();
						SgAsmX86Instruction *intx = isSgAsmX86Instruction(insn);

						// Correcting the CFG after instructions like int3 - generally its unknow but we are braching
						// to the next instruction in continuous
						if(chain && intx && (intx->get_kind()==x86_int3 || intx->get_kind()==x86_int) ){
							mlog[INFO]<<"Found Interrupt Instruction at : "<<StringUtility::intToHex(args.bblock->address())<<
								" - Changing new Control Flow Graph accordingly"<<std::endl;
							args.bblock->successors().clear();
							rose_addr_t fallthroughVa = insn->get_address() + insn->get_size();
							args.bblock->insertSuccessor(fallthroughVa,args.partitioner.instructionProvider().instructionPointerRegister().get_nbits());
						}
						return chain;
					}

				// Build's Custom Graph(inter-procedural graph) from the given intra-procedural graph
				DfCfg& 
					DfCfgBuilder::build(ControlFlowGraph::ConstVertexIterator &startVertex,DfCfg::VertexIterator &beginVertex,DfCfg::VertexIterator &endVertex) {
						// Start Building DFCFG
						mlog[INFO]<<"Inserted RET Vertex for Basic Block at : "<<StringUtility::intToHex(startVertex->value().address())<<std::endl;
						callStack.push_back(CallFrame(dfCfg,startVertex->value().address()));
						endVertex = insertVertex(DfCfgVertex(DfCfgVertex::FUNCRET,startVertex->value().address()));
						retMap.insert(startVertex->value().address(),endVertex);

						// Travel Current CFG to builf DfCfg
						for (CfgTraversal t(cfg, startVertex, ENTER_EVENTS|LEAVE_EDGE); t; ++t) {
							if (t.event() == ENTER_VERTEX ) {
								if (t.vertex()->value().type() == V_BASIC_BLOCK) {
									if(startVertex->id()!=t.vertex()->id())
										findOrInsertBasicBlockVertex(t.vertex());
									else
										beginVertex = findOrInsertBasicBlockVertex(t.vertex());
									if (partitioner.basicBlockIsFunctionReturn(t.vertex()->value().bblock()))
										t.skipChildren();               // we're handling return successors explicitly in findOrInsertBasicBlockVertex
								} else {
									mlog[WARN] << "Inserting indeterminate Vertex"<<std::endl;
									insertVertex(DfCfgVertex::INDET, t.vertex());
								}
							} else {
								ASSERT_require(t.event()==ENTER_EDGE || t.event()==LEAVE_EDGE);
								ControlFlowGraph::ConstEdgeIterator edge = t.edge();

								if (edge->value().type() == E_CALL_RETURN ) {
									// Do nothing; we handle call-return edges as part of function calls.
								} else if (edge->value().type() == E_FUNCTION_CALL) {
									if (t.event() == ENTER_EDGE) {
										// Enter Edge first time detected
										DfCfg::VertexIterator callFrom = findVertex(edge->source());
										SgAsmInstruction *callInst = edge->source()->value().bblock()->instructions().back();
										ASSERT_require(isValidVertex(callFrom));

										// Checks to see if the call is a library call or not , plus some other checks to see if the
										// target address is certain thunk pattern or not
										if (callStack.size() <= maxCallStackSize && edge->target()->value().type()==V_BASIC_BLOCK &&
												interproceduralPredicate(cfg, edge, callStack.size()) && !checkForLibraryCall(callInst) && 
												!checkForLibraryFunction(edge->target()->value().bblock(),callInst) ) {
											// Incorporate the call into the dfCfg
											rose_addr_t target_address = edge->target()->value().address();
											callStack.push_back(CallFrame(dfCfg,target_address));
											if(!retMap.exists(target_address)){
												mlog[INFO]<<"Inserted another RET Vertex for Basic Block at : "<<StringUtility::intToHex(target_address)<<std::endl;
												retMap.insert(target_address,insertVertex(DfCfgVertex(DfCfgVertex::FUNCRET,callStack.back().funcAddr)));
												DfCfg::VertexIterator callTo =  findOrInsertBasicBlockVertex(edge->target());
												ASSERT_require(isValidVertex(callTo));
												if(checkRepeat(callFrom, callTo)){
													mlog[INFO]<<"Inserting the Edge from Basic Block at "<<StringUtility::intToHex(edge->source()->value().bblock()->address())<<
														" to Basic Block at "<<StringUtility::intToHex(target_address)<<std::endl;
													dfCfg.insertEdge(callFrom, callTo);
												}
											}
											else {
												//  Inlining already detected function.Cloning using the existing one
												mlog[INFO]<<"Inlining already traversed function at : "<<StringUtility::intToHex(target_address)<<std::endl;
												DfCfg::VertexIterator callTo =  findOrInsertBasicBlockVertex(edge->target());
												DfCfg::VertexIterator retVertex;
												try{
													retVertex = copyFunction(callTo,callStack.back().funcAddr,callFrom);
												}catch(...){
													mlog[WARN]<<"Error in Copying Function at :"<<StringUtility::intToHex(target_address)<<std::endl;
												}
												retMap.insert(callStack.back().funcAddr,retVertex);
											}
										} else {
											// Faking different call - could be library calls or a normal function but call stack limit is already reached
											mlog[INFO]<<"Found Fake Vertex at : "<<StringUtility::intToHex(callInst->get_address())<<std::endl;
											callStack.push_back(CallFrame(dfCfg,0));
											callStack.back().wasFaked = true;
											callStack.back().call_inst = callInst;
											t.skipChildren();
										}
									} else {
										ASSERT_require(t.event() == LEAVE_EDGE);
										ASSERT_require(callStack.size()>1);

										if(callStack.back().wasFaked){
											// Build the library-call vertex and wire it up so the CALL goes to the library-call vertex, which then
											// flows to the CALL's return-point.
											Function::Ptr callee;
											if (edge->target()->value().type() == V_BASIC_BLOCK)
												callee = edge->target()->value().function();
											mlog[INFO]<<"Inserting Fake Vertex for call at "<<StringUtility::intToHex(callStack.back().call_inst->get_address())<<std::endl;
											DfCfg::VertexIterator function = insertVertex(DfCfgVertex(callee,callStack.back().call_inst));
											callStack.pop_back();
											DfCfg::VertexIterator dfSource = findVertex(edge->source());
											DfCfg::VertexIterator returnTo = findOrInsertCallReturnVertex(edge->source());
											ASSERT_not_null(returnTo->value().bblock());
											ASSERT_require(isValidVertex(dfSource));
											if(checkRepeat(dfSource, function)){
												mlog[INFO]<<"Inserting the Edge from Basic Block at "<<StringUtility::intToHex(edge->source()->value().bblock()->address())<<
													" to Fake Vertex "<<std::endl;
												dfCfg.insertEdge(dfSource, function);
											}
											if (isValidVertex(returnTo) && checkRepeat(function, returnTo)){
												mlog[INFO]<<"Inserting the Edge from Fake Vertex to Basic Block at : "<<StringUtility::intToHex(returnTo->value().bblock()->address())<<
													""<<std::endl;
												dfCfg.insertEdge(function, returnTo);
											}
										}
										else if (!callStack.back().wasFaked) {
											// Wire up the return from the called function back to the return-to point in the caller.
											DfCfg::VertexIterator returnFrom;
											rose_addr_t funcAddr = callStack.back().funcAddr;
											if(isValidVertex(callStack.back().functionReturnVertex)){
												returnFrom = callStack.back().functionReturnVertex;
											}
											else{
												returnFrom = retMap[callStack.back().funcAddr];
											}
											//ASSERT_not_null(returnFrom);
											callStack.pop_back();
											DfCfg::VertexIterator returnTo = findOrInsertCallReturnVertex(edge->source());
											if (isValidVertex(returnFrom) && isValidVertex(returnTo) && checkRepeat(returnFrom, returnTo)){
												mlog[INFO]<<"Inserting the Edge from Return Vertex of function at "<<StringUtility::intToHex(funcAddr)<<
													" to Basic Block at "<<StringUtility::intToHex(returnTo->value().bblock()->address())<<std::endl;
												dfCfg.insertEdge(returnFrom, returnTo);
											}
											ASSERT_require(!callStack.empty());
										}
									}
								}
								else {
									// Generic edges
									if (t.event()==ENTER_EDGE || t.event() == LEAVE_EDGE ) {
										DfCfg::VertexIterator dfSource = findVertex(edge->source());
										ASSERT_require(isValidVertex(dfSource));
										DfCfg::VertexIterator dfTarget = findVertex(edge->target()); // the called function
										if (isValidVertex(dfTarget)&&checkRepeat(dfSource,dfTarget)){
											mlog[INFO]<<"Inserting Edge from Basic Block at : "<<StringUtility::intToHex(dfSource->value().bblock()->address())<<
												"to Basic Block at : "<<StringUtility::intToHex(dfTarget->value().bblock()->address())<<std::endl;
											dfCfg.insertEdge(dfSource, dfTarget);
										}
									}
								}
							}
						}
						return dfCfg;
					}

				DfCfg&
					DfCfgBuilder::startBuilding(ControlFlowGraph::ConstVertexIterator &startVertex){

						// Travel the Initial AST(not complete until we call buildAst), currently it has only SAGE nodes 
						// related to headers, thats all we need
						Traversal t(idataExtent,newIATAddress);
						t.traverse(SageInterface::getProject(),preorder);					//

						DfCfg::VertexIterator endVertex,beginVertex;
						return build(startVertex,beginVertex,endVertex);
					}

				void dumpDfCfg(std::ostream &out, const DfCfg &dfCfg) {
					out <<"digraph dfCfg {\n";
					BOOST_FOREACH (const DfCfg::Vertex &vertex, dfCfg.vertices()) {
						out <<vertex.id() <<" [ label=";
						switch (vertex.value().type()) {
							case DfCfgVertex::BBLOCK:
								out <<"\"" <<vertex.value().bblock()->printableName() <<"\"";
								break;
							case DfCfgVertex::FAKED_CALL:
								if (Function::Ptr callee = vertex.value().callee()) {
									out <<"<fake call to " <<vertex.value().callee()->printableName() <<">";
								} else {
									out <<"\"fake call to indeterminate function\"";
								}
								break;
							case DfCfgVertex::FUNCRET:
								out <<"\"function return\"";
								break;
							case DfCfgVertex::INDET:
								out <<"\"indeterminate\" ";
								break;
						}
						out <<" ];\n";
					}

					BOOST_FOREACH (const DfCfg::Edge &edge, dfCfg.edges()) {
						out <<edge.source()->id() <<" -> " <<edge.target()->id() <<";\n";
					}

					out <<"}\n";
				}

				//////                              ///////
				/////       RegisterStateGeneric     //////
				/////                               ///////

				void 
					RegisterStateGeneric::setAllWriters(const RegisterDescriptor &desc, std::set<rose_addr_t> &Writers){
						Extent desc_extent(desc.get_offset(), desc.get_nbits());		
						allWriters_[desc].insert(desc_extent, Writers);
					}

				std::set<rose_addr_t>
					RegisterStateGeneric::allWriters(const RegisterDescriptor &desc) const {
						std::set<rose_addr_t> retval;
						allWritersMaps::const_iterator wi = allWriters_.find(desc);
						if (wi!=allWriters_.end()) {
							Extent desc_extent(desc.get_offset(), desc.get_nbits());
							for (writersParts::const_iterator pi=wi->second.begin(); pi!=wi->second.end(); ++pi) {
								if ((pi->first).overlaps(desc_extent)){
									retval.insert((pi->second).value.begin(),(pi->second).value.end());
								}
							}
						}
						return retval;
					}
				//////////////////////////////////////////////////END//////////////////////////////////////////////
				////////////////////////////////////////////////////////////////////////////////////////////////////


				//////                              ///////
				/////       MemoryCellList           //////
				/////                               ///////
				BaseSemantics::SValuePtr 
					MemoryCellList::readMemory(const BaseSemantics::SValuePtr &addr, const BaseSemantics::SValuePtr &dflt,
							BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) ROSE_OVERRIDE {
						ASSERT_not_null(addr);
						ASSERT_require(dflt!=NULL && (!byte_restricted || dflt->get_width()==8));
						bool short_circuited;
						CellList found = scan(addr, dflt->get_width(), addrOps, valOps, short_circuited/*out*/);
						size_t nfound = found.size();
						BaseSemantics::SValuePtr retval;
						if (1!=nfound || !short_circuited) {
							retval = dflt; // found no matches, multiple matches, or we fell off the end of the cell list
							cells.push_front(MemoryCell::promote(protocell->create(addr, dflt)));
						} else {
							retval = found.front()->get_value();
							if (retval->get_width()!=dflt->get_width()) {
								ASSERT_require(!byte_restricted); // can't happen if memory state stores only byte values
								retval = valOps->unsignedExtend(retval, dflt->get_width()); // extend or truncate
							}
						}
						ASSERT_require(retval->get_width()==dflt->get_width());
						return retval;
					}

				void 
					MemoryCellList::writeMemory(const BaseSemantics::SValuePtr &addr, const BaseSemantics::SValuePtr &value,
							BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) ROSE_OVERRIDE {
						ASSERT_require(!byte_restricted || value->get_width()==8);
						MemoryCellPtr cell = MemoryCell::promote(protocell->create(addr, value));
						cells.push_front(cell);
						latest_written_cell = cell;
					}

				void 
					MemoryCellList::print(std::ostream &stream, BaseSemantics::Formatter &fmt) const
					{
						for (CellList::const_iterator ci=cells.begin(); ci!=cells.end(); ++ci)
							stream <<fmt.get_line_prefix() <<(**ci+fmt) <<"\n";
					}

				MemoryCellList::CellList 
					MemoryCellList::scan(const BaseSemantics::SValuePtr &addr, size_t nbits, BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps,
							bool &short_circuited/*out*/) const {
						short_circuited = false;
						CellList retval;
						MemoryCellPtr tmpcell = MemoryCell::promote(protocell->create(addr, valOps->undefined_(nbits)));
						for (CellList::const_iterator ci=cells.begin(); ci!=cells.end(); ++ci) {
							if (tmpcell->may_alias(*ci, addrOps)) {
								retval.push_back(*ci);
								if ((short_circuited = tmpcell->must_alias(*ci, addrOps)))
									break;
							}
						}
						return retval;
					}

				std::set<rose_addr_t> 
					MemoryCellList::get_latest_writers(const BaseSemantics::SValuePtr &addr, size_t nbits,
							BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) const{
						ASSERT_not_null(addr);
						std::set<rose_addr_t> retval;
						bool short_circuited;
						CellList found = scan(addr, nbits, addrOps, valOps, short_circuited/*out*/);
						for (CellList::iterator fi=found.begin(); fi!=found.end(); ++fi) {
							MemoryCellPtr cell = *fi;
							if (cell->latestWriter())
								retval.insert(cell->latestWriter().get());
						}
						return retval;
					}

				std::set<rose_addr_t> 
					MemoryCellList::allWriters(const BaseSemantics::SValuePtr &addr, size_t nbits,
							BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) const {
						ASSERT_not_null(addr);
						std::set<rose_addr_t> retval;
						std::set<rose_addr_t> temp;
						bool short_circuited;
						CellList found = scan(addr, nbits, addrOps, valOps, short_circuited/*out*/);
						for (CellList::iterator fi=found.begin(); fi!=found.end(); ++fi) {
							MemoryCellPtr cell = *fi;
							if (cell->get_latest_writers().size()){	
								temp = cell->get_latest_writers();
								retval.insert(temp.begin(),temp.end());
							}
						}
						return retval;
					}
				std::set<rose_addr_t> 
					MemoryCellList::rangeWriters(const BaseSemantics::SValuePtr &addr, size_t nbits,
							BaseSemantics::RiscOperators *addrOps, BaseSemantics::RiscOperators *valOps) const{
						ASSERT_not_null(addr);
						std::set<rose_addr_t> retval;
						std::set<rose_addr_t> temp;
						size_t nbytes = nbits/8;
						for (size_t bytenum=0; bytenum<nbytes; ++bytenum) {
							BaseSemantics::SValuePtr byte_addr = addrOps->add(addr, valOps->number_(addr->get_width(), bytenum));
							temp = allWriters(byte_addr,8,addrOps,valOps);
							retval.insert(temp.begin(),temp.end());
						}
						return retval;
					}

				//////////////////////////////////////////////////END//////////////////////////////////////////////
				////////////////////////////////////////////////////////////////////////////////////////////////////

				//////                              ///////
				/////       RiscOperators           //////
				/////                               ///////


				BaseSemantics::SValuePtr 
					RiscOperators::readRegister(const RegisterDescriptor &reg) ROSE_OVERRIDE{
						BaseSemantics::SValuePtr retval = IS2::SymbolicSemantics::RiscOperators::readRegister(reg);
						AbstractLocation *aLoc = new AbstractLocation(reg);
						readList.push_back(new ValueAbstractPair(retval,aLoc));
						return retval;
					}
				void 
					RiscOperators::writeRegister(const RegisterDescriptor &reg, const BaseSemantics::SValuePtr &a_) ROSE_OVERRIDE{
						IS2::SymbolicSemantics::SValuePtr a = IS2::SymbolicSemantics::SValue::promote(a_->copy());
						AbstractLocation *aLoc = new AbstractLocation(reg);
						writeList.push_back(new ValueAbstractPair(a,aLoc));
						state->get_register_state()->writeRegister(reg,a,this);
						if (SgAsmInstruction *insn = get_insn()) {
							std::set<rose_addr_t> temp;
							temp.insert(insn->get_address());
							RegisterStateGeneric::promote(state->get_register_state())->setAllWriters(reg,temp);
						}
					}
				BaseSemantics::SValuePtr 
					RiscOperators::readMemory(const RegisterDescriptor &segreg,
							const BaseSemantics::SValuePtr &address,
							const BaseSemantics::SValuePtr &dflt,
							const BaseSemantics::SValuePtr &condition) ROSE_OVERRIDE {
						size_t nbits = dflt->get_width();
						ASSERT_require(0 == nbits % 8);
						ASSERT_require(1==condition->get_width()); // FIXME: condition is not used


						// Read the bytes and concatenate them together. InsnSemanticsExpr will simplify the expression so that reading after
						// writing a multi-byte value will return the original value written rather than a concatenation of byte extractions.
						BaseSemantics::SValuePtr retval;
						size_t nbytes = nbits/8;
						BaseSemantics::MemoryStatePtr mem = state->get_memory_state();
						for (size_t bytenum=0; bytenum<nbits/8; ++bytenum) {
							size_t byteOffset = ByteOrder::ORDER_MSB==mem->get_byteOrder() ? nbytes-(bytenum+1) : bytenum;
							BaseSemantics::SValuePtr byte_dflt = extract(dflt, 8*byteOffset, 8*byteOffset+8);
							BaseSemantics::SValuePtr byte_addr = add(address, number_(address->get_width(), bytenum));
							IS2::SymbolicSemantics::SValuePtr byte_value = IS2::SymbolicSemantics::SValue::promote(state->readMemory(byte_addr, byte_dflt, this, this));
							if (0==bytenum) {
								retval = byte_value;
							} else if (ByteOrder::ORDER_MSB==mem->get_byteOrder()) {
								retval = IS2::SymbolicSemantics::SValue::promote(concat(byte_value, retval));
							} else {
								retval = IS2::SymbolicSemantics::SValue::promote(concat(retval, byte_value));
							}
						}
						ASSERT_require(retval!=NULL && retval->get_width()==nbits);
						if(address->is_number() && !retval->is_number()){
							rose_addr_t buf=0;
							size_t sz = map.readQuick((void *)&buf,address->get_number(),nbits);
							if(sz!=0){
								retval = number_(sz,buf);
							}
						}
						AbstractLocation *aLoc = new AbstractLocation(address,nbits);
						readList.push_back(new ValueAbstractPair(retval,aLoc));
						return retval;
					}

				void 
					RiscOperators::writeMemory(const RegisterDescriptor &segreg,
							const BaseSemantics::SValuePtr &address,
							const BaseSemantics::SValuePtr &value_,
							const BaseSemantics::SValuePtr &condition) ROSE_OVERRIDE {
						IS2::SymbolicSemantics::SValuePtr value = IS2::SymbolicSemantics::SValue::promote(value_->copy());
						size_t nbits = value->get_width();
						AbstractLocation *aLoc = new AbstractLocation(address,nbits);
						writeList.push_back(new ValueAbstractPair(value_,aLoc));
						ASSERT_require(0 == nbits % 8);
						ASSERT_require(1==condition->get_width()); // FIXME: condition is not used
						size_t nbytes = nbits/8;
						BaseSemantics::MemoryStatePtr mem = state->get_memory_state();
						for (size_t bytenum=0; bytenum<nbytes; ++bytenum) {
							size_t byteOffset = ByteOrder::ORDER_MSB==mem->get_byteOrder() ? nbytes-(bytenum+1) : bytenum;
							BaseSemantics::SValuePtr byte_value = extract(value, 8*byteOffset, 8*byteOffset+8);
							BaseSemantics::SValuePtr byte_addr = add(address, number_(address->get_width(), bytenum));
							state->writeMemory(byte_addr, byte_value, this, this);
							// Update the latest writer info if we have a current instruction and the memory state supports it.
							if (SgAsmInstruction *insn = get_insn()) {
								MemoryCellListPtr cells = MemoryCellList::promote(mem);
								MemoryCellPtr cell = MemoryCell::promote(cells->get_latest_written_cell());
								ASSERT_not_null(cell); // we just wrote to it!
								cell->latestWriter(insn->get_address());
								std::set<rose_addr_t> temp;
								temp.insert(insn->get_address());
								cell->set_latest_writers(temp);
							}
						}
					}

				//////////////////////////////////////////////////END//////////////////////////////////////////////
				////////////////////////////////////////////////////////////////////////////////////////////////////
				void
					State::init() {
						// clone+clear might be slower than creating a new state from scratch, but its simpler and it makes sure that any other
						// state configuration that might be present (like pointers to memory maps) will be initialized properly regardless of the
						// state subtype.
						semanticState_ = ops_->get_state()->clone();
						semanticState_->clear();
					}

				std::ostream&
					operator<<(std::ostream &out, const State &state) {
						out <<*state.semanticState();
						return out;
					}

				bool
					State::merge(const Ptr &other) {
						using namespace rose::BinaryAnalysis::Partitioner2::InterDataFlow;
						RegisterStateGenericPtr reg1 = RegisterStateGeneric::promote(semanticState_->get_register_state());
						RegisterStateGenericPtr reg2 = RegisterStateGeneric::promote(other->semanticState_->get_register_state());
						bool registersChanged = mergeRegisterStates(reg1, reg2);

						MemoryCellListPtr mem1 = MemoryCellList::promote(semanticState_->get_memory_state());
						MemoryCellListPtr mem2 = MemoryCellList::promote(other->semanticState_->get_memory_state());
						bool memoryChanged = mergeMemoryStates(mem1, mem2);

						return registersChanged || memoryChanged;
					}

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
							dstValue= ops_->undefined_(dstValue->get_width());
							return false;
						} else if (dstValue->must_equal(srcValue)) {        // dstValue == srcValue
							return false;
						}else {                                            // dstValue becomes TOP
							dstValue = ops_->undefined_(dstValue->get_width());
							return true;
						}
					}

				bool
					State::mergeRegisterStates(const rose::BinaryAnalysis::Partitioner2::InterDataFlow::RegisterStateGenericPtr &dstState,
							const rose::BinaryAnalysis::Partitioner2::InterDataFlow::RegisterStateGenericPtr &srcState) const {
						bool changed = false;
						BOOST_FOREACH (const rose::BinaryAnalysis::Partitioner2::InterDataFlow::RegisterStateGeneric::RegPair &reg_val, srcState->get_stored_registers()) {
							const RegisterDescriptor &reg = reg_val.desc;
							const BaseSemantics::SValuePtr &srcValue = reg_val.value;
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
							// We should adjust latestWriter also, but unfortunately we can only store one writer per bit of the register's value,
							// and it's hard to get information about the individual bits.
							// Merge writer sets , added function get_latest_writers and set_latest_writers to BaseSemantics2.h
							// to add multiple writers to each RegisterStateGeneric class
							// converge to a fixed point during the dataflow loop).
							std::set<rose_addr_t> srcWriters = srcState->allWriters(reg);
							std::set<rose_addr_t> dstWriters = dstState->allWriters(reg);
							// If all the possible entry states are different , the merged state reflects that the value is unknown,
							// and the resulting list of modifiers is the combination of the sets from each entry state
							if (srcWriters.size()!=dstWriters.size() || !std::equal(srcWriters.begin(), srcWriters.end(), dstWriters.begin())) {
								dstWriters.insert(srcWriters.begin(),srcWriters.end());
								dstState->setAllWriters(reg,dstWriters);
								// Make the Memory cells semantic value undefined after the merging of different states.
								changed=true;
							}
						}
						return changed;
					}

				bool
					State::mergeMemoryStates(const rose::BinaryAnalysis::Partitioner2::InterDataFlow::MemoryCellListPtr &dstState,
							const rose::BinaryAnalysis::Partitioner2::InterDataFlow::MemoryCellListPtr &srcState) const {
						using namespace rose::BinaryAnalysis::InstructionSemantics2::BaseSemantics;
						bool changed = false;
						BOOST_REVERSE_FOREACH (const rose::BinaryAnalysis::Partitioner2::InterDataFlow::MemoryCellPtr &srcCell, srcState->get_cells()) {
							// Get the source and destination values
							SValuePtr srcValue = ops_->undefined_(8);
							srcValue = srcState->readMemory(srcCell->get_address(), srcValue, ops_.get(), ops_.get());
							bool shortCircuited = false;
							if (dstState->scan(srcCell->get_address(), 8, ops_.get(), ops_.get(), shortCircuited /*out*/).empty()) {
								// dstState doesn't even know about this address, so we just consider it as undefined value
								dstState->writeMemory(srcCell->get_address(), ops_->undefined_(8), ops_.get(), ops_.get());
								changed = true;
							} else {
								// dstState has this address, so merge the src and dst values
								SValuePtr dstValue = dstState->readMemory(srcCell->get_address(), ops_->undefined_(8), ops_.get(), ops_.get());
								if (mergeSValues(dstValue /*in,out*/, srcValue)) {
									dstState->writeMemory(srcCell->get_address(), dstValue, ops_.get(), ops_.get());
									changed = true;
								}
								// Merge writer sets , added function get_latest_writers and set_latest_writers to BaseSemantics2.h
								// to add multiple writers to each MemoryCell class
								// converge to a fixed point during the dataflow loop).
								std::set<rose_addr_t> srcWriters = srcState->allWriters(srcCell->get_address(), 8, ops_.get(), ops_.get());
								std::set<rose_addr_t> dstWriters = dstState->allWriters(srcCell->get_address(), 8, ops_.get(), ops_.get());
								// If all the possible entry states are different , the merged state reflects that the value is unknown,
								// and the resulting list of modifiers is the combination of the sets from each entry state
								if (srcWriters.size()!=dstWriters.size() || !std::equal(srcWriters.begin(), srcWriters.end(), dstWriters.begin())) {
									dstWriters.insert(srcWriters.begin(),srcWriters.end());
									rose::BinaryAnalysis::Partitioner2::InterDataFlow::MemoryCellList::CellList dstCells = dstState->scan(srcCell->get_address(), 8, ops_.get(), ops_.get(),
											shortCircuited /*out*/);
									BOOST_FOREACH (rose::BinaryAnalysis::Partitioner2::InterDataFlow::MemoryCellPtr &dstCell, dstCells)
										dstCell->set_latest_writers(dstWriters);
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

