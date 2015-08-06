///
///     Written By: Shubham Bansal (illusionist.neo@gmail.com)
///     Copyright(c) Shubham Bansal (iN3O)
///     Blog :- http://in3o.me
///

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

// Basic namespaces required throughout the Code
using namespace rose;
using namespace rose::Diagnostics;
using namespace rose::BinaryAnalysis;
using namespace Sawyer::Message::Common;

// Short names for Namespaces because
// using big names in code is pain in
// the ass
namespace IS2 = InstructionSemantics2;
namespace P2 = Partitioner2;
namespace CS = P2::ClassSemantics;
/*
 * 					RECOVERING Object Oriented Data Structure from C++ Compiled Binaries ( Windows PE files )
 *	- 
 *
 *
 *
 */

// Describe and parse the command-line
static Sawyer::CommandLine::ParserResult
parseCommandLine(int argc, char *argv[], Settings &settings){
	using namespace Sawyer::CommandLine;


	Parser parser;
	parser
		.purpose("Finds C++ Object Oriented dataStructures from Binary/Malware")
		.version("0.2v", ROSE_CONFIGURE_DATE)
		.chapter(1, "BinClass - Command-line Switches")
		.doc("Synopsis",
				"@prop{programName} [@v{switches}] @v{specimen_names}")
		.doc("Description",
				"Parses,dissassembles,partitions the specimens,builds Def-Use chain and deduces OOP structures")
		.doc("Specimens", P2::Engine::specimenNameDocumentation())
		.doc("Bugs","[Lot]-bugs",
				"Surely Many, and I'm interested in every single of them. Send them to <illusionist.neo@gmail.com>.");

	// Generic switches
	SwitchGroup gen = CommandlineProcessing::genericSwitches();
	gen.insert(Switch("use-semantics")
			.intrinsicValue(true, settings.useSemantics)
			.doc("The partitioner can either use quick and naive methods of determining instruction characteristics, or "
				"it can use slower but more accurate methods, such as symbolic semantics.  This switch enables use of "
				"the slower symbolic semantics, or the feature can be disabled with @s{no-use-semantics}. The default is " +
				std::string(settings.useSemantics?"true":"false") + "."));
	gen.insert(Switch("no-use-semantics")
			.key("use-semantics")
			.intrinsicValue(false, settings.useSemantics)
			.hidden(true));
	gen.insert(Switch("config")
			.argument("path", anyParser(settings.configurationName))
			.doc("Directory containing configuration files, or a configuration file itself.  A directory is searched "
				"recursively searched for files whose names end with \".json\" or and each file is parsed and used to "
				"to configure the partitioner.  The JSON file contents are made by me Shubham Bansal (iN3O)"
				"(illusionist.neo@gmail.com). It should have a top-level \"config.exports\" table whose keys are "
				"function names and whose values are have a \"function.delta\" integer. The delta does not include "
				"popping the return address from the stack in the final RET instruction.  Function names of the form "
				"\"lib:func\" are translated to the ROSE format \"func@lib\". Default is : "+settings.configurationName+"."));

	// Switches for disassembly
	SwitchGroup dis("Disassembly switches");
	dis.insert(Switch("isa")
			.argument("architecture", anyParser(settings.isaName))
			.doc("Instruction set architecture. Specify \"list\" to see a list of possible ISAs."));
	dis.insert(Switch("allow-discontiguous-blocks")
			.intrinsicValue(true, settings.allowDiscontiguousBlocks)
			.doc("This setting allows basic blocks to contain instructions that are discontiguous in memory as long as "
				"the other requirements for a basic block are still met. Discontiguous blocks can be formed when a "
				"compiler fails to optimize away an opaque predicate for a conditional branch, or when basic blocks "
				"are scattered in memory by the introduction of unconditional jumps.  The @s{no-allow-discontiguous-blocks} "
				"switch disables this feature and can slightly improve partitioner performance by avoiding cases where "
				"an unconditional branch initially creates a larger basic block which is later discovered to be "
				"multiple blocks.  The default is to " + std::string(settings.allowDiscontiguousBlocks?"":"not ") +
				"allow discontiguous basic blocks."));
	dis.insert(Switch("no-allow-discontiguous-blocks")
			.key("allow-discontiguous-blocks")
			.intrinsicValue(false, settings.allowDiscontiguousBlocks)
			.hidden(true));
	dis.insert(Switch("find-function-padding")
			.intrinsicValue(true, settings.findFunctionPadding)
			.doc("Look for padding such as zero bytes and certain instructions like no-ops that occur prior to the "
				"lowest address of a function and attach them to the function as static data.  The "
				"@s{no-find-function-padding} switch turns this off.  The default is to " +
				std::string(settings.findFunctionPadding?"":"not ") + "search for padding."));
	dis.insert(Switch("no-find-function-padding")
			.key("find-function-padding")
			.intrinsicValue(false, settings.findFunctionPadding)
			.hidden(true));
	dis.insert(Switch("find-dead-code")
			.intrinsicValue(true, settings.findDeadCode)
			.doc("Use ghost edges (non-followed control flow from branches with opaque predicates) to locate addresses "
				"for unreachable code, then recursively discover basic blocks at those addresses and add them to the "
				"same function.  The @s{no-find-dead-code} switch turns this off.  The default is " +
				std::string(settings.findDeadCode?"true":"false") + "."));
	dis.insert(Switch("no-find-dead-code")
			.key("find-dead-code")
			.intrinsicValue(false, settings.findDeadCode)
			.hidden(true));
	dis.insert(Switch("post-analysis")
			.intrinsicValue(true, settings.doPostAnalysis)
			.doc("Run all post-partitioning analysis functions.  For instance, calculate stack deltas for each "
				"instruction, and may-return analysis for each function.  Some of these phases will only work if "
				"instruction semantics are enabled (see @s{use-semantics}).  The @s{no-post-analysis} switch turns "
				"this off, although analysis will still be performed where it is needed for partitioning.  The "
				"default is to " + std::string(settings.doPostAnalysis?"":"not ") + "perform the post analysis phase."));
	dis.insert(Switch("no-post-analysis")
			.key("post-analysis")
			.intrinsicValue(false, settings.doPostAnalysis)
			.hidden(true));
	dis.insert(Switch("intra-function-code")
			.intrinsicValue(true, settings.intraFunctionCode)
			.doc("Near the end of processing, if there are regions of unused memory that are immediately preceded and "
				"followed by the same single function then a basic block is create at the beginning of that region and "
				"added as a member of the surrounding function.  A function block discover phase follows in order to "
				"find the instructions for the new basic blocks and to follow their control flow to add additional "
				"blocks to the functions.  These two steps are repeated until no new code can be created.  This step "
				"occurs before the @s{intra-function-data} step if both are enabled.  The @s{no-intra-function-code} "
				"switch turns this off. The default is to " + std::string(settings.intraFunctionCode?"":"not ") +
				"perform this analysis."));
	dis.insert(Switch("no-intra-function-code")
			.key("intra-function-code")
			.intrinsicValue(false, settings.intraFunctionCode)
			.hidden(true));

	dis.insert(Switch("intra-function-data")
			.intrinsicValue(true, settings.intraFunctionData)
			.doc("Near the end of processing, if there are regions of unused memory that are immediately preceded and "
				"followed by the same function then add that region of memory to that function as a static data block."
				"The @s{no-intra-function-data} switch turns this feature off.  The default is " +
				std::string(settings.intraFunctionData?"true":"false") + "."));
	dis.insert(Switch("no-intra-function-data")
			.key("intra-function-data")
			.intrinsicValue(false, settings.intraFunctionData)
			.hidden(true));

	dis.insert(Switch("interrupt-vector")
			.argument("addresses", P2::addressIntervalParser(settings.interruptVector))
			.doc("A table containing addresses of functions invoked for various kinds of interrupts. " +
				P2::AddressIntervalParser::docString() + " The length and contents of the table is architecture "
				"specific, and the disassembler will use available information about the architecture to decode the "
				"table.  If a single address is specified, then the length of the table is architecture dependent, "
				"otherwise the entire table is read."));


	SwitchGroup dataFlow("DataFlow switches");
	dataFlow.insert(Switch("output-def-use")
			.intrinsicValue(true,settings.doOutputDefUse)
			.doc("Analyse the specimen. Do Dataflow Analaysis using the standard WorKList Algorithm and build Def-Use Chain."
				"Output Def-Use chains Interprocedural."));
	dataFlow.insert(Switch("output-objects")
			.intrinsicValue(true,settings.doOutputObjects)
			.doc("Analyse the specimen. Output the Objects extracted into file mentioned by the flag @s[yaml-file]"));
	dataFlow.insert(Switch("use-smt")
			.intrinsicValue(true,settings.useSMTSolver)
			.doc("Use Satisfiability modulo theory for precise Calculation"));
	dataFlow.insert(Switch("no-use-smt")
			.key("use-smt")
			.intrinsicValue(false, settings.useSMTSolver)
			.hidden(true));
	dataFlow.insert(Switch("max-iter")
			.argument("maxIterations",nonNegativeIntegerParser(settings.maxIterations),"10000")
			.doc("Select the maximum no. of iteration to run dataFlow Analysis to"));
	dataFlow.insert(Switch("max-iter-per-vertex")
			.argument("maxIterationsPerVertex",nonNegativeIntegerParser(settings.maxIterationsPerVertex),"1")
			.doc("Maximum no. of times each Vertex is analysed - saving from wasting iteration in future"));
	dataFlow.insert(Switch("max-class-size")
			.argument("maxClassSize",nonNegativeIntegerParser(settings.maxIterations),"0x100")
			.doc("Maximum SIze of a class possible"));


	// Switches for output
	SwitchGroup out("Output switches");
	out.insert(Switch("list-aum")
			.intrinsicValue(true, settings.doListAum)
			.doc("Emit a listing of the address usage map after the CFG is discovered.  The @s{no-list-aum} switch is "
				"the inverse."));
	out.insert(Switch("no-list-aum")
			.key("list-aum")
			.intrinsicValue(false, settings.doListAum)
			.hidden(true));
	out.insert(Switch("list-functions")
			.intrinsicValue(true, settings.doListFunctions)
			.doc("Produce a table of contents showing all the functions that were detected.  The @s{no-list-functions} "
				"switch disables this.  The default is to " + std::string(settings.doListFunctions?"":"not ") +
				"show this information. See @s{select-functions}."));
	out.insert(Switch("no-list-functions")
			.key("list-functions")
			.intrinsicValue(false, settings.doListFunctions)
			.hidden(true));
	out.insert(Switch("show-map")
			.intrinsicValue(true, settings.doShowMap)
			.doc("Show the memory map that was used for disassembly.  The @s{no-show-map} switch turns this off. The "
				"default is to " + std::string(settings.doShowMap?"":"not ") + "show the memory map."));
	out.insert(Switch("no-show-map")
			.key("show-map")
			.intrinsicValue(false, settings.doShowMap)
			.hidden(true));
	out.insert(Switch("show-stats")
			.intrinsicValue(true, settings.doShowStats)
			.doc("Emit some information about how much of the input was disassembled."));
	out.insert(Switch("no-show-stats")
			.key("show-stats")
			.intrinsicValue(false, settings.doShowStats)
			.hidden(true));
	out.insert(Switch("yaml-file")
			.argument("Yaml Dump",anyParser(settings.yamlOutputFile))
			.doc("Output Yaml file describing all the deduced data-structures. Default is : "+ settings.yamlOutputFile + "."));
	out.insert(Switch("defuse-file")
			.argument("Def-Use Chain",anyParser(settings.defUseOutputFile))
			.doc("Output File name containing Def-Use Chain. Default is : " + settings.defUseOutputFile + "."));
	out.insert(Switch("verbose")
			.intrinsicValue(true, settings.verbose)
			.doc("Detailed Verbose Output"));
	out.insert(Switch("no-verbose")
			.key("verbose")
			.intrinsicValue(false, settings.verbose)
			.hidden(true));

	// Switches controlling GraphViz output
	SwitchGroup dot("Graphviz switches");
	dot.insert(Switch("gv-basename")
			.argument("path", anyParser(settings.gvBaseName))
			.doc("Base name for GraphViz dot files.  The full name is created by appending details about what is "
				"contained in the file.  For instance, a control flow graph for the function \"main\" has the "
				"string \"cfg-main.dot\" appended.  The default is \"" + settings.gvBaseName + "\"."));
	dot.insert(Switch("gv-subgraphs")
			.intrinsicValue(true, settings.gvUseFunctionSubgraphs)
			.doc("Organize GraphViz output into subgraphs, one per function.  The @s{no-gv-subgraphs} switch disables "
				"subgraphs. The default is to " + std::string(settings.gvUseFunctionSubgraphs?"":"not ") + "emit "
				"subgraphs for those GraphViz files where it makes sense."));
	dot.insert(Switch("no-gv-subgraphs")
			.key("gv-subgraphs")
			.intrinsicValue(false, settings.gvUseFunctionSubgraphs)
			.hidden(true));

	dot.insert(Switch("gv-show-funcret")
			.intrinsicValue(true, settings.gvShowFunctionReturns)
			.doc("Show the function return edges in control flow graphs. These are the edges originating at a basic block "
				"that serves as a function return and usually lead to the indeterminate vertex.  Including them in "
				"multi-function graphs makes the graphs more complicated than they need to be for visualization. The "
				"@s{no-gv-show-funcret} switch disables these edges. The default is to " +
				std::string(settings.gvShowFunctionReturns?"":"not ") + "show these edges."));
	dot.insert(Switch("no-gv-show-funcret")
			.key("gv-show-funcret")
			.intrinsicValue(false, settings.gvShowFunctionReturns)
			.hidden(true));

	dot.insert(Switch("gv-show-insns")
			.intrinsicValue(true, settings.gvShowInstructions)
			.doc("Show disassembled instructions in the GraphViz output rather than only starting addresses. Emitting "
				"just addresses makes the GraphViz files much smaller but requires a separate assembly listing to "
				"interpret the graphs.  The @s{no-gv-show-instructions} causes only addresses to be emitted.  The "
				"default is to emit " + std::string(settings.gvShowInstructions?"instructions":"only addresses") + "."));
	dot.insert(Switch("no-gv-show-insns")
			.key("gv-show-insns")
			.intrinsicValue(false, settings.gvShowInstructions)
			.hidden(true));
	dot.insert(Switch("gv-call-graph")
			.intrinsicValue(true, settings.gvCallGraph)
			.doc("Emit a function call graph to the GraphViz file whose name is specified by the @s{gv-basename} prefix "
				"followed by the string \"cg.dot\". The @s{no-gv-call-graph} switch disables this output. The default "
				"is to " + std::string(settings.gvCallGraph?"":"not ") + "produce this file.\n"));
	dot.insert(Switch("no-gv-call-graph")
			.key("gv-call-graph")
			.intrinsicValue(false, settings.gvCallGraph)
			.hidden(true));
	dot.insert(Switch("gv-cfg")
			.intrinsicValue(true, settings.gvControlFlowGraph)
			.doc("Emit a constrol flow  graph to the GraphViz file whose name is specified by the @s{gv-basename} prefix "
				"followed by the string \"cfg-global.dot\". The @s{no-gv-cfg} switch disables this output. The default "
				"is to " + std::string(settings.gvControlFlowGraph?"":"not ") + "produce this file.\n"));
	dot.insert(Switch("no-gv-cfg")
			.key("gv-cfg")
			.intrinsicValue(false, settings.gvControlFlowGraph)
			.hidden(true));
	// Switches for debugging
	SwitchGroup dbg("Debugging switches");
	dbg.insert(Switch("trigger")
			.argument("what", anyParser(settings.triggers))
			.whichValue(SAVE_ALL)
			.doc("Activates a debugging aid triggered by a certain event. For instance, if you're trying to figure "
				"out why a function prologue pattern created a function at a location where you think there should "
				"have already been an instruction, then it would be useful to have a list of CFG-attached instructions "
				"at the exact point when the function prologue was matched. The switch "
				"\"@s{trigger} insn-list:bblock=0x0804cfa1:insns=0x0804ca00,0x0804da10\" will do such a thing. Namely, "
				"the first time a basic block at 0x0804cfa1 is added to the CFG it will list all CFG-attached instructions "
				"between the addresses 0x0804ca00 and 0x0804da10.  Multiple @s{trigger} switches can be specified. Each "
				"one takes a value which is the name of the debugging aid (e.g., \"insn-list\") and zero or more "
				"configuration arguments with a colon between the name and each argument."
				"\n\n"
				"In the descriptions that follow, leading hyphens can be omitted and an equal sign can separate the "
				"name and value. That is, \":bblock=0x123\" works just as well as \":--bblock 0x123\".  Integers may "
				"generally be specified in C/C++ syntax: hexadecimal (leading \"0x\"), binary (leading \"0b\"), "
				"octal (leading \"0\"), or decimal.  Intervals can be specified with a single integer to represent a "
				"singleton interval, a minimum and maximum value separated by a comma as in \"20,29\", a beginning "
				"and exclusive end separated by a hpyhen as in \"20-30\", or a beginning and size separated by a \"+\" "
				"as in \"20+10\"."
				"\n\n"
				"Debugging aids generally send their output to the rose::BinaryAnalysis::Partitioner2[DEBUG] stream. "
				"There is no need to turn this stream on explicitly from the command line since the debugging aids "
				"temporarily enable it.  They assume that if you took the time to specify their parameters then you "
				"probably want to see their output!"
				"\n\n"
				"The following debugging aids are available:"
				"@named{cfg-dot}{" + P2::Modules::CfgGraphVizDumper::docString() + "}"
				"@named{hexdump}{" + P2::Modules::HexDumper::docString() + "}"
				"@named{insn-list}{" + P2::Modules::InstructionLister::docString() + "}"
				"@named{debugger}{" + P2::Modules::Debugger::docString() + "}"
				));
	return parser.with(gen).with(dis).with(dataFlow).with(out).with(dot).with(dbg).parse(argc, argv).apply();
}

static void
emitControlFlowGraphs(const P2::Partitioner &partitioner, const Settings &settings) {
	if(!settings.gvControlFlowGraph)
		return;
	std::string fileName = settings.gvBaseName + "cfg-global.dot";
	std::ofstream out(fileName.c_str());
	if (out.fail()) {
		mlog[ERROR] <<"cannot write to CFG file \"" <<fileName <<"\"\n";
	} else {
		mlog[INFO] <<"generating CFG GraphViz file: " <<fileName <<"\n";
		P2::GraphViz::CfgEmitter gv(partitioner);
		gv.defaultGraphAttributes().insert("overlap", "scale");
		gv.useFunctionSubgraphs(settings.gvUseFunctionSubgraphs);
		gv.showInstructions(settings.gvShowInstructions);
		gv.showReturnEdges(settings.gvShowFunctionReturns);
		gv.emitWholeGraph(out);
	}
}

static void
emitFunctionCallGraph(const P2::Partitioner &partitioner, const Settings &settings) {
	if (!settings.gvCallGraph)
		return;
	std::string fileName = settings.gvBaseName + "cg.dot";
	std::ofstream out(fileName.c_str());
	if (out.fail()) {
		mlog[ERROR] <<"cannot write to CG file \"" <<fileName <<"\"\n";
	} else {
		mlog[INFO] <<"generating call graph: " <<fileName <<"\n";
		P2::GraphViz::CgEmitter gv(partitioner);
		gv.defaultGraphAttributes().insert("overlap", "scale");
		gv.emitCallGraph(out);
	}
}

P2::FunctionCallGraph
functionCallGraph(P2::Partitioner &partitioner,bool allowParallelEdges=true) {
	P2::FunctionCallGraph cg;
	size_t edgeCount = allowParallelEdges ? 0 : 1;
	BOOST_FOREACH (const P2::ControlFlowGraph::Edge &edge, partitioner.cfg().edges()) {
		if (edge.source()->value().type()==P2::V_BASIC_BLOCK && edge.target()->value().type()==P2::V_BASIC_BLOCK) {
			P2::BasicBlock::Ptr targetBlock = edge.target()->value().bblock();
			P2::Function::Ptr source = edge.source()->value().function();
			P2::Function::Ptr target = edge.target()->value().function();
			if (source!=NULL && target!=NULL && edge.value().type()==P2::E_FUNCTION_CALL && source!=target )
				cg.insertCall(source, target, edge.value().type(), edgeCount);
		}
	}
	return cg;
}

SMTSolver* getSolver(){
	YicesSolver *solver = new YicesSolver;
	solver->set_linkage(YicesSolver::LM_LIBRARY);
	return solver;
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

int main( int argc, char * argv[] ){

	// Timer to check the time taken by each step
	// Used to optimize different level of code . Not started yet.
	Sawyer::Stopwatch timer(false);

	// Configure diagnostic output
	// Do this explicitly since librose doesn't do this automatically yet
	rose::Diagnostics::initialize();

	// Settings for the Analysis
	Settings settings;

	// Parse the command-line
	Sawyer::CommandLine::ParserResult cmdline = parseCommandLine(argc, argv, settings);
	std::vector<std::string> specimenNames = cmdline.unreachedArgs();
	Disassembler *disassembler = NULL;
	if (!settings.isaName.empty())
		disassembler = Disassembler::lookup(settings.isaName);
	if (specimenNames.empty())
		throw std::runtime_error("no specimen specified; see --help");


	// Create an engine to drive the partitioning.  This is entirely optional, you can do all the things manually also.  
	// All an engine does is define the sequence of partitioning calls that need to be made in order to recognize instructions, 
	// basic blocks, data blocks, and functions. We instantiate the engine early because it has some nice methods that we can use.
	Partitioner2::Engine engine;

	timer.restart();
	// Load the specimen as raw data or an ELF or PE container.
	MemoryMap map = engine.loadSpecimens(specimenNames);
	mlog[INFO]<<"Engine took : "<<timer.stop()<<" in loading the Specimens"<<std::endl;

	// Obtain which disassembler to use , like - x86,x64
	if (NULL==(disassembler = engine.obtainDisassembler(disassembler)))
		throw std::runtime_error("an instruction set architecture must be specified with the \"--isa\" switch");

	// Get the primary interpretation needed below (ELF has only one).
	SgAsmInterpretation *interp = engine.interpretation();
	ASSERT_not_null(interp);

	// Travel the AST for important information about the import table and directories
	// Travel the Initial AST(not complete until we call buildAst), currently it has only SAGE nodes 
	// related to headers, thats all we need
	SgProject *Project = SageInterface::getProject();

	timer.restart();
	// Create a partitioner that's tuned for a certain architecture, and then tune it even more depending on our command-line.
	Partitioner2::Partitioner partitioner = engine.createTunedPartitioner();

	// Enable Symbolic Execution
	partitioner.enableSymbolicSemantics(settings.useSemantics);

	// Insert Callbacks each time a new Basic Block is identified, This is to adjust the CFG according to the needs
	// 1. PePrivilege will identify the interrupt instructions which are considered as previledged instructions and
	//    adjust the CFG according to it.
	partitioner.basicBlockCallbacks().append(CS::PePrivilege::instance(settings.verbose));

	// Rose donot follow the traditional rule of assuming that BasicBlocks are contiguous address space
	// Assume the following case - Prologue of some functions
	// 				- addr1:        jmp addr2
	//				- addr2:		push ebp
	//				- addr3:		mov ebp,esp
	// In the above case addr1 and addr2 are not contiguous addresses but still Rose considers both instructiosn
	// addr1 and addr2 are the part of the same basic block if there no other reference to addr2 other than
	// by the instruction at addr1. [VERY INTELLIGENT]
	if (!settings.allowDiscontiguousBlocks)
		partitioner.basicBlockCallbacks().append(P2::Modules::PreventDiscontiguousBlocks::instance());

	// Insert debugging aids
	BOOST_FOREACH (const std::string &s, settings.triggers) {
		if (boost::starts_with(s, "cfg-dot:")) {
			P2::Modules::CfgGraphVizDumper::Ptr aid = P2::Modules::CfgGraphVizDumper::instance(s.substr(8));
			partitioner.cfgAdjustmentCallbacks().append(aid);
		} else if (boost::starts_with(s, "hexdump:")) {
			P2::Modules::HexDumper::Ptr aid = P2::Modules::HexDumper::instance(s.substr(8));
			partitioner.cfgAdjustmentCallbacks().append(aid);
		} else if (boost::starts_with(s, "insn-list:")) {
			P2::Modules::InstructionLister::Ptr aid = P2::Modules::InstructionLister::instance(s.substr(10));
			partitioner.cfgAdjustmentCallbacks().append(aid);
		} else if (boost::starts_with(s, "debugger:")) {
			P2::Modules::Debugger::Ptr aid = P2::Modules::Debugger::instance(s.substr(9));
			partitioner.cfgAdjustmentCallbacks().append(aid);
		} else {
			throw std::runtime_error("invalid debugging aid for \"trigger\" switch: " + s);
		}
	}
	// Show what we'll be working on (stdout for the record, and diagnostics also)
	if (settings.doShowMap)
		partitioner.memoryMap().dump(mlog[INFO]);

	// Find functions for an interrupt vector.
	engine.makeInterruptVectorFunctions(partitioner, settings.interruptVector);

	/*Run the partitioner: disassemble and partition - Does the following steps
	 *
	 * Find interesting places at which to disassemble.  This traverses the interpretation (if any) to find things like
	 * specimen entry points, exception handling, imports and exports, and symbol tables.
	 * => engine.makeContainerFunctions(partitioner, interp);
	 *
	 * Do an initial pass to discover functions and partition them into basic blocks and functions. Functions for which the CFG
	 * is a bit wonky won't get assigned any basic blocks (other than the entry blocks we just added above).
	 * => engine.discoverFunctions(partitioner);
	 * Perform a final pass over all functions and issue reports about which functions have unreasonable control flow.
	 * => engine.attachBlocksToFunctions(partitioner, true); 
	 */
	engine.runPartitioner(partitioner);

	// Attach Data addressess to the function where it is getting used
	engine.attachSurroundedDataToFunctions(partitioner);

	// Loading of the configuation files especially built for this Analysis
	if (!settings.configurationName.empty()) {
		if(settings.verbose)
			mlog[INFO] <<"loading configuration files";
		partitioner.configuration().loadFromFile(settings.configurationName);
		if(settings.verbose)
			mlog[INFO] <<"; configured\n";
	}

	// Various fix-ups
	if (settings.findDeadCode)
		engine.attachDeadCodeToFunctions(partitioner);  // find unreachable code and add it to functions
	if (settings.findFunctionPadding)
		engine.attachPaddingToFunctions(partitioner);   // find function alignment padding before entry points
	if (settings.intraFunctionCode)
		engine.attachAllSurroundedCodeToFunctions(partitioner);
	if (settings.intraFunctionData)
		engine.attachSurroundedDataToFunctions(partitioner); // find data areas that are enclosed by functions

	// FixUp the library call thunks which are not idetified by Rose
	CS::libraryThunkFixups(partitioner,interp);

	// Analyze each basic block and function and cache results.  We do this before listing the CFG or building the AST.
	if (settings.doPostAnalysis) {
		if(settings.verbose)
			mlog[INFO] <<"running all post analysis phases\n";
		engine.updateAnalysisResults(partitioner);
	}

	mlog[INFO]<<" finished partitioning in : "<<timer.stop()<<" seconds\n";

	//-------------------------------------------------------------- 
	// The rest of main() is just about showing the results...
	//--------------------------------------------------------------

	if (settings.doShowStats) {
		mlog[INFO] <<"CFG contains " <<StringUtility::plural(partitioner.nFunctions(), "functions") <<"\n";
		mlog[INFO] <<"CFG contains " <<StringUtility::plural(partitioner.nBasicBlocks(), "basic blocks") <<"\n";
		mlog[INFO] <<"CFG contains " <<StringUtility::plural(partitioner.nDataBlocks(), "data blocks") <<"\n";
		mlog[INFO] <<"CFG contains " <<StringUtility::plural(partitioner.nInstructions(), "instructions") <<"\n";
		mlog[INFO] <<"CFG contains " <<StringUtility::plural(partitioner.nBytes(), "bytes") <<"\n";
		mlog[INFO] <<"Instruction cache contains "
			<<StringUtility::plural(partitioner.instructionProvider().nCached(), "instructions") <<"\n";
	}

	// Export Control Flow graph if the appropriate flag is set in settings
	emitControlFlowGraphs(partitioner, settings);
	// Export Function Call graph if the appropriate flag is set
	emitFunctionCallGraph(partitioner, settings);

	// Lists Address Usage map of the PE file
	if (settings.doListAum) {
		mlog[INFO] <<"Final address usage map:\n";
		partitioner.aum().print(mlog[INFO], "  ");
	}

	// Lists all functions identified the rose partitioner2
	if (settings.doListFunctions) {
		BOOST_FOREACH (const P2::Function::Ptr& function, partitioner.functions()) {
			rose_addr_t entryVa = function->address();
			mlog[INFO] <<partitioner.functionName(function) <<" -> "<<StringUtility::intToHex(entryVa)<<"\n";
		}
	}

	// File setup for outputing the defuse chain data structure
	std::filebuf useDefFile;
	if(settings.doOutputDefUse){
		if ( settings.doOutputDefUse && !settings.defUseOutputFile.empty())
			useDefFile.open(settings.defUseOutputFile.c_str(),std::ios::out);
		else
			throw std::runtime_error("no output file specified; see --help");
	}
	std::ostream defUseOs(&useDefFile);

	// File setup for outputing the object data structure
	std::filebuf yamlOutputFile;
	if(settings.doOutputObjects){
		if (!settings.yamlOutputFile.empty())
			yamlOutputFile.open(settings.yamlOutputFile.c_str(),std::ios::out);
		else
			throw std::runtime_error("no yaml outfile specified; see --help");
	}
	std::ostream yamlObjectOs(&yamlOutputFile);


	// Setup for DEF-USE chain building Engine
	const RegisterDictionary *regdict = partitioner.instructionProvider().registerDictionary();

	// SMTSolver - can be used dynamic linkage as well as static executable linkage
	// currently dynamic linkage is not working so using statci executable linkage
	SMTSolver *solver = NULL;
	if(settings.useSMTSolver)
		solver = getSolver();

	// Creating an instance of the Modified Risoperator class specially build for this def-Use analysis
	CS::RiscOperatorsPtr ops = CS::RiscOperators::instance(regdict,map,solver);

	// Setting the flag to build the defuse chain
	// If this flag is not set then the def-use will not build the def use chain
	ops->set_compute_useDefChain();

	// Dispatcher class instance for the input specimen.
	// Depending on the specimen type, Dispatcher class can be different, like for X86 specimen, it will
	// be DispatcherX86, for Powerpc specimen DispatcherPowerPc
	P2::BaseSemantics::DispatcherPtr cpu = partitioner.instructionProvider().dispatcher()->create(ops);

	// Especial FunctionCallGraph built for the Def-Use Analysis
	P2::FunctionCallGraph cg = functionCallGraph(partitioner);

	// Main Engine to build the Def-Use chain
	const IS2::BaseSemantics::RiscOperatorsPtr& ops_ = cpu->get_operators();
	CS::Engine buildEngine(partitioner,cpu,cg,ops_,settings,solver);

	// STAGE - 1 Calculate the InterProcedural DataFlow analysis data-structures
	// * This the most important BASE for the further deduction algorithm
	// * Def-Use chain is build using the Summary Based DataFlow analysis as mentioned in the paper - LisTT 
	//   @ref [http://binsec.gforge.inria.fr/pdf/saw14-verimag.pdf] but completely different implementation
	//   and precise according the requirement of the further analysis.
	// * Summary of the function is saved in the data-structure made especially for the summary required for
	//   connection of different functions so that the further requirement is full-filled for connections
	// * Chain is made Interprocedural but connecting the different functions at the call instructions.
	// * Calling convention is also identified during the def-use chain building which helps in connecting
	//   functions and following dataflow accross the functions.
	// * Currently connection between functions are made by making the dependencies at the call instruction
	//   with the arguments supplied to the called function and making a proper assumption if the function
	//   returns the this-ptr supplied in ECX register.
	timer.restart();
	buildEngine.buildDependencies();
	if(settings.doOutputDefUse){
		buildEngine.print(defUseOs);
		useDefFile.close();
	}
	mlog[INFO]<<"Completed STAGE 1 in "<<timer.stop()<<" seconds"<<std::endl;

	// Main Engine for Extracting C++ Object Oriented Data-Structures
	CS::ExtractOOP extracter(partitioner,cpu,buildEngine,ops_,settings,solver);
	extracter.setrdataAddressRange(interp);
	extracter.setStaticDataRange(interp);
	extracter.setTextSectionRange(interp);

	// Stage - 2 Find __thiscall convention following Functions for further Analysis.
	// Looking for thiscall__ calling conventions only because by default C++ Object methods uses thiscall__ calling
	// conventions only but it can be changed specifically for each methods

	// [STAGE 3] Identify Object instances,this-ptrs,Methods,Contructors and inheritance

	// Identifying object instances,this-ptrs,methods,constructors and inheritence of the objects
	// initiated by the "new" library call (i.e. Heap Objects)
	// * Top-to-Bottom method to find Objects

	// [STAGE 4] Find Virtual Function Table for each class/Object Identified
	// * Virtual table is found when an .rodata address is written at the this-ptr of that class
	// using mov [reg],XXXXXX where XXXXX is the virtual table pointer

	// built from all the cross references of the already found contructors
	// For example :-
	//  * Suppose a Class named object1 has a constructor [ object1:object() ] which is already identified by
	//    the above findHeapThisPtr.
	//  * This function tries to find all the cross references to the function(object1:object()) and starts 
	//    building from bottom-to-top. Suppose that cross reference is in function main(), then this function
	//    search for the instrcution which is calling the object1 constructor and detect all the new this-ptrs
	//    found in the main function and follow the top-down procedure(as followed by the findHeapThisPtr) from there

	// [STAGE 5] Identify Data Members corresponding to each function
	// * Data Members are found if some value is written to or read from an address in the address range of the class
	// * These Data Members are found by analysing the class methods of each class to find all instances following
	//   one of the following cases :-
	//    -  Uses [ecx+xxx] where xxx is the offset of the dataMember and the size of the value read gives the size of
	//       datamember
	//    -  Defines [ecx+xxx] where xxx is the offset of the dataMember and the size of the value written gives the size of
	//       datamember
	timer.restart();
	extracter.extractAllObjects();
	mlog[INFO]<<"Completed Object Extraction in "<<timer.stop()<<" seconds"<<std::endl;

	// Printing all the deduced Class/Objects details in yaml format
	// Can be converted into json by any online tool or python :P
	if(settings.doOutputObjects){
		extracter.print(yamlObjectOs);
		yamlOutputFile.close();
		mlog[INFO]<<"Successfully extracted all the Object information in : "<<settings.yamlOutputFile<<std::endl;
	}

	exit(0);
}
