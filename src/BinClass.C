///
///     Written By: Shubham Bansal (illusionist.neo@gmail.com)
///     Copyright(c) Shubham Bansal
///

#include "sage3basic.h"
#include <rose.h>
#include <rosePublicConfig.h>
#include <rose_strtoull.h>
#include <iostream>
#include <fstream>
#include <AsmFunctionIndex.h>
#include <AsmUnparser.h>
#include <BinaryControlFlow.h>
#include <BinaryLoader.h>
#include <Disassembler.h>
#include <Partitioner2/GraphViz.h>
#include <Partitioner2/ModulesM68k.h>
#include <Partitioner2/ModulesPe.h>
#include <Partitioner2/Modules.h>
#include <Partitioner2/Utility.h>
#include <Diagnostics.h>
#include <InterDataFlow.h>
#include <thisCallAnalysis.h>
#include <Partitioner2/Engine.h>
#include <Partitioner2/ControlFlowGraph.h>
#include <Partitioner2/Partitioner.h>
#include <sawyer/GraphTraversal.h>
#include <SymbolicSemantics2.h>
#include <rose_strtoull.h>
#include <sawyer/Assert.h>
#include <sawyer/CommandLine.h>
#include <sawyer/ProgressBar.h>
#include <sawyer/Stopwatch.h>
#include <stringify.h>

using namespace rose::Diagnostics;
using namespace rose::BinaryAnalysis;
using namespace rose;
using namespace Sawyer::Message::Common;

namespace IS2 = InstructionSemantics2;
namespace P2 = Partitioner2;
namespace ID = P2::InterDataFlow;
namespace CS = P2::CallSemantics;

enum DataFlowType{
	INTERPROCEDURAL,
	INTRAPROCEDURAL,
};


struct Settings{
	std::string isaName;                                // instruction set architecture name
	AddressInterval interruptVector;                    // table of interrupt handling functions
	bool allowDiscontiguousBlocks;                      // can basic blocks be discontiguous in memory?
	bool findFunctionPadding;                           // look for pre-entry-point padding?
	bool findDeadCode;                                  // do we look for unreachable basic blocks?
	bool useSemantics;                                  // should we use symbolic semantics?
	bool doPostAnalysis;                                // perform post-partitioning analysis phase?
	bool doListCfg;                                     // list the control flow graph
	bool doListAum;                                     // list the address usage map
	bool doListAsm;                                     // produce an assembly-like listing with AsmUnparser
	bool doListFunctions;                               // produce a function index
	bool doListFunctionAddresses;                       // list function entry addresses
	bool doListInstructionAddresses;                    // show instruction addresses
	bool doListContainer;                               // generate information about the containers if present
	bool doShowStats;                                   // show some statistics
	bool doShowMap;                                     // show the memory map
	std::vector<std::string> triggers;                  // debugging aids
	std::string gvBaseName;                             // base name for GraphViz files
	bool gvShowInstructions;                            // show disassembled instructions in GraphViz files?
	std::vector<std::string> gvCfgFunctions;            // produce CFG dot files for these functions
	bool gvCallGraph;                                   // produce a function call graph?
	DataFlowType interOrIntra;                          // Select the type of Data-Flow Analysis
	bool doPrintDefUse;                                 // Print def-use chain or not
	rose_addr_t depth;                                  // Depth you want to go for interProcedural analysis
	rose_addr_t maxIterations;                          // Maximum number of iteration to run dataFlow Analysis to
	rose_addr_t minHeapAllocSize;                       // Minimum heap size allocated to each heap allocation - required for new library call
	rose_addr_t maxIterationsPerVertex;                 // Maximum no. of times each Vertex is analysed - saving from wasting iteration in future
	std::string startVertexName;                        // starting function vertex name/address
	std::string outputFile;                             // Output FileName
	Settings():
		isaName("i386"),doPostAnalysis(true),doListCfg(false),doListAum(false),doListAsm(true),
		doListFunctions(false),doListFunctionAddresses(false),doPrintDefUse(false),useSemantics(true),
		doShowMap(false),startVertexName("start_"),outputFile("output.txt"),maxIterations(10000),minHeapAllocSize(0x100),
		doListInstructionAddresses(false),doShowStats(false),gvShowInstructions(true),gvCallGraph(false),depth(10),
		allowDiscontiguousBlocks(true),findFunctionPadding(true),findDeadCode(true),maxIterationsPerVertex(5){}
};

// Describe and parse the command-line
static Sawyer::CommandLine::ParserResult
parseCommandLine(int argc, char *argv[], Settings &settings){
	using namespace Sawyer::CommandLine;


	Parser parser;
	parser
		.purpose("Finds C++ Object Oriented dataStructures from Binary/Malware")
		.version("1.0v", ROSE_CONFIGURE_DATE)
		.chapter(1, "BinFlow - Command-line Switches")
		.doc("Synopsis",
				"@prop{programName} [@v{switches}] @v{specimen_names}")
		.doc("Description",
				"Parses,dissassembles,partitions the specimens,builds Def-Use chain and deduces OOP structures")
		.doc("Specimens", P2::Engine::specimenNameDocumentation())
		.doc("Bugs","[Lot]-bugs",
				"Surely Many, and we're interested in every single of them. Send them to <illusionist.neo@gmail.com>.");

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

	dis.insert(Switch("interrupt-vector")
			.argument("addresses", P2::addressIntervalParser(settings.interruptVector))
			.doc("A table containing addresses of functions invoked for various kinds of interrupts. " +
				P2::AddressIntervalParser::docString() + " The length and contents of the table is architecture "
				"specific, and the disassembler will use available information about the architecture to decode the "
				"table.  If a single address is specified, then the length of the table is architecture dependent, "
				"otherwise the entire table is read."));


	SwitchGroup dataFlow("DataFlow switches");
	dataFlow.insert(Switch("list-def-use")
			.intrinsicValue(true,settings.doPrintDefUse)
			.doc("Analyse the specimen. Do Dataflow Analaysis using the standard WorKList Algorithm and build Def-Use Chain."
				"Print Def-Use chains Interprocedural/Interaprocedural depending on switch @s{select-type} mentioned"));
	dataFlow.insert(Switch("start-function")
			.argument("Function name/address",anyParser(settings.startVertexName))
			.doc("Starting Function name to start the parsing and dataflow.Instead of name, address can also b given in hex like 0xdeadbeef."
				"Do @s{list-functions} to list function names and address"));
	dataFlow.insert(Switch("select-type")
			.argument("DataFlowType",enumParser(settings.interOrIntra)
				->with("inter",INTERPROCEDURAL)
				->with("intra",INTRAPROCEDURAL)
				->with("default",INTERPROCEDURAL))
			.doc("Select which type of DataFlow you want.It could be interprocedural or intraprocedural depending upon"
				"the switch paramenter. \"inter\" will do interprocedural which is default and highly recommeneded to give"
				"precise details of dataflow among different functions. "));
	dataFlow.insert(Switch("inter-depth")
			.argument("depth",nonNegativeIntegerParser(settings.depth),"10")
			.doc("Select depth of the function call you want dataflow to analyse. Recommeneded depth is <= 10. But it all"
				"depends on the binary/Malware."));
	dataFlow.insert(Switch("max-iter")
			.argument("maxIterations",nonNegativeIntegerParser(settings.maxIterations),"10000")
			.doc("Select the maximum no. of iteration to run dataFlow Analysis to"));
	dataFlow.insert(Switch("min-heap-alloc-size")
			.argument("minHeapAllocSize",nonNegativeIntegerParser(settings.minHeapAllocSize),"256")
			.doc("Minimum heap size allocated to each heap allocation - required for new library call"));//minHeapAllocSize
	dataFlow.insert(Switch("max-iter-per-vertex")
			.argument("maxIterationsPerVertex",nonNegativeIntegerParser(settings.maxIterationsPerVertex),"5")
			.doc("Maximum no. of times each Vertex is analysed - saving from wasting iteration in future"));


	// Switches for output
	SwitchGroup out("Output switches");
	out.insert(Switch("list-asm")
			.intrinsicValue(true, settings.doListAsm)
			.doc("Produce an assembly listing.  This is the default; it can be turned off with @s{no-list-asm}."));
	out.insert(Switch("no-list-asm")
			.key("list-asm")
			.intrinsicValue(false, settings.doListAsm)
			.hidden(true));
	out.insert(Switch("list-cfg")
			.intrinsicValue(true, settings.doListCfg)
			.doc("Emit a listing of the CFG after it is discovered."));
	out.insert(Switch("no-list-cfg")
			.key("list-cfg")
			.intrinsicValue(false, settings.doListCfg)
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
	out.insert(Switch("list-function-addresses")
			.intrinsicValue(true, settings.doListFunctionAddresses)
			.doc("Produce a listing of function entry addresses, one address per line in hexadecimal format. Each address "
				"is followed by the word \"existing\" or \"missing\" depending on whether a non-empty basic block exists "
				"in the CFG for the function entry address.  The listing is disabled with @s{no-list-function-addresses}. "
				"See also, @s{select-functions}."));
	out.insert(Switch("no-list-function-addresses")
			.key("list-function-addresses")
			.intrinsicValue(false, settings.doListFunctionAddresses)
			.hidden(true));
	out.insert(Switch("list-instruction-addresses")
			.intrinsicValue(true, settings.doListInstructionAddresses)
			.doc("Produce a listing of instruction addresses.  Each line of output will contain three space-separated "
				"items: the address interval for the instruction (address followed by \"+\" followed by size), the "
				"address of the basic block to which the instruction belongs, and the address of the function to which "
				"the basic block belongs.  If the basic block doesn't belong to a function then the string \"nil\" is "
				"printed for the function address field.  This listing is disabled with the "
				"@s{no-list-instruction-addresses} switch.  The default is to " +
				std::string(settings.doListInstructionAddresses?"":"not ") + "show this information."));
	out.insert(Switch("no-list-instruction-addresses")
			.key("list-instruction-addresses")
			.intrinsicValue(false, settings.doListInstructionAddresses)
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
	out.insert(Switch("Output")
			.argument("Output File",anyParser(settings.outputFile))
			.doc("Output File name for output"));

	// Switches controlling GraphViz output
	SwitchGroup dot("Graphviz switches");
	dot.insert(Switch("gv-basename")
			.argument("path", anyParser(settings.gvBaseName))
			.doc("Base name for GraphViz dot files.  The full name is created by appending details about what is "
				"contained in the file.  For instance, a control flow graph for the function \"main\" has the "
				"string \"cfg-main.dot\" appended.  The default is \"" + settings.gvBaseName + "\"."));
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

int main( int argc, char * argv[] ){

	// Configure diagnostic output
	rose::Diagnostics::initialize();
	Settings settings;
	// Parse the command-line
	Sawyer::CommandLine::ParserResult cmdline = parseCommandLine(argc, argv, settings);
	std::vector<std::string> specimenNames = cmdline.unreachedArgs();
	std::string filename("TestCaseCreator.exe");
	std::string startvertexname="start_";
	Disassembler *disassembler = NULL;
	if (!settings.isaName.empty())
		disassembler = Disassembler::lookup(settings.isaName);
	if (specimenNames.empty())
		throw std::runtime_error("no specimen specified; see --help");
	if(!settings.startVertexName.empty())
		startvertexname = settings.startVertexName;
	// Create an engine to drive the partitioning.  This is entirely optional, you can do all the things manually also.  
	// All an engine does is define the sequence of partitioning calls that need to be made in order to recognize instructions, 
	// basic blocks, data blocks, and functions. We instantiate the engine early because it has some nice methods that we can use.
	Partitioner2::Engine engine;

	// Load the specimen as raw data or an ELF or PE container.
	MemoryMap map = engine.load(specimenNames);

	// Obtain which disassembler to use , like - x86,x64
	if (NULL==(disassembler = engine.obtainDisassembler(disassembler)))
		throw std::runtime_error("an instruction set architecture must be specified with the \"--isa\" switch");

	// Get the primary interpretation needed below (ELF has only one).
	SgAsmInterpretation *interp = engine.interpretation();
	ASSERT_not_null(interp);

	// Create a partitioner that's tuned for a certain architecture, and then tune it even more depending on our command-line.
	Sawyer::Stopwatch partitionTime;
	Partitioner2::Partitioner partitioner = engine.createTunedPartitioner();
	// Enable Symbolic Execution
	partitioner.enableSymbolicSemantics(settings.useSemantics);
	// Insert Callbacks each time a new Basic Block is identified, This is to adjust the CFG according to the needs
	partitioner.basicBlockCallbacks().append(ID::PePrivilege::instance());
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

	Stream info(mlog[INFO] <<"Starting Disassembler,partitioning,building Logs");
	// Find functions for an interrupt vector.
	engine.makeInterruptVectorFunctions(partitioner, settings.interruptVector);
	// Run the partitioner: disassemble and partition
	engine.runPartitioner(partitioner, interp);

	// Attach Data addressess to the function where it is getting used
	engine.attachSurroundedDataToFunctions(partitioner);

	// Attach Some Padding to each function before and after function address interval
	engine.attachPaddingToFunctions(partitioner);

	// Various fix-ups
	if (settings.findDeadCode)
		engine.attachDeadCodeToFunctions(partitioner);  // find unreachable code and add it to functions
	if (settings.findFunctionPadding)
		engine.attachPaddingToFunctions(partitioner);   // find function alignment padding before entry points

	// Now that the partitioner's work is all done, try to give names to some things.  Most functions will have been given
	// names when we marked their locations, but import thunks can be scattered all over the place and its nice if we give them
	// the same name as the imported function to which they point.  This is especially important if there's no basic block at
	// the imported function's address (i.e., the dynamic linker hasn't run) because ROSE's AST can't represent basic blocks
	// that have no instructions, and therefore the imported function's address doesn't even show up in ROSE.
	engine.applyPostPartitionFixups(partitioner, interp);

	// Analyze each basic block and function and cache results.  We do this before listing the CFG or building the AST.
	if (settings.doPostAnalysis) {
		mlog[INFO] <<"running all post analysis phases (--post-analysis)\n";
		engine.updateAnalysisResults(partitioner);
	}

	info <<"; completed in " <<partitionTime <<" seconds.\n";

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

	mlog[INFO]<<"Starting Vertex : "<<startvertexname<<std::endl; 
	P2::ControlFlowGraph::ConstVertexIterator startVertex = ID::vertexForInstruction(partitioner, startvertexname);
	if (startVertex == partitioner.cfg().vertices().end())
		throw std::runtime_error("no --begin vertex at " + startvertexname);

	/// Initialise New Inter-Procedural ControlFlowGraph instance
	ID::DfCfgBuilder dfcfgbuilder(partitioner,partitioner.cfg(),ID::INTERPROCEDURAL,settings.depth);
	if(INTERPROCEDURAL!=settings.interOrIntra){
		dfcfgbuilder.interproceduralPredicate = ID::NOT_INTERPROCEDURAL;
	}

	// Build the starting graph from the beginVertex
	// This Graph doesn't contain the virtual function attached to them - We need
	// to process the graph to get those virtual function and attach it to the CFG
	mlog[INFO]<<"Building Inter-Procedural Control Flow Graph\n";
	try{
		dfcfgbuilder.startBuilding(startVertex);
	}catch (...){
		mlog[ERROR]<<"Error in Building Inter-Procedural Control Flow Graph\n";
	}
	ID::DfCfg &dfcfg = dfcfgbuilder.getdfCfg();
	std::filebuf fb;
	if (!settings.outputFile.empty())
		fb.open(settings.outputFile.c_str(),std::ios::out);
	else
		throw std::runtime_error("no outfile specified; see --help");
	std::ostream os(&fb);
	// Dump the Inter-Procedural Control Flow Graph with Virtual Function attached to them
	if(settings.doListCfg)
		dumpDfCfg(os,dfcfg);

	/// Initialising and Setting Up various settings and classes to work with them in future for analysis
	const RegisterDictionary *regdict = partitioner.instructionProvider().registerDictionary();
	ID::RiscOperatorsPtr ops = ID::RiscOperators::instance(regdict,map);
	ASSERT_always_not_null(ops);
	P2::BaseSemantics::DispatcherPtr cpu = partitioner.instructionProvider().dispatcher()->create(ops);
	RegisterDescriptor STACK_POINTER = partitioner.instructionProvider().stackPointerRegister();
	RegisterDescriptor STACK_SEGMENT = partitioner.instructionProvider().stackSegmentRegister();
	rose_addr_t startVertexId = dfcfgbuilder.findVertex(startVertex)->id();
	ID::Engine buildDependencies(dfcfg,cpu,partitioner,settings.maxIterations,settings.minHeapAllocSize,settings.maxIterationsPerVertex);

	// [STAGE 1] Calculate the InterProcedural DataFlow analysis
	buildDependencies.runToFixedPoint(startVertexId,buildDependencies.initialState());
	if(settings.doPrintDefUse){
		mlog[INFO]<<"Printing out the Reaching Definitions to the file : "<<settings.outputFile<<std::endl;
		try{
			buildDependencies.print(os);
		}catch(...){
			mlog[WARN]<<"Got error in printing the Reaching Definitions"<<std::endl;
		}
		mlog[INFO]<<"DONE printing the Reaching Definitions"<<std::endl;
	}

	// [STAGE 2] Find __thiscall convention following Functions for further Analysis
	CS::thisCallFunctions thiscall(partitioner,buildDependencies.useChain,buildDependencies.defChain,
			buildDependencies.depOnChain,buildDependencies.depOfChain,cpu,dfcfgbuilder.functionToInstruction,
			buildDependencies.startHeap,STACK_SEGMENT);
	mlog[INFO]<<"Starting detecting Calling conventions in functions. Looking for thiscall__ calling conventions only"
		<<std::endl;
	thiscall.detectCallingConvention();

	// [STAGE 3] Identify Object instances , Methods and Contructors
	mlog[INFO]<<"Starting to find the thisptrs and constructors corresponding to those thisptrs "<<std::endl;
	mlog[INFO]<<"Looking for May Be constructors"<<std::endl;
	thiscall.lookupMayBeConstructors();
	mlog[INFO]<<"Analyzing all instances initialized by new library call[GLOBAL]"<<std::endl;
	BOOST_FOREACH(SgAsmInstruction *insn ,dfcfgbuilder.newCallingInstructions)
		thiscall.findObjectMethodsFromNew(insn,dfcfgbuilder.newIATAddress);
	mlog[INFO]<<"Analyzing all instances initialized by lea instruction[LOCAL]"<<std::endl;
	BOOST_FOREACH(SgAsmInstruction* insn,buildDependencies.classInstanceStart)
		thiscall.findObjectMethodsFromLea(insn);

	// [STAGE 4] Find Virtual Function Table
	mlog[INFO]<<"Starting analysis of Virtual Functions Tables "<<std::endl;
	BOOST_FOREACH(const P2::Function::Ptr &constructor , thiscall.sureConstructors){
		mlog[INFO]<<"Analysing function : "<<StringUtility::intToHex(constructor->address())<<std::endl;
		BOOST_FOREACH(const P2::BaseSemantics::SValuePtr &thisptr,thiscall.classMap[constructor]->thisptrs){
			thiscall.findVirtualTable(constructor,thisptr);
		}
	}

	// [STAGE 5] Find the inheritance
	mlog[INFO]<<"Starting looking for inheritance of each class"<<std::endl;
	BOOST_FOREACH(const P2::Function::Ptr &constructor , thiscall.sureConstructors){
		mlog[INFO]<<"Analysing Class with id : "<<StringUtility::numberToString(thiscall.classMap[constructor]->id)<<
			" for inheritance"<<std::endl;
		thiscall.lookForInheritance(constructor);
	}

	// [STAGE 5] Identify DataMembers corresponding to each function
	mlog[INFO]<<"Starting analysis of functions for DataMembers"<<std::endl;
	thiscall.findDataMembers(settings.minHeapAllocSize);

	// Print Deducted Classes
	mlog[INFO]<<"Printing out the classes deducted to the file : "<<settings.outputFile<<std::endl;
	BOOST_FOREACH(CS::classDetails::Ptr &eachclass , thiscall.classMap.values()){
		eachclass->print(os);
	}
	mlog[INFO]<<"Done Everything.\n"<<"Adios Amigo"<<std::endl;
	fb.close();

	exit(0);
}
