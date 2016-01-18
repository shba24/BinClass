## A sample Makefile to build a ROSE tool.
##
## Important: remember that Makefile recipes must contain tabs:
##
##     <target>: [ <dependency > ]*
##         [ <TAB> <command> <endl> ]+
## So you have to replace spaces with Tabs if you copy&paste this file from a browser!

## ROSE installation contains
##   * libraries, e.g. "librose.la"
##   * headers, e.g. "rose.h"
ROSE_INSTALL=/usr/local/Rose

## ROSE uses the BOOST C++ libraries
BOOST_INSTALL=/root/boost/1.50.0

## Your translator
TRANSLATOR=BinClass
TRANSLATOR_SOURCE=$(TRANSLATOR).C

## Input testcode for your translator
TESTCODE=testcode.cpp

#ROSE_LIBS = $(top_builddir)/src/librose.la -lm  $(JAVA_JVM_LINK) \
#  $(SQLITE_DATABASE_LIBS) $(QT_LIBS)  $(BOOST_LDFLAGS) $(BOOST_DATE_TIME_LIB) \
#  $(BOOST_THREAD_LIB) $(BOOST_FILESYSTEM_LIB) $(BOOST_PROGRAM_OPTIONS_LIB) \
#  $(BOOST_REGEX_LIB)  $(BOOST_SYSTEM_LIB) $(BOOST_SERIALIZATION_LIB)  \
#  $(BOOST_WAVE_LIB) $(BOOST_IOSTREAMS_LIB) $(SQLITE3_LDFLAGS)  $(RT_LIBS) \
#  $(ROSE_YICES_LIBS_WITH_PATH) $(ROSE_PHP_LIBS_WITH_PATH) $(ROSE_DWARF_LIBS_WITH_PATH) \
#  $(ROSE_GUI_LIBS_WITH_PATH) $(ROSE_QT_LIBS_WITH_PATH) $(ROSE_SSL_LIBS) $(ROSE_ETHER_LIBS) \
#  $(ROSE_INTEL_COMPILER_MATH_LIBS) $(ROSE_ATERM_LIBS) $(ROSE_EXPERIMENTAL_OFP_LIBS)

#ROSE_SEPARATE_LIBS = $(ROSE_LIBS)

BOOST_DATE_TIME_LIB = -lboost_date_time
BOOST_FILESYSTEM_LIB = -lboost_filesystem
BOOST_IOSTREAMS_LIB = -lboost_iostreams
BOOST_LDFLAGS = -L/root/boost/1.50.0/lib/
BOOST_PROGRAM_OPTIONS_LIB = -lboost_program_options
BOOST_REGEX_LIB = -lboost_regex
BOOST_SYSTEM_LIB = -lboost_system
BOOST_THREAD_LIB = -lboost_thread
BOOST_WAVE_LIB = -lboost_wave
ROSE_YICES_LIBS = -lyices
YAML_LIB = -lyaml-cpp



#-------------------------------------------------------------
# Makefile Targets
#-------------------------------------------------------------

all: $(TRANSLATOR)

# compile the translator and generate an executable
# -g is recommended to be used by default to enable debugging your code
# Note: depending on the version of boost, you may have to use something like -I $(BOOST_ROOT)/include/boost-1_40 instead. 
# g++ -g -c thisCallAnalysis.C -pthread -I../include -I$(BOOST_INSTALL)/include -I$(ROSE_INSTALL)/include/rose -L$(ROSE_INSTALL)/lib -L$(BOOST_INSTALL)/lib -lrose $(BOOST_IOSTREAMS_LIB) $(BOOST_SYSTEM_LIB) -o thisCallAnalysis.o
$(TRANSLATOR): $(TRANSLATOR_SOURCE)
	g++ -g -c ClassSemantics.C -O3 -fomit-frame-pointer -DNDEBUG  -I../include -pthread -I$(BOOST_INSTALL)/include -I../include -I/usr/lib/yices-1.0.40/include/ -I$(ROSE_INSTALL)/include/rose -L$(ROSE_INSTALL)/lib -L$(BOOST_INSTALL)/lib -lrose $(BOOST_IOSTREAMS_LIB) $(BOOST_SYSTEM_LIB) $(YAML_LIB) -o ClassSemantics.o
	g++ -g -c Engine.C -O3 -fomit-frame-pointer -DNDEBUG -I../include -pthread -I$(BOOST_INSTALL)/include -I../include -I/usr/lib/yices-1.0.40/include/ -I$(ROSE_INSTALL)/include/rose -L$(ROSE_INSTALL)/lib -L$(BOOST_INSTALL)/lib -lrose $(BOOST_IOSTREAMS_LIB) $(BOOST_SYSTEM_LIB) $(YAML_LIB) -o Engine.o
	g++ -g -c OopExtractAnalysis.C -O3 -fomit-frame-pointer -DNDEBUG -I../include -pthread -I$(BOOST_INSTALL)/include -I../include -I/usr/lib/yices-1.0.40/include/ -I$(ROSE_INSTALL)/include/rose -L$(ROSE_INSTALL)/lib -L$(BOOST_INSTALL)/lib -lrose $(BOOST_IOSTREAMS_LIB) $(BOOST_SYSTEM_LIB) $(YAML_LIB) -o OopExtractAnalysis.o
	g++ -g ClassSemantics.o OopExtractAnalysis.o Engine.o $(TRANSLATOR_SOURCE) -O3 -fomit-frame-pointer -DNDEBUG -pthread -I../include -I$(BOOST_INSTALL)/include -I/usr/lib/yices-1.0.40/include/ -L/usr/lib/jvm/ -I$(ROSE_INSTALL)/include/rose /usr/lib/yices-1.0.40/lib/libyices.a -L$(ROSE_INSTALL)/lib -L$(BOOST_INSTALL)/lib -lrose $(BOOST_IOSTREAMS_LIB) $(BOOST_SYSTEM_LIB) -lboost_filesystem $(YAML_LIB) -o $(TRANSLATOR)

# test the translator
check: $(TRANSLATOR)
	source ./set.rose ; ./$(TRANSLATOR) -c -I. -I$(ROSE_INSTALL)/include $(TESTCODE) 

clean:
	rm -rf $(TRANSLATOR) *.o rose_* *.dot

