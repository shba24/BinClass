# README #

### BinClass ###

* Recovering Object information from a C++ compiled Binary/Malware (mainly written for PE files) , linked dynamically and completely Stripped.
* 0.4v **last updated on 3-July-2015**

### How to Use ? ###

**Option 1**: Download and Install Rose Compiler from git repository. Build Rose and its dependencies on your PC.

#### BOOST Library Installation ####
   * Download BOOST at www.boost.org/users/download (suggested to use version<=1.53 )
   * tar -zxf BOOST-[VersionNumber].tar.gz
   * mkdir installTree (eg. BOOST_INSTALL )
   * ./bootstrap.sh --prefix=[installTree] (For help use ./bootstrap.sh --help )
   * ./bjam install --prefix=[installTree]

* You might need to compile some boost
libraries also. I usually need these for boost-1.53: chrono date_time
filesystem iostreams program_options random regex signals system
thread wave. I also add "-sNO_COMPRESSION=1 -sNO_ZLIB=1 -sNO_BZIP2=1"
to the bjam (or b2) command.

#### Rose Framework Installation ####
   * git clone https://github.com/iN3O/edg4x-rose
   * mkdir buildRose
   * cd buildRose
   * export JAVA_HOME=/usr/apps/java/jdk1.5.0-11
   * export LD_LIBRARY_PATH=$JAVA_HOME/jre/lib/i386/server:$LD_LIBRARY_PATH
   * export LD_LIBRARY_PATH=[BOOST_INSTALL]/lib:$LD_LIBRARY_PATH
   * ../edg4x-rose/configure --prefix=[ROSE_INSTALL] --with-boost=[BOOST_INSTALL] ----with-  boost-libdir=BOOST_INSTALL/lib  --without-haskell --disable-php --disable-cuda --disable- doxygen-developer-docs --with-yaml=/path/to/yaml --with-yices=/path/to/yices  --enable-binary-analysis --with-boost-thread --with-java=$JAVA_HOME  --with-C_OPTIMIZE=-O0 --with-CXX_OPTIMIZE=-O0  ( ROSE_INSTALL is the location where you want to install Rose )
   * make -jx ( where x is the number of core you want to build with. suggested "3" )
   * make check ( for testing the installation ) (optional)
   * make install
   * make installcheck ( for testing the installation ) (optional)

**NOTE** : This might take from 2-4 hours. If you can't wait that long then look at option 2 [below].

***Option 2** : [Download](http://www.rosecompiler.org/Ubuntu-ROSE-Demo-V2.tar.gz)(6.8 GB) the Ubuntu 14.04 Virtual machine build with all necessary flags.
  * Username : demo
  * password : password

#### Dependencies ####
  * BOOST Library (version<=1.53)
  * YAML library [download](https://github.com/jbeder/yaml-cpp)
  * Yices SMT Solver library [version 1.0.40](http://yices.csl.sri.com/cgi-bin/yices-newlicense.cgi?file=yices-1.0.40-x86_64-unknown-linux-gnu-static-gmp.tar.gz )

#### Using BinClass ####
  * Go to BinClass/src directory
  * make clean
  * make install
  * ./BinClass --help ( for help with flags and all )
  * (For Example)./BinClass --output-def-use --yaml-file ../results/test_12.yaml ../testfiles/test_12.exe

### TO DO List ###

* Check TO DO file.

### Contact me ###

* Shubham Bansal (iN3O) [ illusionist.neo@gmail.com ]
