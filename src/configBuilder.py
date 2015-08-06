#!/usr/bin/python

# ///
# ///     Written By: Shubham Bansal (illusionist.neo@gmail.com)
# ///     Blog :- http://in3o.me
# ///
# /// The MIT License (MIT)

# /// Copyright (c) 2015 Shubham Bansal(iN3O)

# /// Permission is hereby granted, free of charge, to any person obtaining a copy
# /// of this software and associated documentation files (the "Software"), to deal
# /// in the Software without restriction, including without limitation the rights
# /// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# /// copies of the Software, and to permit persons to whom the Software is
# /// furnished to do so, subject to the following conditions:

# /// The above copyright notice and this permission notice shall be included in
# /// all copies or substantial portions of the Software.

# /// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# /// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# /// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# /// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# /// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# /// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# /// THE SOFTWARE.

import json
import glob,os
for files in glob.glob("../data/win/*.idt"):
	exports = {}
	with open(files,"r") as fp:
		dllName = ""
		for line in fp:
			if ";" not in line:
				args = line.split()
				if len(args)>0 and args[0] == "0" :
					dllName = args[1].split("=")[1].split(".dll")[0].upper()+".dll"
				elif len(args)>=2 and args[0].isdigit():
					ordinal = args[0]
					convention = "stdcall"
					functionName = args[1].split("=")[1]
					delta="-4"
					if len(args)==3:
						delta = str(int(args[2].split("=")[1])-4)
					elif len(args)==4:
						delta = str(int(args[3].split("=")[1])-4)
					if dllName=="":
						print files
					exports[dllName+":"+functionName] ={"function":{"convention":convention,"delta":delta},"ordinal":ordinal}
				else:
					if line.strip() is not "":
						print "Ignoring",line
	final = {"config":{"exports": exports}}
	fd = open("../data/windowsAPI/"+os.path.basename(files).split(".")[0]+".json","wb+")
	json.dump(final,fd)
	fd.close()
