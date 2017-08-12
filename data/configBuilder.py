#!/usr/bin/python

import json
import glob,os
for files in glob.glob("win/*.idt"):
	exports = {}
	print files
	with open(files,"r") as fp:
		dllName = ""
		for line in fp:
			if ";" in line:
				print "Ignoring ",line
			else:
				args = line.split()
				if len(args)>0 and args[0] == "0" :
					dllName = args[1].split("=")[1].split(".dll")[0].upper()+".dll"
				elif len(args)>=2 and args[0].isdigit():
					ordinal = args[0]
					convention = "stdcall"
					functionName = args[1].split("=")[1]
					delta="0"
					if len(args)==3:
						delta = str(int(args[2].split("=")[1])/4)
					elif len(args)==4:
						delta = str(int(args[3].split("=")[1])/4)
					exports[dllName+":"+functionName] ={"function":{"convention":convention,"delta":delta},"ordinal":ordinal}
				else:
					print "Ignoring ",line
	final = {"config":{"exports": exports}}
	fd = open(os.path.basename(files).split(".")[0]+".json","wb+")
	json.dump(final,fd)
	fd.close()
