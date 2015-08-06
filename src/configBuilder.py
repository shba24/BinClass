#!/usr/bin/python

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
