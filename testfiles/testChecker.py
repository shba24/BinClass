#!/usr/bin/python

import sys,os
from pdbparse.symlookup import Lookup
import pefile
import yaml
import json

if __name__=="__main__":
	if len(sys.argv) < 4 :
		print >> sys.stderr, "usage : %s <exe-file> <pdb-file> <yaml-file>"% sys.argv[0]
	PeFile = sys.argv[1]
	PdbFile = sys.argv[2]
	YamlFile = sys.argv[3]
	pe = pefile.PE(PeFile)
	BaseAddr = pe.OPTIONAL_HEADER.ImageBase
	lobj = Lookup([(PdbFile,BaseAddr)])
	lookup = lobj.lookup

	#####################################################3
	OriginalclassInfoYaml = yaml.load(open(YamlFile,"r"))
	classInfoYaml = sorted(OriginalclassInfoYaml,key=lambda classinfo: classinfo['id'])
	finalClassInfo = []
	for classInfo in classInfoYaml:
		eachClass = {}
		eachClass["id"] = classInfo["id"]
		eachClass["instance"] = []
		for instance in classInfo["Instances "]:
			eachClass["instance"].append(lookup(instance))
		eachClass["constructors"] = []
		for constructor in classInfo["Constructors "]:
			eachClass["constructors"].append(lookup(constructor))
		eachClass["virtualFunctionTable"] = []
		for vtable in classInfo["Virtual Tables"]:
			eachClass["virtualFunctionTable"].append(lookup(vtable))
		eachClass["virtualFunctions"] = []
		for virtFunction in classInfo["Virtual Functions "]:
			eachClass["virtualFunctions"].append(lookup(virtFunction))
		eachClass["dataMembers"] = classInfo["Data Members"]
		eachClass["memberFunction"] = []
		for memberFunction in classInfo["Function Members "]:
			eachClass["memberFunction"].append(lookup(memberFunction))
		eachClass["sureParent"] = classInfo["Sure Parent Class"]
		eachClass["parentOrEmbeded"] = classInfo["MayBe Parent/Embedded Class"]
		finalClassInfo.append(eachClass)

	json = json.dumps(finalClassInfo)
	fp = open("output.json","w")
	fp.write(json)
	fp.close()