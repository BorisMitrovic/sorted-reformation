#!/bin/env python

import re, sys
from os import system


import copy


def ftolower(name):
	first = name[0]
	rest = name[1:]
	#return name.lower()
	return (first.lower()+rest)

def plotGraph(links,fin):
	fout = fin[:-3]
	fw = open(fout+'.dot', 'w')
	fp = open(ftolower(fout)+'A.pl','w')
	
	
	print>>fw, "digraph G { "
	print>>fp, "% automatically created subsort hierarchy"
	print>>fp, "\nfactSorts(Ss) :- Ss = ["
	for (fr,to) in links[:-1]:
		print>>fw, '   "' + fr + '" -> "' + to + '";'
		print>>fp, '   (' + ftolower(to) + ' -> ' + ftolower(fr) + '),'
	
	(fr,to) = links[-1]			
	print>>fw, '   "' + fr + '" -> "' + to + '";'
	print>>fp, '   (' + ftolower(to) + ' -> ' + ftolower(fr) + ')'
	
	print>>fw,"}"
	print>>fp, "]."
	fp.close()
	fw.close()
	system("dot -Tpdf "+fout+".dot > "+fout+".pdf")

def topbottom(tax):
	tax = map(lambda (x,y): (y,x), tax)
	return tax


if __name__ == '__main__':


	rscope = re.compile(r"factSorts\(\w*\)\s*:-\s*\w*\s*=\s*\[([^\]]*)")
#	rsub = re.compile(r"\(subclass\s(\w+)\s(\w+)\)")	# KIF
	rsub = re.compile(r"(\w+)\s*->\s*(\w+)")
	
	fname = sys.argv[1]
	
	fr = open(fname,"r")
	page = fr.read()
	page = rscope.findall(page)[0]
	
	conns = rsub.findall(page)
	conns = topbottom(conns)
	
	plotGraph(conns,fname)
	
