#!/usr/bin/python3

import os
import re
import pprint
import sys
from os import listdir
from os.path import isfile, join
from function_breakdown import 
from collections import defaultdict

def run():
    print("Please enter the benchmark dir name [benchmark-reports]")
    benchdirname = readline()
    if benchdirname == '':
        benchdirname = 'benchmark-reports'

    print("Please enter the lh file dir name [./liquidhaskell-study/wi15/unsafe]:")
    targetdirname = readline()
    if targetdiname == "":
        targetdirname = './liquidhaskell-study/wi15/unsafe'

    fileNames = [f for f in listdir(benchdirname) if isfile(join(benchdirname, f))]
    for fName in fileNames:
        fd = open(os.path.join(benchdirname, fName))
        fd.readline())
        targName = fd.readline().strip()
        fileText = fd.read()
        fd.close()
        if 'ERROR OCCURRED IN LIQUIDHASKELL' in fileText:
            with open(os.path.join(targetdiname, targName)) as tfd:
                pass
        
if __name__ == '__main__':
    print("""This only needs to be run once! It will parse the benchmark reports 
             and replace files.""")
    run()
