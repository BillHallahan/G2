#!/usr/bin/python3

import os
import re
import pprint
import sys
from os import listdir
from os.path import isfile, join
from collections import defaultdict

def run():
    print("Please enter the benchmark dir name [benchmark-reports]")
    benchdirname = sys.stdin.readline()
    if benchdirname == '\n':
        benchdirname = 'benchmark-reports'
    benchdirname = benchdirname.strip()

    print("Please enter the lh file dir name [./liquidhaskell-study/wi15/unsafe]:")
    targetdirname = sys.stdin.readline()
    if targetdirname == "\n":
        targetdirname = './liquidhaskell-study/wi15/unsafe'
    targetdirname = targetdirname.strip()

    fileNames = [f for f in listdir(benchdirname) if isfile(join(benchdirname, f))]
    for fName in fileNames:
        filePath = os.path.join(benchdirname, fName)
        fd = open(filePath)
        fd.readline()
        targName = fd.readline().strip()
        fileText = fd.read()
        fd.close()
        if 'ERROR OCCURRED IN LIQUIDHASKELL' in fileText:
            if 'Illegal type specification' in fileText:
                # add_line_to_file(os.path.join(targetdiname, targName))
                pass
            if 'Multiple specifications' in fileText and '{-@ LIQUID "--prune-unsorted" @-}' not in fileText:
                add_line_to_file(os.path.join(targetdirname, targName), '{-@ LIQUID', '{-@ LIQUID "--prune-unsorted" @-}')
            if 'Cannot lift' in fileText:
                add_line_to_file(os.path.join(targetdirname, targName), 'module', ', ' + get_func_needing_a_lift(filePath))

        
def get_func_needing_a_lift(fPath):
    with open(fPath, "r") as in_file:
       for line in in_file:
           if 'Cannot lift' in line:
               lift_func = line.split('`')[1]
               return lift_func



def add_line_to_file(filePath, searchString, addString):
    with open(filePath, "r") as in_file:
        buf = in_file.readlines()
    with open(filePath, "w") as out_file:
        for line in buf:
            if searchString in line:
                line = line + addString + "\n"
            out_file.write(line)

if __name__ == '__main__':
    print("""This only needs to be run once! It will parse the benchmark reports 
             and replace files.""")
    run()
