import os
import subprocess
import sys

antonListsPrjDir = "../liquidhaskell-study/wi15/custom/"
antonListsSrcDir = "../liquidhaskell-study/wi15/custom/custom-list/"

#antonListsPrjDir = "/home/celery/Desktop/list-test/"
#antonListsSrcDir = "/home/celery/Desktop/list-test/custom-list/"
lists = [
    ("flycheck_List.lhs-2015-03-19T23.54.55.lhs", "concat")
  , ("flycheck_List.lhs-2015-03-19T17.01.32.lhs", "replicate")
  , ("flycheck_List.lhs-2015-03-18T05.01.41.lhs", "replicate")
  , ("flycheck_List.lhs-2015-03-16T04.27.03.lhs", "concat")
  , ("flycheck_List.lhs-2015-03-16T04.41.50.lhs", "concat")
  , ("flycheck_List.lhs-2015-03-16T05.14.59.lhs", "concat")
  , ("flycheck_List.lhs-2015-03-16T04.35.08.lhs", "concat")
  , ("flycheck_List.lhs-2015-03-16T23.47.50.lhs", "concat")
  , ("flycheck_List.lhs-2015-03-16T23.25.52.lhs", "foldr1")
  , ("flycheck_List.lhs-2015-03-16T23.23.14.lhs", "foldr1")
  ]


antonMapRedPrjDir = "../liquidhaskell-study/wi15/custom/"
antonMapRedSrcDir = "../liquidhaskell-study/wi15/custom/custom-mapreduce/"

#antonMapRedPrjDir = "/home/celery/Desktop/mapreduce-test/"
#antonMapRedSrcDir = "/home/celery/Desktop/mapreduce-test/custom-mapreduce/"
mapreds = [
    ("flycheck_MapReduce.lhs-2015-03-16T03.34.44.lhs", "group")
  , ("flycheck_MapReduce.lhs-2015-03-20T06.45.53.lhs", "expand")
  , ("flycheck_MapReduce.lhs-2015-03-20T06.45.53.lhs", "collapse")
  , ("flycheck_MapReduce.lhs-2015-03-20T06.45.53.lhs", "mapReduce")
  ]


# List
for (file, func) in lists:
  command = "cabal run G2 -- {0} --liquid {1} --liquid-func {2}"\
            .format(antonListsPrjDir, antonListsSrcDir + file, func)
  print(command)
  proc = subprocess.call(command, shell=True)
  print("----------------------------------")

# Map Reduce
for (file, func) in mapreds:
  command = "cabal run G2 -- {0} --liquid {1} --liquid-func {2}"\
            .format(antonMapRedPrjDir, antonMapRedSrcDir + file, func)
  print(command)
  proc = subprocess.call(command, shell=True)
  print("----------------------------------")

