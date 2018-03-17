import collections
import os
import re
import subprocess
import sys
import time

NVALUE = 1000
TIMEOUT = 300 # seconds
MAXOUTPUTS = 3
# SMTADTS = "--smt-adts"
SMTADTS = ""

projDir = "../liquidhaskell-study/wi15/eval/"

listDir = "eval-list/"
listTargets = [
  ("flycheck_List.lhs-2015-03-16T04.40.42.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T17.52.22.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-14T07.10.40.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T06.39.29.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T23.17.36.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T08.39.11.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T15.21.34.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-16T02.57.17.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T02.52.40.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T05.21.08.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-21T03.57.37.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-16T04.45.26.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T22.40.44.lhs", ["length"]),
  ("flycheck_List.lhs-2015-03-16T03.39.54.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T18.26.34.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-16T04.33.09.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T23.46.07.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T04.12.16.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T04.31.21.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T18.51.17.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T18.17.36.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T15.45.38.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-20T18.25.30.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-20T06.47.16.lhs", ["foldr", "foldr1"]),
  ("flycheck_List.lhs-2015-03-20T06.47.19.lhs", ["foldr", "foldr1"]),
  ("flycheck_List.lhs-2015-03-16T02.57.08.lhs", ["foldr1"]),
  ("flycheck_List.lhs-2015-03-12T17.55.53.lhs", ["length"]),
  ("flycheck_List.lhs-2015-03-20T05.36.56.lhs", ["length"]),
  ("flycheck_List.lhs-2015-03-20T22.44.37.lhs", ["length"]),
  ("flycheck_List.lhs-2015-03-20T05.44.50.lhs", ["length"]),
  ("flycheck_List.lhs-2015-03-19T22.22.08.lhs", ["replicate"]),
  ("flycheck_List.lhs-2015-03-21T03.50.06.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-20T07.43.51.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-20T22.41.16.lhs", ["length"]),
  ("flycheck_List.lhs-2015-03-16T05.15.41.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T04.35.08.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T05.14.59.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T06.19.17.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T23.22.03.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T17.54.27.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T15.29.53.lhs", ["concat", "zipWith"]),
  ("flycheck_List.lhs-2015-03-20T18.27.32.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-16T02.50.44.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T02.20.21.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T04.41.31.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T23.47.50.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T15.40.33.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-20T18.01.30.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T15.43.32.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-16T04.50.23.lhs", ["concat"]),
]

mapreduceDir = "eval-mapreduce/"
mapreduceTargets = [
  ("flycheck_MapReduce.lhs-2015-03-16T04.39.40.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T04.41.23.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T04.41.39.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T04.41.43.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T04.43.09.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T04.44.07.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T04.48.09.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T05.12.50.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T05.15.10.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T05.15.37.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T05.19.56.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T05.21.49.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-16T08.49.45.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-16T17.16.55.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T17.18.13.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T17.33.06.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T19.14.52.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T19.17.16.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-16T19.57.30.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T19.58.26.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T19.58.52.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T20.00.53.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T20.01.49.lhs", ["expand", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-16T20.49.59.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-16T23.01.46.lhs", ["expand"]),
  ("flycheck_MapReduce.lhs-2015-03-16T23.02.06.lhs", ["expand", "collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.01.34.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.08.43.lhs", ["collapse", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.12.28.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.13.16.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.13.27.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.13.35.lhs", ["collapse", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.13.56.lhs", ["expand", "collapse", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.14.16.lhs", ["expand", "collapse", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.15.08.lhs", ["expand", "collapse", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.15.49.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.16.20.lhs", ["expand", "collapse", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-17T00.17.51.lhs", ["expand", "collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-16T03.11.57.lhs", ["expand", "group"]),
  ("flycheck_MapReduce.lhs-2015-03-16T03.12.12.lhs", ["expand", "group", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-21T00.04.03.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-21T00.10.24.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-21T00.11.05.lhs", ["mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-21T00.18.03.lhs", ["mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-21T00.21.15.lhs", ["mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-21T00.32.19.lhs", ["mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-20T06.56.46.lhs", ["collapse", "mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-20T06.57.08.lhs", ["collapse"]),
  ("flycheck_MapReduce.lhs-2015-03-20T06.57.13.lhs", ["mapReduce"]),
  ("flycheck_MapReduce.lhs-2015-03-20T06.57.47.lhs", ["mapReduce"]),
  ]

kmeansDir = "eval-kmeans/"
kmeansTargets = [
  ("flycheck_KMeans.lhs-2015-03-13T03.28.38.lhs", ["nearest", "mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T03.56.38.lhs", ["nearest", "mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T04.00.43.lhs", ["nearest", "mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-14T23.01.59.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T01.10.59.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T04.40.25.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T11.06.49.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T23.40.29.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-17T00.01.12.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-17T01.18.29.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-19T07.35.57.lhs", ["nearest", "mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-19T23.25.22.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T00.02.26.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T01.00.12.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T07.00.37.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T07.07.32.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T09.12.47.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T16.35.45.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T23.58.45.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T00.11.56.lhs", ["centroid"]),
  ("flycheck_KMeans.lhs-2015-03-21T00.25.34.lhs", ["centroid"]),
  ("flycheck_KMeans.lhs-2015-03-21T01.15.54.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T04.59.15.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T06.05.53.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-15T04.10.05.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-18T06.45.46.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-18T02.54.03.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T01.31.45.lhs", ["kmeans1", "centroid"]),
  ("flycheck_KMeans.lhs-2015-03-17T00.14.50.lhs", ["mergeCluster"]),
  ("flycheck_KMeans.lhs-2015-03-17T00.01.10.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-17T01.21.52.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-17T00.04.26.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-14T23.05.47.lhs", ["kmeans1", "centroid"]),
  ("flycheck_KMeans.lhs-2015-03-14T23.32.02.lhs", ["kmeans1"]),
]


# Evaluation runner.
def runEval(evalDir, evalList, runStats):
  for (file, funs) in evalList:
    for f in funs:
      command = "cabal run G2 -- {0} --liquid {1} --liquid-func {2} --n {3} --time {4} --max-outputs {5} {6}"\
                .format(projDir + evalDir, projDir + evalDir + file, f, NVALUE, TIMEOUT, MAXOUTPUTS, SMTADTS)
      print(command)
      startTime = time.time()
      p = subprocess.Popen(command, stdout=subprocess.PIPE, shell=True)
      (output, err) = p.communicate()
      print(output)
      p_status = p.wait()
      deltaTime = time.time() - startTime

      if re.search("violating ([^f]*[^i]*[^x]*[^m]*[^e])\'s refinement type", output) is not None:
        hasConcrete = re.search("violating ([^f]*[^i]*[^x]*[^m]*[^e])\'s refinement type\nConcrete",
                                output) is not None
        hasAbstract = "Abstract" in output
        runStats[f]['C'] = runStats[f]['C'] + 1 if hasConcrete else runStats[f]['C']
        runStats[f]['A'] = runStats[f]['A'] + 1 if hasAbstract else runStats[f]['A']
        runStats['hist'].append((file, f, hasConcrete, hasAbstract, deltaTime))
        print((file, f, hasConcrete, hasAbstract, deltaTime))
      else:
        runStats['hist'].append((file, f, False, False, deltaTime))
        print((file, f, False, False, deltaTime))

      sys.stdout.flush()

# Get all the RHS of the file-functions pairs.
rhs = [x for xs in (map(lambda p: p[1], listTargets + mapreduceTargets + kmeansTargets))
         for x in xs]

# Generate a statistics over the source -- used for the LHS of the eval table.
sourceStats = {}
for x in rhs:
  if x in sourceStats:
    sourceStats[x] = sourceStats[x] + 1
  else:
    sourceStats[x] = 1

# Maybe print it :)
print(sourceStats)

runStats = { 'hist': [] }
for k in sourceStats.keys():
  runStats[k] = { 'A': 0, 'C': 0 }

startTime = time.time()

arg = sys.argv[1].lower()
if arg == "list":
  runEval(listDir, listTargets, runStats)
elif arg == "mapreduce":
  runEval(mapreduceDir, mapreduceTargets, runStats)
elif arg == "kmeans":
  runEval(kmeansDir, kmeansTargets, runStats)
else:
  exit("what?")

# Some formatted printing -- pretty dull at the moment
for (file, fun, hasConcrete, hasAbstract, elapsed) in runStats['hist']:
  if hasAbstract or hasConcrete:
    print("PASS: {0}:{1}  -- C: {3}, A: {4} -- {2}"\
          .format(file, fun, elapsed, int(hasConcrete), int(hasAbstract)))
  else:
    print("FAIL: {0}:{1}  --                -- {2}"\
          .format(file, fun, elapsed))

for k in runStats:
  if k != 'hist':
    print(k + " : " + str(runStats[k]))

print("Script elapsed time: "  + str(time.time() - startTime))

totalTime = sum(map(lambda n: n[4], runStats['hist']))
print("G2 time: " + str(totalTime))

