import collections
import os
import subprocess
import sys

NVALUE = 1000
TIMEOUT = 300 # seconds

projDir = "../liquidhaskell-study/wi15/eval/"

listDir = "eval-list/"
listTargets = [
  ("flycheck_List.lhs-2015-03-16T04.40.42.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-14T20.14.02.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T17.52.22.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-14T07.10.40.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T06.39.29.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T23.17.36.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-14T08.22.35.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T08.39.11.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T15.21.34.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-14T20.10.53.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T02.57.17.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T02.52.40.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T05.21.08.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-21T03.57.37.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-16T04.45.26.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T22.40.44.lhs", ["length"]),
  ("flycheck_List.lhs-2015-03-16T03.39.54.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T18.26.34.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-16T05.26.17.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-13T00.46.41.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T04.33.09.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T23.46.07.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T04.12.16.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-14T20.16.11.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-16T04.31.21.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-21T04.29.05.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-21T04.44.45.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-21T04.23.00.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T18.51.17.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T18.17.36.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-21T04.16.43.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-20T15.45.38.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-20T18.25.30.lhs", ["zipWith"]),
  ("flycheck_List.lhs-2015-03-16T04.10.39.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-14T08.13.12.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-12T21.35.30.lhs", ["concat"]),
  ("flycheck_List.lhs-2015-03-15T03.14.02.lhs", ["replicate"]),
  ("flycheck_List.lhs-2015-03-19T16.57.18.lhs", ["replicate"]),
  ("flycheck_List.lhs-2015-03-15T03.12.59.lhs", ["replicate"]),
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
  ("flycheck_KMeans.lhs-2015-03-20T22.21.08.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-14T23.22.51.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T23.40.29.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T00.44.30.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T01.10.59.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-17T01.18.29.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T04.16.30.lhs", ["nearest", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T16.35.45.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T03.28.38.lhs", ["nearest", "mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-17T00.01.12.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T22.28.13.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T04.18.23.lhs", ["nearest", "centroid", "kmeans", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T00.25.34.lhs", ["centroid"]),
  ("flycheck_KMeans.lhs-2015-03-21T01.22.06.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T01.19.03.lhs", ["kmeans1", "normalize"]),
  ("flycheck_KMeans.lhs-2015-03-20T07.00.37.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T09.12.47.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T23.58.45.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T05.03.59.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T00.51.07.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T11.06.49.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-14T23.26.59.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T10.46.55.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T23.58.54.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-19T23.25.22.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T04.32.28.lhs", ["nearest", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T01.00.12.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T04.02.21.lhs", ["nearest", "mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T03.56.38.lhs", ["nearest", "mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T07.07.32.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T00.02.26.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T00.11.56.lhs", ["centroid"]),
  ("flycheck_KMeans.lhs-2015-03-20T23.59.23.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-14T23.01.59.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T04.59.15.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T10.06.45.lhs", ["mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T01.04.09.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-19T07.35.57.lhs", ["nearest", "mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T04.21.39.lhs", ["nearest", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T05.14.17.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-13T04.00.43.lhs", ["nearest", "mergeCluster", "centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T04.40.25.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T22.00.55.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T06.05.53.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-21T01.15.54.lhs", ["kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-16T23.49.23.lhs", ["centroid", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T01.33.52.lhs", ["normalize", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T01.13.35.lhs", ["normalize", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T01.43.08.lhs", ["normalize", "kmeans1"]),
  ("flycheck_KMeans.lhs-2015-03-20T01.29.54.lhs", ["normalize", "kmeans1"]),
]

def runEval(evalDir, evalList):
  for (file, funs) in evalList:
    for f in funs:
      command = "G2 -- {0} --liquid {1} --liquid-func {2} --n {3}"\
                .format(projDir, evalDir + file, f, NVALUE)
      print(command)
      p = subprocess.Popen(command, stdout=subprocess.PIPE, shell=True)
      (output, err) = p.communicate()
      p_status = p.wait()
      print("output: " + output)
      
def flatten(l):
    for el in l:
        if isinstance(el, collections.Iterable) and not isinstance(el, basestring):
            for sub in flatten(el):
                yield sub
        else:
            yield el

rhs = flatten(map(lambda p: p[1], listTargets + mapreduceTargets + kmeansTargets))
stats = {}
for x in rhs:
  if x in stats:
    stats[x] = stats[x] + 1
  else:
    stats[x] = 1
# print(stats)

runEval(listDir, listTargets)

# print(listTargets)
# print(mapreduceTargets)
# print(kmeansTargets)
