import os
import subprocess
import sys

proj  = sys.argv[1]
src   = sys.argv[2]
entry = sys.argv[3]
ticks = int(sys.argv[4])

dumps = "dumps"

if not os.path.exists(dumps):
  os.makedirs(dumps)

for i in range(0, ticks):
  run = "cabal run G2 -- {0} {1} defs/PrimDefs.hs {2} --n {3} > {4}/hue-{5}.hs".format(proj, src, entry, str(i), dumps, str(i))
  print run
  proc = subprocess.Popen(run, shell=True)
  proc.wait()

