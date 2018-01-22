import os
import subprocess
import sys

proj  = sys.argv[1]
src   = sys.argv[2]
entry = sys.argv[3]
ticks = int(sys.argv[4])

dumps = "dumps2"

if not os.path.exists(dumps):
  os.makedirs(dumps)

for i in range(0, ticks):
  # time cabal run G2 tests/Liquid/ defs/PrimDefs.hs -- --liquid tests/Liquid/Peano.hs --liquid-func fromInt --n 98
  run = "time cabal run G2 {0} defs/PrimDefs.hs -- --liquid {1} --liquid-func {2} --n {3} > {4}/hue-{5}.txt".format(proj, src, entry, str(i), dumps, str(i))
  print run
  proc = subprocess.Popen(run, shell=True)
  proc.wait()
