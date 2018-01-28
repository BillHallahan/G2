import os
import subprocess
import sys

# proj    = sys.argv[1]
# src     = sys.argv[2]
# base    = sys.argv[3]
# prelude = sys.argv[4]
# entry   = sys.argv[5]
# start   = 0
# ticks   = 500 if (len(sys.argv) < 5) else int(sys.argv[6])
# assumep  = None
# assertp  = None

proj    = "tests/Samples/"
src     = "tests/Samples/Tupes.hs"
prelude = "defs/PrimDefs.hs"
entry   = "oneTwo"
start   = 20
ticks   = 30
assumep = None
assertp = None

dumps = "dumps"

if not os.path.exists(dumps):
  os.makedirs(dumps)

for i in range(start, ticks + 1):
  run = "time cabal run G2 -- {0} {1} {2} {3}" \
          .format(proj, src, prelude, entry)
  run = run + " --n {0}".format(str(i))

  if assumep is not None:
    run = run + " --assume {0}".format(assumep)

  if assertp is not None:
    run = run + " --assert {0}".format(assertp)

  run = run + " > {0}/hue-{1}.hs".format(dumps, str(i))

  print run
  proc = subprocess.call(run, shell=True)

