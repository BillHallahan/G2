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

proj    = "tests/Samples"
src     = "tests/Samples/HigherOrderMath.hs"
prelude = "../base-4.9.1.0/Prelude.hs"
entry   = "fixed"
start   = 0
ticks   = 300
assumep = "isTrue1"
assertp = None

dumps = "dumps"

if not os.path.exists(dumps):
  os.makedirs(dumps)

for i in range(start, ticks + 1):
  run = "cabal run G2 -- {0} {1} {2} {3}" \
          .format(proj, src, prelude, entry)
  run = run + " --n {0}".format(str(i))

  if assumep is not None:
    run = run + " --assume {0}".format(assumep)

  if assertp is not None:
    run = run + " --assert {0}".format(assertp)

  run = run + " > {0}/hue-{1}.hs".format(dumps, str(i))

  print run
  proc = subprocess.call(run, shell=True)

