import os
import subprocess
import sys

proj = sys.argv[1]
lhdir = sys.argv[2]

dumps = "lh-dumps"

# https://stackoverflow.com/a/9816863/2704964
def absoluteFilePaths(directory):
  for dirpath,_,filenames in os.walk(directory):
    for f in filenames:
      yield os.path.abspath(os.path.join(dirpath, f))

if not os.path.exists(dumps):
  os.makedirs(dumps)

for f in absoluteFilePaths(lhdir):
  run = "time cabal run G2 -- {0} --liquid-file-test {2}" \
        .format(proj, base, f)

  print run
  proc = subprocess.call(run, shell=True)

