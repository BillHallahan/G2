import os
import subprocess
import sys

proj = sys.argv[1]
lhdir = sys.argv[2]
timeout = 120 # seconds
dumps = "lh-dumps"

# https://stackoverflow.com/a/9816863/2704964
def absoluteFilePaths(directory):
  for dirpath,_,filenames in os.walk(directory):
    for f in filenames:
      if f.endswith(".hs") or f.endswith(".lhs"):
        yield os.path.abspath(os.path.join(dirpath, f))

if not os.path.exists(dumps):
  os.makedirs(dumps)

for f in absoluteFilePaths(lhdir):
  command = "cabal run G2 -- {0} --liquid-file-test {1}".format(proj, f)
  print(command)
  proc = subprocess.call(command, shell=True)
  # proc = subprocess.call(command, shell=True, timeout=timeout)

