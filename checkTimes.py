import sys
import re

fle = sys.argv[1]
func = sys.argv[2]

with open(fle) as f:
    lines = f.readlines()

lines = [s for s in lines if (":" + func + " ") in s]

times = map(lambda lns : re.findall("[\d\.]+$", lns), lines)
times = sum(times, [])

print (len(times))

ftimes = map(float, times)

stime = sum(ftimes, 0)

avg = stime / len(times)

print avg