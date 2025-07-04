#!/usr/bin/env python
# Tests Verify on the Zeno suite

import os
import re
import subprocess
import time

exe_name = str(subprocess.run(["cabal", "exec", "which", "Verify"], capture_output = True).stdout.decode('utf-8')).strip()

def run_verify(filename, thm, time_limit):
    start_time = time.monotonic();
    res = call_verify_process(filename, thm, time_limit);
    end_time = time.monotonic();
    elapsed = end_time - start_time;
    return res;

def call_verify_process(filename, thm, time_limit):
    try:
        args = [exe_name, "verify/" + filename, thm, "--time", str(time_limit)]
        res = subprocess.run(args, universal_newlines=True, capture_output=True, timeout=40);
        return res.stdout
    except subprocess.TimeoutExpired as TimeoutEx:
        # extra line break at end to match the one from normal termination
        return "Timeout - Script"
        # return TimeoutEx.stdout.decode('utf-8') + "\nTimeout\n"

def unmodified_theorems():
    ret = []
    for i in range(1, 86):
        if i < 10:
            ret.append(("prop_0" + str(i), []))
        else:
            ret.append(("prop_" + str(i), []))
    return ret

def test_suite_general(fname_in,suite, time_limit):
    verified = 0
    cex = 0
    timeout = 0
    for (thm, settings) in suite:
        print(thm)
        res = run_verify(fname_in, thm, time_limit)
        if "Verified" in res:
            print("Verified")
            verified += 1
        if "Counterexample" in res:
            print("Counterexample")
            cex += 1
        if "Timeout" in res:
            print("Timeout")
            timeout +=1
        if "error" in res:
            print("error")
            timeout +=1
    return (verified, cex, timeout)

def test_suite_csv(timeout):
    return test_suite_general("Zeno.hs", unmodified_theorems(), timeout)

def main():
    (v, c, t) = test_suite_csv(20)

    print("Verified " + str(v))
    print("Counterexample " + str(c))
    print("Timeout " + str(t))

if __name__ == "__main__":
    main()