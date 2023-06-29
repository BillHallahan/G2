#!/usr/bin/env python
# Tests G2's LiquidHaskell type Inference on all files in the ../LiquidInf directory

import os
import re
import subprocess
import time
import eval

def skip_list():
    return  [ "M02.hs"
            , "M19.hs"
            , "M20.hs"
            , "M21.hs"
            , "M22.hs"
            , "M29.hs"
            , "M32.hs"
            , "M33.hs"
            , "M34.hs"
            , "M36.hs"
            , "M40.hs"
            , "M42.hs"
            , "M45.hs"
            , "M46.hs"]

def createCompTable(haskell, chc, z3):
    for (hlog, clog, z3log) in zip(haskell, chc, z3):
        (file, htime, _, _ , _, _, _, _, _, _, _) = hlog
        (_, ctime) = clog
        (_, z3time) = z3log

        if htime is None:
            print_htime = "timeout"
        else:
            print_htime = htime 
        print(file + " & " + print_htime + " & " + ctime + " & " + z3time)

def runZ3():
    return runOther("z3", z3GetTime, ["time"])

def z3GetTime(res, res_err):
    time = re.match("\s*(\d*\.\d*)", res_err)
    return time.group(1)

def runCHC():
    return runOther("./tests/LiquidInf/Paper/Eval/chc_verifier", chcGetTime)

def chcGetTime(res, _):
    time = res.splitlines()[-1].replace("Total time: ", "")
    print(time)
    return time


def runOther(tool, getTime, pre=[]):
    all_files = os.listdir("tests/LiquidInf/Paper/Eval/Compare_CHC")
    all_files.sort()
    
    log = []
    
    for file in all_files:
        print(file)
        args = pre + ["gtimeout", "600", tool, "tests/LiquidInf/Paper/Eval/Compare_CHC/" + file]
        res = subprocess.run(args, capture_output = True);
        out = res.stdout.decode('utf-8')
        err = res.stderr.decode('utf-8')
        if out == "":
            log.append((file, "timeout"))
        else:
            time = getTime(out, err)
            log.append((file, time))
    return log

def main():
    try:
        os.mkdir("logs");
    except:
        pass;

    # (log_test, safe_test, num_test) = test_pos_folder("tests/LiquidInf/Paper/Eval/Test", "240");
    # print(str(safe_test) + "/" + str(num_test) + " Safe");
    
    # log = log_test
    # (log_haskell, safe_compare, num_compare) = eval.test_pos_folder("tests/LiquidInf/Paper/Eval/Compare", "600", ["--use-invs"], skip = skip_list());

    log_z3 = runZ3()
    log_chc = runCHC()

    (log_haskell, safe_compare, num_compare) = eval.test_pos_folder("tests/LiquidInf/Paper/Eval/Compare", "600", ["--use-invs"]);
    print(str(safe_compare) + "/" + str(num_compare) + " Safe");

    eval.create_table(log_haskell)
    eval.create_simple_table(log_haskell)

    print(log_chc)
    print(log_haskell)

    print("\begin{tabular}{| l | c | c | c |}")
    print("\hline")
    print("File & Lynx & CHC & Z3 \\ \hline")
    createCompTable(log_haskell, log_chc, log_z3)
    print("\end{tabular}")

if __name__ == "__main__":
    main()
