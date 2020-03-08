#!/usr/bin/env python
# Tests G2's LiquidHaskell type Inference on all files in the ../LiquidInf directory

import os
import re
import subprocess
import time

def run_infer(file):
    start_time = time.monotonic();
    res = call_infer_process(file);
    end_time = time.monotonic();
    elapsed = end_time - start_time;

    try:
        check_safe = res.splitlines()[-2].decode('utf-8');
    except IndexError:
        if res == "Timeout":
            check_safe = "Timeout";
        else:
            check_safe = "";

    return (check_safe, elapsed);

def call_infer_process(file):    
    try:
        code_file = open(file, "r");
        code = code_file.read();
        code_file.close();

        args_re = re.search("--\s*cmd_line\s*=\s*\(([^)]*)\)\s*", code);

        extra_args = [];
        if args_re and args_re.group(1):
            extra_args = [args_re.group(1)];

        args = ["gtimeout", "180", "cabal", "run", "Inference", file
               , "--", "--timeout-sygus", "45"]

        res = subprocess.run(args + extra_args
                            , capture_output = True);
        return res.stdout;
    except subprocess.TimeoutExpired:
        res.terminate()
        return "Timeout"

def test_pos_folder(folder):
    all_files = os.listdir(folder);
    num_files = count_files(all_files);
    safe_num = 0;

    for file in all_files:
        if file.endswith(".hs"):
            print(file);

            (check_safe, elapsed) = run_infer(os.path.join(folder, file));

            if check_safe == "Safe":
                print("\tSafe - " + str(elapsed) + "s");
                safe_num += 1
            elif check_safe == "Timeout":
                print("\tTimeout")
            else:
                print("\tUnsafe")

    return (safe_num, num_files)

def test_neg_folder(folder):
    all_files = os.listdir(folder);
    num_files = count_files(all_files);
    safe_num = 0;

    for file in all_files:
        if file.endswith(".hs"):
            print(file);

            (check_safe, elapsed) = run_infer(os.path.join(folder, file));

            if check_safe == "Counterexample":
                print("\tCounterexample - " + str(elapsed) + "s");
                safe_num += 1
            elif check_safe == "Timeout":
                print("\tTimeout")
            else:
                print("\tUnsafe")

    return (safe_num, num_files)

def count_files(all_files):
    num_files = 0;
    for file in all_files:
        if file.endswith(".hs"):
            num_files += 1;

    return num_files

def main():
    (safe_real, num_real) = test_pos_folder("tests/LiquidInf/Real");
    (safe_art, num_art) = test_pos_folder("tests/LiquidInf/Artificial/Pos");

    (ce_art, num_ce_art) = test_neg_folder("tests/LiquidInf/Artificial/Neg");

    print(str(safe_real + safe_art) + "/" + str(num_real + num_art) + " Safe");

    print(str(ce_art) + "/" + str(num_ce_art) + " Counterexamples");


if __name__ == "__main__":
    main()