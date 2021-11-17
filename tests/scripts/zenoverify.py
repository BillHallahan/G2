#!/usr/bin/env python
# Tests RewriteV on the Zeno suite

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

def run_zeno(thm, var_settings):
    start_time = time.monotonic();
    res = call_zeno_process(thm, var_settings);
    end_time = time.monotonic();
    elapsed = end_time - start_time;

    try:
        check_unsat = res.splitlines()[-1].decode('utf-8');
        print(check_unsat);
    except IndexError:
        if res == "Timeout":
            check_unsat = "Timeout";
        else:
            check_unsat = "";
    return (check_unsat, elapsed);

def call_zeno_process(thm, var_settings):
    try:
        timeout = "20"
        #args = ["cabal", "run", "RewriteV", "tests/RewriteVerify/Correct/Zeno.hs", thm]
        args = ["dist/build/RewriteV/RewriteV", "tests/RewriteVerify/Correct/Zeno.hs", thm]
        res = subprocess.run(args + var_settings, capture_output = True, timeout = 10);
        return res.stdout;
    except subprocess.TimeoutExpired:
        #res.terminate()
        return "Timeout".encode('utf-8')


def call_infer_process(file):    
    try:
        code_file = open(file, "r");
        code = code_file.read();
        code_file.close();

        args_re = re.search("--\s*cmd_line\s*=\s*\(([^)]*)\)\s*", code);

        extra_args = [];
        if args_re and args_re.group(1):
            extra_args = args_re.group(1).split(" ");

        timeout = "120"
        timeout_re = re.search("--\s*timeout\s*=\s*([0-9]*)\s*", code);
        if timeout_re and timeout_re.group(1):
            timeout = timeout_re.group(1);

        timeout_sygus = "30"
        timeout_sygus_re = re.search("--\s*timeout-sygus\s*=\s*([0-9]*)\s*", code);
        if timeout_sygus_re and timeout_sygus_re.group(1):
            timeout_sygus = timeout_sygus_re.group(1);

        args = ["gtimeout", timeout, "cabal", "run", "Inference", file
               , "--", "--timeout-sygus", timeout_sygus]

        res = subprocess.run(args + extra_args
                            , capture_output = True);
        return res.stdout;
    except subprocess.TimeoutExpired:
        res.terminate()
        return "Timeout"

equivalences = [
    "p01",
    "p02",
    "p03",
    "p04",
    "p06",
    "p07",
    "p08",
    "p09",
    "p10",
    "p11",
    "p12",
    "p13",
    "p14",
    "p15",
    "p17",
    "p19",
    "p20",
    "p22",
    "p23",
    "p24",
    "p25",
    "p31",
    "p32",
    "p33",
    "p34",
    "p35",
    "p36",
    "p38",
    "p39",
    "p40",
    "p41",
    "p42",
    "p43",
    "p44",
    "p45",
    "p46",
    "p47",
    "p49",
    "p50",
    "p51",
    "p52",
    "p53",
    "p54",
    "p55",
    "p56",
    "p57",
    "p58",
    "p61",
    "p64",
    "p67",
    "p72",
    "p73",
    "p74",
    "p75",
    "p79",
    "p80",
    "p81",
    "p82",
    "p83",
    "p84"
]

def test_equivalences_basic():
    unsat_num = 0;
    for thm in equivalences:
        print(thm);
        (check_unsat, elapsed) = run_zeno(thm, []);
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat == "Timeout":
            print("\tTimeout")
        else:
            print("\tFailed")
    return unsat_num

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
                # print("check_safe =" + repr(check_safe) + "|")
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

def orig():
    (safe_real, num_real) = test_pos_folder("tests/LiquidInf/Real");
    (safe_art, num_art) = test_pos_folder("tests/LiquidInf/Artificial/Pos");

    (ce_art, num_ce_art) = test_neg_folder("tests/LiquidInf/Artificial/Neg");

    print(str(safe_real + safe_art) + "/" + str(num_real + num_art) + " Safe");

    print(str(ce_art) + "/" + str(num_ce_art) + " Counterexamples");

def main():
    # (safe_real, num_real) = test_pos_folder("tests/LiquidInf/Real");
    #(safe_art, num_art) = test_pos_folder("tests/LiquidInf/Art_LIA/Pos");

    #(ce_art, num_ce_art) = test_neg_folder("tests/LiquidInf/Art_LIA/Neg");

    unsat_num = test_equivalences_basic()

    # print(str(safe_real + safe_art) + "/" + str(num_real + num_art) + " Safe");

    # print(str(ce_art) + "/" + str(num_ce_art) + " Counterexamples");


if __name__ == "__main__":
    main()