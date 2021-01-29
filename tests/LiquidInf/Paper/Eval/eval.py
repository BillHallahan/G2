#!/usr/bin/env python
# Tests G2's LiquidHaskell type Inference on all files in the ../LiquidInf directory

import os
import re
import subprocess
import time

def run_infer(file, name, timeout):
    # get info about the file
    (funcs, depth) = get_counts(file)

    # actual run the test
    start_time = time.monotonic();
    res = call_infer_process(file, timeout);
    end_time = time.monotonic();
    elapsed = end_time - start_time;

    try:
        check_safe = res.splitlines()[-2].decode('utf-8');
        f = open("logs/" + name + ".txt", "w")
        f.write(res.decode("utf-8") );
        f.close();
    except IndexError:
        if res == "Timeout":
            check_safe = "Timeout";
        else:
            check_safe = "";
    elapsed = adj_time(check_safe, elapsed)

    # run the test without extra fc
    no_fc_start_time = time.monotonic();
    no_fc_res = call_infer_process(file, timeout, ["--no-use-extra-fc"]);
    no_fc_end_time = time.monotonic();
    no_fc_elapsed = no_fc_end_time - no_fc_start_time;
    no_fc_check_safe = res.splitlines()[-2].decode('utf-8');
    no_fc_elapsed = adj_time(no_fc_check_safe, no_fc_elapsed)

    return (check_safe, elapsed, funcs, depth, no_fc_elapsed);

def call_infer_process(file, timeout, passed_args = []):    
    try:
        code_file = open(file, "r");
        code = code_file.read();
        code_file.close();

        args_re = re.search("--\s*cmd_line\s*=\s*\(([^)]*)\)\s*", code);

        extra_args = [];
        if args_re and args_re.group(1):
            extra_args = [args_re.group(1)];

        timeout_re = re.search("--\s*timeout\s*=\s*([0-9]*)\s*", code);
        if timeout_re and timeout_re.group(1):
            timeout = timeout_re.group(1);

        timeout_sygus = "10"
        timeout_sygus_re = re.search("--\s*timeout-sygus\s*=\s*([0-9]*)\s*", code);
        if timeout_sygus_re and timeout_sygus_re.group(1):
            timeout_sygus = timeout_sygus_re.group(1);

        args = ["gtimeout", timeout, "cabal", "run", "Inference", file
               , "--", "--timeout-sygus", timeout_sygus]

        res = subprocess.run(args + extra_args + passed_args, capture_output = True);
        return res.stdout;
    except subprocess.TimeoutExpired:
        res.terminate()
        return "Timeout"

def get_counts(file):
    args = ["cabal", "run", "Inference", file, "--", "--count"]

    res = subprocess.run(args, capture_output = True);
    depth = res.stdout.splitlines()[-2].decode('utf-8');
    funcs = res.stdout.splitlines()[-1].decode('utf-8');
    return (funcs, depth);

def adj_time(check_safe, time):
    if check_safe == "Safe":
        return time;
    else:
        return None;

def test_pos_folder(folder, timeout):
    all_files = os.listdir(folder);
    num_files = count_files(all_files);
    safe_num = 0;

    log = []

    for file in all_files:
        if file.endswith(".lhs") or file.endswith(".hs"):
            print(file);

            (check_safe, elapsed, funcs, depth, no_fc_elapsed) = run_infer(os.path.join(folder, file), file, timeout);

            if check_safe == "Safe":
                print("\tSafe - " + str(elapsed) + "s");
                safe_num += 1
            elif check_safe == "Timeout":
                print("\tTimeout")
            else:
                # print("check_safe =" + repr(check_safe) + "|")
                print("\tUnsafe")

            log.append((file, elapsed, funcs, depth, no_fc_elapsed))

    return (log, safe_num, num_files)

def test_neg_folder(folder, timeout):
    all_files = os.listdir(folder);
    num_files = count_files(all_files);
    safe_num = 0;

    for file in all_files:
        if file.endswith(".lhs") or file.endswith(".hs"):
            print(file);

            (check_safe, elapsed, _, _, _) = run_infer(os.path.join(folder, file), file, timeout);

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
        if file.endswith(".lhs") or file.endswith(".hs"):
            num_files += 1;

    return num_files

def create_table(log):
    print("\\begin{tabular}{| l | r | r | r | r |}");
    print("\\hline");
    print("File & Functions & Levels & Time & Time (no extra constraints) \\\\ \\hline");

    for (file, elapsed, funcs, depth, no_fc_time) in log:
        file_clean = file.replace("_", "\\_")
        if elapsed is not None:
            p_time = "{:.1f}".format(elapsed);
        else:
            p_time = "timeout"

        if no_fc_time is not None:
            p_no_fc_time = "{:.1f}".format(no_fc_time);
        else:
            p_no_fc_time = "timeout"

        print(file_clean  + " & " + funcs + " & " + depth + " & " +  p_time + " & " + p_no_fc_time + "\\\\ \\hline");

    print("\\end{tabular}");

def main():
    try:
        os.mkdir("logs");
    except:
        pass;

    (log_book, safe_book, num_book) = test_pos_folder("tests/LiquidInf/Paper/Eval/Prop_Book_Inv", "240");
    print(str(safe_book) + "/" + str(num_book) + " Safe");

    (log_hw, safe_hw, num_hw) = test_pos_folder("tests/LiquidInf/Paper/Eval/Prop_HW", "240");
    print(str(safe_hw) + "/" + str(num_hw) + " Safe");

    (log_inv, safe_inv, num_inv) = test_pos_folder("tests/LiquidInf/Paper/Eval/Prop_Invented", "240");
    print(str(safe_inv) + "/" + str(num_inv) + " Safe");

    (log_kmeans, safe_kmeans, num_kmeans) = test_pos_folder("tests/LiquidInf/Paper/Eval", "900");
    print(str(safe_kmeans) + "/" + str(num_kmeans) + " Safe");

    log = log_book + log_hw + log_inv + log_kmeans

    create_table(log)

if __name__ == "__main__":
    main()