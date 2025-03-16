#!/usr/bin/env python

import re
import os
import subprocess
import time

# Calling and reading from G2
exe_name = str(subprocess.run(["cabal", "exec", "which", "G2"], capture_output = True).stdout.decode('utf-8')).strip()

def run_g2(filename, func, var_settings, timeout):
    start_time = time.monotonic();
    res = call_g2_process(filename, func, var_settings, timeout);
    end_time = time.monotonic();
    elapsed = end_time - start_time;
    return res

def call_g2_process(filename, func, var_settings, time_limit):
    try:
        args = [exe_name, filename, func]
        res = subprocess.run(args + var_settings, universal_newlines=True, capture_output=True, timeout=time_limit);
        return res.stdout
    except subprocess.TimeoutExpired as TimeoutEx:
        # extra line break at end to match the one from normal termination
        return TimeoutEx.stdout.decode('utf-8') + "\nTimeout\n"

def run_nofib_bench(filename, var_settings, timeout):
    return run_g2(filename, "main", ["--check-asserts", "--error-asserts", "--accept-times", "--n", "30000"] + var_settings, timeout)

def run_nofib_bench_nrpc(filename, var_settings, timeout):
    return run_g2(filename, "main", ["--check-asserts", "--error-asserts", "--accept-times", "--n", "30000", "--nrpc", "--higher-order", "symbolic-nrpc"] + var_settings, timeout)

def process_output(out):
    reached = re.findall(r"State Accepted: ((?:\d|\.)*)", out)
    reached_time = list(map(lambda x : float(x), reached))
    print(reached_time)

# Read in the types of bugs
def read_bug_types(setpath):
    bug_tys = {}

    name = "((?:\w|/|-)*)"
    sp_name = "\s*" + name + "\s*"
    file = os.path.join(setpath, "bug_types.txt")
    with open(file, 'r') as file:
        for line in file:
            reached = re.match(sp_name + "," + sp_name + "(?:#.*)?", line)
            bug_tys.update({ reached.group(1) : int(reached.group(2)) })
    return bug_tys

def run_nofib_set(setname, var_settings, timeout):
        setpath = os.path.join("nofib-buggy-symbolic/", setname)
        all_files_dirs = os.listdir(setpath);

        print(setpath)

        bug_types = read_bug_types(setpath);
        print(bug_types)

        for file_dir in all_files_dirs:
            bt = bug_types.get(file_dir)

            if bt == 2:
                continue;
            
            if bt == None:
                print("Bug type not found: " + file_dir)
                continue;

            bench_path = os.path.join(setpath, file_dir)
            if os.path.isdir(bench_path):
                final_path = os.path.join(bench_path, "Main.hs")
                if os.path.isfile(final_path):
                    print(file_dir);
                    res_bench = run_nofib_bench(final_path, var_settings, timeout)
                    print("Baseline:")
                    process_output(res_bench)
                    res_bench_nrpc = run_nofib_bench_nrpc(final_path, var_settings, timeout)
                    print("NRPC:")
                    process_output(res_bench_nrpc)

run_nofib_set("imaginary", [], 60)
