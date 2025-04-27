#!/usr/bin/env python

import re
import os
import subprocess
import time

# Calling and reading from G2
exe_name = str(subprocess.run(["cabal", "exec", "which", "G2"], capture_output = True).stdout.decode('utf-8')).strip()

def run_g2(filename, func, var_settings):
    start_time = time.monotonic();
    res = call_g2_process(filename, func, var_settings);
    end_time = time.monotonic();
    elapsed = end_time - start_time;
    return res

def call_g2_process(filename, func, var_settings):
    args = [exe_name, filename, func]
    res = subprocess.run(args + var_settings, universal_newlines=True, capture_output=True);
    return res.stdout

def run_nofib_bench(filename, var_settings, timeout):
    # --check-asserts --error-asserts --accept-times --print-num-nrpc --print-num-red-rules --solver-time --print-num-solver-calls --no-step-limit --search subpath --time 60
    return run_g2(filename, "main", ["--check-asserts", "--error-asserts", "--accept-times", "--print-num-nrpc", "--print-num-red-rules", "--solver-time", "--print-num-solver-calls", "--no-step-limit", "--search", "subpath", "--time", str(timeout)] + var_settings)

def run_nofib_bench_nrpc(filename, var_settings, timeout):
    return run_nofib_bench(filename, ["--nrpc", "--higher-order", "symbolic"] + var_settings, timeout)

def read_float(pre, out):
    reg = re.search(pre + r": ((?:\d|\.|e|-)*)", out)
    res_num = -1
    if reg:
        res_num = float(reg.group(1))
    return res_num

def read_int(pre, out):
    reg = re.search(pre + r": ((?:\d)*)", out)
    res_num = -1
    if reg:
        res_num = int(reg.group(1))
    return res_num

def process_output(out):
    nrpcs = re.findall(r"NRPCs Generated: ((?:\d)*)", out)
    nrpcs_num = list(map(lambda x : int(x), nrpcs))
    reached = re.findall(r"State Accepted: ((?:\d|\.|e|-)*)", out)
    reached_time = list(map(lambda x : float(x), reached))
    red_rules_num = read_int("# Red Rules", out)
    # red_rules = re.search(r"# Red Rules: ((?:\d)*)", out)
    # red_rules_num = -1
    # if red_rules:
    #     red_rules_num = int(red_rules.group(1))
    smt_solving_time_num = read_float("SMT Solving Time", out)
    gen_solving_time_num = read_float("General Solving Time", out)
    # solving_time = re.search(r"General Solving Time: ((?:\d|\.|e|-)*)", out)
    # solving_time_num = -1
    # if solving_time:
    #     solving_time_num = float(solving_time.group(1))
    gen_solver_calls_num = read_int("General Solver Calls", out)
    # gen_solver_calls = re.search(r"General Solver Calls: ((?:\d)*)", out)
    # gen_solver_calls_num = -1
    # if gen_solver_calls:
    #     gen_solver_calls_num = int(gen_solver_calls.group(1))
    smt_solver_calls_num = read_int("SMT Solver Calls", out)
    # smt_solver_calls = re.search(r"SMT Solver Calls: ((?:\d)*)", out)
    # smt_solver_calls_num = -1
    # if smt_solver_calls:
    #     smt_solver_calls_num = int(smt_solver_calls.group(1))
    out = reached_time
    if len(nrpcs_num) == len(reached_time):
        out = list(zip(nrpcs_num, reached_time))
    print(out)
    print("Red Rules #: " + str(red_rules_num))
    print("SMT Solving time: " + str(smt_solving_time_num))
    print("Gen Solving time: " + str(gen_solving_time_num))
    print("SMT Solver calls: " + str(smt_solver_calls_num))
    print("General Solver calls: " + str(gen_solver_calls_num))

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
                    print("")
                    print(file_dir);
                    res_bench = run_nofib_bench(final_path, var_settings, timeout)
                    print("Baseline:")
                    process_output(res_bench)
                    res_bench_nrpc = run_nofib_bench_nrpc(final_path, var_settings, timeout)
                    print("NRPC:")
                    process_output(res_bench_nrpc)

run_nofib_set("imaginary", [], 60)
