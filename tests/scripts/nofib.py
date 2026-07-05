#!/usr/bin/env python

import re
import os
import subprocess
import time

exe_name = str(subprocess.run(["cabal", "exec", "which", "G2"], capture_output = True).stdout.decode('utf-8')).strip()

def read_hpc_times(out):
    times = []
    read = False
    tick_time_list = []
    
    for line in out.splitlines():
        if line.startswith("End of tick times"):
            read = False
        if read:
            match = re.search(r'\((\d+),"(.*?)"\)\s*-\s*([0-9]*\.[0-9]+)', line)
            if match != None:
                key = (int(match.group(1)), match.group(2))
                value = round(float(match.group(3)), 2)
                tick_time_list.append((key, value))
                times.append(line)
        if line.startswith("All tick times:"):
            read = True
    return tick_time_list, times

def read_int(pre, out, default_val= -1):
    return read_int_gen(pre + r": ((?:\d)*)", out, default_val)

def read_int_gen(pre, out, default_val= -1):
    reg = re.search(pre, out)
    res_num = default_val
    if reg:
        res_num = int(reg.group(1))
    return res_num

def read_float(pre, out):
    reg = re.search(pre + r": ((?:\d|\.|e|-)*)", out)
    res_num = -1
    if reg:
        res_num = float(reg.group(1))
    return res_num

def calculate_hpc_coverage(hpc_res, total = -1):
    rel_hpc_res = list(filter(lambda x: x[0] != "CallForHPC", hpc_res))
    print("calculate hpc converage")
    print(hpc_res)
    print(rel_hpc_res)
    found = map(lambda x : x[2], rel_hpc_res)
    calc_total = map(lambda x : x[3], rel_hpc_res)
    coverage = 0
    total = calc_total if total == -1 else [total]
    print(list(map(lambda x : ((x[4]), (x[5])), rel_hpc_res)))
    hpc_branch_nums = sum(map(lambda x : (int(x[4]) + int(x[5])), rel_hpc_res))
    try:
        return (sum(found) / sum(total)), hpc_branch_nums
    except:
        return 0, hpc_branch_nums

# Calling and reading from G2
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
    # --include nofib-symbolic/common --hpc --hpc-print-times --print-num-red-rules --solver-time --print-num-solver-calls --print-num-higher-states --no-step-limit --search subpath --subpath-len 2 --hpc-discard-strat --print-encodeFloat --validate --measure-coverage --time 60
    return run_g2(filename, "cover", ["--include", "nofib-symbolic/common",
                                       "--hpc", "--hpc-print-times", "--print-num-red-rules", "--solver-time", "--print-num-solver-calls", "--print-num-higher-states",
                                       "--no-step-limit", "--search", "subpath", "--subpath-len", "2", "--hpc-discard-strat", "--print-encodeFloat",
                                       "--validate", "--measure-coverage", "--time", str(timeout)] + var_settings)

def run_nofib_bench_nrpc(filename, var_settings, timeout):
    return run_nofib_bench(filename, ["--lib-nrpc", "--print-num-nrpc"] + var_settings, timeout)

def process_output(out, use_reach_ticks = False):
    nrpcs = re.findall(r"NRPCs Generated: ((?:\d)*)", out)
    nrpcs_num = list(map(lambda x : int(x), nrpcs))

    red_rules_num = read_int("# Red Rules", out)
    smt_solving_time_num = read_float("SMT Solving Time", out)
    gen_solving_time_num = read_float("General Solving Time", out)
    gen_solver_calls_num = read_int("General Solver Calls", out)
    smt_solver_calls_num = read_int("SMT Solver Calls", out)

    reached = re.search(r"Ticks reached: (\d*)", out)
    total = re.search(r"Tick num: (\d*)", out)
    last = re.search(r"Last tick reached: ((\d|\.)*)", out)

    reachable_ticks_search = re.search(r"Reachable ticks: (\d*)", out)
    reachable_ticks = int(reachable_ticks_search.group(1)) if use_reach_ticks and reachable_ticks_search != None else -1
    hpc_exp = re.findall(r"module (.*)>-----\n\s*((?:\d)*)% expressions used \(((?:\d)*)/((?:\d)*)\)(?:\n|[^-])*boolean coverage \((?:\d*)/(\d*)\)(?:\n|[^-])*alternatives used \((?:\d*)/(\d*)\)", out)
    print("hpc_exp = " + str(hpc_exp))
    hpc_exp_num = list(map(lambda x : (x[0], int(x[1]), int(x[2]), int(x[3]), (x[4]), (x[5])), hpc_exp))
    hpc_reached, branch_num = calculate_hpc_coverage(hpc_exp_num, total = reachable_ticks)
    hpc_reached = round(hpc_reached * 100, 1)

    tick_times_list, all_times = read_hpc_times(out)
    coverage = 0.0
    last_time = 0.0
    avg_nrpc = round((sum(nrpcs_num)/len(nrpcs_num) if len(nrpcs_num) > 0 else 0), 2)
    total_f = 0.0

    if reached != None and total != None and last != None:
        reached_f = float(reached.group(1))
        total_f = int(total.group(1)) if reachable_ticks == -1 else reachable_ticks
        # print(reached.group(1))
        # print(total.group(1))

        coverage = round(((reached_f / total_f)*100), 1)
        print("Last time is: "+ last.group(1))
        last_time = round(float(last.group(1)), 1) if last.group(1) else 0.0

        print("hpc reached = " + str(hpc_reached))
        print("g2 reached = " + str(reached.group(1)))
        print("total = " + str(total.group(1)))
        print("% reached = " + str(coverage))
        print("last time = " + last.group(1))
        print("all_times = " + str(all_times))
        print("Red Rules #: " + str(red_rules_num))
        print("SMT Solving time: " + str(smt_solving_time_num))
        print("Gen Solving time: " + str(gen_solving_time_num))
        print("SMT Solver calls: " + str(smt_solver_calls_num))
        print("General Solver calls: " + str(gen_solver_calls_num))
        print ("# nrpcs = " + str(nrpcs_num))
        print("# branches = " + str(branch_num))

    return hpc_reached, coverage, last_time, avg_nrpc, tick_times_list, total_f, branch_num


def run_nofib_set(setname, var_settings, timeout, use_reach_ticks = False):
        setpath = os.path.join("nofib-symbolic/", setname)
        all_files_dirs = os.listdir(setpath);

        print(setpath)

        for file_dir in all_files_dirs:
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

run_nofib_set("imaginary", [], 10, use_reach_ticks = False)
