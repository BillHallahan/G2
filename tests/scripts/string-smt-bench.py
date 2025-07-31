#!/usr/bin/env python

import re
import os
import subprocess
import time

exe_name = str(subprocess.run(["cabal", "exec", "which", "G2"], capture_output = True).stdout.decode('utf-8')).strip()

smt_solvers = ["z3", "cvc5", "ostrich", "z3-noodler"]

# outputting latex
def generate_latex(res_all):
    solvers = ["conc"] + smt_solvers


    print(r"\begin{tabular}{| l |" + "".join(map(lambda _ : " c | c |", solvers)) + "}")
    print("\hline")
    multi_smt = " & ".join(map(lambda s : r"\multicolumn{2}{l|}{" + s + "}", solvers))
    print(" & " + multi_smt + r"\\ \hline")

    cov_last_lab = " & ".join(map(lambda s : r"Cov (\%) & Last (s)", solvers))
    print("Benchmark & " + cov_last_lab + r"\\ \hline")

    for (file_dir, bench_res) in res_all:
        line = file_dir + " & "
        bench_res = map(lambda rl: str(rl[0]) + " & " + str(rl[1]), bench_res)
        bench_res = " & ".join(bench_res)
        print(line + bench_res + r"\\ \hline")

    print(r"\end{tabular}")

# dealing with HPC
def calculate_hpc_coverage(hpc_res):
    rel_hpc_res = list(filter(lambda x: x[0] != "CallForHPC", hpc_res))
    print("calculate hpc converage")
    print(hpc_res)
    print(rel_hpc_res)
    found = map(lambda x : x[2], rel_hpc_res)
    total = map(lambda x : x[3], rel_hpc_res)
    coverage = 0
    print(list(map(lambda x : ((x[4]), (x[5])), rel_hpc_res)))
    hpc_branch_nums = sum(map(lambda x : (int(x[4]) + int(x[5])), rel_hpc_res))
    try:
        return (sum(found) / sum(total)), hpc_branch_nums
    except:
        return 0, hpc_branch_nums

def read_hpc_times(out):
    times = []
    read = False
    for line in out.splitlines():
        if line.startswith("End of tick times"):
            read = False
        if read:
            times.append(line)
        if line.startswith("All tick times:"):
            read = True
    return times

# Calling and reading from G2
def run_g2(filename, func, var_settings, timeout):
    start_time = time.monotonic();
    res = call_g2_process(filename, func, var_settings, timeout);
    end_time = time.monotonic();
    elapsed = end_time - start_time;
    return res

def call_g2_process(filename, func, var_settings, to):
    args = [exe_name, filename, func]
    try:
        res = subprocess.run(args + var_settings, universal_newlines=True, capture_output=True, timeout = to * 5);
        return res.stdout
    except subprocess.TimeoutExpired:
        return ""

def run_bench(filename, var_settings, timeout, solver):
    # --include nofib-symbolic/common --hpc --hpc-print-times --no-step-limit --search subpath --time 60
    settings = ["--include", "nofib-symbolic/common", "--hpc", "--hpc-print-times"
               , "--no-step-limit", "--search", "subpath", "--measure-coverage"
               , "--time", str(timeout)
               , "--smt", solver] + var_settings
    print(*settings)
    return run_g2(filename, "main", settings, timeout)

def run_bench_smt(filename, var_settings, timeout, solver):
    return run_bench(filename, ["--smt-strings"] + var_settings, timeout, solver)

def process_output(out):
    reached = re.search(r"Ticks reached: (\d*)", out)
    total = re.search(r"Tick num: (\d*)", out)
    last = re.search(r"Last tick reached: ((\d|\.)*)", out)

    all_times = read_hpc_times(out)

    hpc_exp = re.findall(r"module (.*)>-----\n\s*((?:\d)*)% expressions used \(((?:\d)*)/((?:\d)*)\)(?:\n|[^-])*boolean coverage \((?:\d*)/(\d*)\)(?:\n|[^-])*alternatives used \((?:\d*)/(\d*)\)", out)
    hpc_exp_num = list(map(lambda x : (x[0], int(x[1]), int(x[2]), int(x[3]), (x[4]), (x[5])), hpc_exp))
    hpc_reached, branch_num = calculate_hpc_coverage(hpc_exp_num)
    hpc_reached = round(hpc_reached * 100, 1)

    if reached != None and total != None and last != None:
        reached_f = float(reached.group(1))
        total_f = float(total.group(1))
        # print(reached.group(1))
        # print(total.group(1))
        print("% reached = " + str(reached_f / total_f))
        print("hpc reached = " + str(hpc_reached))
        print("last time = " + last.group(1))
        print("all_times = " + str(all_times))
    
    return (hpc_reached, last)

def run_nofib_set(setname, var_settings, timeout):
        setpath = os.path.join("string-to-smt-benchmark/", setname)
        all_files_dirs = os.listdir(setpath);

        okasaki_bench = ["BinaryHeap.hs", "LeftistHeap.hs", "RedBlackTree.hs"]

        print(setpath)

        res_all = []

        for file_dir in all_files_dirs:
            res_bench = []
            bench_path = os.path.join(setpath, file_dir)
            isOkasaki = True if file_dir in okasaki_bench else False
            if os.path.isdir(bench_path) or file_dir in okasaki_bench:
                final_path = os.path.join(bench_path, "Main.hs") if not isOkasaki else bench_path
                if os.path.isfile(final_path):
                    print(file_dir);
                    res_base = run_bench(final_path, var_settings, timeout, "z3")
                    print("Baseline:")
                    last_reached = process_output(res_base)
                    res_bench.append(last_reached)
                    for solver_name in smt_solvers:
                        solver = "z3" if solver_name == "z3-noodler" else solver_name
                        extra_var = ["--smt-path", "z3-noodler"] if solver == "z3-noodler" else []
                        res_smt = run_bench_smt(final_path, var_settings + extra_var, timeout, solver)
                        print("SMT " + solver_name + ":")
                        last_reached = process_output(res_smt)
                        res_bench.append(last_reached)
                res_all.append((file_dir, res_bench))

        return res_all

res_imag = run_nofib_set("nofib-symbolic/imaginary", [], 120)
res_spec = run_nofib_set("nofib-symbolic/spectral", [], 120)
res_progs = run_nofib_set("programs", [], 120)

generate_latex(res_imag + res_spec + res_progs)