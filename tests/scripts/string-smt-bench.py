#!/usr/bin/env python

import re
import os
import subprocess
import time

import shutil

exe_name = str(subprocess.run(["cabal", "exec", "which", "G2"], capture_output = True).stdout.decode('utf-8')).strip()

smt_solvers = ["z3", "z3str3"] # "cvc5", "ostrich", "z3-noodler"]

# outputting latex
def cov_generate_latex(res_all):
    solvers = ["conc"] + smt_solvers

    print(r"\begin{tabular}{| l |" + "".join(map(lambda _ : " c | c |", solvers)) + "}")
    print("\hline")
    multi_smt = " & ".join(map(lambda s : r"\multicolumn{2}{l|}{" + s + "}", solvers))
    print(" & " + multi_smt + r"\\ \hline")

    cov_last_lab = " & ".join(map(lambda s : r"Cov (\%) & Last (s)", solvers))
    print("Benchmark & " + cov_last_lab + r"\\ \hline")

    for (file_dir, bench_res) in res_all:
        line = file_dir + " & "
        best_cov = max([x["reached"] for x in bench_res])
        rch_ls_pairs = map(lambda rl: (r"\textbf{" + str(rl["reached"]) + "}" if rl["reached"] == best_cov else str(rl["reached"]))
                                      + " & " 
                                      + ("-" if rl["last"] == -1 else str(rl["last"])), bench_res)
        res_line = " & ".join(rch_ls_pairs)
        print(line + res_line + r"\\ \hline")

    print(r"\end{tabular}")

def solver_cov_res_csv(res_all):
    solvers = ["conc"] + smt_solvers

    for (file_dir, bench_res) in res_all:
        print(file_dir)
        for (solver, bench) in zip(solvers, bench_res):
            solving = bench["solving_time"]
            sat_c = bench["sat_count"]
            unsat_c = bench["unsat_count"]
            unknown_c = bench["unknown_count"]
            line = solver + "," + solving + "," + sat_c + "," + unsat_c + "," + unknown_c
            print(line)

def cex_generate_latex(res_all):
    solvers = ["conc"] + smt_solvers

    print(r"\begin{tabular}{| l |" + "".join(map(lambda _ : " c |", solvers)) + "}")
    print("\hline")
    multi_smt = " & ".join(solvers)
    print(" & " + multi_smt + r"\\ \hline")

    found_lab = " & ".join(map(lambda s : r" Time (s)", solvers))
    print("Benchmark & " + found_lab + r"\\ \hline")

    for (file_dir, bench_res) in res_all:
        line = file_dir + " & "
        bench_res = map(lambda r : "-" if r == -1 else str(r), bench_res)
        bench_res = " & ".join(bench_res)
        print(line + bench_res + r"\\ \hline")

    print(r"\end{tabular}")

def cex_generate_csv(res_all):
    csv = ""
    solvers = ["conc"] + smt_solvers
    for (prop, bench_res) in res_all:
        csv += prop + "\n"
        # print(bench_res)
        for (solver, solver_res) in zip(solvers, bench_res):
            # print(solver_res)
            csv += solver + "," + ",".join(map(str, solver_res["found"])) + "\n"
    return csv

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

def run_bench(filename, func, var_settings, timeout, solver):
    # --include nofib-symbolic/common --hpc --hpc-print-times --no-step-limit --search subpath --time 60
    settings = ["--include", "nofib-symbolic/common"
               , "--no-step-limit", "--search", "subpath"
               , "--print-sol-counts", "--print-num-solver-calls", "--solver-time"
               , "--time", str(timeout)
               , "--smt", solver] + var_settings
    print(*settings)
    return run_g2(filename, func, settings, timeout)

def run_bench_smt(filename, func, var_settings, timeout, solver):
    return run_bench(filename, func, ["--smt-strings"] + var_settings, timeout, solver)

def cov_process_output(out):
    reached = re.search(r"Ticks reached: (\d*)", out)
    total = re.search(r"Tick num: (\d*)", out)
    last = re.search(r"Last tick reached: ((\d|\.)*)", out)

    solving_time = re.search(r"SMT Solving Time: ((\d|\.)*)", out)
    sat_c = re.search(r"# SAT: ((\d|\.)*)", out)
    unsat_c = re.search(r"# UNSAT: ((\d|\.)*)", out)
    unknown_c = re.search(r"# Unknown: ((\d|\.)*)", out)

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

        print("solving time = " + str(solving_time.group(1)))
        print("sat count = " + str(sat_c.group(1)))
        print("unsat count = " + str(unsat_c.group(1)))
        print("unknown count = " + str(unknown_c.group(1)))

    if last != None:
        last = round(float(last[1]), 1)
    else:
        last = -1
    
    return { "reached" : hpc_reached
           , "last" : last
           , "solving_time" : solving_time.group(1)
           , "sat_count" : sat_c.group(1)
           , "unsat_count" : unsat_c.group(1)
           , "unknown_count" : unknown_c.group(1) }

def cex_process_output(out):
    found = re.search(r"State Accepted Time: ((\d|\.)*)", out)
    found_float = -1
    if found != None:
        print("Found counterexample = " + str(found[1]))
        found_float = float(found[1])

    solving_time = re.search(r"SMT Solving Time: ((\d|\.)*)", out)
    sat_c = re.search(r"# SAT: ((\d|\.)*)", out)
    unsat_c = re.search(r"# UNSAT: ((\d|\.)*)", out)
    unknown_c = re.search(r"# Unknown: ((\d|\.)*)", out)

    print("solving time = " + str(solving_time.group(1)))
    print("sat count = " + str(sat_c.group(1)))
    print("unsat count = " + str(unsat_c.group(1)))
    print("unknown count = " + str(unknown_c.group(1)))

    return { "found" : found_float
           , "solving_time" : solving_time.group(1)
           , "sat_count" : sat_c.group(1)
           , "unsat_count" : unsat_c.group(1)
           , "unknown_count" : unknown_c.group(1) }

def run_nofib_set(setname, var_settings, timeout):
        setpath = os.path.join("string-to-smt-benchmark/", setname)
        all_files_dirs = os.listdir(setpath);

        okasaki_bench = ["BinaryHeap.hs", "LeftistHeap.hs", "RedBlackTree.hs"]

        print(setpath)

        cov_settings = [ "--hpc", "--hpc-print-times", "--measure-coverage" ] + var_settings

        res_all = []

        for file_dir in all_files_dirs:
            res_bench = []
            bench_path = os.path.join(setpath, file_dir)
            isOkasaki = True if file_dir in okasaki_bench else False
            if os.path.isdir(bench_path) or file_dir in okasaki_bench:
                path1 = os.path.join(bench_path, "Main.hs") if not isOkasaki else bench_path
                path2 = os.path.join(bench_path, "Main.lhs") if not isOkasaki else bench_path
                final_path = path1 if os.path.isfile(path1) else path2
                if os.path.isfile(final_path):
                    print(file_dir);
                    res_base = run_bench(final_path, "main", cov_settings, timeout, "z3")
                    print("Baseline:")
                    last_reached = cov_process_output(res_base)
                    res_bench.append(last_reached)
                    for solver_name in smt_solvers:
                        solver = "z3" if solver_name == "z3-noodler" else solver_name
                        extra_var = ["--smt-path", "z3-noodler"] if solver_name == "z3-noodler" else []
                        print(extra_var)
                        res_smt = run_bench_smt(final_path, "main", cov_settings + extra_var, timeout, solver)
                        print("SMT " + solver_name + ":")
                        last_reached = cov_process_output(res_smt)
                        res_bench.append(last_reached)
                res_all.append((file_dir, res_bench))

        return res_all

def run_properties(setname, filename, var_settings, timeout, properties):
        setpath = os.path.join("string-to-smt-benchmark/", setname)
        bench_path = os.path.join(setpath, filename)
        print(bench_path)

        only_one = var_settings + ["--max-outputs", "1", "--accept-times"]

        res_all = []

        for prop in properties:
            print(prop)
            res_bench = []
            res_base = run_bench(bench_path, prop, only_one, timeout, "z3")
            print("Baseline:")
            last_reached = cex_process_output(res_base)
            res_bench.append(last_reached)
            for solver_name in smt_solvers:
                solver = "z3" if solver_name == "z3-noodler" else solver_name
                extra_var = ["--smt-path", "z3-noodler"] if solver_name == "z3-noodler" else []
                res_smt = run_bench_smt(bench_path, prop, only_one + extra_var, timeout, solver)
                print("SMT " + solver_name + ":")
                found_cex = cex_process_output(res_smt)
                res_bench.append(found_cex)
            res_all.append((prop, res_bench))

        return res_all

def writeParamCalls(file_name, prop, incr_by, min_param, max_param):
    file = open(file_name, "a")
    file.write("\n")
    for i in range(min_param, max_param + incr_by, incr_by):
        file.write(prop + "_" + str(i) + " = " + prop + " " + str(i) + "\n")
    file.close()

def run_param_properties(setname, filename, var_settings, timeout, properties, incr_by = 10, min_param = 10, max_param = 100):
        setpath = os.path.join("string-to-smt-benchmark/", setname)
        param_bench_path = os.path.join(setpath, filename)

        only_one = var_settings + ["--check-asserts", "--max-outputs", "1", "--accept-times"]

        res_all = []

        for prop in properties:
            use_bench_path = os.path.join(setpath, "param_" + filename)
            print(param_bench_path)
            print(use_bench_path)

            shutil.copy(param_bench_path, use_bench_path)
            writeParamCalls(use_bench_path, prop, incr_by, min_param, max_param)

            print(prop)
            res_for_each_prop = []

            solver_res_bench = []
            for i in range(min_param, max_param + incr_by, incr_by):
                res_base = run_bench(use_bench_path, prop + "_" + str(i), only_one, timeout, "z3")
                print("Baseline " + str(i) + ":")
                last_reached = cex_process_output(res_base)
                solver_res_bench.append(last_reached)
            res_for_each_prop.append(solver_res_bench)

            for solver_name in smt_solvers:
                solver_res_bench = []
                for i in range(min_param, max_param + incr_by, incr_by):
                    solver = "z3" if solver_name == "z3-noodler" else solver_name
                    extra_var = ["--smt-path", "z3-noodler"] if solver_name == "z3-noodler" else []
                    res_smt = run_bench_smt(use_bench_path, prop + "_" + str(i),  only_one + extra_var, timeout, solver)
                    print("SMT " + solver_name + " " + str(i) + ":")
                    found_cex = cex_process_output(res_smt)
                    solver_res_bench.append(found_cex)
                res_for_each_prop.append(solver_res_bench)
            res_all.append((prop, res_for_each_prop))

            file = open("string_cex_results.txt", "a")
            file.write(cex_generate_csv([(prop, res_for_each_prop)]))
            file.close()

        return res_all

time_lim = 6

# res_imag = run_nofib_set("nofib-symbolic/imaginary", [], time_lim)
# res_spec = run_nofib_set("nofib-symbolic/spectral", [], time_lim)
# res_progs = run_nofib_set("programs", [], time_lim)

# cov_generate_latex(res_imag + res_spec + res_progs)
# cov_generate_latex(res_imag)
# solver_cov_res_csv(res_imag)

time_lim = 30

props = map(lambda x : "prop" + str(x), list(range(1, 3)))
res_props = run_param_properties("properties", "ParamProperties.hs", [], time_lim, props)

# print(res_props)
# cex_generate_latex(res_props)
print(cex_generate_csv(res_props))