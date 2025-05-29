#!/usr/bin/env python

import re
import os
import subprocess
import time
from tabulate import tabulate

exe_name = str(subprocess.run(["cabal", "exec", "which", "G2"], capture_output = True).stdout.decode('utf-8')).strip()
latex_str_tbl1 = ""
latex_str_tbl2 = ""
latex_str_tbl3 = ""

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
    # --include nofib-symbolic/common --higher-order symbolic --hpc --hpc-print-times --print-num-nrpc --print-num-red-rules --solver-time --print-num-solver-calls --no-step-limit --search subpath --hpc-discard-strat --time 60
    return run_g2(filename, "main", ["--include", "nofib-symbolic/common", "--higher-order", "symbolic",
                                     "--hpc", "--hpc-print-times", "--print-num-nrpc", "--print-num-red-rules", "--solver-time", "--print-num-solver-calls",
                                     "--no-step-limit", "--search", "subpath", "--subpath-len", "8", "--hpc-discard-strat", "--measure-coverage", "--time", str(timeout)] + var_settings)

def run_nofib_bench_nrpc(filename, var_settings, timeout):
    return run_nofib_bench(filename, ["--nrpc"] + var_settings, timeout)

def generate_string_for_cov(benchmark, tickCount, covBL, covNRPC, lastTimeBL, lastTimeNrpc):
    #cichelli & \textbf{4} & 3 & 9.5 & 11 & 2\\ \hline
    tempBCov = str(covBL)
    tempNCov = str(covNRPC)
    tempBTime = str(lastTimeBL)
    tempNTime = str(lastTimeNrpc)

    global latex_str_tbl1
    common_str = " & "
    
    if covBL > covNRPC:
        tempBCov = r"\textbf{" + str(covBL) + "}"
    elif covNRPC > covBL:
        tempNCov = r"\textbf{" + str(covNRPC) + "}"
    else:
        if abs(lastTimeNrpc - lastTimeBL) >= 1 :
            if lastTimeBL < lastTimeNrpc :
                tempBTime = r"\textbf{" + str(lastTimeBL) + "}"
            elif lastTimeNrpc < lastTimeBL:
                tempNTime = r"\textbf{" + str(lastTimeNrpc) + "}"
    
    latex_str_tbl1 = latex_str_tbl1 + benchmark + common_str + str(tickCount) + common_str + tempBCov + common_str + tempBTime + common_str + tempNCov + common_str + tempNTime + r"\\ \hline " + "\n"


def generate_str_for_pos_ord(benchmark, bTick1s, nTick1s, bTick3s, nTick3s, bTick5s, nTick5s):
    result = ""
    common_str = " & "
    tempTick1s = str(bTick1s) + "/" + str(nTick1s)
    tempTick3s = str(bTick3s) + "/" + str(nTick3s)
    tempTick5s = str(bTick5s) + "/" + str(nTick5s)
    result = benchmark + common_str + tempTick1s + common_str + tempTick3s + common_str + tempTick5s + r"\\ \hline " + "\n"

    return result

def generate_graph_string(benchmark, bCoordinates, nCoordinates):

    str = r"\begin{tikzpicture}" + "\n" + r"\centering" + "\n" + r"\begin{axis}[" + "\n" + r"title={Baseline vs NRPC(" + \
    benchmark + ")}," + "\n" + r"xlabel={Time (s)}," + "\n" + r"ylabel={No. of Ticks}," + "\n" + "grid=major," + "\n" + \
    r"width=\columnwidth," + "\n" + r"]" + "\n" + r"\addplot[color=blue,mark=*,smooth] plot coordinates {" + "\n" + bCoordinates + \
    r"};" + "\n" + r"\addlegendentry{Baseline}" + "\n" + r"\addplot[smooth,color=red,mark=x] plot coordinates {" + "\n" +\
    nCoordinates + "\n" + r"};" + "\n" + r"\addlegendentry{NRPC}" + "\n" + r"\end{axis}" + "\n" + r"\end{tikzpicture}"

    return str


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

def calculate_graph(tick_times):
    if not tick_times:
        return "(0, 0)"
    count = 0
    numTickMap = []
    lastTickTime = tick_times[0][1]
    for tick, time in tick_times:
        if time != lastTickTime :
            numTickMap.append((lastTickTime, count))
            count = 1
            lastTickTime = time
        else:
            count += 1
    numTickMap.append((lastTickTime, count))

    pair_strings = [f"({x}, {y})" for x, y in numTickMap]
    coordinates = " ".join(pair_strings)

    return coordinates

def calculate_order(base_tick_times, nrpc_tick_times):
    nrpc1 = 0
    nrpc3 = 0
    nrpc5 = 0
    base1 = 0
    base3 = 0
    base5 = 0
    zippedList = zip(base_tick_times, nrpc_tick_times)
    for ((baseTick, baseMod), baseTime) , ((nrpcTick, nrpcMod), nrpcTime) in zippedList:
        if baseTick == nrpcTick and baseMod == nrpcMod:
            continue
        timeDiff = nrpcTime - baseTime
        # NRPCs are doing better
        if timeDiff < 0:
            if abs(timeDiff) >= 1:
                nrpc1 += 1
            if abs(timeDiff) >= 3:
                nrpc3 += 1
            if abs(timeDiff) >= 5:
                nrpc5 += 1
        # Baseline is doing better
        else:
            if abs(timeDiff) >= 1:
                base1 += 1
            if abs(timeDiff) >= 3:
                base3 += 1
            if abs(timeDiff) >= 5:
                base5 += 1
    return base1, base3, base5, nrpc1, nrpc3, nrpc5

def calculate_time_diff(base_tick_times_map, nrpc_tick_times_map):
    nrpc1 = 0
    nrpc3 = 0
    nrpc5 = 0
    base1 = 0
    base3 = 0
    base5 = 0
    for tick, base_time in base_tick_times_map.items():
        if tick in nrpc_tick_times_map:
            nrpc_tick_time = nrpc_tick_times_map[tick]
            timeDiff = nrpc_tick_time - base_time
            if timeDiff < 0:
                if abs(timeDiff) >= 1:
                    nrpc1 += 1
                if abs(timeDiff) >= 3:
                    nrpc3 += 1
                if abs(timeDiff) >= 5:
                    nrpc5 += 1
            else:
                if abs(timeDiff) >= 1:
                    base1 += 1
                if abs(timeDiff) >= 3:
                    base3 += 1
                if abs(timeDiff) >= 5:
                    base5 += 1
        
    return base1, base3, base5, nrpc1, nrpc3, nrpc5

def calculate_hpc_coverage(hpc_res):
    rel_hpc_res = list(filter(lambda x: x[0] != "CallForHPC", hpc_res))
    print("calculate hpc converage")
    print(hpc_res)
    print(rel_hpc_res)
    found = map(lambda x : x[2], rel_hpc_res)
    total = map(lambda x : x[3], rel_hpc_res)
    coverage = 0
    try:
        return (sum(found) / sum(total))
    except:
        return 0

def read_runnable_benchmarks(setpath) :
    lines = {}
    file = os.path.join(setpath, "run_benchmarks.txt")
    with open(file, 'r') as file :
        lines = [line.rstrip('\n') for line in file.readlines()]
    return lines

def process_output(out):
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

    hpc_exp = re.findall(r"module (.*)>-----\n\s*((?:\d)*)% expressions used \(((?:\d)*)/((?:\d)*)\)", out)
    hpc_exp_num = list(map(lambda x : (x[0], int(x[1]), int(x[2]), int(x[3])), hpc_exp))
    hpc_reached = round((calculate_hpc_coverage(hpc_exp_num) * 100), 2)

    tick_times_list, all_times = read_hpc_times(out)
    coverage = 0.0
    last_time = 0.0
    avg_nrpc = round((sum(nrpcs_num)/len(nrpcs_num) if len(nrpcs_num) > 0 else 0), 2)
    total_f = 0.0

    if reached != None and total != None and last != None:
        reached_f = float(reached.group(1))
        total_f = float(total.group(1))

        coverage = round(((reached_f / total_f)*100), 2)
        print("Last time is: "+ last.group(1))
        last_time = round(float(last.group(1)), 2) if last.group(1) else 0.0

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
    return hpc_reached, coverage, last_time, avg_nrpc, tick_times_list, total_f


def run_nofib_set(setname, var_settings, timeout):
        global latex_str_tbl1
        global latex_str_tbl2
        global latex_str_tbl3
        setpath = os.path.join("nofib-symbolic-functions/", setname)
        all_files_dirs = os.listdir(setpath);
        lhs_files = ["digits-of-e1", "digits-of-e2", "boyer", "circsim", "fibheaps", "knights",
                     "para", "primetest", "rewrite", "secretary", "sphere", "fft2"]

        run_benchmarks = read_runnable_benchmarks(setpath)
        print(run_benchmarks)

        data = []

        headers = ["Benchmark", "#Total Ticks", "B HPC cov %", "B cov %", "B last time",
                    "N HPC cov %", "N cov %", "N last time", "Pos 1-sec B/N", "Pos 3-sec B/N", 
                    "Pos 5-sec B/N", "Diff tick 1s", "Diff tick 3s", "Diff tick 5s", "Avg # Nrpcs"]
        
        tempStr = r"\multicolumn{4}{l}{\textbf{" + setname + r"}}\\ \hline " + "\n"
        latex_str_tbl1 += tempStr
        latex_str_tbl2 += tempStr
        latex_str_tbl3 += tempStr

        for file_dir in run_benchmarks:
            bench_path = os.path.join(setpath, file_dir)
            if os.path.isdir(bench_path):
                if file_dir in lhs_files:
                    final_path = os.path.join(bench_path, "Main.lhs")
                else:
                    final_path = os.path.join(bench_path, "Main.hs")
                if os.path.isfile(final_path):
                    print(file_dir);
                    res_bench = run_nofib_bench(final_path, var_settings, timeout)
                    print("Baseline:")
                    base_hpc_cov, base_cov, base_last, avg, base_tick_times, base_total = process_output(res_bench)
                    res_bench_nrpc = run_nofib_bench_nrpc(final_path, var_settings, timeout)
                    print("NRPC:")
                    nrpc_hpc_cov, nrpc_cov, nrpc_last, avg_nrpc, nrpc_tick_times, nrpc_total  = process_output(res_bench_nrpc)
                    bt1, bt3, bt5, nt1, nt3, nt5 = calculate_time_diff(dict(base_tick_times), dict(nrpc_tick_times))
                    bo1, bo3, bo5, no1, no3, no5 = calculate_order(base_tick_times, nrpc_tick_times)

                    graph_latex = generate_graph_string(file_dir, calculate_graph(base_tick_times), calculate_graph(nrpc_tick_times))

                    data.append([file_dir, base_total, base_hpc_cov, str(base_cov), base_last, nrpc_hpc_cov, str(nrpc_cov), nrpc_last,
                                 str(bt1) + "/" + str(nt1), str(bt3) + "/" + str(nt3), str(bt5) + "/" + str(nt5),
                                 str(bo1) + "/" + str(no1), str(bo3) + "/" + str(no3), str(bo5) + "/" + str(no5),
                                 str(avg_nrpc)])
                    generate_string_for_cov(file_dir, base_total, base_hpc_cov, nrpc_hpc_cov, base_last, nrpc_last)
                    latex_str_tbl2 += generate_str_for_pos_ord(file_dir, bt1, nt1, bt3, nt3, bt5, nt5)
                    latex_str_tbl3 += generate_str_for_pos_ord(file_dir, bo1, no1, bo3, no3, bo5, no5)
                    print("\n")
                    print("Graph latex for: " + file_dir + ": \n" + graph_latex)
                    print("\n")
        print(tabulate(data, headers=headers, tablefmt="grid"))
        print("\n")

run_nofib_set("imaginary", [], 300)
run_nofib_set("spectral", [], 300)

print("Latex string for coverage table\n")
print(latex_str_tbl1)
print("\nLatex string for table 2\n")
print(latex_str_tbl2)
print("\nLatex string for table 3\n")
print(latex_str_tbl3)
