#!/usr/bin/env python

import re
import os
import subprocess
import time
from tabulate import tabulate

exe_name = str(subprocess.run(["cabal", "exec", "which", "G2"], capture_output = True).stdout.decode('utf-8')).strip()

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
    # --include nofib-symbolic/common --higher-order symbolic --hpc --hpc-print-times --no-step-limit --search subpath --time 60
    return run_g2(filename, "main", ["--include", "nofib-symbolic/common", "--higher-order", "symbolic",
                                     "--hpc", "--hpc-print-times", "--no-step-limit", "--search", "subpath", "--time", str(timeout)] + var_settings)

def run_nofib_bench_nrpc(filename, var_settings, timeout):
    return run_nofib_bench(filename, ["--nrpc"] + var_settings, timeout)

def process_output(out):
    reached = re.search(r"Ticks reached: (\d*)", out)
    total = re.search(r"Tick num: (\d*)", out)
    last = re.search(r"Last tick reached: ((\d|\.)*)", out)

    all_times = read_hpc_times(out)

    coverage = "";
    last_time = "";

    if reached != None and total != None and last != None:
        reached_f = float(reached.group(1))
        total_f = float(total.group(1))
        coverage = str(round(((reached_f / total_f)*100), 2))
        last_time = last.group(1)

        print("reached = " + str(reached.group(1)))
        print("total = " + str(total.group(1)))
        print("% reached = " + coverage)
        print("last time = " + last_time)
        print("all_times = " + str(all_times))
    return coverage, last_time

def read_runnable_benchmarks(setpath) :
    lines = {}
    file = os.path.join(setpath, "run_benchmarks.txt")
    with open(file, 'r') as file :
        lines = [line.rstrip('\n') for line in file.readlines()]
    return lines


def run_nofib_set(setname, var_settings, timeout):
        setpath = os.path.join("nofib-symbolic-functions/", setname)
        all_files_dirs = os.listdir(setpath);
        lhs_files = ["digits-of-e1", "digits-of-e2", "boyer", "circsim", "fibheaps", "knights",
                     "para", "primetest", "rewrite", "secretary", "sphere", "fft2"]

        run_benchmarks = read_runnable_benchmarks(setpath)
        print(run_benchmarks)

        data = []

        headers = ["Benchmark", "Baseline cov %", "Baseline last time",
                    "NRPC cov %", "NRPC last time"]

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
                    base_cov, base_last = process_output(res_bench)
                    res_bench_nrpc = run_nofib_bench_nrpc(final_path, var_settings, timeout)
                    print("NRPC:")
                    nrpc_cov, nrpc_last = process_output(res_bench_nrpc)

                    data.append([file_dir, base_cov, base_last, nrpc_cov, nrpc_last])
        print(tabulate(data, headers=headers, tablefmt="grid"))


run_nofib_set("imaginary", [], 60)
run_nofib_set("spectral", [], 60)
