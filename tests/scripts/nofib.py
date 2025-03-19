#!/usr/bin/env python

import re
import os
import subprocess
import time

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
    return run_g2(filename, "main", ["--include", "nofib-symbolic/common", "--hpc", "--hpc-print-times", "--no-step-limit", "--search", "subpath", "--time", str(timeout)] + var_settings)

def run_nofib_bench_nrpc(filename, var_settings, timeout):
    return run_nofib_bench(filename, ["--nrpc", "--higher-order", "symbolic-nrpc"] + var_settings, timeout)

def process_output(out):
    reached = re.search(r"Ticks reached: (\d*)", out)
    total = re.search(r"Tick num: (\d*)", out)
    last = re.search(r"Last tick reached: ((\d|\.)*)", out)

    all_times = read_hpc_times(out)

    if reached != None and total != None and last != None:
        reached_f = float(reached.group(1))
        total_f = float(total.group(1))
        # print(reached.group(1))
        # print(total.group(1))
        print("% reached = " + str(reached_f / total_f))
        print("last time = " + last.group(1))
        print("all_times = " + str(all_times))


def run_nofib_set(setname, var_settings, timeout):
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

run_nofib_set("imaginary", [], 60)
