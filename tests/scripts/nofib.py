#!/usr/bin/env python

import re
import os
import subprocess
import time

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
    return run_g2(filename, "main", ["--include", "nofib-symbolic/common", "--hpc"] + var_settings, timeout)

def process_output(out):
    reached = re.search(r"Ticks reached: (\d*)", out)
    total = re.search(r"Tick num: (\d*)", out)
    last = re.search(r"Last tick reached: ((\d|\.)*)", out)

    if reached != None and total != None and last != None:
        reached_f = float(reached.group(1))
        total_f = float(total.group(1))
        # print(reached.group(1))
        # print(total.group(1))
        print("% reached = " + str(reached_f / total_f))
        print("last time = " + last.group(1))


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
                    res = run_nofib_bench(final_path, var_settings, timeout)
                    process_output(res)

run_nofib_set("imaginary", [], 60)
