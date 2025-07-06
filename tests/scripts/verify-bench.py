#!/usr/bin/env python
# Tests Verify on the Zeno suite

import os
import re
import subprocess
import time

exe_name = str(subprocess.run(["cabal", "exec", "which", "Verify"], capture_output = True).stdout.decode('utf-8')).strip()
latex_tbl1 = ""
latex_tbl2 = ""

def generate_table1(property, approxTime, nrpcTime, nAppTime) :
    global latex_tbl1
    common_str = " & "
    prop = re.sub(r"_", r"\\_", property)
    temp = prop + common_str + str(nAppTime) + common_str + str(approxTime) + common_str + str(nrpcTime)
    latex_tbl1 += temp + r"\\ \hline " + "\n"

def generate_table2(property, time) :
    global latex_tbl2
    common_str = " & "
    prop = re.sub(r"_", r"\\_", property)
    temp = prop + common_str + str(time)
    latex_tbl2 += temp + r"\\ \hline " + "\n"

def process_output(out):
    reg = re.search(r"Execution Time: ((?:\d|\.|e|-)*)", out)
    res_num = -1
    if reg:
        res_num = float(reg.group(1))
    return res_num

def run_verify(filename, thm, time_limit):
    start_time = time.monotonic();
    res = call_verify_process(filename, thm, time_limit);
    end_time = time.monotonic();
    elapsed = end_time - start_time;
    return res;

def call_verify_process(filename, thm, time_limit):
    try:
        args = [exe_name, "verify/tests/" + filename, thm, "--time", str(time_limit)]
        res = subprocess.run(args, universal_newlines=True, capture_output=True);
        return res.stdout
    except subprocess.TimeoutExpired as TimeoutEx:
        # extra line break at end to match the one from normal termination
        return "Timeout"
        # return TimeoutEx.stdout.decode('utf-8') + "\nTimeout\n"

def unmodified_theorems():
    ret = []
    for i in range(1, 86):
        if i < 10:
            ret.append(("prop_0" + str(i), []))
        else:
            ret.append(("prop_" + str(i), []))
    return ret

def read_runnable_benchmarks(setpath, settings) :
    props = []
    lines = []
    file = os.path.join(setpath, "run_props.txt")
    with open(file, 'r') as file :
        for line in file:
            stripped = line.rstrip('\n')
            if stripped == "--":
                lines.append(props)
                props = []
            else:
                props.append((stripped, settings))
        lines.append(props)
    return lines

def test_suite_general(fname_in, suite, time_limit):
    verified = 0
    cex = 0
    timeout = 0
    for (thm, settings) in suite:
        print(thm)
        res = run_verify(fname_in, thm, time_limit)
        runTime = round(float(process_output(res)), 2)
        generate_table1(thm, runTime, runTime, runTime) 
        if "Verified" in res:
            print("Verified")
            verified += 1
        if "Counterexample" in res:
            print("Counterexample")
            cex += 1
            generate_table2(thm, runTime)
        if "Timeout" in res:
            print("Timeout")
            timeout +=1
        if "error" in res:
            print("error")
            timeout +=1
    return (verified, cex, timeout)

# def test_suite_csv(filename, properties, timeout):
#     return test_suite_general(filename, properties, timeout)

def main():
    global latex_tbl1
    global latex_tbl2
    (v, c, t) = test_suite_general("Zeno.hs", unmodified_theorems(), 15)
    ltx_tbl1 = latex_tbl1

    print("Verified :" + str(v))
    print("Counterexample :" + str(c))
    print("Timeout :" + str(t))

    setpath = os.path.join("verify/tests")
    run_bench = read_runnable_benchmarks(setpath, [])
    for benchmark in run_bench :
        (filename, setting) = benchmark[0]
        tempStr = r"\multicolumn{2}{l}{\textbf{" + filename + r"}}\\ \hline " + "\n"
        latex_tbl2 += tempStr
        print("\nBenchmark : " + filename + "\n")
        (v, c, t) = test_suite_general(filename + ".hs", benchmark[1:], 15)
        print("\nTotal properties: " + str(len(benchmark) - 1))
        print("Verified :" + str(v))
        print("Counterexample :" + str(c))
        print("Timeout :" + str(t))
        print("\n")
    print("Latex for table1 is: \n" + ltx_tbl1)
    print("Latex for table2 is: \n" + latex_tbl2)

if __name__ == "__main__":
    main()