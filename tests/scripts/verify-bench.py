#!/usr/bin/env python
# Tests Verify on the Zeno suite

import os
import re
import subprocess
import time

exe_name = str(subprocess.run(["cabal", "exec", "which", "Verify"], capture_output = True).stdout.decode('utf-8')).strip()
latex_tbl1 = ""
latex_tbl2 = ""

def generate_table1(property, approxTime, nrpcTime, nAppTime, timeout) :
    global latex_tbl1
    common_str = " & "
    aTime = str(approxTime) if approxTime < timeout else "-"
    nTime = str(nrpcTime) if nrpcTime < timeout else "-"
    nATime = str(nAppTime) if nAppTime < timeout else "-"
    prop = re.sub(r"_", r"\\_", property)
    temp = prop + common_str + nATime + common_str + aTime + common_str + nTime
    latex_tbl1 += temp + r"\\ \hline " + "\n"

def generate_table2(property, time, timeout) :
    global latex_tbl2
    common_str = " & "
    runTime = str(time) if time < timeout else "-"
    prop = re.sub(r"_", r"\\_", property)
    temp = prop + common_str + runTime
    latex_tbl2 += temp + r"\\ \hline " + "\n"

def process_output(out):
    reg = re.search(r"Execution Time: ((?:\d|\.|e|-)*)", out)
    res_num = -1
    if reg:
        res_num = float(reg.group(1))
    return res_num

def run_verify(filename, thm, time_limit, var_settings):
    start_time = time.monotonic();
    res = call_verify_process(filename, thm, time_limit, var_settings);
    end_time = time.monotonic();
    elapsed = end_time - start_time;
    return res;

def call_verify_process(filename, thm, time_limit, var_settings):
    try:
        args = [exe_name, "verify/tests/" + filename, thm, "--time", str(time_limit)]
        res = subprocess.run(args + var_settings, universal_newlines=True, capture_output=True, timeout=40);
        return res.stdout
    except subprocess.TimeoutExpired as TimeoutEx:
        # extra line break at end to match the one from normal termination
        return "Timeout - Script"
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
        res1 = run_verify(fname_in, thm, time_limit, [])
        runTime1 = round(float(process_output(res1)), 2)
        if fname_in == "Zeno.hs" :
            res2 = run_verify(fname_in, thm, time_limit, ["--no-rev-abs"])
            res3 = run_verify(fname_in, thm, time_limit, ["--no-approx"])
            runTime2 = round(float(process_output(res2)), 2)
            runTime3 = round(float(process_output(res3)), 2)
            generate_table1(thm, runTime1, runTime1, runTime1, time_limit)
        else:
            generate_table2(thm, runTime1, time_limit)

        if "Verified" in res1:
            print("Verified")
            verified += 1
        if "Counterexample" in res1:
            print("Counterexample")
            cex += 1
        if "Timeout" in res1:
            print("Timeout")
            timeout +=1
        if "error" in res1:
            print("error")
            timeout +=1
    return (verified, cex, timeout)

# def test_suite_csv(filename, properties, timeout):
#     return test_suite_general(filename, properties, timeout)

def printRes(v, c, t) :
    print("Verified :" + str(v))
    print("Counterexample :" + str(c))
    print("Timeout :" + str(t))

def main():
    global latex_tbl1
    global latex_tbl2
    (v1, c1, t1) = test_suite_general("Zeno.hs", unmodified_theorems(), 15)
    printRes(v1, c1, t1)
    latex_tbl2 += r"\multicolumn{2}{l}{\textbf{ZenoBadProp}}\\ \hline " + "\n"
    (v2, c2, t2) = test_suite_general("ZenoBadProp.hs", unmodified_theorems(), 15)
    printRes(v2, c2, t2)

    setpath = os.path.join("verify/tests")
    run_bench = read_runnable_benchmarks(setpath, [])
    for benchmark in run_bench :
        (filename, setting) = benchmark[0]
        tempStr = r"\multicolumn{2}{l}{\textbf{" + filename + r"}}\\ \hline " + "\n"
        latex_tbl2 += tempStr
        print("\nBenchmark : " + filename + "\n")
        (v, c, t) = test_suite_general(filename + ".hs", benchmark[1:], 15)
        print("\nTotal properties: " + str(len(benchmark) - 1))
        printRes(v, c, t)
        print("\n")
    print("Latex for table1 is: \n" + latex_tbl1)
    print("Latex for table2 is: \n" + latex_tbl2)

if __name__ == "__main__":
    main()