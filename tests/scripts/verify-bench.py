#!/usr/bin/env python
# Tests Verify on the Zeno suite

from multiprocessing import Pool
import os
import re
import subprocess
import sys
import time

exe_name = str(subprocess.run(["cabal", "exec", "which", "Verify"], capture_output = True).stdout.decode('utf-8')).strip()
latex_tbl1 = "" # Zeno result table
latex_tbl2 = "" # Counterexample tables
latex_coordinates_1 = "" # for graph1: Zeno with both vs approx
latex_coordinates_2 = "" # for graph2: ZenoBadProp with both vs approx
latex_coordinates_3 = "" # for graph3: ZenoBadProp with both vs ra
latex_coordinates_4 = "" # for graph4: TIP with both vs approx
latex_coordinates_5 = "" # for graph5: TIP with both vs ra
latex_coordinates_6 = "" # for graph6: Zeno buggy with both vs approx
latex_coordinates_7 = "" # for graph7: Zeno buggy with both vs ra
latex_coordinates_8 = "" # for graph8: Combine three benchmarks with both vs approx
latex_coordinates_9 = "" # for graph9: Combine three benchmarks with both vs ra
latex_coordinates_10 = "" # for graph10: ZenoBadProp with both vs none
latex_coordinates_11 = "" # for graph11: TIP with both vs none
latex_coordinates_12 = "" # for graph12: Zeno buggy with both vs none
latex_coordinates_13 = "" # for graph13: Combine three benchmarks with both vs none

total_ce_props = 85 # of properties checked for counterexamples

def settings():
    return [ ("All", []),
             ("No approx", ["--no-approx"]),
             ("No shared variables", ["--no-shared-var-heuristic"]),
             ("No argument RAs", ["--no-arg-rev-abs"]),
             ("No RAs", ["--no-rev-abs"]),
             ("No RAs or approx", ["--no-approx", "--no-rev-abs"])
           ]

ver_res = { n : 0 for (n, _) in settings() }
cex_res = { n : 0 for (n, _) in settings() }

ver_time = { n : 0 for (n, _) in settings() }
cex_time = { n : 0 for (n, _) in settings() }

def generate_graph_coordinatinates(filename, timeBoth, timeApprox, timeRA, timeNone) :
    coordinates1 = (timeBoth, timeApprox)
    coordinates2 = (timeBoth, timeRA)
    coordinates3 = (timeBoth, timeNone)

    global latex_coordinates_1, latex_coordinates_2, latex_coordinates_3, latex_coordinates_4
    global latex_coordinates_5, latex_coordinates_6, latex_coordinates_7, latex_coordinates_8, latex_coordinates_9
    global latex_coordinates_10, latex_coordinates_11, latex_coordinates_12, latex_coordinates_13

    # combining results from all three counterexamples
    latex_coordinates_8 += str(coordinates1) + "\n" if not filename == "Zeno.hs" else ""
    latex_coordinates_9 += str(coordinates2) + "\n" if not filename == "Zeno.hs" else ""
    latex_coordinates_13 += str(coordinates3) + "\n" if not filename == "Zeno.hs" else ""

    if filename == "Zeno.hs" :
        latex_coordinates_1 += str(coordinates1) + "\n"
    # Counterexamples graph co-ordinates
    elif filename == "ZenoBadProp.hs":
        latex_coordinates_2 += str(coordinates1) + "\n"
        latex_coordinates_3 += str(coordinates2) + "\n"
        latex_coordinates_10 += str(coordinates3) + "\n"
    elif filename == "Definitions.hs" or filename == "Nat.hs" :
        latex_coordinates_4 += str(coordinates1) + "\n"
        latex_coordinates_5 += str(coordinates2) + "\n"
        latex_coordinates_11 += str(coordinates3) + "\n"
    else:
        latex_coordinates_6 += str(coordinates1) + "\n"
        latex_coordinates_7 += str(coordinates2) + "\n"
        latex_coordinates_12 += str(coordinates3) + "\n"

def generate_table(filename, property, approxTime, raTime, raAppTime, noneTime, timeout) :
    global latex_tbl1, latex_tbl2
    common_str = " & "
    aTime = str(approxTime) if approxTime < timeout else "-"
    nTime = str(raTime) if raTime < timeout else "-"
    nATime = str(raAppTime) if raAppTime < timeout else "-"
    noneOpti = str(noneTime) if noneTime < timeout else "-"
    prop = re.sub(r"_", r"\\_", property)
    temp = prop + common_str + nATime + common_str + aTime + common_str + nTime

    if filename == "Zeno.hs" :
        latex_tbl1 += temp + r"\\ \hline " + "\n"
    else:
        latex_tbl2 += temp + common_str + noneOpti + r"\\ \hline " + "\n"

def generateMetricLatex():
    ltx = r"\multirow{5}{*}{Verified}"
    for (n, _) in settings():
        c = ver_res[n]
        t = ver_time[n]
        ltx += r"& Avg. Time (" + n + ") & " +  str(round(t / c, 2)) + r" \\ \cline{2-3} " + "\n"
    
    for (n, _) in settings():
        c = ver_res[n]
        ltx += r"& Num of prop (" + n + ") & " +  str(c) + r" \\ \cline{2-3} " + "\n"

    ltx += r"\multirow{6}{*}{Counterexamples}"
    for (n, _) in settings():
        c = cex_res[n]
        t = cex_time[n]
        ltx += r"& Avg. Time (" + n + ") & " +  str(round(t / c, 2)) + r" \\ \cline{2-3} " + "\n"

    for (n, _) in settings():
        c = cex_res[n]
        ltx += r"& Num of CE generated (" + n + ") & " +  str(c) + r" \\ \cline{2-3} " + "\n"

    ltx += "& Total Num of Properties & " + str(total_ce_props) + "\\ \hline"

    return ltx

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
        res = subprocess.run(args + var_settings, universal_newlines=True, capture_output=True, timeout=time_limit+30);
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

def run_theorem(arg):
    fname_in, time_limit, var_settings, thm = arg
    res = run_verify(fname_in, thm, time_limit, var_settings)
    return (thm, res)

def test_suite_general(fname_in, suite, time_limit, var_settings):
    verified = 0
    cex = 0
    timeout = 0
    result = {}

    total_ver_time = 0
    total_cex_time = 0

    with Pool(processes=8) as pool:
        arg_suite = [(fname_in, time_limit, var_settings, s) for (s, _) in suite]
        for (thm, res) in pool.imap(run_theorem, arg_suite):
            print(thm)
            runTime = round(float(process_output(res)), 2) if not "Timeout" in res else time_limit
            result[thm] = runTime
            if "Verified" in res:
                print("Verified - " + str(runTime))
                verified += 1
                total_ver_time += float(process_output(res))
            if "Counterexample" in res:
                print("Counterexample - " + str(runTime))
                cex += 1
                total_cex_time += float(process_output(res))
            if "Timeout" in res:
                print("Timeout")
                timeout +=1
            if "error" in res:
                print("error")
                timeout +=1

    print("\n")
    return (verified, cex, timeout, total_ver_time, total_cex_time, result)

# def test_suite_csv(filename, properties, timeout):
#     return test_suite_general(filename, properties, timeout)

def printRes(v, c, t) :
    print("Verified :" + str(v))
    print("Counterexample :" + str(c))
    print("Timeout :" + str(t))
    print("\n")

def runAll(filename, suite, time_limit, var_settings = []) :
    global ver_res, cex_res
    runtimes = {}
    for (name, flags) in settings():
        print("Running " + filename + " with " + str(flags + var_settings) + "\n")
        (ver, cex, timeouts, v_time, c_time, runtime) = test_suite_general(filename, suite, time_limit, flags + var_settings)
        printRes(ver, cex, timeouts)

        ver_res[name] += ver
        cex_res[name] += cex
        ver_time[name] += v_time
        cex_time[name] += c_time
        runtimes[name] = runtime

    res1 = runtimes["All"]
    res2 = runtimes["No RAs"]
    res3 = runtimes["No approx"]
    res4 = runtimes["No RAs or approx"]    
    for thm, runTime in res1.items() :
        runTime2 = res2[thm] # runTime just with approx
        runTime3 = res3[thm] # runTime just with ra
        runTime4 = res4[thm] if thm in res4 else  0.0 # runTime with no optimization
        generate_table(filename, thm, runTime2, runTime3, runTime, runTime4, time_limit)
        generate_graph_coordinatinates(filename, runTime, runTime2, runTime3, runTime4)

def main():
    time_limit = 60
    global latex_tbl1
    global latex_tbl2
    global latex_coordinates_1, latex_coordinates_2, latex_coordinates_3, latex_coordinates_4
    global latex_coordinates_5, latex_coordinates_6, latex_coordinates_7, latex_coordinates_8, latex_coordinates_9
    global total_ce_props

    global ver_res, cex_res

    args = sys.argv[1:]

    runAll("Zeno.hs", unmodified_theorems(), time_limit, args)

    # Counter-example benchmarks
    latex_tbl2 += r"\multicolumn{2}{l}{\textbf{ZenoBadProp}}\\ \hline " + "\n"
    runAll("ZenoBadProp.hs", unmodified_theorems(), time_limit, args)

    setpath = os.path.join("verify/tests")
    run_bench = read_runnable_benchmarks(setpath, [])
    for benchmark in run_bench :
        (filename, setting) = benchmark[0]
        tempStr = r"\multicolumn{2}{l}{\textbf{" + filename + r"}}\\ \hline " + "\n"
        latex_tbl2 += tempStr
        print("\nBenchmark : " + filename + "\n")
        runAll(filename + ".hs", benchmark[1:], time_limit, args)

        curr_num_props = len(benchmark) - 1
        total_ce_props += curr_num_props

        print("\nTotal properties: " + str(len(benchmark) - 1))
        print("\n")

    metricLtx = generateMetricLatex()

    print("Latex for table1 is: \n" + latex_tbl1)
    print("Latex for table2 is: \n" + latex_tbl2)
    print("Metric Latex: \n" + metricLtx)
    print("Co-ordinates for graph 1: \n" + latex_coordinates_1)
    print("Co-ordinates for graph 2: \n" + latex_coordinates_2)
    print("Co-ordinates for graph 3: \n" + latex_coordinates_3)
    print("Co-ordinates for graph 4: \n" + latex_coordinates_4)
    print("Co-ordinates for graph 5: \n" + latex_coordinates_5)
    print("Co-ordinates for graph 6: \n" + latex_coordinates_6)
    print("Co-ordinates for graph 7: \n" + latex_coordinates_7)
    print("Co-ordinates for graph 8: \n" + latex_coordinates_8)
    print("Co-ordinates for graph 9: \n" + latex_coordinates_9)
    print("Co-ordinates for graph 10: \n" + latex_coordinates_10)
    print("Co-ordinates for graph 11: \n" + latex_coordinates_11)
    print("Co-ordinates for graph 12: \n" + latex_coordinates_12)
    print("Co-ordinates for graph 13: \n" + latex_coordinates_13)

if __name__ == "__main__":
    main()