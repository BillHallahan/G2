#!/usr/bin/env python
# Tests Verify on the Zeno suite

import os
import re
import subprocess
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
ver_props_both = 0 # total number of properties verified with no ablation
ver_props_approx = 0 # total number of properties verified with approx
ver_props_ra = 0 # total number of properties verified with rev abs
ce_both = 0 # total number of counterexamples found
ce_approx = 0
ce_ra = 0
total_ce_props = 85 # of properties checked for counterexamples
total_ver_time_both = 0.0
total_ver_time_approx = 0.0
total_ver_time_ra = 0.0

total_ce_time_both = 0.0
total_ce_time_approx = 0.0
total_ce_time_ra = 0.0

def generate_graph_coordinatinates(filename, timeBoth, timeApprox, timeRA) :
    coordinates1 = (timeBoth, timeApprox)
    coordinates2 = (timeBoth, timeRA)

    global latex_coordinates_1, latex_coordinates_2, latex_coordinates_3, latex_coordinates_4
    global latex_coordinates_5, latex_coordinates_6, latex_coordinates_7, latex_coordinates_8, latex_coordinates_9

    # combining results from all three counterexamples
    latex_coordinates_8 += str(coordinates1) + "\n" if not filename == "Zeno.hs" else ""
    latex_coordinates_9 += str(coordinates2) + "\n" if not filename == "Zeno.hs" else ""

    if filename == "Zeno.hs" :
        latex_coordinates_1 += str(coordinates1) + "\n"
    # Counterexamples graph co-ordinates
    elif filename == "ZenoBadProp.hs":
        latex_coordinates_2 += str(coordinates1) + "\n"
        latex_coordinates_3 += str(coordinates2) + "\n"
    elif filename == "Definitions.hs" or filename == "Nat.hs" :
        latex_coordinates_4 += str(coordinates1) + "\n"
        latex_coordinates_5 += str(coordinates2) + "\n"
    else:
        latex_coordinates_6 += str(coordinates1) + "\n"
        latex_coordinates_7 += str(coordinates2) + "\n"

def generate_table(filename, property, approxTime, raTime, raAppTime, timeout) :
    global latex_tbl1, latex_tbl2
    global total_ver_time_approx, total_ver_time_ra, total_ver_time_both
    global total_ce_time_both, total_ce_time_approx, total_ce_time_ra
    common_str = " & "
    aTime = str(approxTime) if approxTime < timeout else "-"
    nTime = str(raTime) if raTime < timeout else "-"
    nATime = str(raAppTime) if raAppTime < timeout else "-"
    prop = re.sub(r"_", r"\\_", property)
    temp = prop + common_str + nATime + common_str + aTime + common_str + nTime

    if filename == "Zeno.hs" :
        latex_tbl1 += temp + r"\\ \hline " + "\n"
        # doing this to caluclate average, only needed for Zeno
        total_ver_time_approx += approxTime if approxTime < timeout  else 0.0
        total_ver_time_ra += raTime if raTime < timeout  else 0.0
        total_ver_time_both += raAppTime if raAppTime < timeout  else 0.0
    else:
        latex_tbl2 += temp + r"\\ \hline " + "\n"
        total_ce_time_both += raAppTime if raAppTime < timeout  else 0.0
        total_ce_time_approx += approxTime if approxTime < timeout  else 0.0
        total_ce_time_ra += raTime if raTime < timeout  else 0.0

def generateMetricLatex(avgVerBoth, avgVerApprox, avgVerRa, avgCeBoth, avgCeApprox, avgCeRa):
    ltx = r"\multirow{5}{*}{Verified} & Avg. Time (Both) & " +  str(avgVerBoth) + r" \\ \cline{2-3} " + "\n" \
    + r"& Avg. Time (Approximation) & " + str(avgVerApprox) + r"\\ \cline{2-3}" + "\n" \
    + r"& Avg. Time (Rev. Abs.) & " + str(avgVerRa) + r" \\ \cline{2-3}" + "\n" \
    + r"& Num of prop (Both) & " + str(ver_props_both) + r" \\ \cline{2-3}" + "\n" \
    + r"& Num of props (Approximation) & " + str(ver_props_approx) + r"\\ \cline{2-3}" + "\n" \
    + r"& Num of prop (Rev. Abs.) & " + str(ver_props_ra) + r"\\ \hline" + "\n" \
    + r"\multirow{6}{*}{Counterexamples} & Avg. Time (Both) & " + str(avgCeBoth) + r" \\ \cline{2-3} " + "\n" \
    + r"& Avg. Time (Approximation) & " + str(avgCeApprox) + r" \\ \cline{2-3}" + "\n" \
    + r"& Avg. Time (Rev. Abs.) & "  + str(avgCeRa) + r"\\ \cline{2-3}" + "\n" \
    + r"& Num of CE generated (Both) & " + str(ce_both) + r" \\ \cline{2-3}" + "\n" \
    + r"& Num of CE generated (Approximation) & " + str(ce_approx) + r" \\ \cline{2-3}" + "\n" \
    + r"& Num of CE generated (Rev. Abs.) & " + str(ce_ra) + r"\\ \cline{2-3}" + "\n" \
    + r"& Total Num of Properties & " + str(total_ce_props) + r"\\ \hline"

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

def test_suite_general(fname_in, suite, time_limit, var_settings):
    verified = 0
    cex = 0
    timeout = 0
    result = {}
    for (thm, settings) in suite:
        print(thm)
        res = run_verify(fname_in, thm, time_limit, var_settings)
        runTime = round(float(process_output(res)), 2)
        result[thm] = runTime

        if "Verified" in res:
            print("Verified")
            verified += 1
        if "Counterexample" in res:
            print("Counterexample")
            cex += 1
        if "Timeout" in res:
            print("Timeout")
            timeout +=1
        if "error" in res:
            print("error")
            timeout +=1

    print("\n")
    return (verified, cex, timeout, result)

# def test_suite_csv(filename, properties, timeout):
#     return test_suite_general(filename, properties, timeout)

def printRes(v, c, t) :
    print("Verified :" + str(v))
    print("Counterexample :" + str(c))
    print("Timeout :" + str(t))
    print("\n")

def runAll(filename, suite, time_limit) :
    global ce_both, ce_approx, ce_ra, ver_props_both, ver_props_approx, ver_props_ra
    # Both on
    print("Running " + filename + " with both approaches\n")
    (vBoth, cBoth, tBoth, res1) = test_suite_general(filename, suite, time_limit, [])
    printRes(vBoth, cBoth, tBoth)

    # Just approximation on
    print("Running " + filename + " with just approximations\n")
    (vApp, cApp, tApp, res2) = test_suite_general(filename, suite, time_limit, ["--no-rev-abs"])
    printRes(vApp, cApp, tApp)

    # Just rev abs on
    print("Running " + filename + " with just rev abs\n")
    (vRa, cRa, tRa, res3) = test_suite_general(filename, suite, time_limit, ["--no-approx"])
    printRes(vRa, cRa, tRa)

    ce_both += cBoth
    ce_approx += cApp
    ce_ra += cRa

    ver_props_both += vBoth
    ver_props_approx += vApp
    ver_props_ra += vRa

    for thm, runTime in res1.items() :
        runTime2 = res2[thm] # runTime just with approx
        runTime3 = res3[thm] # runTime just with ra
        generate_table(filename, thm, runTime2, runTime3, runTime, time_limit)
        generate_graph_coordinatinates(filename, runTime, runTime2, runTime3)

def main():
    global latex_tbl1
    global latex_tbl2
    global latex_coordinates_1, latex_coordinates_2, latex_coordinates_3, latex_coordinates_4
    global latex_coordinates_5, latex_coordinates_6, latex_coordinates_7, latex_coordinates_8, latex_coordinates_9
    global total_ce_props, total_ver_time_both, total_ver_time_approx, total_ver_time_ra
    global ver_props_both, ver_props_approx, ver_props_ra
    global total_ce_time_both, total_ce_time_approx, total_ce_time_ra
    global ce_both, ce_approx, ce_ra

    runAll("Zeno.hs", unmodified_theorems(), 15)

    # Counter-example benchmarks
    latex_tbl2 += r"\multicolumn{2}{l}{\textbf{ZenoBadProp}}\\ \hline " + "\n"
    runAll("ZenoBadProp.hs", unmodified_theorems(), 15)

    avg_time_both = total_ver_time_both / ver_props_both if not ver_props_both == 0 else 0
    avg_time_approx = total_ver_time_approx / ver_props_approx if not ver_props_approx == 0 else 0
    avg_time_ra = total_ver_time_ra / ver_props_ra if not ver_props_ra == 0 else 0

    setpath = os.path.join("verify/tests")
    run_bench = read_runnable_benchmarks(setpath, [])
    for benchmark in run_bench :
        (filename, setting) = benchmark[0]
        tempStr = r"\multicolumn{2}{l}{\textbf{" + filename + r"}}\\ \hline " + "\n"
        latex_tbl2 += tempStr
        print("\nBenchmark : " + filename + "\n")
        runAll(filename + ".hs", benchmark[1:], 15)

        curr_num_props = len(benchmark) - 1
        total_ce_props += curr_num_props

        print("\nTotal properties: " + str(len(benchmark) - 1))
        print("\n")

    avg_time_ce_both = total_ce_time_both / ce_both if not ce_both == 0 else 0
    avg_time_ce_approx = total_ce_time_approx / ce_approx if not ce_approx == 0 else 0
    avg_time_ce_ra = total_ce_time_ra / ce_ra if not ce_ra == 0 else 0

    metricLtx = generateMetricLatex(round(avg_time_both, 2), round(avg_time_approx, 2), round(avg_time_ra, 2), 
                                    round(avg_time_ce_both, 2), round(avg_time_ce_approx, 2), round(avg_time_ce_ra, 2))

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

if __name__ == "__main__":
    main()