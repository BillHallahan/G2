import os
import re
import subprocess
from collections import Counter

data = {}

exe_name = str(subprocess.run(["cabal", "exec", "which", "Verify-Quickcheck"], capture_output = True).stdout.decode('utf-8')).strip()

def read_output(out):
    failed = 0
    total = 0
    time = 0.0

    pattern = r"Benchmark:\s*(\S+)\s+Property:\s*(\S+)\s+Failed after\s+(\d+)\s+tests?,\s*Discarded:\s*(\d+)"
    results = re.findall(pattern, out)

    match = re.search(r"(\d+) out of (\d+) tests failed \(([\d.]+)s\)", out)
    if match:
        failed = int(match.group(1))
        total = int(match.group(2))
        time = float(match.group(3))
    return (results, failed, total, time)

def read_sc_output(out):
    pattern = r'Benchmark:\s*"([^"]+)"\s+Property:\s*"([^"]+)"\s+Status:\s*"([^"]+)"\s+Time:\s*([\d.eE+-]+)'
    results = re.findall(pattern, out)
    passed = []
    timeout = []
    failed = 0

    for result in results:
        bench, prop, status, time = result
        if status == "PASS":
            passed.append(result)
        elif status == "TIMEOUT":
            timeout.append(result)
        else:
            failed += 1

    print("Properties that Passed:")
    for bench, prop, st, ti in passed:
        prop_name = prop.replace("_", "\\_")
        print(bench + " - " + prop_name + " & " + st)

    print("\nProperties that timed out")
    for bench, prop, st, ti in timeout:
        prop_name = prop.replace("_", "\\_")
        print(bench + " - " + prop_name + " & " + st)


def call_pbtt(time_limit, toolName, var_settings):
    try:
        args = [exe_name, toolName]
        res = subprocess.run(args + var_settings, universal_newlines=True, capture_output=True, timeout=time_limit+30);
        return res.stdout
    except subprocess.TimeoutExpired as TimeoutEx:
        # extra line break at end to match the one from normal termination
        return "Timeout - Script"
    
def call_smallcheck(time_limit, depth):
    out1 = call_pbtt(time_limit, "sc", ["--smallcheck-depth", str(depth)])
    print("Running small check for depth " + str(depth))
    read_sc_output(out1)

def call_quickcheck(time_limit):
    # Counter-example benchmarks
    run_limit = 10
    table3 = ""
    for i in range(run_limit):
        output = call_pbtt(time_limit, "qc", [])
        (res, failed_p, tot_p, time_taken) = read_output(output)
        table3 += str(failed_p) + " & " + str(time_taken) + r"\\ \hline" + "\n"
        for (bench, prop, tf, dis) in res:
            if bench in data:
                ps = data[bench]
                if prop in ps:
                    (t, d) = ps[prop]
                    t.append(int(tf))
                    d.append(int(dis))
                else:
                    ps[prop] = ([int(tf)], [int(dis)])
            else:
                tc_list = [int(tf)]
                dis_list = [int(dis)]
                temp = {}
                temp[prop] = (tc_list, dis_list)
                data[bench] = temp
    table2 = ""
    for key, val in data.items():
        header = r"\multicolumn{4}{l}{\textbf{"+ key + r"}}\\ \hline"
        print(header)
        for k, (t, d) in val.items():
            avg_t = round(sum(t) / len(t), 1)
            avg_d = round(sum(d) / len(d), 1)
            prop_name = k.replace("_", "\\_")
            if len(t) < run_limit:
                table2 += key + "-" + prop_name + " & " + str(len(t)) + " & " + str(avg_t) + " & " +  str(avg_d) + "& " + r"\\ \hline" + "\n"
            print(prop_name + " & " + str(len(t)) + " & " + str(avg_t) + " & " +  str(avg_d) + r"\\ \hline")
    
    print("\nTable 2 where quickcheck fails to generate counterexample atleast once")
    print(table2)

    print("\n Table 3 shows the number of properties where Quickcheck found counterexample during each run ")
    print(table3)


def main():
    time_limit = 60
    call_quickcheck(time_limit)
    depths = [3,4,5]
    for depth in depths:
        call_smallcheck(time_limit, depth)


if __name__ == "__main__":
    main()