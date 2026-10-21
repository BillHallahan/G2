import os
import re
import subprocess
from collections import Counter

data = {}
sc_data = {}

exe_name = str(subprocess.run(["cabal", "exec", "which", "Verify-Quickcheck"], capture_output = True).stdout.decode('utf-8')).strip()

def read_output(out):
    failed = 0
    total = 0
    time = 0.0

    pattern1 = r"Benchmark:\s*(\S+)\s+Property:\s*(\S+)\s+Passed:\s*(\d+),\s*Discarded:\s*(\d+)"

    pattern2 = r"Benchmark:\s*(\S+)\s+Property:\s*(\S+)\s+Failed after\s+(\d+)\s+tests?,\s*Discarded:\s*(\d+)"

    resPass = re.findall(pattern1, out)
    resFail = re.findall(pattern2, out)

    match = re.search(r"(\d+) out of (\d+) tests failed \(([\d.]+)s\)", out)
    if match:
        failed = int(match.group(1))
        total = int(match.group(2))
        time = float(match.group(3))
    return (resFail, resPass, failed, total, time)

def print_sc():
    row1 = r"\# of Passed & "
    row2 = r"\# of Timeouts & "
    row3 = r"\# of CEx & "
    row4 = r"Avg. Time (s) & "
    
    header = " & "
    for key, val in sc_data.items():
        header += key + " & "
        row1 += str(val[0]) + " & "
        row2 += str(val[1]) + " & "
        row3 += str(val[2]) + " & "
        row4 += str(val[3]) + " & "

    print(header)
    print(row1)
    print(row2)
    print(row3)
    print(row4)

def read_sc_output(out, depth):
    pattern = r'Benchmark:\s*"([^"]+)"\s+Property:\s*"([^"]+)"\s+Status:\s*"([^"]+)"\s+Time:\s*([\d.eE+-]+)'
    results = re.findall(pattern, out)
    passed = []
    timeout = []
    failed = []
    total_time = 0

    for result in results:
        bench, prop, status, time = result
        if status == "PASS":
            passed.append(result)
        elif status == "TIMEOUT":
            timeout.append(result)
        else:
            failed.append(result)
            total_time += float(time)

    avg_time = round(total_time/len(failed), 4)
    key = "Depth " + str(depth)
    sc_data[key] = [len(passed), len(timeout), len(failed), avg_time]

    print("\nProperties that succeeded:")
    print(passed)

    print("\nProperties that timed out:")
    print(timeout)

    return (passed + timeout)


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
    print("\nRunning small check for depth " + str(depth))
    res = read_sc_output(out1, depth)
    return res

def call_quickcheck(time_limit):
    # Counter-example benchmarks
    run_limit = 100
    table3 = ""
    total_time = 0
    fail_count = 0
    pass_count = 0
    num_prop = 0
    for i in range(run_limit):
        output = call_pbtt(time_limit, "qc", [])
        (resFail, resPass, failed_p, tot_p, time_taken) = read_output(output)
        total_time += time_taken
        fail_count += len(resFail)
        pass_count += len(resPass)
        num_prop = tot_p
        table3 += str(failed_p) + " & " + str(time_taken) + r"\\ \hline" + "\n"
        for (bench, prop, tf, dis) in resFail:
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
    
    avg_fail = fail_count/(run_limit)
    avg_pass = pass_count/(run_limit)
    avg_time = round(total_time/run_limit, 2)

    sc_data["QuickCheck"] = [avg_pass, 0, avg_fail, avg_time]
    
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

    print("Average pass: " + str(avg_pass))
    print("Average fail: " + str(avg_fail))
    print("Average time: " + str(avg_time))


def main():
    time_limit = 1800
    # Run QuickCheck
    call_quickcheck(time_limit)

    # Run Smallcheck
    out1 = call_smallcheck(time_limit, 3)
    out2 = call_smallcheck(time_limit, 4)
    out3 = call_smallcheck(time_limit, 5)

    print_sc()


if __name__ == "__main__":
    main()