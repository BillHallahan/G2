import os
import re
import subprocess

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


def call_verify_quickcheck(time_limit):
    try:
        args = [exe_name]
        res = subprocess.run(args, universal_newlines=True, capture_output=True, timeout=time_limit+30);
        return res.stdout
    except subprocess.TimeoutExpired as TimeoutEx:
        # extra line break at end to match the one from normal termination
        return "Timeout - Script"

def main():
    time_limit = 60
    # Counter-example benchmarks
    run_limit = 10
    table3 = ""
    for i in range(run_limit):
        output = call_verify_quickcheck(time_limit)
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
            if len(t) < 10:
                table2 += key + "-" + prop_name + " & " + str(len(t)) + " & " + str(avg_t) + " & " +  str(avg_d) + r"\\ \hline" + "\n"
            print(prop_name + " & " + str(len(t)) + " & " + str(avg_t) + " & " +  str(avg_d) + r"\\ \hline")
    
    print("\nTable 2 where quickcheck fails to generate counterexample atleast once")
    print(table2)

    print("\n Table 3 shows the number of properties where Quickcheck found counterexample during each run ")
    print(table3)
        


if __name__ == "__main__":
    main()