#!/usr/bin/env python
# Tests Nebula on the Zeno suite

import os
import re
import subprocess
import time

exe_name = str(subprocess.run(["cabal", "exec", "which", "Nebula"], capture_output = True).stdout.decode('utf-8')).strip()

def run_zeno(filename, thm, var_settings, timeout):
    start_time = time.monotonic();
    res = call_zeno_process(filename, thm, var_settings, timeout);
    end_time = time.monotonic();
    elapsed = end_time - start_time;

    # there's always an extra empty string at the end for now
    lines = res.split("\n")
    depth1 = 0
    depth2 = 0
    cx_text = []
    # the numbers 4 and 5 are dependent on the initial printing
    # if that printing changes, these need to change too
    left_str = lines[4]
    right_str = lines[5]
    check_unsat = lines[-2]
    depth1 = check_depth("Max", lines)
    depth2 = check_depth("Sum", lines)
    cx_idx = check_cx(lines)
    if cx_idx < 0:
        cx_text = lines[cx_idx:]
    print(check_unsat);
    return {
        "left":left_str,
        "right":right_str,
        "result":check_unsat,
        "time":elapsed,
        "min_max_depth":depth1,
        "min_sum_depth":depth2,
        "cx":cx_text
    }

def call_zeno_process(filename, thm, var_settings, time_limit):
    try:
        args = [exe_name, "tests/RewriteVerify/Correct/" + filename, thm]
        res = subprocess.run(args + var_settings, universal_newlines=True, capture_output=True, timeout=time_limit);
        return res.stdout
    except subprocess.TimeoutExpired as TimeoutEx:
        # extra line break at end to match the one from normal termination
        return TimeoutEx.stdout.decode('utf-8') + "\nTimeout\n"

# ver should be either "Max" or "Sum"
def check_depth(ver, lines):
    depths = [0]
    for utf in lines:
        line = utf
        if line[:17] == ("<<Min " + ver + " Depth>>"):
            depth_str = line[18:]
            depths.append(int(depth_str))
    return max(depths)

def check_cx(lines):
    for i in range(1, 1 + len(lines)):
        line = lines[-i]
        if "COUNTEREXAMPLE FOUND" in line:
            return -i
    return 0

n = "n"
x = "x"
xs = "xs"
m = "m"
y = "y"
ys = "ys"
zs = "zs"
i = "i"
j = "j"
a = "a"
b = "b"
c = "c"
p = "p"
f = "f"
k = "k"

def unmodified_theorems():
    ret = []
    for i in range(1, 86):
        if i < 10:
            ret.append(("p0" + str(i), []))
        else:
            ret.append(("p" + str(i), []))
    return ret

modified_total = [
    ("p01", [n]),
    ("p19", [n]),
    ("p23", [a]),
    ("p23", [b]),
    ("p32", [a, b]),
    ("p34", [a]),
    ("p43", [p, xs]),
    ("p47", [a]),
    ("p49", [xs, ys]),
    ("p51", [xs]),
    ("p56", [n, m]),
    #("p58", [n, xs, ys]),
    ("p72", [i]),
    ("p73", [p, xs]),
    ("p74", [i, xs]),
    ("p79", [n]),
    ("p83", [ys]),
    ("p84", [ys])
]

modified_finite = [
    ("p03fin", [n]),
    ("p03finB", [xs]),
    ("p04fin", []),
    ("p05finE", [x, xs]),
    ("p05finF", [n, xs]),
    ("p06fin", []),
    ("p07fin", []),
    ("p08fin", []),
    ("p10fin", []),
    ("p15finA", [x]),
    ("p15finB", [xs]),
    ("p16finA", [xs]),
    ("p18fin", []),
    ("p20finA", []),
    ("p21fin", []),
    ("p24fin", [b]),
    ("p25fin", [a]),
    ("p26finA", [x]),
    ("p26finB", [xs]),
    ("p27finA", [xs, ys]),
    ("p28finA", [xs]),
    ("p29finA", [xs]),
    ("p30finA", [xs]),
    ("p37finB", [x]),
    ("p37finC", [xs]),
    ("p38finB", [xs]),
    ("p48finB", []),
    ("p52finA", []),
    ("p53finA", []),
    ("p54fin", [m]),
    ("p57finA", [m, xs]),
    ("p57finB", [n, xs]),
    ("p58finA", [n, xs, ys]),
    ("p58finB", [n, xs, ys]),
    ("p59finA", [ys]),
    ("p60finB", []),
    ("p61fin", []),
    ("p62finA", []),
    ("p63finA", [n]),
    ("p64fin", []),
    ("p65finA", [m]),
    ("p66fin", [p, xs]),
    ("p68finA", [xs]),
    ("p68finB", [n]),
    ("p69finA", [m]),
    ("p70finC", [n]),
    ("p70finD", [m]),
    ("p71finA", [y, xs]),
    ("p71finB", [x, xs]),
    ("p75fin", [m, xs]),
    ("p76finB", [m, xs]),
    ("p76finC", [n, xs]),
    ("p77finA", [x]),
    ("p78finB", []),
    ("p81fin", [n, m, xs]),
    ("p81finA", [n, m, xs]),
    ("p85finB", [ys]),
    ("p85finC", [xs])
]

modified_cycle = [
    ("p03", [n, xs, ys]),
    ("p04", [n, xs]),
    ("p05", [n, x, xs]),
    ("p06", [n, m]),
    ("p07", [n, m]),
    ("p08", [k, m, n]),
    ("p10", [m]),
    ("p15", [x, xs]),
    ("p16", [x, xs]),
    ("p18", [i, m]),
    ("p20", [xs]),
    ("p21", [n, m]),
    ("p24", [a, b]),
    ("p25", [a, b]),
    ("p26", [x, xs, ys]),
    ("p27", [x, xs, ys]),
    ("p28", [x, xs]),
    ("p29", [x, xs]),
    ("p30", [x, xs]),
    ("p37", [x, xs]),
    ("p38", [n, xs]),
    ("p48", [xs]),
    ("p52", [n, xs]),
    ("p53", [n, xs]),
    ("p54", [n, m]),
    ("p57", [n, m, xs]),
    ("p58", [n, xs, ys]),
    ("p59", [xs, ys]),
    ("p60", [xs, ys]),
    ("p61", [xs, ys]),
    ("p62", [xs, x]),
    ("p63", [n, xs]),
    ("p64", [x, xs]),
    ("p65", [i, m]),
    ("p66", [p, xs]),
    ("p68", [n, xs]),
    ("p69", [n, m]),
    ("p70", [m, n]),
    ("p71", [x, y, xs]),
    ("p75", [n, m, xs]),
    ("p76", [n, m, xs]),
    ("p77", [x, xs]),
    ("p78", [xs]),
    ("p81", [n, m, xs]),
    ("p85", [xs, ys])
]

# subtraction of 1 happens in here
def print_depth(depth):
    if depth > 0:
        print("\tAll concretizations checked up to depth " + str(depth - 1))
    else:
        print("\tConcretizations of depth 0 still remaining")

def test_suite_general(suite, fname_in, fname_out, timeout = 25):
    unsat_num = 0
    sat_num = 0
    # index to ensure uniqueness
    k = 0
    min_max_depth_dict = {}
    min_sum_depth_dict = {}
    if fname_out is not None:
        file = open(fname_out + ".csv", "w")
        file.write("Name,LHS,RHS,Total,Outcome,Time,Min Max Depth,Min Sum Depth\n")
    for (thm, settings) in suite:
        print(thm, settings)
        d = run_zeno(fname_in, thm, settings, timeout)
        check_unsat = d["result"]
        elapsed = d["time"]
        min_max_depth = d["min_max_depth"]
        min_sum_depth = d["min_sum_depth"]
        min_max_depth_dict[thm] = min_max_depth
        min_sum_depth_dict[thm] = min_sum_depth
        if fname_out is not None:
            # replace commas with semicolons to work with CSV format
            l_str = d["left"].replace(",", ";")
            r_str = d["right"].replace(",", ";")
            file.write(thm + "," + l_str + "," + r_str + ",")
            file.write(total_string(settings) + ",")
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
            if fname_out is not None:
                file.write("Verified," + str(elapsed) + "s,")
        elif check_unsat == "SAT ()":
            print("\tFailed - " + str(elapsed) + "s")
            sat_num += 1
            if fname_out is not None:
                file.write("Failed," + str(elapsed) + "s,")
        elif check_unsat[:7] == "Unknown":
            print("\tIncomplete - " + str(elapsed) + "s")
            if fname_out is not None:
                file.write("Incomplete," + str(elapsed) + "s,")
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
            if fname_out is not None:
                file.write("Timeout," + str(elapsed) + "s,")
        else:
            print("\tError - " + str(elapsed) + "s")
            if fname_out is not None:
                file.write("Error," + str(elapsed) + "s,")
        print("\tMin Max Depth:")
        print_depth(min_max_depth)
        print("\tMin Sum Depth:")
        print_depth(min_sum_depth)
        if fname_out is not None:
            file.write(str(min_max_depth) + "," + str(min_sum_depth) + "\n")
        cx = d["cx"]
        if len(cx) > 0 and fname_out is not None:
            cx_file = open(fname_out + "-" + thm + "-" + str(k) + ".txt", "w")
            cx_file.write(thm + " ")
            cx_file.write(str(settings))
            cx_file.write("\n")
            for ln in cx:
                cx_file.write(ln)
                cx_file.write("\n")
            cx_file.close()
        k += 1
    print(unsat_num, "Confirmed out of", len(suite))
    print(sat_num, "Rejected out of", len(suite))
    if fname_out is not None:
        file.close()

def total_string(settings):
    if len(settings) == 0:
        return ""
    t_str = settings[0]
    for t in settings[1:]:
        t_str += " " + t
    return t_str

def test_suite_csv(fname, suite, timeout = 25):
    return test_suite_general(suite, "TestZeno.hs", fname, timeout)

def main():
    t = 60
    test_suite_csv("ZenoUnaltered", unmodified_theorems(), t)
    test_suite_csv("ZenoTotal", modified_total, t)
    test_suite_csv("ZenoFinite", modified_finite, t)
    test_suite_csv("ZenoCycle", modified_cycle, t)

if __name__ == "__main__":
    main()
