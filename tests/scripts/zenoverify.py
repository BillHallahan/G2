#!/usr/bin/env python
# Tests RewriteV on the Zeno suite

import os
import re
import subprocess
import time

def run_zeno(filename, thm, var_settings, timeout):
    start_time = time.monotonic();
    res = call_zeno_process(filename, thm, var_settings, timeout);
    end_time = time.monotonic();
    elapsed = end_time - start_time;

    lines = res.splitlines()
    depth1 = 0
    depth2 = 0
    try:
        # the numbers 4 and 5 are dependent on the initial printing
        # if that printing changes, these need to change too
        left_str = lines[4].decode('utf-8');
        right_str = lines[5].decode('utf-8');
        check_unsat = lines[-1].decode('utf-8');
        depth1 = check_depth("Max", lines)
        depth2 = check_depth("Sum", lines)
        print(check_unsat);
    except IndexError:
        left_str = lines[4].decode('utf-8');
        right_str = lines[5].decode('utf-8');
        if res == "Timeout":
            check_unsat = "Timeout";
            depth1 = check_depth("Max", lines)
            depth2 = check_depth("Sum", lines)
        else:
            check_unsat = "";
    return {
        "left":left_str,
        "right":right_str,
        "result":check_unsat,
        "time":elapsed,
        "min_max_depth":depth1,
        "min_sum_depth":depth2
    }
    #return (left_str, right_str, check_unsat, elapsed);

def call_zeno_process(filename, thm, var_settings, time):
    try:
        args = ["dist/build/RewriteV/RewriteV", "tests/RewriteVerify/Correct/" + filename, thm]
        #limit_settings = ["--", "--limit", "15"]
        limit_settings = []
        res = subprocess.run(args + var_settings + limit_settings, capture_output = True, timeout = time);
        return res.stdout;
    except subprocess.TimeoutExpired as TimeoutEx:
        return (TimeoutEx.stdout.decode('utf-8') + "\nTimeout").encode('utf-8')

# TODO don't need the Unknown iteration-limit depth anymore
'''
def check_depth(lines):
    depths = [0]
    for line in lines:
        if line[:21] == "<<Current Min Depth>>":
            depth_str = line[22:]
            depths.append(int(depth_str))
    return max(depths)
'''

# ver should be either "Max" or "Sum"
def check_depth(ver, lines):
    depths = [0]
    for utf in lines:
        line = utf.decode('utf-8')
        if line[:17] == ("<<Min " + ver + " Depth>>"):
            depth_str = line[18:]
            depths.append(int(depth_str))
            #print(ver, depth_str)
    #print("Max", ver, max(depths))
    return max(depths)

equivalences = [
    "p01",
    "p02",
    "p04",
    "p06",
    "p07",
    "p08",
    "p09",
    "p10",
    "p11",
    "p12",
    "p13",
    "p14",
    "p15",
    "p17",
    "p19",
    "p20",
    "p22",
    "p23",
    "p24",
    "p25",
    "p31",
    "p32",
    "p33",
    "p34",
    "p35",
    "p36",
    "p38",
    "p39",
    "p40",
    "p41",
    "p42",
    "p43",
    "p44",
    "p45",
    "p46",
    "p47",
    "p49",
    "p50",
    "p51",
    "p52",
    "p53",
    "p54",
    "p55",
    "p56",
    "p57",
    "p58",
    "p61",
    "p64",
    "p67",
    "p72",
    "p73",
    "p74",
    "p75",
    "p79",
    "p80",
    "p81",
    "p82",
    "p83",
    "p84"
]

equivalences_all_total = [
    ("p01", ["n", "xs"]),
    ("p02", ["n", "xs", "ys"]),
    ("p04", ["n", "xs"]),
    ("p09", ["i", "j", "k"]),
    ("p11", ["xs"]),
    ("p12", ["f", "n", "xs"]),
    ("p13", ["n", "x", "xs"]),
    ("p14", ["p", "xs", "ys"]),
    ("p15", ["x", "xs"]),
    ("p17", ["n"]),
    ("p19", ["n", "xs"]),
    ("p20", ["xs"]),
    ("p22", ["a", "b", "c"]),
    ("p23", ["a", "b"]),
    ("p31", ["a", "b", "c"]),
    ("p32", ["a", "b"]),
    ("p33", ["a", "b"]),
    ("p34", ["a", "b"]),
    ("p35", ["xs"]),
    ("p36", ["xs"]),
    ("p38", ["n", "xs"]),
    ("p39", ["n", "x", "xs"]),
    ("p40", ["xs"]),
    ("p41", ["f", "n", "xs"]),
    ("p42", ["n", "x", "xs"]),
    ("p43", ["p", "xs"]),
    ("p44", ["x", "xs", "ys"]),
    ("p45", ["x", "y", "xs", "ys"]),
    ("p46", ["xs"]),
    ("p47", ["a"]),
    ("p49", ["xs", "ys"]),
    ("p50", ["xs"]),
    ("p51", ["x", "xs"]),
    ("p52", ["n", "xs"]),
    ("p53", ["n", "xs"]),
    ("p55", ["n", "xs", "ys"]),
    ("p56", ["n", "m", "xs"]),
    ("p57", ["n", "m", "xs"]),
    ("p58", ["n", "xs", "ys"]),
    ("p67", ["xs"]),
    ("p72", ["i", "xs"]),
    ("p73", ["p", "xs"]),
    ("p74", ["i", "xs"]),
    ("p75", ["n", "m", "xs"]),
    ("p79", ["m", "n", "k"]),
    ("p80", ["n", "xs", "ys"]),
    ("p81", ["n", "m", "xs"]),
    ("p82", ["n", "xs", "ys"]),
    ("p83", ["xs", "ys", "zs"]),
    ("p84", ["xs", "ys", "zs"])
]

equivalences_should_fail = [
    ("p06", ["n", "m"]),
    ("p07", ["n", "m"]),
    ("p08", ["k", "m", "n"]),
    ("p10", ["m"]),
    ("p24", ["a", "b"]),
    ("p25", ["a", "b"]),
    ("p54", ["n", "m"]),
    ("p61", ["xs", "ys"]),
    ("p64", ["x", "xs"]),
]

custom_finite = [
    "p06fin",
    "p07fin",
    "p08fin",
    "p10fin",
    "p18fin",
    "p21fin",
    "p64fin"
]

finite_long = [
    ("p24fin", ["a", "b"]),
    ("p25fin", ["a", "b"]),
    ("p54fin", ["m"]),
    ("p61fin", []),
    ("p65finA", ["m"]),
    ("p69finA", ["m"]),
]


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

more_finite = [
    ("p03fin", [n, xs]),
    ("p03finA", [n, xs]),
    ("p04fin", [n]),
    ("p05finC", [n, x, xs]),
    ("p15fin", [x, xs]),
    ("p20fin", [xs]),
    ("p48fin", [xs]),
    ("p61fin", [xs]),
    ("p70fin", [m, n]),
    ("p78fin", [xs]),
    ("p78finA", [xs]),
    #("p81fin", [n, m, xs]), shouldn't need finiteness
    ("p85fin", [xs, ys]),
    ("p85finA", [xs, ys]),

    ("p54fin", [n]),
    #("p65finA", [i, m]), slow
    #("p69finA", [n, m]), slow
    ("p70finA", [m, n]),
    ("p38finA", [n, xs]),
    ("p57fin", [n, m, xs]),
    ("p85finB", [xs, ys]),
    ("p85finC", [xs, ys]),

    ("p26fin", [x, xs, ys]),
    ("p59fin", [xs, ys]),

    ("p16fin", [x, xs]),
    #("p24fin", [a]), slow
    #("p24finA", [a]), not needed
    #("p25fin", [a]), slow
    ("p38fin", [n, xs]),
    #("p65fin", [i, m]),
    #("p69fin", [n, m])
]

extra_theorems = [
    ("p27fin", [x, xs, ys]),
    ("p28fin", [x, xs]),
    ("p29fin", [x, xs]),
    ("p30fin", [x, xs]),
    ("p37fin", [x, xs]),
    ("p60fin", [xs, ys]),
    ("p62fin", [xs, x]),
    ("p63fin", [n, xs]),
    ("p66fin", [p, xs]),
    ("p68fin", [n, xs]),
    ("p71fin", [x, y, xs]),
    ("p76fin", [n, m, xs]),
    ("p77fin", [x, xs])
]

# this includes even the slow ones
old_successes = [
    ("p01", [n]),
    ("p02", []), # slow
    ("p06fin", []),
    ("p07fin", []),
    ("p08fin", []),
    ("p09", []),
    ("p10fin", []),
    ("p11", []),
    ("p12", []),
    ("p13", []),
    ("p14", []),
    ("p16finA", [xs]), # extra slow, took about 2:10
    ("p17", []),
    ("p18fin", []),
    ("p19", [n]),
    ("p21fin", []),
    ("p22", []),
    ("p23", []),
    ("p24fin", [b]), # slow
    ("p25fin", [a]), # slow
    ("p31", []),
    ("p32", [a, b]),
    ("p33", []),
    ("p34", [a]),
    ("p35", []),
    ("p36", []),
    ("p39", []),
    ("p40", []),
    ("p41", []),
    ("p42", []),
    ("p43", [p, xs]),
    ("p44", []),
    ("p45", []),
    ("p46", []),
    ("p49", [xs, ys]),
    ("p50", []),
    ("p51", [xs]),
    ("p54fin", [m]),
    ("p56", [n, m]),
    ("p61fin", []), # slow
    ("p64fin", []),
    ("p65finA", ["m"]),
    ("p66fin", [p, xs]),
    ("p67", []),
    ("p69finA", ["m"]),
    ("p73", [p, xs]), # slow, but only a little
    ("p79", [n]),
    ("p82", [])
]

ground_truth = [
    ("p01", [n]),
    ("p02", []), # slow
    ("p03fin", [n]),
    ("p03finB", [n, xs]),
    ("p04fin", []),
    ("p05finE", [x]),
    ("p05finF", [n]),
    ("p06fin", []),
    ("p07fin", []),
    ("p08fin", []),
    ("p09", []),
    ("p10fin", []),
    ("p11", []),
    ("p12", []),
    ("p13", []),
    ("p14", []),
    ("p15finA", [x]),
    ("p15finB", [xs]),
    ("p16finA", [xs]), # extra slow, took about 2:10
    ("p17", []),
    ("p18fin", []),
    ("p19", [n]),
    ("p20finA", []),
    ("p21fin", []),
    ("p22", []),
    ("p23", []),
    ("p24fin", [b]), # slow
    ("p25fin", [a]), # slow
    ("p26finA", [x]),
    ("p26finB", [xs]),
    ("p27finA", [xs, ys]),
    ("p28finA", [xs]),
    ("p29finA", [xs]),
    ("p30finA", [xs]),
    ("p31", []),
    ("p32", [a, b]),
    ("p33", []),
    ("p34", [a]),
    ("p35", []),
    ("p36", []),
    ("p37finB", [x]),
    ("p37finC", [xs]),
    ("p38finB", []),
    ("p39", []),
    ("p40", []),
    ("p41", []),
    ("p42", []),
    ("p43", [p, xs]),
    ("p44", []),
    ("p45", []),
    ("p46", []),
    ("p47", []),
    ("p48finB", []),
    ("p49", [xs, ys]),
    ("p50", []),
    ("p51", [xs]),
    ("p52finA", []),
    ("p53finA", []),
    ("p54fin", [m]),
    ("p55", []),
    ("p56", [n, m]),
    ("p57finA", []),
    ("p57finB", [n, xs]),
    ("p58", [n, xs, ys]),
    ("p59finA", [ys]),
    ("p60finB", []),
    ("p61fin", []), # slow
    ("p62finA", []),
    ("p63finA", [n]),
    ("p64fin", []),
    ("p65finA", [m]),
    ("p66fin", [p, xs]),
    ("p67", []),
    ("p68finA", [xs]),
    ("p68finB", [n]),
    ("p69finA", [m]),
    ("p70finC", [n]),
    ("p70finD", [m]),
    ("p71finA", [y]),
    ("p71finB", [x]),
    ("p72", [i]),
    ("p73", [p, xs]), # slow, but only a little
    ("p74", [i, xs]),
    ("p75fin", [m, xs]),
    ("p76finB", [m, xs]),
    ("p76finC", [n]),
    ("p77finA", [x]),
    ("p78finB", []),
    ("p79", [n]),
    ("p80", []),
    ("p81", [n, m, xs]),
    ("p82", []),
    ("p83", [ys]),
    ("p84", [ys]),
    ("p85finB", [xs, ys]),
    ("p85finC", [xs, ys])
]

ground_truth_all_total = [
    ("p01", [n, xs]),
    ("p02", [n, xs, ys]), # slow
    ("p03fin", [n, xs, ys]),
    ("p03finB", [n, xs, ys]),
    ("p04fin", [n, xs]),
    ("p05finE", [n, x, xs]),
    ("p05finF", [n, x, xs]),
    ("p06fin", [n, m]),
    ("p07fin", [n, m]),
    ("p08fin", [k, m, n]),
    ("p09", [i, j, k]),
    ("p10fin", [m]),
    ("p11", [xs]),
    ("p12", [f, n, xs]),
    ("p13", [n, x, xs]),
    ("p14", [p, xs, ys]),
    ("p15finA", [x, xs]),
    ("p15finB", [x, xs]),
    ("p16finA", [x, xs]), # extra slow, took about 2:10
    ("p17", [n]),
    ("p18fin", [i, m]),
    ("p19", [n, xs]),
    ("p20finA", [xs]),
    ("p21fin", [n, m]),
    ("p22", [a, b, c]),
    ("p23", [a, b]),
    ("p24fin", [a, b]), # slow
    ("p25fin", [a, b]), # slow
    ("p26finA", [x, xs, ys]),
    ("p26finB", [x, xs, ys]),
    ("p27finA", [x, xs, ys]),
    ("p28finA", [x, xs]),
    ("p29finA", [x, xs]),
    ("p30finA", [x, xs]),
    ("p31", [a, b, c]),
    ("p32", [a, b]),
    ("p33", [a, b]),
    ("p34", [a, b]),
    ("p35", [xs]),
    ("p36", [xs]),
    ("p37finB", [x, xs]),
    ("p37finC", [x, xs]),
    ("p38finB", [n, xs]),
    ("p39", [n, x, xs]),
    ("p40", [xs]),
    ("p41", [f, n, xs]),
    ("p42", [n, x, xs]),
    ("p43", [p, xs]),
    ("p44", [x, xs, ys]),
    ("p45", [x, y, xs, ys]),
    ("p46", [xs]),
    ("p47", [a]),
    ("p48finB", [xs]),
    ("p49", [xs, ys]),
    ("p50", [xs]),
    ("p51", [x, xs]),
    ("p52finA", [n, xs]),
    ("p53finA", [n, xs]),
    ("p54fin", [n, m]),
    ("p55", [n, xs, ys]),
    ("p56", [n, m, xs]),
    ("p57finA", [n, m, xs]),
    ("p57finB", [n, m, xs]),
    ("p58", [n, xs, ys]),
    ("p59finA", [xs, ys]),
    ("p60finB", [xs, ys]),
    ("p61fin", [xs, ys]), # slow
    ("p62finA", [xs, x]),
    ("p63finA", [n, xs]),
    ("p64fin", [x, xs]),
    ("p65finA", [i, m]),
    ("p66fin", [p, xs]),
    ("p67", [xs]),
    ("p68finA", [n, xs]),
    ("p68finB", [n, xs]),
    ("p69finA", [n, m]),
    ("p70finC", [m, n]),
    ("p70finD", [m, n]),
    ("p71finA", [x, y, xs]),
    ("p71finB", [x, y, xs]),
    ("p72", [i, xs]),
    ("p73", [p, xs]), # slow, but only a little
    ("p74", [i, xs]),
    ("p75fin", [n, m, xs]),
    ("p76finB", [n, m, xs]),
    ("p76finC", [n, m, xs]),
    ("p77finA", [x, xs]),
    ("p78finB", [xs]),
    ("p79", [m, n, k]),
    ("p80", [n, xs, ys]),
    ("p81", [n, m, xs]),
    ("p82", [n, xs, ys]),
    ("p83", [xs, ys, zs]),
    ("p84", [xs, ys, zs]),
    ("p85finB", [xs, ys]),
    ("p85finC", [xs, ys])
]

# TODO theorems with altered finiteness
# construct the final list from this using a function
ground_truth_altered_finite = [
    ("p03fin", [n], 2),
    ("p03finB", [n, xs], 2),
    ("p04fin", [], 1),
    ("p05finE", [x], 4),
    ("p05finF", [n], 4),
    ("p06fin", [], 1),
    ("p07fin", [], 1),
    ("p08fin", [], 1),
    ("p10fin", [], 1),
    ("p15finA", [x], 2),
    ("p15finB", [xs], 4),
    ("p16finA", [xs], 2),
    ("p18fin", [], 1),
    ("p20finA", [], 2),
    ("p21fin", [], 1),
    ("p24fin", [b], 1),
    ("p25fin", [a], 1),
    ("p26finA", [x], 2),
    ("p26finB", [xs], 3),
    ("p27finA", [xs, ys], 6),
    ("p28finA", [xs], 3),
    ("p29finA", [xs], 3),
    ("p30finA", [xs], 3),
    ("p37finB", [x], 2),
    ("p37finC", [xs], 3),
    ("p38finB", [], 3),
    ("p48finB", [], 2),
    ("p52finA", [], 2),
    ("p53finA", [], 2),
    ("p54fin", [m], 1),
    ("p57finA", [], 2),
    ("p57finB", [n, xs], 2),
    ("p59finA", [ys], 2),
    ("p60finB", [], 4),
    ("p61fin", [], 1),
    ("p62finA", [], 2),
    ("p63finA", [n], 2),
    ("p64fin", [], 1),
    ("p65finA", [m], 1),
    ("p66fin", [p, xs], 1),
    ("p68finA", [xs], 3),
    ("p68finB", [n], 2),
    ("p69finA", [m], 1),
    ("p70finC", [n], 2),
    ("p70finD", [m], 2),
    ("p71finA", [y], 3),
    ("p71finB", [x], 3),
    ("p75fin", [m, xs], 1),
    ("p76finB", [m, xs], 3),
    ("p76finC", [n], 3),
    ("p77finA", [x], 2),
    ("p78finB", [], 2),
    ("p85finB", [xs, ys], 1) #85C omitted because it would be the same
]

def make_altered_finite_list(suite):
    alt_suite = []
    for (thm, settings, qty) in suite:
        for i in range(qty):
            alt_suite.append((thm + str(i + 1), settings))
    return alt_suite

def totality_change(suite):
    alt_suite = []
    for (thm, settings) in suite:
        for i in range(len(settings)):
            alt_rule = (thm, settings[:i] + settings[(i+1):])
            alt_suite.append(alt_rule)
    return alt_suite

# subtraction of 1 happens in here
def print_depth(depth):
    if depth > 0:
        print("\tAll concretizations checked up to depth " + str(depth - 1))
    else:
        print("\tConcretizations of depth 0 still remaining")

'''
Results for totality-altered ground truth, 1/16/22:
p01 SAT
p03fin Timeout
p03finB SAT SAT
p05finE Timeout
p05finF Timeout
p15finA timeout
p15finB t
p16finA t
p19 SAT
p24fin fail
p25fin t
p26finA t
p26finB t
p27finA t t
p28finA t
p29finA t
p30finA t
p32 S S
p34 S
p37finB t
p37finC t
p43 S S
p49 S S
p51 S
p54fin S
p56 S S
p57finB SAT for xs, timeout for n
p58 S S S
p59finA t
p63finA t
p65finA S
p66fin S S
p68finA t
p68finB t
p69finA S
p70finC S
p70finD S
p71finA t
p71finB t
p72 S
p73 S S
p74 S S
p75fin timeout for xs, SAT for m
p76finB t t
p76finC t
p77finA t
p79 S
p81 S S S
p83 S
p84 S
p85finB S S
p85finC S S
'''

def test_suite_simple(suite, timeout = 25):
    unsat_num = 0;
    for thm in suite:
        print(thm);
        d = run_zeno("Zeno.hs", thm, [], timeout);
        check_unsat = d["result"]
        elapsed = d["time"]
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
    print(unsat_num, "Confirmed out of", len(suite))

def test_suite(suite, timeout = 25):
    unsat_num = 0;
    min_max_depth_dict = {}
    min_sum_depth_dict = {}
    for (thm, settings) in suite:
        print(thm, settings);
        d = run_zeno("Zeno.hs", thm, settings, timeout);
        check_unsat = d["result"]
        elapsed = d["time"]
        min_max_depth = d["min_max_depth"]
        min_sum_depth = d["min_sum_depth"]
        min_max_depth_dict[thm] = min_max_depth
        min_sum_depth_dict[thm] = min_sum_depth
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat[:7] == "Unknown":
            print("\tIncomplete - " + str(elapsed) + "s")
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
        print("\tMin Max Depth:")
        print_depth(min_max_depth)
        print("\tMin Sum Depth:")
        print_depth(min_sum_depth)
    print(unsat_num, "Confirmed out of", len(suite))

# TODO make this system more modular?
def test_suite_ground(suite, timeout = 25):
    unsat_num = 0;
    min_max_depth_dict = {}
    min_sum_depth_dict = {}
    for (thm, settings) in suite:
        print(thm, settings);
        d = run_zeno("TestZeno.hs", thm, settings, timeout);
        check_unsat = d["result"]
        elapsed = d["time"]
        min_max_depth = d["min_max_depth"]
        min_sum_depth = d["min_sum_depth"]
        min_max_depth_dict[thm] = min_max_depth
        min_sum_depth_dict[thm] = min_sum_depth
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat[:7] == "Unknown":
            print("\tIncomplete - " + str(elapsed) + "s")
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
        print("\tMin Max Depth:")
        print_depth(min_max_depth)
        print("\tMin Sum Depth:")
        print_depth(min_sum_depth)
    print(unsat_num, "Confirmed out of", len(suite))

def total_string(settings):
    if len(settings) == 0:
        return ""
    t_str = settings[0]
    for t in settings[1:]:
        t_str += " " + t
    return t_str

def test_suite_csv(suite, timeout = 25):
    unsat_num = 0;
    min_max_depth_dict = {}
    min_sum_depth_dict = {}
    file = open("outcomes.csv", "w")
    file.write("Name,LHS,RHS,Total,Outcome,Time,Min Max Depth,Min Sum Depth\n")
    for (thm, settings) in suite:
        print(thm, settings);
        d = run_zeno("Zeno.hs", thm, settings, timeout);
        check_unsat = d["result"]
        elapsed = d["time"]
        l_str = d["left"]
        r_str = d["right"]
        min_max_depth = d["min_max_depth"]
        min_sum_depth = d["min_sum_depth"]
        min_max_depth_dict[thm] = min_max_depth
        min_sum_depth_dict[thm] = min_sum_depth
        file.write(thm + "," + l_str + "," + r_str + ",")
        file.write(total_string(settings) + ",")
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
            file.write("Verified," + str(elapsed) + "s,")
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
            file.write("Timeout," + str(elapsed) + "s,")
        else:
            print("\tFailed - " + str(elapsed) + "s")
            file.write("Failed," + str(elapsed) + "s,")
        print("\tMin Max Depth:")
        print_depth(min_max_depth)
        print("\tMin Sum Depth:")
        print_depth(min_sum_depth)
        file.write(str(min_max_depth) + "," + str(min_sum_depth) + "\n")
    print(unsat_num, "Confirmed out of", len(suite))
    file.close()

# For tests that should not return unsat
def test_suite_fail(suite, timeout = 25):
    sat_num = 0;
    for (thm, settings) in suite:
        print(thm, settings);
        d = run_zeno("Zeno.hs", thm, settings, timeout);
        check_unsat = d["result"]
        elapsed = d["time"]
        if check_unsat == "UNSAT ()":
            print("\tIncorrectly verified - " + str(elapsed) + "s");
        elif check_unsat == "Timeout":
            print("\tDid not verify - Timeout - " + str(elapsed) + "s")
            sat_num += 1
        elif check_unsat == "SAT ()":
            print("\tDid not verify - Sat - " + str(elapsed) + "s")
            sat_num += 1
        else:
            print("\tDid Not verify - Other" + str(elapsed) + "s")
            sat_num += 1
    print(sat_num, "Confirmed out of", len(suite))

def main():
    #test_suite_simple(custom_finite)
    #test_suite(equivalences_all_total)
    #test_suite(finite_long, 120)
    #test_suite_fail(equivalences_should_fail)
    #test_suite(more_finite)
    #test_suite(old_successes, 150)
    #test_suite_ground(ground_truth)
    #test_suite_ground(totality_change(ground_truth))
    #test_suite_ground([("p48finB", [xs])], 45)
    test_suite_ground(old_successes, 60)

if __name__ == "__main__":
    main()
