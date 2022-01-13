#!/usr/bin/env python
# Tests RewriteV on the Zeno suite

import os
import re
import subprocess
import time

def run_zeno(filename, thm, var_settings, timeout):
    start_time = time.monotonic();
    res = call_zeno_process(thm, var_settings, timeout);
    end_time = time.monotonic();
    elapsed = end_time - start_time;

    lines = res.splitlines()
    try:
        # the numbers 4 and 5 are dependent on the initial printing
        # if that printing changes, these need to change too
        left_str = lines[4].decode('utf-8');
        right_str = lines[5].decode('utf-8');
        check_unsat = lines[-1].decode('utf-8');
        print(check_unsat);
    except IndexError:
        left_str = lines[4].decode('utf-8');
        right_str = lines[5].decode('utf-8');
        if res == "Timeout":
            check_unsat = "Timeout";
        else:
            check_unsat = "";
    return (left_str, right_str, check_unsat, elapsed);

def call_zeno_process(thm, var_settings, time):
    try:
        args = ["dist/build/RewriteV/RewriteV", "tests/RewriteVerify/Correct/" + filename, thm]
        limit_settings = ["--", "--limit", "15"]
        res = subprocess.run(args + var_settings + limit_settings, capture_output = True, timeout = time);
        return res.stdout;
    except subprocess.TimeoutExpired as TimeoutEx:
        return (TimeoutEx.stdout.decode('utf-8') + "\nTimeout").encode('utf-8')

equivalences = [
    "p01",
    "p02",
    # "p03",
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
    # ("p03", ["n", "xs", "ys"]),
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
    ("p03finB", []),
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
    ("p57finB", []),
    ("p58", []),
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
    ("p75fin", [m]),
    ("p76finB", [m, xs]),
    ("p76finC", [n]),
    ("p77finA", [x]),
    ("p78finB", []),
    ("p79", [n]),
    ("p80", []),
    ("p81", [n, m, xs]),
    ("p82", []),
    ("p83", []),
    ("p84", []),
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

def test_suite_simple(suite, timeout = 25):
    unsat_num = 0;
    for thm in suite:
        print(thm);
        (l, r, check_unsat, elapsed) = run_zeno("Zeno.hs", thm, [], timeout);
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
    for (thm, settings) in suite:
        print(thm, settings);
        (l, r, check_unsat, elapsed) = run_zeno("Zeno.hs", thm, settings, timeout);
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
    print(unsat_num, "Confirmed out of", len(suite))

# TODO make this system more modular?
def test_suite_ground(suite, timeout = 25):
    unsat_num = 0;
    for (thm, settings) in suite:
        print(thm, settings);
        (l, r, check_unsat, elapsed) = run_zeno("TestZeno.hs", thm, settings, timeout);
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
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
    file = open("outcomes.csv", "w")
    file.write("Name,LHS,RHS,Total,Outcome,Time\n")
    for (thm, settings) in suite:
        print(thm, settings);
        (l_str, r_str, check_unsat, elapsed) = run_zeno("Zeno.hs", thm, settings, timeout);
        file.write(thm + "," + l_str + "," + r_str + ",")
        file.write(total_string(settings) + ",")
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
            file.write("Verified," + str(elapsed) + "s\n")
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
            file.write("Timeout," + str(elapsed) + "s\n")
        else:
            print("\tFailed - " + str(elapsed) + "s")
            file.write("Failed," + str(elapsed) + "s\n")
    print(unsat_num, "Confirmed out of", len(suite))
    file.close()

# For tests that should not return unsat
def test_suite_fail(suite, timeout = 25):
    sat_num = 0;
    for (thm, settings) in suite:
        print(thm, settings);
        (l, r, check_unsat, elapsed) = run_zeno("Zeno.hs", thm, settings, timeout);
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
    test_suite(old_successes, 150)

if __name__ == "__main__":
    main()
