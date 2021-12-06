#!/usr/bin/env python
# Tests RewriteV on the Zeno suite

import os
import re
import subprocess
import time

def run_zeno(thm, var_settings):
    start_time = time.monotonic();
    res = call_zeno_process(thm, var_settings);
    end_time = time.monotonic();
    elapsed = end_time - start_time;

    try:
        check_unsat = res.splitlines()[-1].decode('utf-8');
        print(check_unsat);
    except IndexError:
        if res == "Timeout":
            check_unsat = "Timeout";
        else:
            check_unsat = "";
    return (check_unsat, elapsed);

def call_zeno_process(thm, var_settings):
    try:
        args = ["dist/build/RewriteV/RewriteV", "tests/RewriteVerify/Correct/Zeno.hs", thm]
        limit_settings = ["--", "--limit", "10"]
        res = subprocess.run(args + var_settings + limit_settings, capture_output = True, timeout = 20);
        return res.stdout;
    except subprocess.TimeoutExpired:
        return "Timeout".encode('utf-8')

equivalences = [
    "p01",
    "p02",
    "p03",
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
    ("p03", ["n", "xs", "ys"]),
    ("p04", ["n", "xs"]),
    ("p06", ["n", "m"]),
    ("p07", ["n", "m"]),
    ("p08", ["k", "m", "n"]),
    ("p09", ["i", "j", "k"]),
    ("p10", ["m"]),
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
    ("p24", ["a", "b"]),
    ("p25", ["a", "b"]),
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
    ("p54", ["n", "m"]),
    ("p55", ["n", "xs", "ys"]),
    ("p56", ["n", "m", "xs"]),
    ("p57", ["n", "m", "xs"]),
    ("p58", ["n", "xs", "ys"]),
    ("p61", ["xs", "ys"]),
    ("p64", ["x", "xs"]),
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

custom_finite = [
    "p06fin",
    "p07fin",
    "p08fin",
    "p10fin",
    "p18fin",
    "p21fin",
    "p64fin"
]

n = "n"
x = "x"
xs = "xs"
m = "m"
y = "y"
ys = "ys"
i = "i"
a = "a"
p = "p"

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
    ("p81fin", [n, m, xs]),
    ("p85fin", [xs, ys]),
    ("p85finA", [xs, ys]),

    ("p54fin", [n]),
    ("p65finA", [i, m]),
    ("p69finA", [n, m]),
    ("p70finA", [m, n]),
    ("p38finA", [n, xs]),
    ("p57fin", [n, m, xs]),
    ("p85finB", [xs, ys]),
    ("p85finC", [xs, ys]),

    ("p26fin", [x, xs, ys]),
    ("p59fin", [xs, ys]),

    ("p16fin", [x, xs]),
    ("p24fin", [a]),
    ("p24finA", [a]),
    ("p25fin", [a]),
    ("p38fin", [n, xs]),
    ("p65fin", [i, m]),
    ("p69fin", [n, m])
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

def test_equivalences_basic():
    unsat_num = 0;
    for thm in equivalences:
        print(thm);
        (check_unsat, elapsed) = run_zeno(thm, []);
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
    return unsat_num

def test_custom_finite():
    unsat_num = 0;
    for thm in custom_finite:
        print(thm);
        (check_unsat, elapsed) = run_zeno(thm, []);
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
    return unsat_num

def test_equivalences_all_total():
    unsat_num = 0;
    for (thm, settings) in equivalences_all_total:
        print(thm, settings);
        (check_unsat, elapsed) = run_zeno(thm, settings);
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
    return unsat_num

def test_more_finite():
    unsat_num = 0;
    for (thm, settings) in more_finite:
        print(thm, settings);
        (check_unsat, elapsed) = run_zeno(thm, settings);
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
    return unsat_num

def test_extra_theorems():
    unsat_num = 0;
    for (thm, settings) in extra_theorems:
        print(thm, settings);
        (check_unsat, elapsed) = run_zeno(thm, settings);
        if check_unsat == "UNSAT ()":
            print("\tVerified - " + str(elapsed) + "s");
            unsat_num += 1
        elif check_unsat == "Timeout":
            print("\tTimeout - " + str(elapsed) + "s")
        else:
            print("\tFailed - " + str(elapsed) + "s")
    return unsat_num

def main():
    #unsat_num = test_equivalences_basic()
    #unsat_num = test_custom_finite()
    #unsat_num = test_equivalences_all_total()
    unsat_num = test_more_finite()
    #unsat_num = test_extra_theorems()
    print(unsat_num, "Confirmed out of", len(extra_theorems))

if __name__ == "__main__":
    main()
