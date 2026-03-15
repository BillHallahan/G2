# combine together results from running:
# 1) Nova
# 2) CycleQ
# 3) Propel
# results from each project are expected to be located in verify-results/*
# at the top level of G2.

import re

# Nova results should be a latex table with one row per function where
# the first column is name of benchmark and second column is time.
def readNova(file):
    contents = open(file)
    res = {}
    for lne in contents.readlines():
        mtch = re.match("([a-zA-Z0-9]+)\s*\&\s*([0-9.]+|\s*-)", lne)
        res[mtch.group(1)] = mtch.group(2)
    return res

def readPropel(file):
    return readNova(file)

def readCycleQFile(res, ty, file):
    contents = open(file)
    for lne in (contents.readlines()[3:][:-2]):
        mtch = re.match("([a-zA-Z0-9]+)\s*\&\s*([0-9.]+|\s*NaN)\s*\&", lne)
        res[mtch.group(1) + ty] = mtch.group(2) if mtch.group(2) != "NaN" else "-"
    return res

# CycleQ results should be in the "benchmarks - [benchmark file].tex" files output
# by CycleQ.
def readCycleQ(types):
    fle_start = "verify-results/benchmarks - TypeClasses"
    type_files = [(x, fle_start + x + ".tex") for x in types]
    res = {}
    for (ty, fle) in type_files:
        res = readCycleQFile(res, ty, fle)
    return res

def readNebula(file):
    contents = open(file)
    res = {}
    for lne in (contents.readlines()[1:]):
        lne_pieces = lne.split(",")
        prop = lne_pieces[0]
        outcome = lne_pieces[4]

        if outcome == "Verified":
            res[prop] = lne_pieces[5]
        elif outcome == "Failed":
            res[prop] = "CEx"
        elif outcome == "Timeout":
            res[prop] = "-"
        elif outcome == "Error":
            res[prop] = "ERROR"
    return res


def joinResults(prop_list, res):
    lines = ""
    for prop in prop_list:
        lne = ""
        lne += prop
        for r in res:
            lne += " & "
            if prop in r:
                lne += r[prop]
            else:
                lne += " "
        lne += " \\\\\n"
        lines += lne
    return lines

# reading in benchmark results
nova_res = readNova("verify-results/nova.txt")
nebula_res = readNebula("verify-results/NebulaTypeClasses.csv")

cycleq_types = [ "Function",
                 "List",
                 "Maybe",
                 "NonEmpty",
                 "Reader",
                 "State",
                 "Tree",
                 "Tuple",
                 "ZipList" ]
cycleq_res = readCycleQ(cycleq_types)

propel_res = readPropel("verify-results/propel.txt")


# forming prop names
semigroupLaws = ["semigroupAssociativity"]
monoidLaws = ["monoidRightIdentity", "monoidLeftIdentity", "monoidConcatenation"]
functorLaws = ["fmapId", "fmapComposition"]
applicativeLaws = ["appIdentity", "appComposition", "appHomomorphism", "appInterchange"]
monadLaws = ["monadLeftIdentity", "monadRightIdentity", "monadAssociativity"]

all_laws = semigroupLaws + monoidLaws + functorLaws + applicativeLaws + monadLaws

list_laws = [law + "List" for law in all_laws]
zip_list_laws = [law + "ZipList" for law in applicativeLaws]
nonempty_list_laws = [law + "NonEmpty" for law in semigroupLaws + functorLaws + applicativeLaws + monadLaws]
tree_laws = [law + "Tree" for law in functorLaws + applicativeLaws]
maybe_laws = [law + "Maybe" for law in all_laws]
state_laws = [law + "State" for law in functorLaws + applicativeLaws + monadLaws]
reader_laws = [law + "Reader" for law in functorLaws + applicativeLaws + monadLaws]
tuple_laws = [law + "Tuple" for law in all_laws]
function_laws = [law + "Function" for law in semigroupLaws + functorLaws + applicativeLaws + monadLaws]

all_type_laws = list_laws + zip_list_laws + nonempty_list_laws + tree_laws + maybe_laws + state_laws + reader_laws + tuple_laws + function_laws

print(joinResults(all_type_laws, [nova_res, nebula_res, cycleq_res, propel_res]))