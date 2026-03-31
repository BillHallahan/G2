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
        res[mtch.group(1)] = " \\cellcolor{red!10}-" if mtch.group(2) == "-" else mtch.group(2)
    return res

def readPropel(file):
    return readNova(file)

# Nova results should be a latex table with one row per function where
# the first column is name of benchmark and second column is time.
def readHipSpec(file):
    contents = open(file)
    res = {}
    for lne in contents.readlines():
        res_match =" \s*([0-9.]+|unknown|unproved|timeout)"
        mtch = re.match("([a-zA-Z0-9]+)\s*\&" + res_match, lne)
        res_out = mtch.group(2)
        res_out = " \\cellcolor{red!10}-" if res_out == "unproved" or res_out == "timeout" else res_out
        res_out = "\\cellcolor{gray!30}" if res_out == "unknown" else res_out
        res[mtch.group(1)] = res_out
    return res

def readCycleQFile(res, ty, file):
    contents = open(file)
    for lne in (contents.readlines()[3:][:-2]):
        mtch = re.match("([a-zA-Z0-9]+)\s*\&\s*([0-9.]+|\s*NaN)\s*\&", lne)
        res_out = mtch.group(2)
        try:
            res_out = str(float(res_out) / 1000)
        except ValueError:
            break
        res[mtch.group(1) + ty] = res_out if res_out != "nan" else "\\cellcolor{red!10}-"
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
            res[prop] = lne_pieces[5].replace("s","")
        elif outcome == "Failed":
            res[prop] = "\\cellcolor{red!10}CEx"
        elif outcome == "Timeout":
            res[prop] = "\\cellcolor{red!10}-"
        elif outcome == "Error":
            res[prop] = "ERROR"
    return res


def joinResults(prop_list, res):
    data = {}
    lines = ""
    for prop in prop_list:
        lne = ""
        # lne += prop
        for r in res:
            lne += " & "
            if prop in r:
                try:
                    lne += str(round(float(r[prop]),2))
                except ValueError:
                    lne += r[prop]
            else:
                lne += "\\cellcolor{gray!30}"
        lne += " \\\\"
        data[prop] = lne
        lines += lne
    return (lines, data)

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

hipspec_res = readHipSpec("verify-results/hipspec.txt")

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

(org, data_dict) = joinResults(all_type_laws, [nova_res, nebula_res, cycleq_res, hipspec_res, propel_res])

# print(org)
print("\n\n")

# Pair of 
typeclass_types = [("semigroup", ["Associativity"],["List", "Tuple", "NonEmpty", "Function", "Maybe"]),
                   ("monoid", ["RightIdentity", "LeftIdentity", "Concatenation"] ,["List", "Tuple", "Maybe"]),
                   ("functor", ["Id", "Composition"], ["List", "Tuple", "Maybe", "NonEmpty", "Tree", "State", "Reader", "Function"]),
                   ("applicative", ["Identity", "Composition", "Homomorphism", "Interchange"], ["List", "Tuple", "Maybe", "NonEmpty", "Tree", "State", "Reader", "Function", "ZipList"]),
                   ("monad", ["LeftIdentity", "RightIdentity", "Associativity"], ["List", "Tuple", "Maybe", "NonEmpty", "State", "Reader", "Function"])]

def formTable(class_types, fun_data):
    lines = ""
    for (type_class, rules, supported_types) in class_types:
        type_class_new = type_class
        if type_class == "functor":
            type_class_new = "fmap" 
        elif type_class_new == "applicative":
            type_class_new = "app" 
        
        for rule in rules:
            heading = "\multicolumn{6}{l}{\\textbf{" + type_class.capitalize() + "-" + rule +"}}\\\ \hline"
            line = heading
            line += "\n "
            for type in supported_types :
                name = type_class_new + rule + type
                name_data = fun_data.get(name)
                line += str(type) + " " + str(name_data) + " \\hline \n"
            lines += line 
    return lines

print(formTable(typeclass_types, data_dict))