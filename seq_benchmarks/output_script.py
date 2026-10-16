import re
import os

benchCategory = ["Equiv", "T props", "F Equiv",  "F Props"]
solverOrder = ["cvc5", "z3", "cvc5,z3", "cvc5,z3--no-string-simplifier", "concrete"]
duplicateData = {"insort" : "insert", "sort" : "isort", "len":"length"}

true_prop = {}
false_prop = {}
func_def_false = {}
func_def_true = {}

allData = []

t_prop_tbl = {}
f_prop_tbl = {}

def calculate_avg_time(arr):
    timeouts = 0
    unknowns = 0
    verified = 0
    refuted = 0
    tot_time = 0
    t_s = 0
    t_us = 0
    t_uk = 0
    t_st = 0

    for val in arr:

        if val[1] == "EOther" :
            return (0,0,0,0,0,0,0,0, 0, 0)
        
        (n, r, t, st, sats, unsats, unk) = val
        
        if r == "EUnknown" :
            unknowns += 1
        elif r == "ECounterexample":
            refuted += 1
        elif r == "ETimeout":
            timeouts += 1
        else:
            verified += 1
        x = round(float(t), 1) if t != "-" else 0
        tot_time += x
        t_s += int(sats)
        t_us += int(unsats)
        t_uk += int(unk)

        t_st += round(float(st), 1)

    avg = tot_time/(len(arr) - timeouts)
    t_sc = t_s + t_us + t_uk
    per_s = round((t_s / t_sc) * 100, 1)
    per_us = round((t_us / t_sc) * 100, 1)
    per_uk = round((t_uk / t_sc) * 100, 1)

    avg_st = round(t_st / len(arr), 1)

    return (len(arr), round(avg, 1), verified, refuted, timeouts, unknowns, per_s, per_us, per_uk, avg_st)

def print_table(tbl):
    for key, value in tbl.items():
        row = key + " & " + value + r" \\ \hline"
        print(row)

def updateDict(dict, key, addToValue):
    if key in dict:
        value = dict[key]
        updatedValue = value + " & " + addToValue
        dict[key] = updatedValue
    else:
        dict[key] = addToValue

def updateDictionary(dictSol, key, val):
    if key in dictSol:
        dictSol[key].append(val)
    else:
        dictSol[key] = [val]

def removeDuplicates(dictDef):
    newdata = {}
    data = {}

    for key, value in dictDef.items():
        temp = {}
        for val in value:
            res = list(val)
            k = res[0]
            if k in duplicateData:
                present = duplicateData[k]
                k = present
            temp[k] = res[1:]
        newdata[key] = temp

    # for key, value in newdata.items():
    #     print("Key is:" + key)
    #     print(value)

    for key, value in newdata.items():
        temp = []
        for k, v in value.items():
            v.insert(0, k)
            temp.append(tuple(v))

        data[key] = temp

    return(data)

def read_output(logsDirPath):
    logDirs = os.listdir(logsDirPath)
    header = "Properties"
    global func_def_true, func_def_false, allData, true_prop, false_prop

    for log in logDirs:
        if "solver_logs" == log:
            continue;
        if "logs" in log:
            parts = log.split("_")
            solver = parts[1] if parts[1] else parts[2]
            header += " & " + solver
            
            file_path = os.path.join(logsDirPath, log)
            filesInLog = os.listdir(file_path)

            for benchmarks in filesInLog:
                benchPath = os.path.join(file_path, benchmarks)
                if os.path.isfile(benchPath):
                    with open(benchPath, 'r') as file:
                        for line in file:
                            if not line.strip():
                                continue
                            data = line.strip().split(",")
                            name = data[0]
                            time_taken = data[2]
                            if "prop" in name:
                                nameUpdated = name.replace("_", "\\_")
                                if "False" in benchmarks:
                                    updateDict(f_prop_tbl, nameUpdated, time_taken)
                                    val = tuple(data)
                                    updateDictionary(false_prop, solver, val)
                                else:
                                    updateDict(t_prop_tbl, nameUpdated, time_taken)
                                    val = tuple(data)
                                    updateDictionary(true_prop, solver, val)

                            else:
                                if "False" in benchmarks:
                                    updateDictionary(func_def_false, solver, tuple(data))
                                    updateDict(f_prop_tbl, name, time_taken)
                                    
                                else:
                                    updateDictionary(func_def_true, solver, tuple(data))
                                    # updateDict(t_prop_tbl, name, time_taken)
    # func_def_false = removeDuplicates(func_def_false)
    func_def_true = removeDuplicates(func_def_true)

    allData = [func_def_true, true_prop, func_def_false, false_prop]

    header += r" \\ \hline"
    count = 0
    sum1 = ""
    sum2 = ""
    cols = "\\#V/R & A.T"
    cols2 = "S\\% & U\\% & N\\% & T "
    headerSum1r1 = "Bench- & \\# p & " + " & ".join(rf"\multicolumn{{2}}{{c|}}{{{x}}}" for x in solverOrder) + r" \\" + r"\cline{3-12}"
    headerSum1r2 = "mark & &"
    headerSum2r1 = "Bench- & " + " & ".join(rf"\multicolumn{{4}}{{c|}}{{{x}}}" for x in solverOrder) + r" \\" + r"\cline{2-21}"
    headerSum2r2 = "mark &"
    ovr_str1 = "Overall "

    colTemp = 0
    global benchCategory
    tp = 0
    overdict = {}
    for data in allData:
        sorted_data = {key: data[key] for key in solverOrder if key in data}
        res1 = ""
        res2 = ""
        numProps = 0
        colTemp = len(sorted_data.items())

        for key, value in sorted_data.items():
            (len1, avg1, ver1, ref1, tim1, unk1, p_s1, p_us1, p_uk1, avgSt1) = calculate_avg_time(value)
            res1 += " & " + str(ver1) + "/" + str(ref1) + " & " + str(avg1)
            res2 += " & " + str(p_s1) + " & " + str(p_us1) + " & " + str(p_uk1) + " & " + str(avgSt1)
            numProps = len1
            if key in overdict:
                (v, r, t) = overdict[key]
                overdict[key] = (v + ver1, r + ref1, t + avg1)
            else:
                overdict[key] = (ver1, ref1, avg1)
        res1 = benchCategory[count] + " & " + str(numProps) + res1
        res2 = benchCategory[count] + res2
        sum1 += res1 + r" \\ \cline{1-2}" + "\n" if count < 3 else res1 + r" \\ \hline"
        sum2 += res2 + r" \\ \cline{1-1}" + "\n" if count < 3 else res2 + r" \\ \hline"
        count += 1
        tp += numProps

    ovr_str1 += " & " + str(tp)

    for k, val in overdict.items():
        (v, r, t) = val
        ovr_str1 += " & " + str(v) + "/" + str(r) + " & " + str(round(t/4, 1))

    colms = (cols + " & ") * colTemp
    colms2 = (cols2 + " & ") * 5
    headerSum1r2 += colms[:-3] + r" \\ \hline"
    headerSum2r2 += colms2[:-3] + r" \\ \hline"

    print("\nTable for True props\n")
    print(header)
    print_table(t_prop_tbl)

    print("\nTable for False props\n")
    print(header)
    print_table(f_prop_tbl)
    
    print("\nSummary Table 1\n")
    print(headerSum1r1)
    print(headerSum1r2)
    print(sum1)
    print(ovr_str1 + r"\\ \hline")
    print("\nSummary Table 2\n")
    print(headerSum2r1)
    print(headerSum2r2)
    print(sum2)

    print()

current_path = os.path.join(os.getcwd(), "/SeqProperties")
print(current_path)
read_output("/g2/seq_benchmarks/SeqProperties")