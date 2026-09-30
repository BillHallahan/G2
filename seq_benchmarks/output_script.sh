import re
import os

true_prop = []
false_prop = []
func_def_false = []
func_def_true = []

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

    for (n, r, t, st, sats, unsats, unk) in arr:
        if r == "EUnknown" :
            unknowns += 1
        elif r == "ECounterexample":
            refuted += 1
        elif r == "ETimeout":
            timeouts += 1
        else:
            verified += 1
        x = round(float(t), 2) if t != "-" else 0
        tot_time += x
        t_s += int(sats)
        t_us += int(unsats)
        t_uk += int(unk)

        t_st += round(float(st), 2)

    avg = tot_time/(len(arr) - timeouts)
    t_sc = t_s + t_us + t_uk
    per_s = round((t_s / t_sc) * 100, 2)
    per_us = round((t_us / t_sc) * 100, 2)
    per_uk = round((t_uk / t_sc) * 100, 2)

    avg_st = round(t_st / len(arr), 2)

    return (len(arr), round(avg, 2), verified, refuted, timeouts, unknowns, per_s, per_us, per_uk, avg_st)

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

def read_output(logsDirPath):
    logDirs = os.listdir(logsDirPath)
    header = "Properties"

    for log in logDirs:
        if "logs" in log:
            parts = log.split("_")
            solver = parts[1]
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
                            # print(benchPath)
                            time_taken = data[2]
                            if "prop" in name:
                                if "False" in benchmarks:
                                    updateDict(f_prop_tbl, name, time_taken)
                                    # Avg. Time (s) & 1.47 & 1.36 & 1.98 & 0.85 & 1.78 & 0.49 & 0.93 & 0.29\\ \hline
                                    false_prop.append(tuple(data))
                                else:
                                    updateDict(t_prop_tbl, name, time_taken)
                                    true_prop.append(tuple(data))
                            else:
                                if "False" in benchmarks:
                                    func_def_false.append(tuple(data))
                                else:
                                    func_def_true.append(tuple(data))

    header += r" \\ \hline"

    # print("Data for Equivalent False")
    # print(func_def_false)

    # print("\nData for Equivalent True")
    # print(func_def_true)
                                    
    print("\nTable for True props\n")
    print(header)
    print_table(t_prop_tbl)

    print("\nTable for False props\n")
    print(header)
    print_table(f_prop_tbl)

    print("\nSummary Table 1\n")
    print("Benchmarks & # of properties & Average Time & # of Verified/Refuted & # of timeouts & # of unknowns" + r" \\ \hline")
    (len1, avg1, ver1, ref1, tim1, unk1, p_s1, p_us1, p_uk1, avgSt1) = calculate_avg_time(func_def_true)
    print("Equivalences" + " & " + str(len1) + " & " + str(avg1) + " & " + str(ver1) + " & " + str(tim1) + " & " + str(unk1) + r" \\ \hline")
    (len2, avg2, ver2, ref2, tim2, unk2, p_s2, p_us2, p_uk2, avgSt2) = calculate_avg_time(func_def_false)
    print("Incorrect Equiv" + " & " + str(len2) + " & " + str(avg2) + " & " + str(ref2) + " & " + str(tim2) + " & " + str(unk2) + r" \\ \hline")
    (len3, avg3, ver3, ref3, tim3, unk3, p_s3, p_us3, p_uk3, avgSt3) = calculate_avg_time(true_prop)
    print("True Props" + " & " +  str(len3) + " & " + str(avg3) + " & " + str(ver3) + " & " + str(tim3) + " & " + str(unk3) + r" \\ \hline")
    (len4, avg4, ver4, ref4, tim4, unk4, p_s4, p_us4, p_uk4, avgSt4) = calculate_avg_time(false_prop)
    print("False Props" + " & " + str(len4) + " & " + str(avg4) + " & " + str(ref4) + " & " + str(tim4) + " & " + str(unk4) + r" \\ \hline")

    print("\nSummary Table 2\n")
    print("Benchmarks & Sat (%) & UnSat (%) & Unknown (%) & Avg. Solving Time (s)" + r" \\ \hline")
    print("Equivalences" + " & " + str(p_s1) + " & " + str(p_us1) + " & " + str(p_uk1) + " & " + str(avgSt1) + r" \\ \hline")
    print("Incorrect Equiv" + " & " + str(p_s2) + " & " + str(p_us2) + " & " + str(p_uk2) + " & " + str(avgSt2) + r" \\ \hline")
    print("True Props" + " & " + str(p_s3) + " & " + str(p_us3) + " & " + str(p_uk3) + " & " + str(avgSt3) + r" \\ \hline")
    print("False Props" + " & " + str(p_s4) + " & " + str(p_us4) + " & " + str(p_uk4) + " & " + str(avgSt4) + r" \\ \hline")

    print()

current_path = os.path.join(os.getcwd(), "seq_benchmarks/logs")
print(current_path)
read_output(current_path)