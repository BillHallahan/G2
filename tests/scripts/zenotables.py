#!/usr/bin/env python

# code for CSV interpretation
# header not included in output
# everything in output is a string
def csv_matrix(fname):
    file = open(fname + ".csv", "r")
    lines = file.readlines()
    file.close()
    mat = []
    for line in lines[1:]:
        line_list = line.replace("\n", "").split(",")
        line_list[1] = line_list[1].replace(";", ",")
        line_list[2] = line_list[2].replace(";", ",")
        mat.append(line_list)
    return mat

def num_finite(row):
    f1 = row[1].count("walk")
    f2 = row[2].count("walk")
    return max(f1, f2)

def num_total(row):
    spaces = row[3].count(" ")
    if spaces == 0:
        if len(row[3]) > 0:
            return 1
        else:
            return 0
    else:
        return 1 + spaces

# successes, then failures, then timeouts
def table_results(mat):
    v = 0
    f = 0
    t = 0
    for row in mat:
        if row[4] == "Verified":
            v += 1
        elif row[4] == "Failed":
            f += 1
        elif row[4] == "Timeout":
            t += 1
    return (v, f, t)

# the last character for time is always s
# returns a string, not a number
def avg_verify_time(mat):
    num_verified = 0
    total_time = 0
    for row in mat:
        if row[4] == "Verified":
            num_verified += 1
            total_time += eval(row[5][:-1])
    if num_verified == 0:
        return "N/A"
    else:
        return str(round(total_time / num_verified, 1))

def avg_reject_time(mat):
    num_failed = 0
    total_time = 0
    for row in mat:
        if row[4] == "Failed":
            num_failed += 1
            total_time += eval(row[5][:-1])
    if num_failed == 0:
        return "N/A"
    else:
        return str(round(total_time / num_failed, 1))

# filter the matrix before giving it to this
# does not include category name
def results_row_entries(mat):
    num_thms = len(mat)
    (v, f, t) = table_results(mat)
    avg_time1 = avg_verify_time(mat)
    avg_time2 = avg_reject_time(mat)
    return [str(num_thms), str(v), str(f), str(t), avg_time1, avg_time2]

# on left are rows with num_total equal to n
# on right are the rest
def partition_total(mat, n):
    mat1 = []
    mat2 = []
    for row in mat:
        if num_total(row) == n:
            mat1.append(row)
        else:
            mat2.append(row)
    return (mat1, mat2)

def partition_finite(mat, n):
    mat1 = []
    mat2 = []
    for row in mat:
        if num_finite(row) == n:
            mat1.append(row)
        else:
            mat2.append(row)
    return (mat1, mat2)    

# input matrix is from CSV
def results_matrix(mat):
    headers = [
        "Category",
        "\# Thms",
        "\# V",
        "\# C",
        "\# TO",
        "Avg. V Time (s)",
        "Avg. C Time (s)"
    ]
    (no_total, some_total) = partition_total(mat, 0)
    (pure, unused1) = partition_finite(no_total, 0)
    (one_total, multiple_total) = partition_total(some_total, 1)
    (unused2, some_finite) = partition_finite(mat, 0)
    (one_finite, multiple_finite) = partition_finite(some_finite, 1)
    out_mat = [headers]
    categories = [
        ("All",mat),
        ("Nothing Total or Finite",pure),
        ("One Total Variable",one_total),
        ("One Finite Variable",one_finite),
        ("Multiple Total Variables",multiple_total),
        ("Multiple Finite Variables",multiple_finite)
    ]
    for (c, m) in categories:
        out_mat.append([c] + results_row_entries(m))
    return out_mat

def good_matrix(mat):
    out_mat = []
    for row in mat:
        out_mat.append(row[:3] + row[4:6])
    return out_mat

# input to this is output from results_matrix
def bad_matrix(mat):
    out_mat = []
    for row in mat:
        out_mat.append(row[:2] + row[3:5] + row[6:])
    return out_mat

# don't escape braces
def latex_table(mat):
    lines = []
    lines.append("\\begin{figure}[t]")
    lines.append("\\begin{center}")
    # row alignment depends on number of rows
    tabular = "\\begin{tabular}{ | l | "
    for i in range(1, len(mat[0])):
        tabular += "c | "
    lines.append(tabular + "}")
    lines.append("\\hline")
    for row in mat:
        ln = ""
        ln += row[0]
        for entry in row[1:]:
            ln += " & " + entry
        ln += " \\\\ \\hline"
        lines.append(ln)
    lines.append("\\end{tabular}")
    lines.append("\\end{center}")
    lines.append("\\end{figure}")
    return lines

def write_latex(fname, lines):
    file = open(fname + ".txt", "w")
    for line in lines:
        file.write(line + "\n")
    file.close()

def main():
    for group in ["ZenoUnaltered", "ZenoTotal", "ZenoFinite", "ZenoCycle"]:
        lat = latex_table(results_matrix(csv_matrix(group)))
        write_latex("Results" + group, lat)

if __name__ == "__main__":
    main()
