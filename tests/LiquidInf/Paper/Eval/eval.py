#!/usr/bin/env python
# Tests G2's LiquidHaskell type Inference on all files in the ../LiquidInf directory

import os
import re
import subprocess
import time

exe_name = str(subprocess.run(["cabal", "exec", "which", "Inference"], capture_output = True).stdout.decode('utf-8')).strip()

def run_infer(file, name, timeout, extra_opts=[]):
    if not os.path.exists("logs/" + name + ".txt"):
        # get info about the file
        (funcs, depth) = get_counts(file)

        # actual run the test
        # start_time = time.perf_counter();
        # res = call_infer_process(file, timeout);
        # end_time = time.perf_counter();
        # elapsed = end_time - start_time;
        (check_safe, res, res_err, counts, elapsed) = call_with_timing(file, timeout, extra_opts)

        f = open("logs/" + name + ".txt", "w")
        f.write(res.decode("utf-8") + "\n" + res_err.decode("utf-8"));
        f.close();

        # MAKES EVERYTHING AFTER THIS TIMEOUT QUICKLY
        timeout = "1";

        # run the test without extra fc
        # no_fc_start_time = time.perf_counter();
        # no_fc_res = call_infer_process(file, timeout, extra_opts + ["--no-use-extra-fc"])
        # no_fc_end_time = time.perf_counter();
        # no_fc_elapsed = no_fc_end_time - no_fc_start_time;
        # no_fc_check_safe = no_fc_res.splitlines()[-2].decode('utf-8');
        # no_fc_counts = get_opt_counts(no_fc_res);
        (_, _, _, no_fc_counts, no_fc_elapsed) = call_with_timing(file, timeout, extra_opts + ["--no-use-extra-fc"])

        no_lev_dec_counts = empty_counts()
        no_lev_dec_elapsed = None
        if counts["searched_below"] is not None and int(counts["searched_below"]) > 0:
            (_, _, _, no_lev_dec_counts, no_lev_dec_elapsed) = call_with_timing(file, timeout, extra_opts + ["--no-use-level-dec"])

        no_n_mdl_counts = empty_counts()
        no_n_mdl_elapsed = None
        if counts["negated_model"] is not None and int(counts["negated_model"]) > 0:
            (_, _, _, no_n_mdl_counts, no_n_mdl_elapsed) = call_with_timing(file, timeout, extra_opts + ["--no-use-negated-models"])

        return (check_safe, elapsed, funcs, depth, counts
                          , no_fc_elapsed, no_fc_counts
                          , no_lev_dec_elapsed, no_lev_dec_counts
                          , no_n_mdl_elapsed, no_n_mdl_counts);
    else:
        None

def call_with_timing(file, timeout, passed_args = []):
    start_time = time.perf_counter();
    (res, res_err) = call_infer_process(file, timeout, passed_args);
    end_time = time.perf_counter();
    elapsed = end_time - start_time;

    try:
        check_safe = res.splitlines()[-2].decode('utf-8')
        counts = get_opt_counts(res)
    except IndexError:
        counts = { "negated_model": None
                 , "searched_below" : None
                 , "backtracks": None
                 , "loop_count" : None }
        if res == "Timeout":
            check_safe = "Timeout";
        else:
            check_safe = "";

    elapsed = adj_time(check_safe, elapsed)

    return (check_safe, res, res_err, counts, elapsed)

def get_opt_counts(res):
    check_safe = res.splitlines()[-2].decode('utf-8')
    if check_safe == "Safe":
        negated_model = res.splitlines()[-3].decode('utf-8')
        searched_below = res.splitlines()[-4].decode('utf-8')
        backtrack_count = res.splitlines()[-5].decode('utf-8')
        loop_count = res.splitlines()[-6].decode('utf-8')

        counts = { "negated_model": negated_model
                 , "searched_below" : searched_below
                 , "backtracks": backtrack_count
                 , "loop_count" : loop_count }
    else:
        counts = { "negated_model": None
                 , "searched_below" : None
                 , "backtracks": None
                 , "loop_count" : None }
    return counts

def empty_counts():
    return { "negated_model": None
           , "searched_below" : None
           , "backtracks": None
           , "loop_count" : None }


def call_infer_process(file, timeout, passed_args = []):    
    try:
        code_file = open(file, "r");
        code = code_file.read();
        code_file.close();

        args_re = re.search("--\s*cmd_line\s*=\s*\(([^)]*)\)\s*", code);

        extra_args = [];
        if args_re and args_re.group(1):
            extra_args = [args_re.group(1)];

        timeout_re = re.search("--\s*timeout\s*=\s*([0-9]*)\s*", code);
        if timeout_re and timeout_re.group(1):
            timeout = timeout_re.group(1);

        timeout_sygus = "10"
        timeout_sygus_re = re.search("--\s*timeout-sygus\s*=\s*([0-9]*)\s*", code);
        if timeout_sygus_re and timeout_sygus_re.group(1):
            timeout_sygus = timeout_sygus_re.group(1);


        args = ["gtimeout", timeout, exe_name, file # ["gtimeout", timeout, "cabal", "run", "Inference", file
               , "--timeout-sygus", timeout_sygus]

        res = subprocess.run(args + extra_args + passed_args, capture_output = True);
        return (res.stdout, res.stderr);
    except subprocess.TimeoutExpired:
        res.terminate()
        return "Timeout"

def get_counts(file):
    args = ["cabal", "run", "Inference", file, "--", "--count"]

    res = subprocess.run(args, capture_output = True);
    depth = res.stdout.splitlines()[-2].decode('utf-8');
    funcs = res.stdout.splitlines()[-1].decode('utf-8');
    return (funcs, depth);

def adj_time(check_safe, time):
    if check_safe == "Safe":
        return time;
    else:
        return None;

def test_pos_folder(folder, timeout, extra_opts=[], skip = []):
    all_files = os.listdir(folder);
    num_files = count_files(all_files);
    safe_num = 0;

    log = []

    for file in all_files:
        if file in skip:
            continue;
        if file.endswith(".lhs") or file.endswith(".hs"):
            print(file);

            res = run_infer(os.path.join(folder, file), file, timeout, extra_opts);
            if res is not None:
                (check_safe, elapsed, funcs, depth, counts
                           , no_fc_elapsed, no_fc_counts
                           , no_lev_dec_elapsed, no_lev_dex_count
                           , no_n_mdl_elapsed, no_n_mdl_count) = res

                if check_safe == "Safe":
                    print("\tSafe - " + str(elapsed) + "s");
                    safe_num += 1
                elif check_safe == "Timeout":
                    print("\tTimeout")
                else:
                    # print("check_safe =" + repr(check_safe) + "|")
                    print("\tUnsafe")

                log.append((file, elapsed, funcs, depth, counts
                                , no_fc_elapsed, no_fc_counts
                                , no_lev_dec_elapsed, no_lev_dex_count
                                , no_n_mdl_elapsed, no_n_mdl_count))

    return (log, safe_num, num_files)

def test_neg_folder(folder, timeout):
    all_files = os.listdir(folder);
    num_files = count_files(all_files);
    safe_num = 0;

    for file in all_files:
        if file.endswith(".lhs") or file.endswith(".hs"):
            print(file);

            (check_safe, elapsed, _, _, _, _, _) = run_infer(os.path.join(folder, file), file, timeout);

            if check_safe == "Counterexample":
                print("\tCounterexample - " + str(elapsed) + "s");
                safe_num += 1
            elif check_safe == "Timeout":
                print("\tTimeout")
            else:
                print("\tUnsafe")

    return (safe_num, num_files)

def count_files(all_files):
    num_files = 0;
    for file in all_files:
        if file.endswith(".lhs") or file.endswith(".hs"):
            num_files += 1;

    return num_files

def create_table(log):
    print("\\begin{tabular}{| l | c | c | c | c | c |>{\\columncolor[gray]{0.8}} c | c |>{\\columncolor[gray]{0.8}} c | c |>{\\columncolor[gray]{0.8}} c | c |>{\\columncolor[gray]{0.8}} c |}");
    print("\\hline");
    print("  \multicolumn{3}{|c|}{}       & \\multicolumn{4}{|c|}{} & \\multicolumn{2}{|c|}{} & \\multicolumn{2}{|c|}{\# Level} & \\multicolumn{2}{|c|}{\# Negated} \\\\");
    print("  \multicolumn{3}{|c|}{}       & \\multicolumn{4}{|c|}{Time (s)} & \\multicolumn{2}{|c|}{\# Loop} & \\multicolumn{2}{|c|}{Decensions} & \\multicolumn{2}{|c|}{Models} \\\\ \\hline");
    print("File & Functions & Levels & EC & No EC  & No Lev Dec &  No Neg Models               & EC & No EC                    & EC & No EC                                 & EC & No EC \\\\ \\hline");

    for (file, elapsed, funcs, depth, counts
             , no_fc_time, no_fc_counts
             , no_lev_dec_elapsed, no_lev_dex_count
             , no_n_mdl_elapsed, no_n_mdl_count) in log:
        file_clean = file.replace("_", "\\_")
        if elapsed is not None:
            p_time = "{:.1f}".format(elapsed);
        else:
            p_time = "timeout"

        p_loop_count = val_or_NA(counts["loop_count"])
        p_backtracks = val_or_NA(counts["backtracks"])
        p_searched_below = val_or_NA(counts["searched_below"])
        p_negated_model = val_or_NA(counts["negated_model"])

        if no_fc_time is not None:
            p_no_fc_time = "{:.1f}".format(no_fc_time);
        else:
            p_no_fc_time = "timeout"

        if no_lev_dec_elapsed is not None:
            p_no_lev_dec_elapsed = "{:.1f}".format(no_lev_dec_elapsed);
        else:
            p_no_lev_dec_elapsed = "-"

        if no_n_mdl_elapsed is not None:
            p_no_n_mdl_elapsed = "{:.1f}".format(no_n_mdl_elapsed);
        else:
            p_no_n_mdl_elapsed = "-"

        p_no_fc_loop_count = val_or_NA(no_fc_counts["loop_count"])
        p_no_fc_loop_count = val_or_NA(no_fc_counts["backtracks"])
        p_no_fc_searched_below = val_or_NA(no_fc_counts["searched_below"])
        p_no_fc_negated_model = val_or_NA(no_fc_counts["negated_model"])

        print(file_clean  + " & " + funcs + " & " + depth + " & "
                                  + p_time + " & " + p_no_fc_time + " & " + p_no_lev_dec_elapsed + " & " + p_no_n_mdl_elapsed + " & "
                                  + p_loop_count + " & " + p_no_fc_loop_count + " & "
                                  + p_searched_below + " & " + p_no_fc_searched_below + " & "
                                  + p_negated_model + " & " + p_no_fc_negated_model
                                  + "\\\\ \\hline");

    print("\\end{tabular}");

def create_simple_table(log):
    print("\\begin{tabular}{| l | c | c | c | c | c | c | c |}");
    print("\\hline");
    print(" &  &  &  & & & \# Level & \# Negated \\\\ \\hline");
    print("File & Functions & Levels & Time (s) & \# Loops & \# Backtracks & Decensions & Models \\\\ \\hline");

    for (file, elapsed, funcs, depth, counts
             , no_fc_time, no_fc_counts
             , _, _
             , _, _) in log:
        file_clean = file.replace("_", "\\_")
        if elapsed is not None:
            p_time = "{:.1f}".format(elapsed);
        else:
            p_time = "timeout"

        p_loop_count = val_or_NA(counts["loop_count"])
        p_backtracks = val_or_NA(counts["backtracks"])
        p_searched_below = val_or_NA(counts["searched_below"])
        p_negated_model = val_or_NA(counts["negated_model"])

        if no_fc_time is not None:
            p_no_fc_time = "{:.1f}".format(no_fc_time);
        else:
            p_no_fc_time = "timeout"

        p_no_fc_loop_count = val_or_NA(no_fc_counts["loop_count"])
        p_no_fcbacktracks = val_or_NA(no_fc_counts["backtracks"])
        p_no_fc_searched_below = val_or_NA(no_fc_counts["searched_below"])
        p_no_fc_negated_model = val_or_NA(no_fc_counts["negated_model"])

        print(file_clean  + " & " + funcs + " & " + depth + " & "
                                  + p_time + " & " # + p_no_fc_time + " & "
                                  + p_loop_count + " & " # + p_no_fc_loop_count + " & "
                                  + p_backtracks + " & " # + p_no_fc_loop_count + " & "
                                  + p_searched_below + " & " # + p_no_fc_searched_below + " & "
                                  + p_negated_model # + " & " + p_no_fc_negated_model
                                  + "\\\\ \\hline");

    print("\\end{tabular}");

def val_or_NA(val):
    if val is not None:
        return val
    else:
        return "N/A"

def skip_list():
    return  [ "Queen.hs"
            , "Soli.hs"
            , "Twice.hs"]

def main():
    try:
        os.mkdir("logs");
    except:
        pass;

    # (log_test, safe_test, num_test) = test_pos_folder("tests/LiquidInf/Paper/Eval/Test", "240");
    # print(str(safe_test) + "/" + str(num_test) + " Safe");
    
    # log = log_test


    (log_book, safe_book, num_book) = test_pos_folder("tests/LiquidInf/Paper/Eval/Prop_Book_LIA_Inv", "240");
    print(str(safe_book) + "/" + str(num_book) + " Safe");

    (log_book_sets, safe_book_sets, num_book_sets) = test_pos_folder("tests/LiquidInf/Paper/Eval/Prop_Book_Sets", "240");
    print(str(safe_book_sets) + "/" + str(num_book_sets) + " Safe");

    (log_hw, safe_hw, num_hw) = test_pos_folder("tests/LiquidInf/Paper/Eval/Prop_HW", "240");
    print(str(safe_hw) + "/" + str(num_hw) + " Safe");

    (log_inv, safe_inv, num_inv) = test_pos_folder("tests/LiquidInf/Paper/Eval/Prop_LIA_Invented", "240");
    print(str(safe_inv) + "/" + str(num_inv) + " Safe");

    (log_sato, safe_sato, num_sato) = test_pos_folder("tests/LiquidInf/Paper/Eval/Sato", "240", skip = skip_list());
    print(str(safe_sato) + "/" + str(num_sato) + " Safe");

    (log_kmeans, safe_kmeans, num_kmeans) = test_pos_folder("tests/LiquidInf/Paper/Eval", "1080");
    print(str(safe_kmeans) + "/" + str(num_kmeans) + " Safe");


    log = log_book + log_book_sets + log_hw + log_inv + log_sato + log_kmeans

    create_table(log)
    create_simple_table(log)

if __name__ == "__main__":
    main()