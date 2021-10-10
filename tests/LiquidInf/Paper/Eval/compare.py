#!/usr/bin/env python
# Tests G2's LiquidHaskell type Inference on all files in the ../LiquidInf directory

import os
import re
import subprocess
import time
import eval

def main():
    try:
        os.mkdir("logs");
    except:
        pass;

    # (log_test, safe_test, num_test) = test_pos_folder("tests/LiquidInf/Paper/Eval/Test", "240");
    # print(str(safe_test) + "/" + str(num_test) + " Safe");
    
    # log = log_test


    (log_compare, safe_compare, num_compare) = eval.test_pos_folder("tests/LiquidInf/Paper/Eval/Compare", "300", []);
    print(str(safe_compare) + "/" + str(num_compare) + " Safe");

    (log_compare_res, safe_compare_res, num_compare_res) = eval.test_pos_folder("tests/LiquidInf/Paper/Eval/Compare", "300", ["--restrict-coeffs"]);
    print(str(safe_compare_res) + "/" + str(num_compare_res) + " Safe");

    eval.create_table(log_compare)
    eval.create_simple_table(log_compare)

if __name__ == "__main__":
    main()