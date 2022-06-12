#!/usr/bin/env python
# Tests G2's LiquidHaskell type Inference on all files in the ../LiquidInf directory

import os
import re
import subprocess
import time
import eval

def skip_list():
    return  [ "M02.hs"
            , "M19.hs"
            , "M20.hs"
            , "M21.hs"
            , "M22.hs"
            , "M29.hs"
            , "M32.hs"
            , "M33.hs"
            , "M34.hs"
            , "M36.hs"
            , "M40.hs"
            , "M42.hs"
            , "M45.hs"
            , "M46.hs"]
def main():
    try:
        os.mkdir("logs");
    except:
        pass;

    # (log_test, safe_test, num_test) = test_pos_folder("tests/LiquidInf/Paper/Eval/Test", "240");
    # print(str(safe_test) + "/" + str(num_test) + " Safe");
    
    # log = log_test


    (log_compare, safe_compare, num_compare) = eval.test_pos_folder("tests/LiquidInf/Paper/Eval/Compare", "600", ["--use-invs"], skip = skip_list());
    print(str(safe_compare) + "/" + str(num_compare) + " Safe");

    eval.create_table(log_compare)
    eval.create_simple_table(log_compare)

if __name__ == "__main__":
    main()
