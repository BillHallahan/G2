#!/usr/bin/python3

import os

error_lh = []
error_g2 = []
no_error = []

abstract_counter = []
step_lim_hit = []
timeout_hit = []

count = 0

abstract = 0
concrete = 0
timeout = 0
step = 0

for_func = None

for fn in os.listdir("./benchmark-reports"):
    with open("./benchmark-reports/" + fn) as file:

        r = file.read()

        if r.find("Multiple specification") != -1:
            print(file)
            