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
        lines = r.splitlines()

        if len(lines) < 3 or lines[3] != "foldr1":
            continue

        if r.find("G2") != -1:
            if r.find("ERROR OCCURRED IN LIQUIDHASKELL") != -1:
                error_lh.append(fn)
            else:
                error_g2.append(fn)
        else:
            no_error.append(fn)

            if r.find("Abstract") != -1:
                abstract_counter.append(fn)
                abstract += 1
            elif r.find("Concrete") != -1:
                concrete += 1
            elif r.find("Timeout") != -1:
                timeout_hit.append(fn)
                timeout += 1
            else:
                step_lim_hit.append(fn)
                step += 1

        file.close()

        count += 1

print("No Error:")
print(no_error)

print("Step limit hit:")
print(step_lim_hit)

print("Timeout hit:")
print(timeout_hit)

print("Error LH:")
print(error_lh)

print("Error G2:")
print(error_g2)

print("Total No Error = " + str(len(no_error)))
print("Total Error LH = " + str(len(error_lh)))
print("Total Error G2 = " + str(len(error_g2)))
print("Total = " + str(count))

print("\n")
print("Concrete = " + str(concrete))
print("Abstract = " + str(abstract))
print("Timeout = " + str(timeout))
print("Step Limit = " + str(step))