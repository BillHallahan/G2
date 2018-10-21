#!/usr/bin/python3

import os

error_lh = []
error_g2 = []
no_error = []

count = 0

abstract = 0
concrete = 0
timeout = 0
step = 0

for fn in os.listdir("./benchmark-reports"):
    file = open("./benchmark-reports/" + fn)

    r = file.read()

    if r.find("G2") != -1:
        if r.find("ERROR OCCURRED IN LIQUIDHASKELL") != -1:
            error_lh.append(fn)
        else:
            error_g2.append(fn)
    else:
        no_error.append(fn)

        if r.find("Abstract") != -1:
            abstract += 1
        elif r.find("Concrete") != -1:
            concrete += 1
        elif r.find("Timeout") != -1:
            timeout += 1
        else:
            step += 1

    file.close()

    count += 1



print("No Error:")
print(no_error)

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