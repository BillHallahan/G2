#!/usr/bin/python3

import os
import re
import pprint
import sys
from os import listdir
from os.path import isfile, join
from collections import defaultdict


class G2Target:
    def __init__(self, id, file_name, line_num, func_name, orig_error):
        self.orig_error = orig_error
        self.func_name = func_name
        self.line_num = line_num
        self.file_name = file_name
        self.id = id

    def get_file_hash(self):
        return "%s,%s" % (self.file_name, self.func_name)

    def __str__(self):
        return "%s\n%s\n%s\n%s\n%s\n" % (str(self.id), self.file_name, self.line_num, self.func_name, self.orig_error)


def read_target(dir, target):
    prior_f = open(os.path.join(dir, target))
    id = int(prior_f.readline())
    file_name = prior_f.readline().strip()
    line_num = prior_f.readline().strip()
    func_name = prior_f.readline().strip()
    orig_error = prior_f.readline().strip()
    prior_f.close()
    return G2Target(id, file_name, line_num, func_name, orig_error)

def con_latex(s):
    return s.replace("_","\_")

fixme = 0
badTarget = 0
LHerror = 0
error = 0
none = 0
abstract = 0
concrete = 0
timeout = 0
stepexhaustion = 0
total = 0
stats = defaultdict(lambda: defaultdict(int))
onlyfiles = [f for f in listdir(sys.argv[1]) if isfile(join(sys.argv[1], f))]
for file in onlyfiles:
    t = read_target(sys.argv[1], file)
    with open(join(sys.argv[1], file)) as wholeoutput:
        add_time = False

        outputstr = wholeoutput.read()
        if 'IS_FIXME' in outputstr:
            stats[t.func_name]['fixme'] += 1
            fixme += 1
        elif 'UNABLE TO TARGET FUNC' in outputstr:
            stats[t.func_name]['badTarget'] += 1 
            badTarget += 1
        elif 'G2: ' in outputstr:
            if 'ERROR OCCURRED IN LIQUIDHASKELL' in outputstr:
                stats[t.func_name]['LHError'] += 1
                LHerror += 1
            else:
                add_time = True
                stats[t.func_name]['Error'] += 1
                error += 1
        elif '0m\nERROR:\n\n' in outputstr:
            print(file)
            stats[t.func_name]['None'] += 1
            none += 1
        elif 'Abstract' in outputstr:
            add_time = True
            stats[t.func_name]['Abstract'] += 1
            abstract += 1
        elif 'Concrete' in outputstr:
            add_time = True
            stats[t.func_name]['Concrete'] += 1
            concrete += 1
        elif 'Timeout' in outputstr:
            add_time = True
            stats[t.func_name]['Timeout'] += 1
            timeout += 1
        else:
            add_time = True
            # print(file)
            stats[t.func_name]['StepExhaustion'] += 1
            stepexhaustion += 1
        
        tm = re.search("time = (\d+\.\d+)", outputstr)
        if tm is not  None and add_time:
            time = tm.group(1)
            stats[t.func_name]['Time'] += float(time)

    total += 1
            

print('\\begin{tabular}{ | l | c | c | c | c | c | }')

print('\hline')

print('{: <20}& {: <20}& {: <20}& {: <20}& {: <20}& {: <20} \\\\ \hline'.format('Func','Concrete','Abstract','Timeout','Error','Avg. Time (s)'))

for key in stats:
    if (stats[key]['Concrete'] != 0 or stats[key]['Abstract'] != 0 or stats[key]['Timeout'] != 0 or stats[key]['Error'] != 0 or stats[key]['StepExhaustion'] != 0):
        c = stats[key]['Concrete'] + stats[key]['Abstract'] + stats[key]['Timeout'] + stats[key]['Error'] + stats[key]['StepExhaustion']
        
        print('{: <20}& {: <20}& {: <20}& {: <20}& {: <20}& {: <20} \\\\ \hline'.format(
            con_latex(key),
            stats[key]['Concrete'],
            stats[key]['Abstract'], stats[key]['Timeout'], 
            stats[key]['Error'], round(stats[key]['Time'] / c, 1)))

print('\end{tabular}')

print('fixme')
print(fixme)
print('badTarget')
print(badTarget)
print('LHerror')
print(LHerror)
print('error')
print(error)
print('none')
print(none)
print('abstract')
print(abstract)
print('concrete')
print(concrete)
print('timeout')
print(timeout)
print('stepexhaustion')
print(stepexhaustion)
print('total')
print(total)
