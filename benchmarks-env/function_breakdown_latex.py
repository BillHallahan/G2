#!/usr/bin/python3

import os
import re
import pprint
import sys
import statistics
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

times = []

handled = []

for file in onlyfiles:
    t = read_target(sys.argv[1], file)

    if (t.file_name, t.func_name) in handled:
        continue
    else:
        handled.append((t.file_name, t.func_name))

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
                stats[t.func_name]['occ'] += 1
        elif '0m\nERROR:\n\n' in outputstr:
            stats[t.func_name]['None'] += 1
            none += 1
        elif 'Abstract' in outputstr:
            add_time = True
            stats[t.func_name]['Abstract'] += 1
            abstract += 1
            stats[t.func_name]['occ'] += 1
        elif 'Concrete' in outputstr:
            add_time = True
            stats[t.func_name]['Concrete'] += 1
            concrete += 1
            stats[t.func_name]['occ'] += 1
        elif 'Timeout' in outputstr:
            add_time = True
            stats[t.func_name]['Timeout'] += 1
            timeout += 1
            stats[t.func_name]['occ'] += 1
        else:
            add_time = True
            # print(file)
            stats[t.func_name]['StepExhaustion'] += 1
            stepexhaustion += 1
            stats[t.func_name]['occ'] += 1
        
        tm = re.search("time = (\d+\.\d+)", outputstr)
        if tm is not  None and add_time:
            time = tm.group(1)
            stats[t.func_name]['Time'] += float(time)
            stats[t.func_name]['true_occ'] += 1
            times.append(float(time))

    total += 1
            

print('\\begin{tabular}{ | l | r | r | r | r | r | }')

print('\hline')

print('{: <20}& {: <20}& {: <20}& {: <20}& {: <20}& {: <20} \\\\'.format('Func.','Con.','Abs.','Time','Error','Avg.'))
print('{: <20}& {: <20}& {: <20}& {: <20}& {: <20}& {: <20} \\\\ \hline'.format('','','','out','','Time (s)'))

t_con = 0
t_abs = 0
t_timeout = 0
t_error = 0
t_time = 0

other_con = 0
other_abs = 0
other_timeout = 0
other_error = 0
other_time = 0
other_total = 0


CUT_OFF = 5

for key in stats:
    if (stats[key]['occ'] < CUT_OFF):
        other_con += stats[key]['Concrete']
        other_abs += stats[key]['Abstract']
        other_timeout += stats[key]['Timeout']
        other_error += stats[key]['Error']
        other_time += stats[key]['Time']
        other_total += stats[key]['true_occ']

        t_con += stats[key]['Concrete']
        t_abs += stats[key]['Abstract']
        t_timeout += stats[key]['Timeout']
        t_error += stats[key]['Error']
        t_time += stats[key]['Time']


for key in stats:
    if (stats[key]['Concrete'] != 0 or stats[key]['Abstract'] != 0 or stats[key]['Timeout'] != 0 or stats[key]['Error'] != 0 or stats[key]['StepExhaustion'] != 0) and stats[key]['occ'] >= CUT_OFF:
        c = stats[key]['Concrete'] + stats[key]['Abstract'] + stats[key]['Timeout'] + stats[key]['Error'] + stats[key]['StepExhaustion']
        

        t_con += stats[key]['Concrete']
        t_abs += stats[key]['Abstract']
        t_timeout += stats[key]['Timeout']
        t_error += stats[key]['Error']
        t_time += stats[key]['Time']

        print('{: <20}& {: <20}& {: <20}& {: <20}& {: <20}& {: <20} \\\\ \hline'.format(
            con_latex(key),
            stats[key]['Concrete'],
            stats[key]['Abstract'], stats[key]['Timeout'], 
            stats[key]['Error'], round(stats[key]['Time'] / stats[key]['true_occ'], 1)))

print('{: <20}& {: <20}& {: <20}& {: <20}& {: <20}& {: <20} \\\\ \hline'.format(
            "Other",
            other_con,
            other_abs, other_timeout,
            other_error, round(other_time / other_total, 1)))

print('\\textbf{{ {: <20} }}& \\textbf{{ {: <20} }}&\\textbf{{ {: <20} }}& \\textbf{{ {: <20} }}&\\textbf {{ {: <20} }}& \\textbf{{ {: <20} }} \\\\ \hline'.format(
            "Total",
            t_con,
            t_abs, t_timeout, 
            t_error, round(t_time / total, 1)))

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

print('\n')
print('median = ' + str(statistics.median(times)))
