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


stats = defaultdict(lambda: defaultdict(int))
onlyfiles = [f for f in listdir(sys.argv[1]) if isfile(join(sys.argv[1], f))]
for file in onlyfiles:
    t = read_target(sys.argv[1], file)
    with open(join(sys.argv[1], file)) as wholeoutput:
        outputstr = wholeoutput.read()
        if 'G2: ' in outputstr:
            if 'ERROR OCCURRED IN LIQUIDHASKELL' in outputstr:
                stats[t.func_name]['LHError'] += 1
            else:
                stats[t.func_name]['Error'] += 1
                print(file)
        elif '0m\nERROR:\n\n' in outputstr:
            stats[t.func_name]['None'] += 1
        elif 'Abstract' in outputstr:
            stats[t.func_name]['Abstract'] += 1
        elif 'Concrete' in outputstr:
            stats[t.func_name]['Concrete'] += 1
        elif 'Timeout' in outputstr:
            stats[t.func_name]['Timeout'] += 1
        else:
            stats[t.func_name]['StepExhaustion'] += 1
            


print('{: <20}\t{: <20}\t{: <20}\t{: <20}\t{: <20}\t{: <20}\t{: <20}\t{: <20}'.format('Func','LHError', 'Error','None','Abstract','Concrete','Timeout', 'Step Exhaustion'))

for key in stats:
    print('{: <20}\t{: <20}\t{: <20}\t{: <20}\t{: <20}\t{: <20}\t{: <20}\t{: <20}'.format(
        key, stats[key]['LHError'], stats[key]['Error'],
        stats[key]['None'], stats[key]['Abstract'],
        stats[key]['Concrete'], stats[key]['Timeout'], stats[key]['StepExhaustion']
    ))
