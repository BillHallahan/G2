#!/usr/bin/python3

import subprocess
import os
from tempfile import mkstemp
from shutil import move
from os import fdopen, remove
from ast import literal_eval
from multiprocessing.dummy import Pool

STUDY_DIR = './liquidhaskell-study/wi15/unsafe/'

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


def parse_target_data(t, id) -> G2Target:
    """
    Takes a set of lines from the LOG_CMD and parses them into reaonable target info for G2
    :param t: the target, array of lines from log command
    :return: the data structure representing the target
    """
    file_data = t[0].split(': Error')[0].split('/')[-1].split(':')
    file_name = file_data[0]

    if len(file_data) == 2:
        line_num = literal_eval(file_data[1].split('-')[0])
        func_name = get_first_word_at_line(file_name, line_num)
    else:
        line_num = (int(file_data[1]), file_data[2])
        func_name = t[1].split()[2]

    return G2Target(id, file_name, line_num, func_name, t)


def get_first_word_at_line(file_name, line_num):
    """
    Gets the first word on the specified line of the given file. Used for finding function names. Looks under
    STUDY_DIR
    :param file_name:  the name of the file
    :param line_num:  the line number
    :return: the function name.
    """
    with open(os.path.join(STUDY_DIR, file_name)) as fp:
        word = ''
        for i, line in enumerate(fp):
            if i == (line_num[0] - 1):
                word = line.split()[0]
    return word


def isolate_func_name(file_path, line_num):
    """
    Isolates a function name from a given line number in a file
    :param file_path:  the full path to the file
    :param line_num:  a line number of the function body in the file
    :return: the function name
    """
    f = open(file_path, 'r')
    lines = f.readlines()
    f.close()
    line_num -= 1  # Line is one more than expected
    line = lines[line_num]
    while 'where' not in line:
        line_num -= 1
        line = lines[line_num]
    line_num -= 1
    return lines[line_num].split()[0]

def replace(file_path, pattern, subst):
    #Create temp file
    fh, abs_path = mkstemp()
    with fdopen(fh,'w') as new_file:
        with open(file_path) as old_file:
            for line in old_file:
                new_file.write(line.replace(pattern, subst))
    #Remove original file
    remove(file_path)
    #Move new file
    move(abs_path, file_path)

def run_g2(g2_dir: str, test_dir: str, target_dir: str, recurs_n: int, target: G2Target, recurse):
    """
    Runs G2 on a target with the specified arguments
    :param g2_dir:  the directory of the G2 exe
    :param test_dir:  the dir of target file
    :param target_dir: the directory in which the target file is stored
    :param recurs_n:  the number of symbolic recursions to perform
    :param target:  the target of the exe
    :return: the string result of running G2 on the target
    """
    res = ''
    target_file = os.path.join(target_dir, target.file_name)

    is_fixme = False
    if is_fixme_target(target_file, target.func_name):
        is_fixme = True

    replace(target_file, ' Prop ', ' ')
    cmd = "./G2 %s -- --time 120 --n %d --liquid %s --liquid-func %s" % (
        test_dir, recurs_n, target_file, target.func_name
    )
    proc = subprocess.Popen(cmd, shell=True, encoding='UTF-8', cwd=g2_dir, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, stdin=subprocess.PIPE)
    proc.stdin.close()
    proc.wait()
    err = proc.stderr.read()
    if 'No functions with name' in err:
        if recurse:
            res = "UNABLE TO TARGET FUNC"
            return res
        target.func_name = isolate_func_name(target_dir + target.file_name, int(target.line_num[0]))
        print("FIXED FUNCTION NAME ERROR:")
        print(target.func_name)
        proc.stderr.close()
        proc.stdout.close()
        res = run_g2(g2_dir, test_dir, target_dir, recurs_n, target, True)
        return res
    res = proc.stdout.read() + "\nERROR:\n" + err
    if is_fixme:
        res = 'IS_FIXME\n' + res
    proc.stderr.close()
    proc.stdout.close()
    return res

def is_fixme_target(tFile, fName):
    with open(tFile) as fd:
        for line in fd:
            if fName in line and 'fixme' in line:
                return True
    return False

def create_report(data, directory, file_tag):
    """
    Creates a report file with the given data in the given directory with the given file tag. Files have the
    time created as well as the file tag for a name
    :param data: the report data to write
    :param directory:  the directory to write report data into
    :param file_tag:  the file tag for the file
    :return: None
    """
    if not os.path.exists(directory):
        os.makedirs(directory)
    file_name = "%s.log" % (file_tag)
    with open(os.path.join(directory, file_name), 'w', ) as report:
        report.write(data)


def run_liquid(target_dir, target):
    with open(os.path.join(target_dir, target.file_name + '.log')) as liq_out:
        return ('\nLIQUID_OUT:\n%s' % (liq_out.read()))


def create_g2_report(t: G2Target):
    """
    Creates a g2 report for a specified target
    :param t: the target to write the report for
    :return: None
    """
    g2_res = run_g2('.', './liquidhaskell-study/wi15/', './liquidhaskell-study/wi15/unsafe/', 2000, t, False)
    liquid_res = run_liquid('./liquidhaskell-study/wi15/unsafe/', t)
    print(t.id)
    create_report("%s\n%s\n%s" % (str(t), g2_res, liquid_res), 'benchmark-reports', "%s_%s" % (str(t.id), str(t.file_name)))

def collect_reports_deprecated():
    """
    Depricated manner of collecting reports; has issues since it does not adjust the number of reduction steps to
    G2
    :return: none
    """
    LOG_CMD = "grep -h -A2 'Liquid Type Mismatch' %s*.log" % STUDY_DIR

    # logs = subprocess.check_output(LOG_CMD, shell=True, encoding='UTF-8').split('--')
    logs = []
    for file in os.listdir(STUDY_DIR):
        if file.endswith(".log"):
            try:
                cmd = "grep -h -A2 'Liquid Type Mismatch' %s" % STUDY_DIR + file
                newlogs = subprocess.check_output(cmd, shell=True, encoding='UTF-8').split('--')
                logs.extend(newlogs)
            except:
                pass

    targets_raw = [x.split('\n') for x in logs]
    targets_raw = [[i for i in x if i.replace(' ', '') != ''] for x in targets_raw]
    targets_raw = [x for x in targets_raw if len(x) != 1]

    targets_avail = []
    try:
        with open('target_names.txt') as names:
            for line in names:
                targets_avail.append(line.strip())
    except Exception:
        pass

    targets_done = []
    try:
        with open('done.log') as donelog:
            for line in donelog:
                target_num = int(line.split('_')[0])
                targets_done.append(target_num)
    except Exception:
        pass

    targets = []
    files_and_funcs = []
    for i, t in enumerate(targets_raw):
        if i not in targets_done:
            parse_target = parse_target_data(t, i)
            file_hash = parse_target.get_file_hash()
            if ((parse_target.file_name in targets_avail or len(targets_avail) == 0)
                    and file_hash not in files_and_funcs):
                targets.append(parse_target)
                files_and_funcs.append(file_hash)
    print('Targets remaining: %d' % len(targets))

    # Targets are printed with four fields, and then two spaces and there is the G2 Report
    # for t in targets:
    #     create_g2_report(t)
    pool = Pool(4)
    results = pool.map(create_g2_report, targets)

if __name__ == '__main__':
    collect_reports_deprecated()

