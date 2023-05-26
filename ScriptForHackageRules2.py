# This is a script for finding Hackages that contain rewrite rules


import tarfile  # tar.gz file
import os  # file reading
import re  # regular epxression
import sys  # command line arguments
import shutil  # removing directory
# regular expression pattern
pattern = r"{-# RULE.*#-}"


def reading_info(directory):
    # nested folder 
    if os.path.isdir(directory):
        for file in os.listdir(directory):
            file_path = os.path.join(directory, file)
            result = reading_info(file_path)
            if(result):
                return result
        return False
    else:
        return reading_file(directory)

# reading file
def reading_file(file_path):
        with open(file_path, "r") as file:
            content = file.read()
            # if we do find a rule
            if re.search(pattern, content):
                path = os.path.split(file_path)
                duplicate = path[0]
                with open('hackageRules1.txt', 'a+') as f:
                    f.seek(0)
                    file_content = f.read()
                    if duplicate not in file_content:
                        print("We found a rule in " + duplicate + "\n")
                        f.write(duplicate + "\n")
                return True
        return False

# starter code for getting into the directory 
def starter(directory):
    # getting all the tar.gz file into a directory call contain_rules
    for filename in os.listdir(directory):
        full_path = os.path.join(directory, filename)
        if full_path.endswith(".tar.gz"):
            with tarfile.open(full_path, "r:gz") as tar:
                tar.extractall(path = "./contain_rules")
                #I am moving everything into a new folder call contain_rule
                tar_name =  os.path.split(tar.name)
                file_name = tar_name[1]
                file_path = "./contain_rules/" + file_name[:-7]
                # now I am testing which package contain rules in them 
                result = reading_info(file_path)
                if result == False: 
                    shutil.rmtree(file_path)


# "main"
args = sys.argv
if len(args) != 2:
    raise Exception("Invalid number of commands provided.")
with open("./hackageRules1.txt", 'w') as file:
    file.truncate()
directory = sys.argv[1]
starter(directory)
