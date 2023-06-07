# This is a script for finding Hackages that contain rewrite rules


import tarfile  # tar.gz file
import os  # file reading
import re  # regular epxression
import sys  # command line arguments
import shutil  # removing directory
# regular expression pattern
#regex = r'{.*-#\s*.*RULE.*\s#-.*}'
#pattern = re.compile(regex, re.DOTALL)
pattern = r'{-#[\s\S]*?RULES[\s\S]*?#-}'



def reading_info(directory):
    # nested folder
    print("We are currently reading " + directory + "\n")
    if os.path.isdir(directory):
        try:
            for file in os.listdir(directory):
                file_path = os.path.join(directory, file)
                result = reading_info(file_path)
                if(result):
                    return result
            return False
        except PermissionError:
            pass
    else:
        return reading_file(directory)

       
# reading file
# trying different technique for decoding 
def decode_file(file_path):
    encodings = ['utf-8','Latin-1','utf-16']
    for encoding in encodings:
        try:
            with open(file_path,'r',encoding=encoding) as file:
                content = file.read()
            return content
        except UnicodeDecodeError:
            pass
        except PermissionError:
            pass
    return None

def reading_file(file_path):
        print("We are currently reading file " + file_path + "\n")
        extensions = [".hs",".lhs",'.hsc']
        if any(file_path.endswith(ext) for ext in extensions):
                content = decode_file(file_path)
                # if we do find a rule
                if content == None: raise Exception("Need more decoding format.")
                find = re.search(pattern,content)
                if find:
                    with open('hackageRules1.txt', 'a+') as f:
                        print('we find a rule in ' + file_path + '\n')
                        f.write(file_path + "\n")
                    return True
        return False


# starter code for getting into the directory 
def starter(directory):
    # getting all the tar.gz file into a directory call contain_rules
    for filename in os.listdir(directory):
        full_path = os.path.join(directory, filename)
        if full_path.endswith(".tar.gz") and not full_path.endswith("bgzf-0.1.0.0.tar.gz"):
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
