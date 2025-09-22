# This is a script for is a modification from ScriptForHackageRules2.py
# This script aims to find file that contain GADTs
# Note: to enable GADTs, one must use langauges extension:
# For example: {-# LANGUAGE GADTs #-}
# This script along with nebula_scripts/ScriptForHackageRules2.py
# should be the first step toward dealing with downloaded Hackage
# b/c we are openning the tar.gz folder within the scripts

import tarfile  # tar.gz file
import os  # file reading
import re  # regular epxression
import sys  # command line arguments
import shutil  # removing directory
import requests
from bs4 import BeautifulSoup

# regular expression pattern
pattern = r'{-#\s*LANGUAGE[\s\S]*?\bGADTs\b[\s\S]*?#-}'

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
        extensions = [".hs",".lhs",'.hsc', '.cabal']
        found_gadt = False 
        if any(file_path.endswith(ext) for ext in extensions):
                content = decode_file(file_path)
                # if we do find a GADT
                if content == None: raise Exception("Need more decoding format.")
                # Case 1: .hs/.lhs/.hsc → search for explicit GADT usage (your old pattern)
                if file_path.endswith((".hs", ".lhs", ".hsc")):
                    if re.search(pattern, content):
                        found_gadt = True

                # Case 2: .cabal → look for "default-extensions:" line with GADTs in it
                elif file_path.endswith(".cabal"):
                    # Regex: match "default-extensions:" followed by anything, then "GADTs", then maybe more
                    cabal_pattern = re.compile(r"default-extensions\s*:\s*.*\bGADTs\b.*", re.IGNORECASE)
                    if cabal_pattern.search(content):
                        found_gadt = True
                        
                if found_gadt:
                    # Extract correct top-level package folder
                    parts = file_path.split(os.sep)
                    package_name = parts[2]
                    # remove version suffix b/c you will get 404 in searching when you try to search for it
                    package_name = re.sub(r"-\d+(\.\d+)*$", "", package_name)
                    with open('hackageGADTs1.txt', 'a+') as f:
                        print(f"we find a GADT in {file_path}\n")
                        print(f"The home directory is {package_name}")
                        download_num = get_hackage_downloads(package_name)
                        f.write(f"{file_path} has download number of {download_num}\n")
                    return True       
        return False

def get_hackage_downloads(package: str) -> str:
    """
    Given a Hackage package name, we want to return the download count as a string.
    Example: get_hackage_downloads("aeson") -> "1358456"
    """
    url = f"https://hackage.haskell.org/package/{package}"
    r = requests.get(url)
    r.raise_for_status()

    soup = BeautifulSoup(r.text, "html.parser")

    downloads_tag = soup.find("th", string="Downloads")
    if downloads_tag:
        full_text = downloads_tag.find_next("td").text.strip()
        # Extract the number at the beginning 
        # b/c the download number also include download within last 30 days which we don't care
        match = re.match(r"(\d+)", full_text)
        if match:
            return match.group(1)
        else:
            return "N/A"
    else:
        return "N/A"

# starter code for getting into the directory 
def starter(directory):
    # getting all the tar.gz file into a directory call contain_gadt
    for filename in os.listdir(directory):
        full_path = os.path.join(directory, filename)
        if full_path.endswith(".tar.gz") and not full_path.endswith("bgzf-0.1.0.0.tar.gz"):
            with tarfile.open(full_path, "r:gz") as tar:
                tar.extractall(path = "./contain_gadt")
                #I am moving everything into a new folder call contain_gadt
                tar_name =  os.path.split(tar.name)
                file_name = tar_name[1]
                file_path = "./contain_gadt/" + file_name[:-7]
                # now I am testing which package contain gadt in them 
                result = reading_info(file_path)
                if result == False: 
                    shutil.rmtree(file_path)
        

# "main"
args = sys.argv
if len(args) != 2:
    raise Exception("Invalid number of commands provided. The first argument is the script name. The second argument is the name of the directory contain all of the download hackage")
with open("./hackageGADTs1.txt", 'w') as file:
    file.truncate()
directory = sys.argv[1]
starter(directory)