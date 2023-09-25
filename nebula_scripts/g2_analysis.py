# Run g2_output script before running this script 
# This script analyze the file from g2_result folder
# This script aim to create a corresponding file for each file in g2_results' folder
# This scripts will do the following:
# # of verified rules
# # of counterexamples
# # of "limit hits" (don't know what the regular expression gonna be )
# # of errors from Nebula. (don't know what regular expression to used currently )
# total # of rules
import re
import sys
import os
counter_example = r"Counterexample\s*found" # of counterexamples 
verified  = r'verified' # of verified rules
checking = r'checking'# total # of rules

def starter(directory):
     actual_directory = os.getcwd() + '/' + directory
     os.chdir(actual_directory)
     for root, directories, files in os.walk(actual_directory):
        for file in files:
            file_path = os.path.join(root,file)
            file_name_analysis = os.path.basename(file_path)
            # get the parent directory 
            # so we can create a separate folder outside from the current directory to store files
            parent_dir = os.path.dirname(os.getcwd()) 
            print("The parent directory is " + parent_dir +'\n')
            file_path_analysis = parent_dir + '/g2_analysis/' + file_name_analysis
            if not os.path.exists(file_path_analysis):
                total_counter_example = 0
                total_verified = 0
                total_rule = 0
                with open(file_path,"r") as file:
                    # recording all the info per file
                    for line in file:
                        search_for_counter_example = re.search(counter_example,line,re.IGNORECASE)
                        search_verified = re.search(verified,line,re.IGNORECASE)
                        search_rule = re.search(checking,line,re.IGNORECASE)
                        if search_for_counter_example: total_counter_example += 1
                        if search_verified: total_verified += 1
                        if search_rule: total_rule += 1
                # checking to the upper directory and create a directory 
                os.chdir('..')
                print("We are currently in the home directory call "  + os.getcwd() + "\n")
                # store all those info in a file now 
                analysis_dir = './g2_analysis'  
                os.makedirs(analysis_dir,exist_ok=True)
                os.chdir(analysis_dir)
                print("After changing directory, we are in directory " + os.getcwd() + "\ns")
                with open(file_name_analysis,"a") as file:
                    file.write("Total counter example found in this file: " + str(total_counter_example) + "\n")
                    file.write("Total verified rules found in this file " + str(total_verified) + "\n")
                    file.write("Total rules in this file is " + str(total_rule) + "\n")
                # now I am changing back to the root directory so we can continue reading
                os.chdir(actual_directory)
                

# main:
args = sys.argv
if len(args) != 2:
    raise Exception("Invalid number of commands provided. The first argument is the script name. The second argument is the directory contain all the file that stored the output and error after running with cabal build.")
directory = sys.argv[1]
starter(directory)