# This script is used to modify the cabal file by change or add a build depends and ghc-option
# This script also builds a cabal.project  
# Three arguments needed:
# first argument is the python file
# second argument is the directory that contain all the package that contain rules
# third argument is the location of g2 in one's computer


import os 
import sys
import re
import tempfile

def changing_cabal(directory):
    found_ghc = False
    found_build = False
    extension_to_check = ['library','test-suite','executable']
    # common stanza: binding or expression reused in different parts of the module
    modularity = ['import'] 
    for root, dirs, files in os.walk(directory):
        for file_name in files:
            # process for replace cabal file 
            file_path = os.path.join(root,file_name)
            #print("The file_path is " + file_path)
            if file_path.endswith('.cabal'):
                # make a file directly in the directory where the cabal file is located: root?
                temp_path_info =  tempfile.mkstemp(dir=os.path.dirname(file_path))
                temp_path = temp_path_info[1]
                # writing information of the cabal file into a temp file and then replace the build depends
                try:
                    with open(file_path,'r') as file, open(temp_path,'a') as temp_file:
                        lines = file.readlines()
                        # reading two lines together 
                        for line,next_line in zip(lines,lines[1:]):
                            search_build_depends = re.search("Build-Depends:",line,re.IGNORECASE)
                            if search_build_depends:
                                print("The build-depends before update is " + line)
                                line = line.replace(search_build_depends.group(), search_build_depends.group() + " g2 >= 0.1.0.2, ",1)
                                print("The build-depends after update is " + line)
                                found_build = True
                            for extension in extension_to_check:
                                for module in modularity:
                                    if line.startswith(extension) and not next_line.startswith(module):
                             # finding the correct amount of whitespace to insert in the next line 
                                        without_whitespace = next_line.lstrip()
                                        whitespace_amount = len(next_line) - len(without_whitespace)
                                        line = line + "\n" + " " * whitespace_amount +  "ghc-options:  -fplugin=G2.Nebula -fplugin-opt=G2.Nebula:--limit -fplugin-opt=G2.Nebula:10" + "\n"
                                        print("Chaging line for ghc-option")
                                        print("the line after changing is " + line )
                                        found_ghc = True
                            # taking care of the common stanza case 
                            for module in modularity:
                                if line.startswith(module):
                                    without_whitespace = next_line.lstrip()
                                    whitespace_amount = len(next_line) - len(without_whitespace)
                                    line = line + "\n" + " " * whitespace_amount +  "ghc-options:  -fplugin=G2.Nebula -fplugin-opt=G2.Nebula:--limit -fplugin-opt=G2.Nebula:10" + "\n"
                                    print("Chaging line for ghc-option")
                                    print("the line after changing is " + line)
                                    found_ghc = True
                            temp_file.write(line)
                    #writing build-depends and ghc-option in case of not founding those
                    with open(temp_path, 'a+') as temp:
                        lines = temp.readlines()
                        if lines:
                            # format the ghc option and build-depends against previous line of the file
                            last_line = lines[-1]
                            last_line_whitespace = last_line.lstrip()
                            whitespace_amount = len(last_line) - len(last_line_whitespace)
                            if found_build == False:
                                print("build-depends not found \n")
                                write_line = whitespace_amount * " " + "build-depends: g2 >= 0.1.0.2 " + '\n'
                                temp.write(write_line)
                            if found_ghc == False:
                                print("ghc-option not found \n")
                                write_line = whitespace_amount * " " + "ghc-options:  -fplugin=G2.Nebula -fplugin-opt=G2.Nebula:--limit -fplugin-opt=G2.Nebula:10"
                                temp.write(write_line)
                    os.replace(temp_path, file_path)
                # checking for error just in case and left a error file in the directory 
                except BaseException:
                    os.remove(temp_path)
                    raise Exception("Problems in creating a file")

# cabal.project section 
# determine whether a cabal project exists
def determine_existence(directory):
    for root, dirs, files in os.walk(directory):
        for file_name in files:
            file_path = os.path.join(root,file_name)
            project_info =  os.path.split(file_path)
            project_name = project_info[1]
            if project_name.startswith('cabal.project'): return True
    return False
# making cabal project based on scenario
def changing_project(directory,g2_location):
    existence = determine_existence(directory)
    #not cabal.project
    if existence == False:
        print("making a cabal.project file in " + directory)
        temp_path_info =  tempfile.mkstemp(dir=os.path.dirname(directory))
        temp_path = temp_path_info[1]
        with open(temp_path,'w') as temp:
            temp.write('packages: . ' +  '\n' + '\t' + g2_location + '\n')
        os.rename(temp_path,directory+"/cabal.project")
        #print('Finished creating a cabal.project in ' + os.path.dirname(directory))
    # if there is one, simply adding a new line indicating the location of g2 in one's computer
    else:
        cabal_project = directory + '/cabal.project'
        print('we did have a cabal project in directory ' + directory)
        with open(cabal_project,'a') as file:
            file.write('\n' + 'packages: . ' +  '\n' + "\t" + g2_location + "\n")

def starter(home_directory,g2_location):
     for filename in os.listdir(directory):
        file_path = os.path.join(home_directory,filename)
        if os.path.isdir(file_path):
            print("going into a directory " + file_path)
            changing_cabal(file_path)
            changing_project(file_path,g2_location)





# main:
args = sys.argv
if len(args) != 3:
    raise Exception("Invalid number of commands provided. The first argument is the script name. The second argument is the directory contain all the package that have rules. The third argument describe g2's location in one's computer.")
directory = sys.argv[1]
g2_location = sys.argv[2]
starter(directory,g2_location)



