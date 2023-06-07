# This script is used to modify the cabal file by change or add a build depends and ghc-option
# This script also builds a cabal.project  
# Three arguments needed:
# first argument is the python file
# second argument is the directory that contain all the package that contain rules
# third argument is the location of g2 in one's computer so we can 
import os 
import sys
import re
import tempfile

def changing_cabal(directory):
    found_ghc = False
    found_build = False
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
                        for line in file:
                            search_build_depends = re.search("Build-Depends:",line,re.IGNORECASE)
                            if search_build_depends:
                                print("The build-depends before update is " + line)
                                line = line.replace(search_build_depends.group(), search_build_depends.group() + " g2 >= 0.1.0.2 ",1)
                                print("The build-depends after update is " + line)
                                found_build = True
                            search_ghc_option = re.search("ghc-options:",line,re.IGNORECASE)
                            if  search_ghc_option:
                                print('the ghc before update is ' + line + '\n')
                                line = line.replace(search_ghc_option.group(), search_ghc_option.group() + "  -fplugin=G2.Nebula -fplugin-opt=G2.Nebula:--limit -fplugin-opt=G2.Nebula:10 ",1) + '\n'
                                print("the ghc option after update is " + line)
                                found_ghc = True
                            temp_file.write(line)
                    #writing build-depends and ghc-option in case of not founding those
                    with open(temp_path, 'a+') as temp:
                        if found_build == False:
                            print("build-depends not found \n")
                            temp.write( "build-depends: g2 >= 0.1.0.2 " + '\n')
                        if found_ghc == False:
                            print("ghc-option not found \n")
                            temp.write("ghc-options:  -fplugin=G2.Nebula -fplugin-opt=G2.Nebula:--limit -fplugin-opt=G2.Nebula:10")
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
            temp.write("packages: " + g2_location + "\n")
        os.rename(temp_path,directory+"/cabal.project")
        #print('Finished creating a cabal.project in ' + os.path.dirname(directory))
    # if there is one, simply adding a new line indicating the location of g2 in one's computer
    else:
        cabal_project = directory + '/cabal.project'
        print('we did have a cabal project in directory ' + directory)
        with open(cabal_project,'a') as file:
            file.write('\n' + 'packages: ' + g2_location + '\n')

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
    raise Exception("Invalid number of commands provided.")
directory = sys.argv[1]
g2_location = sys.argv[2]
starter(directory,g2_location)



