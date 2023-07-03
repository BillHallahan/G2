# This script is used to build a cabal project within a directory that contain 
# first argument contain the path to a directory that contain all the package
# second argument contain the location of g2 in one's computer 
import os 
import sys
import tempfile

# determine whether a cabal project exists
def determine_existence(directory):
    for root, dirs, files in os.walk(directory):
        for file_name in files:
            file_path = os.path.join(root,file_name)
            project_info =  os.path.split(file_path)
            project_location = project_info[1]
            #print("We are currently in files " + project_location + '\n')
            if project_location.startswith('cabal.project'): return True
    return False
# making cabal project based on scenario
def changing_project(directory,g2_location):
    existence = determine_existence(directory)
    if existence == False:
        print("making a temp file \n")
        temp_path_info =  tempfile.mkstemp(dir=os.path.dirname(directory))
        temp_path = temp_path_info[1]
        with open(temp_path,'w') as temp:
            temp.write("packages: " + g2_location)
        os.rename(temp_path,directory+"/cabal.project")
        print('Finished creating a cabal.project \n')
    else:
        cabal_project = directory + '/cabal.project'
        print('we did have a cabal project \n')
        with open(cabal_project,'w') as file:
            file.write('package: ' + g2_location)


def starter(home_directory, g2_location):
    print('In home directory ' + home_directory + '\n')
    for filename in os.listdir(home_directory):
        file_path = os.path.join(home_directory,filename)
        if os.path.isdir(file_path):
            print("going into a directory " + file_path + '\n')
            changing_project(file_path,g2_location)





#main:
args = sys.argv
if len(args) != 3:
    raise Exception("Invalid number of commands provided.\n The first argument is the directory contain all the folder of Hackage.\n The second argument contain g2's location on your computer")

home_directory = sys.argv[1]
g2_info = sys.argv[2]
starter(home_directory,g2_info)