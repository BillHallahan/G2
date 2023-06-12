# remember to use Build_cabal_and_project.py 
# on the package so the package will have a dependency on g2 before this script
# so we can run G2 using subprocess 
# This script just record the content of the resulting output after using g2 on package
import subprocess
import sys
import os 
import shutil

def using_subprocess(file_path):
    # chaging the working directory from home to the nested directory
 
        os.chdir(file_path)
        current_dir = os.path.abspath(file_path)
        # write the result to the file
        file = os.path.split(current_dir)
        file_name = file[1] +'.txt'
        source_path = os.getcwd() + '/' + file_name

        print("creating a file called in " + file_name + " in current directory " + os.getcwd())
        with open(file_name,'a') as file:
            # merging the standard out and standard error and redirecting them to the file 
            subprocess.run(['cabal','build'],text=True,stdout=file,stderr=subprocess.STDOUT)
           
        # changing back the home directory
        os.chdir('..')
        print('The source path is ' + source_path + '\n')
        # making a folder called g2_output
        dest_dir = './g2_output'  
        os.makedirs(dest_dir,exist_ok=True)
        os.chdir(dest_dir)
        dest_path = os.getcwd()
        file_name_in_g2 = file_name
        
        # making a same file we just make in g2_output so we could replace it 
        with open(file_name_in_g2, 'w') as file:
            file.write('there is something')
        dest_path = dest_path + '/' + file_name_in_g2
        print('The dest_path is ' + dest_path + '\n')  
        # now I am moving the file from the file_path to the g2's output folder 
        print("Destination path: ", dest_path + '\n')
        print("Source path is :" + source_path + '\n')
        shutil.move(source_path,dest_path)
        #changing back to the home directory 
        os.chdir("../..")
        print("We are in the home directory " + os.getcwd())
        


def starter(home_directory):
     for filename in os.listdir(home_directory):
        file_path = os.path.join(home_directory,filename)
        if os.path.exists(file_path):
            if os.path.isdir(file_path) and not file_path.endswith('g2_output'):
                print("going into a directory " + file_path)
                file_path_in_G2 = home_directory+"/g2_output/" +filename + '.txt'
                if not os.path.exists(file_path_in_G2):
                    using_subprocess(file_path)





# main:
args = sys.argv
if len(args) != 2:
    raise Exception("Invalid number of commands provided. The first argument is the script name. The second argument is the directory contain all the package that have rules.")
directory = sys.argv[1]
starter(directory)
