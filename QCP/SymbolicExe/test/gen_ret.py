import os
import glob

def get_relative_path(path):
   return os.path.relpath(path, os.getcwd() + '/testcases')

directory = os.getcwd()

files = glob.glob(directory + '/testcases/**/*.c', recursive=True)

# make first
os.system('make')

for i, file in enumerate(files):
   files[i] = get_relative_path(file)

for i in range(1, 5):
   print('[generating stage ' + str(i) + '...]')
   flag = True
   for file in files:
      print('generating ' + file)
      path = './testcases/' + file
      command = f'ASAN_OPTIONS=detect_leaks=0 ./main < "{str(path)}" > test.ans -s ' + str(i)
      if os.system(command) != 0:
         print('generate failed: ' + file)
         flag = False
         continue
      mv_command = 'mv test.ans ' + path.replace('.c', '_' + str(i) + '.ans') + '>/dev/null'
      if os.system(mv_command) != 0:
         print('generate failed: ' + file)
         flag = False
         continue
