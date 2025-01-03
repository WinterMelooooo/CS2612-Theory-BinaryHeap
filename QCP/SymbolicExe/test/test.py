import os
import glob

def get_relative_path(path):
   return os.path.relpath(path, os.getcwd() + '/testcases')

directory = os.getcwd()

files = glob.glob(directory + '/testcases/**/*.c', recursive=True)

failed_cases = []
passed_cases = []
result_file = open('test_result.txt', 'w')

# make first
os.system('make')

for i, file in enumerate(files):
   files[i] = get_relative_path(file)

for i in range(1, 5):
   failed_cases = []
   passed_cases = []
   print('[testing stage ' + str(i) + '...]')
   flag = True
   for file in files:
      print('testing ' + file)
      path = './testcases/' + file
      command = f'ASAN_OPTIONS=detect_leaks=0 ./main < "{str(path)}" > test.ans -s ' + str(i)
      if os.system(command) != 0:
         print('test failed: ' + file)
         flag = False
         failed_cases.append(file)
         continue
      diff_command = 'diff test.ans ' + path.replace('.c', '_' + str(i) + '.ans') + '>/dev/null'
      if os.system(diff_command) != 0:
         print('test failed: ' + file)
         flag = False
         failed_cases.append(file)
         continue
      else:
         passed_cases.append(file)
   if flag:
      print('stage ' + str(i) + ' passed')
   else:
      print('stage ' + str(i) + ' failed')
   result_file.write('[stage ' + str(i) + ' failed]\n')
   for case in failed_cases:
      result_file.write(case + '\n')
   result_file.write('\n[stage ' + str(i) + ' passed]\n')
   for case in passed_cases:
      result_file.write(case + '\n')
   result_file.write('\n')

failed_cases = []
passed_cases = []
print('[testing stage ' + str(5) + '...]')
flag = True
for file in files:
   print('testing ' + file)
   path = './testcases/' + file
   command = f'ASAN_OPTIONS=detect_leaks=0 ./main < "{str(path)}" -s ' + str(5)
   if os.system(command) != 0:
      print('test failed: ' + file)
      flag = False
      failed_cases.append(file)
      continue
   coqc_command = 'make test_coq2' + '>/dev/null'
   if os.system(coqc_command) != 0:
      print('test failed: ' + file)
      flag = False
      failed_cases.append(file)
      continue
   else:
      passed_cases.append(file)
if flag:
   print('coq accepted all programs')
else:
   print('state 5 failed')
result_file.write('[stage ' + str(5) + ' failed]\n')
for case in failed_cases:
   result_file.write(case + '\n')
result_file.write('\n[stage ' + str(5) + ' passed]\n')
for case in passed_cases:
   result_file.write(case + '\n')
result_file.write('\n')

os.system('rm test.ans')