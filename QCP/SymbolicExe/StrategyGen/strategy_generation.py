import json
import argparse
import os

from utilities import *
from predicate_recognition import *

parser = argparse.ArgumentParser()
parser.add_argument('--name', type = str, default = 'listlist_app', help = 'file name of the C code')
parser.add_argument('--check', type = bool, default = False, help = 'whether to check the strategy')

args = parser.parse_args()

all_file_name = args.name
definitions = read_definitions(f'./PredicateInput/{all_file_name}_def.c')

Lists = {}
what_struct_name_is = {}
for definition in definitions:
    recognize(definition)

    info = {}
    with open('recognized_info.json', 'r') as file:
        info = json.load(file)
    
    # print(info)
    info = info_refine(info)
    # print(info)
    struct_name = info['struct_name']
    what_struct_name_is[info['predicate'][0][:info['predicate'][0].find('(')]] = struct_name
    duplicate = False
    if not struct_name in Lists:
        Lists[struct_name] = info
    else:
        Lists[struct_name]['predicate'].append(info['predicate'][0])

# print(Lists)
# print(what_struct_name_is)

headfiles_nest = []
headfiles = []

for _, List in Lists.items():
    file_name = print_head_file('./GeneratedStrategy/', List)
    if 'nest_preds' in List and len(List['nest_preds']) > 0:
        headfiles_nest.append(file_name)
    else:
        headfiles.append(file_name)
    print_strategies(List, './GeneratedStrategy/', what_struct_name_is)

# print("?????", all_file_name)
with open(f'./GeneratedStrategy/{all_file_name}.h', 'w') as file:
    for headfile in headfiles_nest:
        print('#include "' + headfile + '"', file=file)
    for headfile in headfiles:
        print('#include "' + headfile + '"', file=file)


# check

if args.check:
    os.chdir('../test/')
    os.system(f'build/symexec --goal-file=../../SeparationLogic/examples/{all_file_name}_goal.v --proof-auto-file=../../SeparationLogic/examples/{all_file_name}_proof_auto.v --proof-manual-file=../../SeparationLogic/examples/{all_file_name}_proof_manual.v --input-file=../StrategyGen/GeneratedStrategy/{all_file_name}.c')