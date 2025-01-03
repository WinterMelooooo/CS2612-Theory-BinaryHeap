import re

class Count():
    def __init__(self) -> None:
        self.tot = 0
    
    def get_id(self):
        self.tot += 1
        return self.tot
    
class VarsGen():
    def __init__(self) -> None:
        self.temps = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'j', 'k', 'm', 'n', 'o','r','s', 'u', 'v', 'w', 'x', 'y', 'z']
        self.p = -1
    
    def get_var(self):
        self.p += 1
        return self.temps[self.p]

def read_definitions(path):
    with open(path, 'r') as file:
        contents = file.read()
    contents = contents.split('\n')
    # print(content)
    defs = []
    for content in contents:
        if content.find('/*') != -1:
            now_str = content
        elif content.find('*/') != -1:
            now_str += content
            defs.append(now_str)
        else:
            now_str += content
    # print(defs)
    return defs

def field_refine(items): # 把变量都变成 '_'
    new_items = []
    for item in items:
        # print("item:", item)
        if item.find('->') != -1:
            var = item[:item.find('->')]
            new_item = item.replace(var+'->', '_->')
        new_items.append(new_item)
    return new_items

def info_refine(info):
    new_info = {}
    new_info['predicate'] = [info['predicate']]
    new_info['type'] = info['type']
    new_info["struct_name"] = info["struct_name"]
    if 'link_field' in info:
        new_info['link_field'] = field_refine(info['link_field'])
    if 'link1_field' in info:
        new_info['link1_field'] = field_refine(info['link1_field'])
    if 'link2_field' in info:
        new_info['link2_field'] = field_refine(info['link2_field'])
    if 'parent_field' in info:
        new_info['parent_field'] = field_refine(info['parent_field'])
    if 'child_field' in info:
        new_info['child_field'] = field_refine(info['child_field'])
    new_info['data_field'] = field_refine(info['data_field'])
    new_info['nest_preds'] = field_refine(info['nest_preds'])
    return new_info

def check_list(info1, info2):
    info1['data_field'].sort()
    info1['nest_preds'].sort()

    print(info2)
    info2['data_field'].sort()
    info2['nest_preds'].sort()

    return info1['link_field'] == info2['link_field'] and info1['data_field'] == info2['data_field'] and info1['nest_preds'] == info2['nest_preds']

def get_pred_def(pred):
    matches = re.findall(r'(?<=\().*(?=\))', pred)
    # print(matches)
    args = []
    if matches:
        args = matches[0].split(',')
    def_str = '(' + pred[:pred.find('(')] + ' : ' + 'Z -> ' * len(args) + 'Assertion)'
    return def_str

def print_head_file(pre_path, info):
    file_name = info["struct_name"] + '_' + info['type'] + '_data' + str(len(info['data_field'])) + '_nest' + str(len(info['nest_preds']))
    with open(pre_path + file_name + '.h', 'w') as file:
        defs = '/*@ Extern Coq '
        for pred in info['predicate']:
            if defs != '/*@ Extern Coq ':
                defs += ' ' * 15
            defs += get_pred_def(pred) + '\n'
        if len(info['nest_preds']) > 0:
            for nest_pred in info['nest_preds']:
                nest = nest_pred[nest_pred.find(':') + 2 : ]
                if defs != '/*@ Extern Coq ':
                    defs += ' ' * 15
                defs += get_pred_def(nest)
        defs += ' */'
        print(defs + '\n', file=file)

        if info['type'] == 'list':
            print('/*@ Import Coq Require Import sll_shape_lib */\n', file=file)
        
        print('/*@ include strategies "' + file_name + '.strategies" */', file=file)
    return file_name + '.h'

def get_list_pred_name(preds): # 找到其中的listrep的为此名称以及lseg的谓词名称
    listrep, lseg = None, None
    for pred in preds:
        matches = re.findall(r'(?<=\().*(?=\))', pred)
        # print(matches)
        args = []
        if matches:
            args = matches[0].split(',')
        if len(args) == 1:
            listrep = pred[:pred.find('(')]
        else:
            lseg = pred[:pred.find('(')]
    return listrep, lseg

def get_nest_map(nest_preds): # 把 nest 的这个 " : " 格式解析出来
    nest = {}
    for nest_pred in nest_preds:
        x = nest_pred[: nest_pred.find(':')-1]
        y = nest_pred[nest_pred.find(':')+2 :]
        if x not in nest:
            nest[x] = []
        nest[x].append(y)
    return nest

def get_field_name(str): # _->xxx 返回 xxx
    return str[str.find('->')+2:]

def data_or_link(p, q, info, what_struct_name_is, only_link=False): # 返回下面这个式子
    # (data_at(field_addr(p, list, data), I32, ?q : Z) || data_at(field_addr(p, list, next), PTR(struct list), ?q : Z))
    nest = get_nest_map(info['nest_preds'])
    exps = []
    for link in info['link_field']:
        field_name = get_field_name(link)
        exps.append(f'data_at(field_addr({p}, {info["struct_name"]}, {field_name}), PTR(struct {info["struct_name"]}), {q} : Z)')
    if only_link:
        return exps[0]
    for data in info['data_field']:
        data_field = get_field_name(data)
        if data in nest:
            for nest_pred in nest[data]:
                nest_field = nest_pred[:nest_pred.find('(')]
                exps.append(f'data_at(field_addr({p}, {info["struct_name"]}, {data_field}), PTR(struct {what_struct_name_is[nest_field]}), {q} : Z)')
        else:
            exps.append(f'data_at(field_addr({p}, {info["struct_name"]}, {data_field}), I32, {q} : Z)')
    return '(' + ' || '.join(exps) + ')'

def expand(p, which_side, info, what_struct_name_is, current_actions, no_link=False): # 展开一个 list 谓词
    # p: 对于哪个变量展开
    # which_side: 在哪边添加
    # current_actions: 已有的 actions，在此基础上增加
    listrep, lseg = get_list_pred_name(info['predicate'])
    nest = get_nest_map(info['nest_preds'])
    actions = current_actions
    temps = VarsGen()
    if not no_link:
        for link in info['link_field']:
            field_name = get_field_name(link)
            exist_var = temps.get_var()
            actions.append(f'{which_side}_exist_add({exist_var} : Z)')
            # left_add(data_at(field_addr(p, list, tail), PTR(struct list), y));
            actions.append(f'{which_side}_add(data_at(field_addr({p}, {info["struct_name"]}, {field_name}), PTR(struct {info["struct_name"]}), {exist_var}))')
            # left_add(listrep(y));
            actions.append(f'{which_side}_add({listrep}({exist_var}))')
    for data in info['data_field']:
        field_name = get_field_name(data)
        if data in nest:
            for nest_pred in nest[data]:
                nest_field = nest_pred[:nest_pred.find('(')]
                exist_var = temps.get_var()
                actions.append(f'{which_side}_exist_add({exist_var} : Z)')
                # right_add(data_at(field_addr(p, listlist, data), PTR(struct list), x));
                actions.append(f'{which_side}_add(data_at(field_addr({p}, {info["struct_name"]}, {field_name}), PTR(struct {what_struct_name_is[nest_field]}), {exist_var}))')
                # right_add(listrep(x))
                actions.append(f'{which_side}_add({nest_field}({exist_var}))')
        else:
            exist_var = temps.get_var()
            actions.append(f'{which_side}_exist_add({exist_var} : Z)')
            # right_add(data_at(field_addr(p, list, data), I32, x));
            actions.append(f'{which_side}_add(data_at(field_addr({p}, {info["struct_name"]}, {field_name}), I32, {exist_var}))')
    return actions

def get_strategy_str(stra):
    return_str = ''
    for strategy in stra:
        return_str += 'id : ' + str(strategy['id']) + '\n'
        return_str += 'priority : ' + strategy['priority'] + '\n'
        if 'left' in strategy:
            return_str += 'left : '
            for i, left in enumerate(strategy['left']):
                if i != 0:
                    return_str += ' ' * 7
                return_str += left + '\n'
        if 'right' in strategy:
            return_str += 'right : '
            for i, left in enumerate(strategy['right']):
                if i != 0:
                    return_str += ' ' * 8
                return_str += left + '\n'
        return_str += 'action : '
        for i, action in enumerate(strategy['action']):
            if i != 0:
                return_str += ' ' * 9
            return_str += action + ';\n'
        return_str += '\n'
    return return_str

def get_list_strategy(info, what_struct_name_is):
    listrep, lseg = get_list_pred_name(info['predicate'])
    struct_name = info["struct_name"]
    stra = []
    """
    ---lseg---
    """
    # 左右的 null 删去
    """
    id : 3
    priority : core(0)
    left : listrep(NULL) at 0
    action : left_erase(0);
    """
    cnt = Count()
    # 两头的 listrep(null) 直接消去
    stra.append({'id': cnt.get_id(), 'priority': 'core(0)', 'left': [f'{listrep}(NULL) at 0'], 'action': ['left_erase(0)']})
    stra.append({'id': cnt.get_id(), 'priority': 'core(0)', 'right': [f'{listrep}(NULL) at 0'], 'action': ['right_erase(0)']})
    
    # id : 5
    # priority : core(0)
    # left : (?p : Z == NULL || NULL == ?p : Z) at 0
    # right : listrep(p) at 1
    # action : right_erase(1);
    stra.append({'id': cnt.get_id(), 'priority': 'core(0)', 'left': ['(?p : Z == NULL || NULL == ?p : Z) at 0'], 'right' : [f'{listrep}(p) at 1'], 'action': ['right_erase(1)']})
    stra.append({'id': cnt.get_id(), 'priority': 'core(0)', 'left': [f'{listrep}(?p : Z) at 0', '(p == NULL || NULL == p) at 1'], 'action': ['left_erase(0)']})

    # id : 7
    # priority : core(1)
    # left : listrep(?p : Z) at 0
    # right : listrep(p) at 1
    # action : left_erase(0);
    #         right_erase(1);
    # 左右一样的谓词消去
    stra.append({'id': cnt.get_id(), 'priority': 'core(1)', 'left': [f'{listrep}(?p : Z) at 0'], 'right' : [f'{listrep}(p) at 1'], 'action': ['left_erase(0)', 'right_erase(1)']})

    # id : 8
    # priority : core(4)
    # left : listrep(?p : Z) at 0
    #     (p != NULL || NULL != p) at 1
    # right : data_at(field_addr(p, list, tail), PTR(struct list), ?q : Z) at 2
    # action : left_erase(0);
    #         left_exist_add(x : Z);
    #         left_exist_add(y : Z);
    #         left_add(data_at(field_addr(p, list, tail), PTR(struct list), y));
    #         left_add(listrep(y));
    stra.append({'id': cnt.get_id(), 'priority': 'core(4)', 'left': [f'{listrep}(?p : Z) at 0', '(p != NULL || NULL != p) at 1'], 'right' : [data_or_link('p', '?q', info, what_struct_name_is)+' at 2'], 'action': expand('p', 'left', info, what_struct_name_is, ['left_erase(0)'])})

    # return get_strategy_str(stra)

    # id : 9
    # priority : core(4)
    # left : (?p : Z != NULL || NULL != ?p : Z) at 0
    # right : listrep(p) at 1
    # action : right_erase(1);
    #         right_exist_add(x : Z);
    #         right_exist_add(y : Z);
    #         right_add(data_at(field_addr(p, list, data), I32, x));
    #         right_add(data_at(field_addr(p, list, next), PTR(struct list), y));
    #         right_add(listrep(y));

    stra.append({'id': cnt.get_id(), 'priority': 'core(4)', 'left': ['(?p : Z != NULL || NULL != ?p : Z) at 0'], 'right' : [f'{listrep}(p) at 1'], 'action': expand('p', 'right', info, what_struct_name_is, ['right_erase(1)'])})

    # id : 10
    # priority : core(3)
    # left : lseg(?p : Z, ?q : Z) at 0
    # right : listrep(p) at 1 
    # action: left_erase(0);
    #         right_erase(1);
    #         right_add(listrep(q));
    stra.append({'id': cnt.get_id(), 'priority': 'core(3)', 'left': [f'{lseg}(?p : Z, ?q : Z) at 0'], 'right' : [f'{listrep}(p) at 1 '], 'action': ['left_erase(0)', 'right_erase(1)', f'right_add({listrep}(q))']})

    # id : 11
    # priority : core(4)
    # left : (data_at(field_addr(?p, list, data), I32, ?q : Z) || data_at(field_addr(?p, list, next), PTR(struct list), ?q : Z)) at 0
    #     (p != NULL || NULL != p) at 1
    # right : listrep(p) at 2
    # action : right_erase(2);
    #         right_exist_add(x : Z);
    #         right_exist_add(y : Z);
    #         right_add(data_at(field_addr(p, list, data), I32, x));
    #         right_add(data_at(field_addr(p, list, next), PTR(struct list), y));
    #         right_add(listrep(y));
    stra.append({'id': cnt.get_id(), 'priority': 'core(4)', 'left': [data_or_link('?p', '?q', info, what_struct_name_is) + ' at 0', '(p != NULL || NULL != p) at 1'], 'right' : [f'{listrep}(p) at 2 '], 'action': expand('p', 'right', info, what_struct_name_is, ['right_erase(2)'])})

    """
    ---lseg---
    """
    # id : 14
    # priority : core(0)
    # right : lseg(?p : Z, p) at 0
    #         listrep(p) at 1
    # action : right_erase(0);
    stra.append({'id': cnt.get_id(), 'priority': 'core(0)', 'right': [f'{lseg}(?p : Z, p) at 0', f'{listrep}(p) at 1'], 'action': ['right_erase(0)']})

    # id : 15
    # priority : core(0)
    # right : lseg(?p : Z, p) at 0
    #         data_at(field_addr(p, list, tail), PTR(struct list), ?q : Z) at 1
    # action : right_erase(0);
    stra.append({'id': cnt.get_id(), 'priority': 'core(0)', 'right': [f'{lseg}(?p : Z, p) at 0', data_or_link('p', '?q', info, what_struct_name_is) + ' at 1'], 'action': ['right_erase(0)']})

    # id : 16
    # priority : core(3)
    # left : lseg(?p : Z, ?q) at 0
    #         data_at(field_addr(q, list, tail), PTR(struct list), ?z : Z) at 1
    #         (q != NULL || NULL != q) at 2
    # right : lseg(p, z) at 3
    # action : left_erase(0);
    #         left_erase(1);
    #         right_erase(3);
    stra.append({'id': cnt.get_id(), 'priority': 'core(3)', 'left': [f'{lseg}(?p : Z, ?q) at 0', data_or_link('q', '?z', info, what_struct_name_is, True) + ' at 1', '(q != NULL || NULL != q) at 2'], 'right': [f'{lseg}(p, z) at 3'], 'action': expand('q', 'right', info, what_struct_name_is, ['left_erase(0)', 'left_erase(1)', 'right_erase(3)'], True)})
    return get_strategy_str(stra)

def print_strategies(info, pre_path, what_struct_name_is):
    file_name = info["struct_name"] + '_' + info['type'] + '_data' + str(len(info['data_field'])) + '_nest' + str(len(info['nest_preds']))
    if info['type'] == 'list':
        strategy = get_list_strategy(info, what_struct_name_is)
    with open(pre_path + file_name + '.strategies', 'w') as file:
        #include "verification_list.h"
        # include "verification_stdlib.h"
        print('#include "verification_list.h"', file=file)
        print('#include "verification_stdlib.h"', file=file)
        print('#include "' + file_name + '.h"\n', file=file)
        print(strategy, file=file)
    return file_name + '.strategies'


# print(get_pred_def('lseg(x, y)'))
# print_strategies()