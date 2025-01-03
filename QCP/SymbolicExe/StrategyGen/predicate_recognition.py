import re
import json

# # test re:
# str = "a23b\na34b\na123b"
# print(re.findall(r"^a(\d+)b", str))

all_pred_types = ['struct', 'list', 'dlist', 'listbox', 'NFtree', 'NFptree', 'tree', 'ptree']

def check_vars(pred, link_vars): # 谓词 pred 里面如果一个都没有出现 link_vars 的任何一个，返回true
    for link_var in link_vars:
        pattern = rf'(?<![\w]){re.escape(link_var)}(?![\w])'
        if re.search(pattern, pred) is not None:
            return False
    return True

def trans_data_at_with_field_addr(pred): # 把 data_at(field_addr(x, y), z) 转成 x->y==z
    x = re.findall(r'field_addr\(([^\),]+)', pred)[0]
    y = re.findall(r'field_addr\([^,]+,([^)]*)\)', pred)[0]
    z = re.findall(r'field_addr\([^)]*\),([^)]*)\)', pred)[0]
    x = x.replace(' ','')
    y = y.replace(' ','')
    z = z.replace(' ','')
    return x, y, z

def trans_data_at(pred): # 把 data_at(x, y) 转成 *x == y
    matches = re.findall(r'(?<=\()[^()]+(?=\))', pred)
    x = ''
    y = ''
    if matches:
        args = matches[0].split(',')
        x = args[0].replace(' ', '')
        y = args[1].replace(' ', '')
    return x, y

def recognize(definition_string) -> None:
    str = definition_string
    str = str.replace('\n', ' ')

    # '/*@ '和'*/'里面的内容
    str = re.findall(r'\/\*@\s([\s\S]*?)\*\/', str)
    str = str[0]
    struct_name = str[:str.find(')')+1]
    struct_name = re.findall(r'struct\s*([^\)]*?)\)', struct_name)[0]
    definition = str[str.find(')')+2:] #谓词定义

    print("def:", definition)
    # print("struct_name:", struct_name)
    predicates = re.findall(r'\S+\([^\(\)]*\)(?!,)', definition) #找出所有谓词
    # print(predicates)
    predicate = predicates[0] # 当前定义的谓词

    predicate_name = re.findall(r'.*(?=\()', predicate)[0] #谓词的名称

    # print("predicate_name:", predicate_name)

    matches = re.findall(r'(?<=\()[^()]+(?=\))', predicate)
    predicate_args = []
    if matches:
        args = matches[0].split(',')
        for arg in args:
            predicate_args.append(arg.replace(' ', ''))

    # print("predicate_args:", predicate_args)

    branches = definition.split('||') # 每个 || 间隔开的东西单独拿出来
    if branches[0].find('exists') == -1:
        branches = branches[1:]

    link_field = []
    data_field = []
    nest_preds = []
    other_field = []
    mark = {}
    nest_field = {} # nest_preds 指向是哪个域
    pred_type = ''

    for s in branches:
        matches = re.findall(r'exists\s+([^,]+),', s) # exist后面的变量
        temp_vars = []
        if matches:
            temp_vars = matches[0].split()
        # print("temp_vars:", temp_vars)
        matches = re.findall(r'exists[^,]*,(.*)', s)
        preds_ = matches[0].split('*')
        preds = []
        for pred in preds_:
            tmp = pred.replace(' ','')
            preds.append(tmp.replace('\t', ''))
        # print("preds:", preds) # 当前分支里面所有谓词
        link_vars = []
        for pred in preds:
            if pred.find(predicate_name) != -1: # 找到迭代的那个谓词
                # print("pred:", pred)
                matches = re.findall(r'(?<=\().*(?=\))', pred)
                # print("matches:", matches)
                next_args = []
                if matches:
                    args = matches[0].split(',')
                    for arg in args:
                        next_args.append(arg.replace(' ', ''))
                # print("next_args:", next_args)
                for arg in next_args:
                    if not arg in predicate_args:
                        link_vars.append(arg)
                        if arg in temp_vars:
                            temp_vars.remove(arg)
        # print("link_vars:", link_vars)

        new_preds = []
        cur_link_field = []
        for pred in preds:
            if pred.find('data_at') != -1 and pred.find('field_addr') == -1: # data_at(x, p) 二阶指针
                x, y = trans_data_at(pred) # *x == y
                if x in predicate_args and y in temp_vars:
                    pred_type = 'listbox'
                continue
            if check_vars(pred, link_vars): # 不包含有link_vars其中任何一个变量
                new_preds.append(pred)
            elif pred.find('data_at') != -1:
                x, y, z = trans_data_at_with_field_addr(pred)
                if x in predicate_args or z in predicate_args: # 是link_field
                    cur_link_field.append(x + "->" + y)
                    mark[x+'->'+y] = 'link'
                else:
                    new_preds.append(pred)

        # print("cur_link_field:", cur_link_field)
        for link in cur_link_field:
            if link not in link_field:
                link_field.append(link)
        # print(new_preds)
        if pred_type == 'listbox':
            for link_var in link_vars:
                if link_var not in link_field:
                    link_field.append(link_var)

        # 除了link_field，其他所有的field
        new_new_preds = new_preds.copy()
        for pred in new_preds:
            if pred.find('data_at') == -1: # 嵌套了其他谓词
                new_new_preds.remove(pred)
                other_pred_name = re.findall(r'.*(?=\()', pred)[0] #谓词的名称
                # print("other_pred_name:", other_pred_name)

                matches = re.findall(r'(?<=\()[^()]+(?=\))', pred)
                other_pred_args = []
                if matches:
                    args = matches[0].split(',')
                    for arg in args:
                        other_pred_args.append(arg.replace(' ', ''))
                for arg in other_pred_args:
                    if arg not in predicate_args:
                        other_var = arg
                        temp_vars.remove(other_var)
                
                # print("other_pred_args:", other_pred_args)

                for _pred in new_preds:
                    if _pred.find('data_at') != -1 and not check_vars(_pred, [other_var]):
                        x, y, z = trans_data_at_with_field_addr(_pred)
                        if z == other_var:
                            nest_preds.append(x+'->'+y+' : '+pred.replace(other_var, x+'->'+y))
                            nest_field[pred.replace(other_var, x+'->'+y)] = x+'->'+y
                            if x+'->'+y not in mark:
                                mark[x+'->'+y] = 'data'
                        new_new_preds.remove(_pred)
        # print("temp_vars:", temp_vars)
        # print("new_new_preds:", new_new_preds)

        for pred in new_new_preds: # 全是 data_at
            if not check_vars(pred, temp_vars): # data_at 中的变量在存在量词里
                x, y, z = trans_data_at_with_field_addr(pred)
                temp_vars.remove(z)
                if x+'->'+y not in data_field:
                    data_field.append(x+'->'+y)
                    if x+'->'+y not in mark:
                        mark[x+'->'+y] = 'data'
            else:
                x, y, z = trans_data_at_with_field_addr(pred)
                if x+'->'+y not in other_field:
                    other_field.append(x+'->'+y)
                    mark[x+'->'+y] = 'link'
    
    # print("other_fields:", other_field)

    for key, value in mark.items():
        # print(key, ':', value)
        if value == 'data':
            if key not in data_field:
                data_field.append(key)

    if len(link_field) == 0:
        pred_type = 'struct' # 无迭代
        data_field.append(definition[definition.find('=')+2:]) # 全部放进 data_field

    if pred_type == '':
        if len(link_field) + len(other_field) == 1:
            pred_type = 'list'
        elif len(link_field) == 1 and len(other_field) == 1:
            pred_type = 'dlist'
        elif len(link_field) + len (other_field) == 2: # NFtree
            if nest_preds == []:
                pred_type = 'NFtree'
            else:
                pred_type = 'NFptree'
        else: # tree
            if nest_preds == []:
                pred_type = 'tree'
            else:
                pred_type = 'ptree'

    info = {}

    print("struct_name:", struct_name)
    info['struct_name'] = struct_name

    print("predicate:", predicate)
    info['predicate'] = predicate

    if pred_type in all_pred_types:
        print("type:", pred_type)
        info['type'] = pred_type
        if pred_type == 'struct':
            print("data_field:", data_field)
            info['data_field'] = data_field
        elif pred_type in ['list', 'listbox']:
            print("link_field:", link_field)
            print("data_field:", data_field)
            info['link_field'] = link_field
            info['data_field'] = data_field
        elif pred_type == 'dlist':
            print("link1_field:", link_field)
            print("link2_field:", other_field)
            print("data_field:", data_field)
            info['link1_field'] = link_field
            info['link2_field'] = other_field
            info['data_field'] = data_field
        elif pred_type in ['NFtree', 'NFptree']:
            print("child_field:", link_field)
            print("data_field:", data_field)
            info['child_field'] = link_field
            info['data_field'] = data_field
        elif pred_type == 'tree':
            print("parent_field:", other_field)
            print("child_field:", link_field)
            print("data_field:", data_field)
            info['parent_field'] = other_field
            info['child_field'] = link_field
            info['data_field'] = data_field
        elif pred_type == 'ptree':
            print("parent_field:", link_field)
            print("child_field:", other_field)
            print("data_field:", data_field)
            info['parent_field'] = link_field
            info['child_field'] = other_field
            info['data_field'] = data_field
        
        print("nest_preds:", nest_preds)
        info['nest_preds'] = nest_preds
    else:
        print("Error: Predicate type is not recognized!")

    with open('recognized_info.json', 'w') as file:
        json.dump(info, file)

if __name__ == '__main__':
    # str = "/*@ Let listrep(l) = l == 0 && emp || exists t, data_at(field_addr(l, link), t) * listrep(t)*/"

    # str = "/*@ Let listrep(l) = l == 0 && emp || exists v t, data_at(field_addr(l, head), v) * data_at(field_addr(l, tail), t) * listrep(t)*/"

    str = "/*@ Let(struct list) lseg(x, y) = x == y && emp || exists v z, data_at(field_addr(x, head), v) * data_at(field_addr(x, tail), z) * lseg(z, y)*/"

    # str = "/*@ Let dlistrep(l, p) = l == 0 && emp || exists t, data_at(field_addr(l, next), t) * data_at(field_addr(l, prev), p) * dlistrep(t, l)*/"

    # str = """/*@ Let dlistrep(l, p) = l == 0 && emp ||
    #   exists v t, data_at(field_addr(l, head), v) * 
    #             data_at(field_addr(l, next), t) *
    #             data_at(field_addr(l, prev), p) *
    #             dlistrep(t, l)*/"""

    # str = "/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp || exists z, data_at(field_addr(x, next), z) * data_at(field_addr(x, prev), xp) * dlseg(z, x, yp, y)*/"

    # str = "/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp || exists z, data_at(field_addr(yp, prev), z) * data_at(field_addr(yp, next), y) * dlseg(x, xp, z, yp)*/"

    # str = """/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp ||
    #       exists v z, data_at(field_addr(x, head), v) *
    #                 data_at(field_addr(x, next), z) *
    #                 data_at(field_addr(x, prev), xp) *
    #                 dlseg(z, x, yp, y)*/"""

    # str = """/*@ Let ptree_rep(p, p_par, p_root, p_top) = p == p_root && p_par == p_top && emp ||
    #   	exists ppar_rch ppar_par ppar_data,
    #                         data_at(field_addr(p_par, left), p) * 
    #                         data_at(field_addr(p_par, right), ppar_rch) * 
    #                         data_at(field_addr(p_par, parent), ppar_par) * 
    #                         data_at(field_addr(p_par, data), ppar_data) *
    #                         tree_rep(ppar_rch, p_par) *
    #                         ptree_rep(p_par, ppar_par, p_root, p_top) ||
    #     exists ppar_lch ppar_par ppar_data, 
    #                         data_at(field_addr(p_par, left), ppar_lch) * 
    #                         data_at(field_addr(p_par, right), p) * 
    #                         data_at(field_addr(p_par, parent), ppar_par) * 
    #                         data_at(field_addr(p_par, data), ppar_data) *
    #                         tree_rep(ppar_lch, p_par) *
    #                         ptree_rep(p_par, ppar_par, p_root, p_top) */"""

    # str= """/*@ Let tree_rep(p, p_par) = p == 0 && emp ||
    #   	exists p_lch p_rch p_data, data_at(field_addr(p, left), p_lch) * 
    #                         data_at(field_addr(p, right), p_rch) * 
    #                         data_at(field_addr(p, parent), p_par) *
    #                         data_at(field_addr(p, data), p_data) * 
    #                         tree_rep(p_lch, p) *
    #                         tree_rep(p_rch, p)*/"""

    # str = """/*@ Let listlistrep(l) = l == 0 && emp || exists v t, data_at(field_addr(l, head), v) * listrep(v) * data_at(field_addr(l, tail), t) * listlistrep(t)*/"""

    # str = "/*@ Let listlseg(x, y) = x == y && emp || exists v z, data_at(field_addr(x, head), v) * listrep(v) * data_at(field_addr(x, tail), z) * listlseg(z, y)*/"
    
    # str = """/*@ Let dlseg(x, xp, yp, y) = x == y && xp == yp && emp || exists z, data_at(field_addr(x, next), z) * data_at(field_addr(x, prev), xp) * dlseg(z, x, yp, y)*/"""

    # str = """/*@ Let NFptree_rep(p, p_root) = p == p_root && emp ||
    #   	exists p_par ppar_data ppar_right, 
    # 		data_at(field_addr(p_par, left), p) * data_at(field_addr(p_par, data), ppar_data) * 
    # 		data_at(field_addr(p_par, right), ppar_right) * NFtree_rep(ppar_right) *
    # 		NFptree_rep(p_par, p_root) ||
    # 	exists p_par ppar_data ppar_left, 
    # 		data_at(field_addr(p_par, right), p) * data_at(field_addr(p_par, data), ppar_data) * 
    # 		data_at(field_addr(p_par, left), ppar_left) * NFtree_rep(ppar_left) *
    # 		NFptree_rep(p_par, p_root)*/"""

    # str = """/*@ Let NFtree_rep(p) = p == 0 && emp ||
    #     exists p_data p_left p_right, data_at(field_addr(p, data), p_data) *
    #         data_at(field_addr(p, left), p_left) * data_at(field_addr(p, right), p_right) * 
    #                 NFtree_rep(p_left) * NFtree_rep(p_right)*/"""

    # str = "/*@ Let listbox_rep(x) = exists p, data_at(x, p) * listrep(p)*/"

    # str = "/*@ Let listbox_seg(x,y) = x == y && emp || exists p, data_at(x, p) * listbox_seg(&(p->tail),y)*/"

    # str = """/*@ Let listbox_seg(x,y) = x == y && emp || 
    #        exists v p, data_at(x, p) * data_at(field_addr(p, head), v) * listbox_seg(&(p->tail),y)*/"""

    recognize(str)
