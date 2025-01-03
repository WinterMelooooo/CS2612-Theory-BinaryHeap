#include <stdio.h>
#include<string.h>
#include "preprocess.h"

//#define PREPROCESS_DEBUG 1

void hash_table_delete_trans(Hash_Table *Hs_Table){
    if (Hs_Table)
	  {
        if (Hs_Table->table)
		    {
            int i = 0;
            for (i = 0; i < MAX_TABLE_SIZE; i++)	//遍历每一个table 
			      {
                Hash_node *p = Hs_Table->table[i];
                Hash_node *q = NULL;
                while (p)		//该点存在存储内容
				{   
                    q = p;
                    Hash_val* tmp = p->value;
                    if(tmp != NULL && tmp->name != NULL) free(tmp->name);
                    free(p->value);
                    free(p->key);
                    p = p->next;
                    free(q);
                }
            }
            free(Hs_Table->table);	//释放表存储指针的内存占用
            Hs_Table->table = NULL;
        }
        free(Hs_Table);		//释放表指针
		Hs_Table = NULL;
    }
	return ;
}

void free_cnf_list(cnf_list* list){
    if(list == NULL) return;
    cnf_list* tmp = list->next;
    free(list->clause);
    free(list);
    free_cnf_list(tmp);
}

void freePredata(PreData* data){
    if(data == NULL) return;
    hash_table_delete_trans(data->var_table);
    hash_table_delete_trans(data->fun_var_table);
    hash_table_delete(data->ufun_table);
    hash_table_delete_trans(data->lia_purify_table);
    hash_table_delete_trans(data->nia_purify_table);
    hash_table_delete_trans(data->uf_purify_table);
    hash_table_delete_trans(data->prop_table);
    freeSmtProplist(data->replace_list);
    freeSmtProplist(data->uf_purify_list);
    freeSmtProplist(data->lia_purify_list);
    freeSmtProplist(data->nia_purify_list);
    free_cnf_list(data->cnf_res);
    for(int i = 1; i <= data->var_cnt_uf; i++){
        free(data->var_list[i]);
    }
    free(data->var_list);
    for(int i = 1; i < data->at_prop_cnt; i++){
        freeSmtProp(data->prop_list[i]);
    }
    free(data->prop_list);
    free(data);
}



Hash_val* initHashVal(){
    Hash_val* hv = (Hash_val*)malloc(sizeof(Hash_val));
    memset(hv, 0, sizeof(Hash_val));
    hv->name = (char*)malloc(sizeof(char)*64);
    memset(hv->name, 0, sizeof(char)*64);
    return hv;
}

PreData* initPreData(){
    PreData* s = (PreData*)malloc(sizeof(PreData));
    memset(s, 0, sizeof(PreData));
    s->var_table = creat_hash_table();
    s->fun_var_table = creat_hash_table();
    s->ufun_table = creat_hash_table();
    s->lia_purify_table = creat_hash_table();
    s->nia_purify_table = creat_hash_table();
    s->uf_purify_table = creat_hash_table();
    s->prop_table = creat_hash_table();
    s->var_list = NULL;
    s->prop_list = NULL;
    s->replace_list = (SmtProplist*)malloc(sizeof(SmtProplist)); //存在尾指针
    s->replace_list->prop = NULL;
    s->replace_list->next = NULL;
    s->uf_purify_list = (SmtProplist*)malloc(sizeof(SmtProplist)); //存在尾指针
    s->uf_purify_list->prop = NULL;
    s->uf_purify_list->next = NULL;
    s->lia_purify_list = (SmtProplist*)malloc(sizeof(SmtProplist)); //存在尾指针
    s->lia_purify_list->prop = NULL;
    s->lia_purify_list->next = NULL;
    s->nia_purify_list = (SmtProplist*)malloc(sizeof(SmtProplist)); //存在尾指针
    s->nia_purify_list->prop = NULL;
    s->nia_purify_list->next = NULL;
    s->cnf_res = (cnf_list*)malloc(sizeof(cnf_list));
    s->cnf_res->clause = NULL;
    s->cnf_res->next = NULL;
    s->var_cnt = 0;
    s->var_cnt_uf = 0;
    s->ufunc_cnt = 0;
    s->purify_cnt = 0;
    s->prop_cnt = 0;
    s->clause_cnt = 0;
    s->int8_max = -1;
    s->int16_max = -1;
    s->int32_max = -1;
    s->int64_max = -1;
    // s->int_max = -1;
    // s->ll_max = -1;
    return s;
}

SmtProp* prop_simplify(SmtProp* p){
    SmtProp* res = NULL;
    switch(p->type){
        case SMTB_PROP: {
            SmtProp* p1 = prop_simplify(p->prop.Binary_prop.prop1);
            SmtProp* p2 = prop_simplify(p->prop.Binary_prop.prop2);
            if(p1->type != SMTTF_PROP && p2->type != SMTTF_PROP){
                res = newSmtProp(SMTB_PROP, p->prop.Binary_prop.op, p1, p2, NULL, NULL, true);
                return res;
            }
            switch(p->prop.Binary_prop.op){
                case SMTPROP_AND:
                    if((p1->type == SMTTF_PROP && p1->prop.TF == false) || (p2->type == SMTTF_PROP && p2->prop.TF == false)){
                        res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, false);
                    }
                    else if(p1->type == SMTTF_PROP && p1->prop.TF == true){
                        if(p2->type == SMTTF_PROP && p2->prop.TF == true){
                            res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
                        }
                        else {
                            res = copy_SmtProp(p2);
                        }
                    }
                    else if(p2->type == SMTTF_PROP && p2->prop.TF == true){
                        res = copy_SmtProp(p1);
                    }
                    break;
                case SMTPROP_OR:
                    if((p1->type == SMTTF_PROP && p1->prop.TF == true) || (p2->type == SMTTF_PROP && p2->prop.TF == true)){
                        res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
                    }
                    else if(p1->type == SMTTF_PROP && p1->prop.TF == false){
                        if(p2->type == SMTTF_PROP && p2->prop.TF == false){
                            res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, false);
                        }
                        else {
                            res = copy_SmtProp(p2);
                        }
                    }
                    else if(p2->type == SMTTF_PROP && p2->prop.TF == false){
                        res = copy_SmtProp(p1);
                    }
                    break;
                case SMTPROP_IMPLY:
                    if((p1->type == SMTTF_PROP && p1->prop.TF == false) || (p2->type == SMTTF_PROP && p2->prop.TF == true)){
                        res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
                    }
                    else if(p1->type == SMTTF_PROP && p1->prop.TF == true){
                        if(p2->type == SMTTF_PROP && p2->prop.TF == false){
                            res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, false);
                        }
                        else {
                            res = copy_SmtProp(p2);
                        }
                    }
                    else if(p2->type == SMTTF_PROP && p2->prop.TF == false){
                        res = newSmtProp(SMTU_PROP, SMTPROP_NOT, copy_SmtProp(p1), NULL, NULL, NULL, true);
                    }
                    break;
                case SMTPROP_IFF:
                    if((p1->type == SMTTF_PROP && p1->prop.TF == true && p2->type == SMTTF_PROP && p2->prop.TF == true)
                      || (p1->type == SMTTF_PROP && p1->prop.TF == false && p2->type == SMTTF_PROP && p2->prop.TF == false)){
                        res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
                    }
                    else if((p1->type == SMTTF_PROP && p1->prop.TF == true && p2->type == SMTTF_PROP && p2->prop.TF == false)
                      || (p1->type == SMTTF_PROP && p1->prop.TF == false && p2->type == SMTTF_PROP && p2->prop.TF == true)){
                        res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, false);
                    }
                    else if(p1->type == SMTTF_PROP && p1->prop.TF == true){
                        res = copy_SmtProp(p2);
                    }
                    else if(p2->type == SMTTF_PROP && p2->prop.TF == true){
                        res = copy_SmtProp(p1);
                    }
                    else if(p1->type == SMTTF_PROP && p1->prop.TF == false){
                        res = newSmtProp(SMTU_PROP, SMTPROP_NOT, copy_SmtProp(p2), NULL, NULL, NULL, true);
                    }
                    else if(p2->type == SMTTF_PROP && p2->prop.TF == false){
                        res = newSmtProp(SMTU_PROP, SMTPROP_NOT, copy_SmtProp(p1), NULL, NULL, NULL, true);
                    }
                    break;
                default: break;
            }
            freeSmtProp(p1);
            freeSmtProp(p2);
            break;
        }
        case SMTU_PROP: {
            SmtProp* p3 = prop_simplify(p->prop.Unary_prop.prop1);
            if(p3->type == SMTTF_PROP && p3->prop.TF == false){
                res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
            }
            else if(p3->type == SMTTF_PROP && p3->prop.TF == true){
                res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, false);
            }
            else {
                res = newSmtProp(SMTU_PROP, p->prop.Unary_prop.op, p3, NULL, NULL, NULL, true);
                return res;
            }
            freeSmtProp(p3);
            break;
        }
        default:
            res = copy_SmtProp(p);
            break;
    }
    return res;
}

//uf是已经purify之后的结果,即其参数只能是variable或者UFterm
char* UFunction_str(UFunction* uf){
    char ** args_str = (char**)malloc(sizeof(char*) * uf->numArgs);
    for (int i = 0; i < uf->numArgs; ++i) {
        if (uf->args[i]->type == SMT_UFTerm) {
            args_str[i] = UFunction_str(uf->args[i]->term.UFTerm);
        }
    }
    int total_len = 0;
    total_len += strlen(uf->name) + 1;
    for (int i = 0; i < uf->numArgs; ++i) {
        if(uf->args[i]->type == SMT_VarName){
            total_len += strlen(uf->args[i]->term.Variable) + 1;
        }
        else if(uf->args[i]->type == SMT_UFTerm){
            total_len += strlen(args_str[i]) + 1;
        }
    }
    char* s = (char*)malloc(sizeof(char) * (total_len + 1));
    memset(s, 0, sizeof(char) * (total_len + 1));
    char* p = s;
    sprintf(s, "%s(", uf->name);
    int len = strlen(s);
    p = s+len;
    for(int i  = 0; i < uf->numArgs; i++){
        if(uf->args[i]->type == SMT_VarName){
            if(i != uf->numArgs-1)
                sprintf(p,"%s,",uf->args[i]->term.Variable);
            else 
                sprintf(p,"%s)",uf->args[i]->term.Variable);
            p = p + strlen(uf->args[i]->term.Variable) + 1;
        }
        else if(uf->args[i]->type == SMT_UFTerm){
            if(i != uf->numArgs-1) sprintf(p, "%s,", args_str[i]);
            else sprintf(p, "%s)", args_str[i]);
            p = p + strlen(args_str[i])+1;
        }
    }
    for (int i = 0; i < uf->numArgs; ++i) {
        if (uf->args[i]->type == SMT_UFTerm) {
            free(args_str[i]);
        }
    }
    free(args_str);
    return s;
}

//liaTerm是已经purify之后的结果，运算符连接的只能是变量或者常数
char* LiaTerm_str(SmtTerm* t){
    char* s;
    switch(t->type){
        case SMT_LiaBTerm: 
        case SMT_NiaBTerm:{
            char* s1 = LiaTerm_str(t->term.BTerm.t1);
            char* s2 = LiaTerm_str(t->term.BTerm.t2);
            s = malloc(sizeof(char) * (strlen(s1) + strlen(s2) + 4));
            if(t->term.BTerm.op == LIA_ADD)
                sprintf(s, "(%s+%s)", s1, s2);
            else if(t->term.BTerm.op == LIA_MINUS)
                sprintf(s, "(%s-%s)", s1, s2);
            else if(t->term.BTerm.op == LIA_MULT)
                sprintf(s, "%s*%s", s1, s2);
            else if(t->term.BTerm.op == LIA_DIV)
                sprintf(s, "%s/%s", s1, s2);
            else {
                printf("invalide binary op : %d\n", t->term.BTerm.op);
                exit(-1);
            }
            free(s1);
            free(s2);
            break;
        }
        case SMT_LiaUTerm: {
            char* s3 = LiaTerm_str(t->term.UTerm.t);
            s = malloc(sizeof(char) * (strlen(s3) + 4));
            sprintf(s, "(-%s)", s3);
            free(s3);
            break;
        }
        case SMT_ConstNum:
            s = (char*)malloc(sizeof(char) * 30);
            sprintf(s, "%d", t->term.ConstNum);
            break;
        case SMT_VarName:
            s = (char*)malloc(sizeof(char) * (strlen(t->term.Variable) + 1));
            sprintf(s, "%s", t->term.Variable);
            break;
        default:
            printf("invalid type in LiaTerm_str\n");
            exit(-1);
            break;
    }
    return s;
}

// 仅限于完成预处理之后的原子命题
char* AtomicProp_str(SmtProp* p){
    char* s;
    switch(p->type){
        case SMTAT_PROP_EQ: 
        case SMTAT_PROP_LIA_EQ: 
        case SMTAT_PROP_NIA_EQ:{
            char* s1 = LiaTerm_str(p->prop.Atomic_prop.term1);
            char* s2 = LiaTerm_str(p->prop.Atomic_prop.term2);
            s = malloc(sizeof(char) * (strlen(s1) + strlen(s2) + 2));
            sprintf(s, "%s=%s", s1, s2);
            free(s1);
            free(s2);
            break;
        }
        case SMTAT_PROP_LIA: {
            char* op;
            switch(p->prop.Atomic_prop.op){
                case SMT_LE: op = "<="; break;
                case SMT_LT: op = "<" ; break;
                case SMT_GE: op = ">="; break;
                case SMT_GT: op = ">" ; break;
                case SMT_EQ: 
                    printf("error in AtomicProp_str, SMT_EQ should't occur in case SMTAT_PROP_LIA\n");
                    exit(-1);
                    break;
            }
            char *s1 = LiaTerm_str(p->prop.Atomic_prop.term1);
            char *s2 = LiaTerm_str(p->prop.Atomic_prop.term2);
            s = malloc(sizeof(char) * (strlen(s1) + strlen(s2) + strlen(op) + 1));
            sprintf(s, "%s%s%s", s1, op, s2);
            free(s1);
            free(s2);
            break;
        }
        case SMTAT_PROP_UF_EQ: {
            char *s1, *s2;
            if(p->prop.Atomic_prop.term1->type == SMT_VarName)
                s1 = LiaTerm_str(p->prop.Atomic_prop.term1);
            else if(p->prop.Atomic_prop.term1->type == SMT_UFTerm)
                s1 = UFunction_str(p->prop.Atomic_prop.term1->term.UFTerm);
            else {
                printf("error in AtomicProp_str, invalid SMTAT_PROP_UF_EQ prop\n");
                exit(-1);
            }
            if(p->prop.Atomic_prop.term2->type == SMT_VarName)
                s2 = LiaTerm_str(p->prop.Atomic_prop.term2);
            else if(p->prop.Atomic_prop.term2->type == SMT_UFTerm)
                s2 = UFunction_str(p->prop.Atomic_prop.term2->term.UFTerm);
            else {
                printf("error in AtomicProp_str, invalid SMTAT_PROP_UF_EQ prop\n");
                exit(-1);
            }
            s = malloc(sizeof(char) * (strlen(s1) + strlen(s2) + 2));
            sprintf(s, "%s=%s", s1, s2);
            free(s1);
            free(s2);
            break;
        }
        default:
            printf("error in AtomicProp_str, invalid input type\n");
            exit(-1);
            break;
    }
    return s;
}

//在purify时，给UFterm起新的变量名，并且增加新的约束，返回新的变量名
//在做uf相关的变量替代(flatten)时，作用类似
// mode = 0 => purify
// mode = 1 => uf_flatten
//与不生成证明的版本相比，这里增加了ufun_table用于记录每个新的变量对应的函数是什么
SmtTerm* new_name_UFterm(SmtTerm* t, PreData* data, int mode){
    SmtTerm* res = NULL;
    if(t->type != SMT_UFTerm){
        printf("\ninvalid term : \n");
        printSmtTerm(t);
        printf("\ninvalid type in new_name_UFterm\n");
        exit(-1);
    }
    char* key1 = UFunction_str(t->term.UFTerm);
    Hash_val* tmp_val = get_value_from_hstable(data->uf_purify_table, key1, strlen(key1));
    if(tmp_val == NULL){
        tmp_val = initHashVal();
        Hash_val* var_val = initHashVal();
        data->var_cnt++;
        tmp_val->num = data->var_cnt;
        var_val->num = data->var_cnt;
        if(mode == 1) {
            ++data->ufunc_cnt;
            sprintf(var_val->name, "f_e%d", data->ufunc_cnt);
            char* arg1 = t->term.UFTerm->args[0]->term.Variable;
            char* arg2 = t->term.UFTerm->args[1]->term.Variable;
            Hash_val* v1 = get_value_from_hstable(data->var_table, arg1, strlen(arg1));
            Hash_val* v2 = get_value_from_hstable(data->var_table, arg2, strlen(arg2));
            if(v1 == NULL || v2 == NULL){
                printf("error in new_uf_name, null hashval\n");
                exit(-1);
            }
            UF_Hash* uf_val = (UF_Hash*)malloc(sizeof(UF_Hash));
            uf_val->arg1 = v1->num;
            uf_val->arg2 = v2->num;
            char* key = var_val->name;
            add_node2HashTable(data->ufun_table, key, strlen(key), uf_val);
        }
        else {
            ++data->purify_cnt;
            sprintf(var_val->name, "v_a%d", data->purify_cnt);
        }
        strcpy(tmp_val->name, var_val->name);
        add_node2HashTable(data->uf_purify_table, key1, strlen(key1), tmp_val);
        add_node2HashTable(data->var_table, var_val->name, strlen(var_val->name), var_val);
        //添加新约束
        SmtTerm* new_var = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
        SmtProp* new_prop = newSmtProp(SMTAT_PROP_UF_EQ, SMT_EQ, NULL, NULL, copy_SmtTerm(t), new_var, true);
        SmtProplist* new_constrain = (SmtProplist*)malloc(sizeof(SmtProplist));
        memset(new_constrain, 0, sizeof(SmtProplist));
        new_constrain->prop = new_prop;
        if(mode == 0){
            new_constrain->next = data->uf_purify_list;
            data->uf_purify_list = new_constrain;
        }
        else if(mode == 1){
            new_constrain->next = data->replace_list;
            data->replace_list = new_constrain;
        }
        res = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
    }
    else {
        res = newSmtTerm(SMT_VarName, 0, 0, tmp_val->name, NULL, NULL, NULL);
    }
    free(key1);
    return res;
}

//在purify时，给Liaterm起新的变量名，并且增加新的约束，返回新的变量名
SmtTerm* new_name_Liaterm(SmtTerm* t, PreData* data){
    SmtTerm* res = NULL;
    if(t->type != SMT_LiaBTerm && t->type != SMT_LiaUTerm && t->type != SMT_ConstNum){
        printf("\ninvalid term : \n");
        printSmtTerm(t);
        printf("\ninvalid type in new_name_Liaterm\n");
        exit(-1);
    }
    char* key1 = LiaTerm_str(t);
    Hash_val* tmp_val = get_value_from_hstable(data->lia_purify_table, key1, strlen(key1));
    if(tmp_val == NULL){
        tmp_val = initHashVal();
        Hash_val* var_val = initHashVal();
        data->var_cnt++;
        data->purify_cnt++;
        tmp_val->num = data->var_cnt;
        var_val->num = data->var_cnt;
        sprintf(tmp_val->name, "v_a%d", data->purify_cnt);
        sprintf(var_val->name, "v_a%d", data->purify_cnt);
        add_node2HashTable(data->lia_purify_table, key1, strlen(key1), tmp_val);
        add_node2HashTable(data->var_table, var_val->name, strlen(var_val->name), var_val);
        //添加新约束
        SmtTerm* new_var = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
        SmtProp* new_prop = newSmtProp(SMTAT_PROP_LIA_EQ, SMT_EQ, NULL, NULL, copy_SmtTerm(t), new_var, true);
        SmtProplist* new_constrain = (SmtProplist*)malloc(sizeof(SmtProplist));
        memset(new_constrain, 0, sizeof(SmtProplist));
        new_constrain->prop = new_prop;
        new_constrain->next = data->lia_purify_list;
        data->lia_purify_list = new_constrain;
        res = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
    }
    else {
        res = newSmtTerm(SMT_VarName, 0, 0, tmp_val->name, NULL, NULL, NULL);
    }
    free(key1);
    return res;
}

//在purify时，给Niaterm起新的变量名，并且增加新的约束，返回新的变量名
SmtTerm* new_name_Niaterm(SmtTerm* t, PreData* data){
    SmtTerm* res = NULL;
    if(t->type != SMT_NiaBTerm){
        printf("\ninvalid term : \n");
        printSmtTerm(t);
        printf("\ninvalid type in new_name_Niaterm\n");
        exit(-1);
    }
    char* key1 = LiaTerm_str(t);
    Hash_val* tmp_val = get_value_from_hstable(data->nia_purify_table, key1, strlen(key1));
    if(tmp_val == NULL){
        tmp_val = initHashVal();
        Hash_val* var_val = initHashVal();
        data->var_cnt++;
        data->purify_cnt++;
        tmp_val->num = data->var_cnt;
        var_val->num = data->var_cnt;
        sprintf(tmp_val->name, "v_a%d", data->purify_cnt);
        sprintf(var_val->name, "v_a%d", data->purify_cnt);
        add_node2HashTable(data->nia_purify_table, key1, strlen(key1), tmp_val);
        add_node2HashTable(data->var_table, var_val->name, strlen(var_val->name), var_val);
        //添加新约束
        SmtTerm* new_var = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
        SmtProp* new_prop = newSmtProp(SMTAT_PROP_NIA_EQ, SMT_EQ, NULL, NULL, copy_SmtTerm(t), new_var, true);
        SmtProplist* new_constrain = (SmtProplist*)malloc(sizeof(SmtProplist));
        memset(new_constrain, 0, sizeof(SmtProplist));
        new_constrain->prop = new_prop;
        new_constrain->next = data->nia_purify_list;
        data->nia_purify_list = new_constrain;
        res = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
    }
    else {
        res = newSmtTerm(SMT_VarName, 0, 0, tmp_val->name, NULL, NULL, NULL);
    }
    free(key1);
    return res;
}

SmtTerm* updateSmtTerm(SmtTerm* t, PreData* data, int mode){
    if(mode == SMT_LiaBTerm || mode == SMT_LiaUTerm){
        //用于lia运算符(+,-)两边 
        if(t->type == SMT_UFTerm){
            SmtTerm* tmp = new_name_UFterm(t, data, 0);
            freeSmtTerm(t);
            t = tmp;
        } else if(t->type == SMT_NiaBTerm){
            SmtTerm* tmp = new_name_Niaterm(t, data);
            freeSmtTerm(t);
            t = tmp;
        }
    }
    else if(mode == SMT_UFTerm){
        //用于uf的参数
        if(t->type == SMT_LiaBTerm || t->type == SMT_LiaUTerm || t->type == SMT_ConstNum){
            SmtTerm* tmp = new_name_Liaterm(t, data);
            freeSmtTerm(t);
            t = tmp;
        }
        else if(t->type == SMT_NiaBTerm){
            SmtTerm* tmp = new_name_Niaterm(t, data);
            freeSmtTerm(t);
            t = tmp;
        }
    }
    else if(mode == SMT_NiaBTerm){
        //用于nia运算符(*,/)两边
        if(t->type == SMT_UFTerm){
            SmtTerm* tmp = new_name_UFterm(t, data, 0);
            freeSmtTerm(t);
            t = tmp;
        } else if(t->type == SMT_LiaBTerm || t->type == SMT_LiaUTerm){
            SmtTerm* tmp = new_name_Liaterm(t, data);
            freeSmtTerm(t);
            t = tmp;
        }
    }
    return t;
}

SmtTerm* term_purify(SmtTerm* t, PreData* data){ 
    SmtTerm* res = NULL;
    switch(t->type){
        case SMT_LiaBTerm:{
            SmtTerm* t1 = term_purify(t->term.BTerm.t1, data);
            SmtTerm* t2 = term_purify(t->term.BTerm.t2, data);
            t1 = updateSmtTerm(t1, data, SMT_LiaBTerm);
            t2 = updateSmtTerm(t2, data, SMT_LiaBTerm);
            res = newSmtTerm(t->type, t->term.BTerm.op, 0, NULL, NULL, t1, t2);
            break;
        }
        case SMT_LiaUTerm:{
            SmtTerm* t1 = term_purify(t->term.BTerm.t1, data);
            t1 = updateSmtTerm(t1, data, SMT_LiaUTerm);
            res = newSmtTerm(t->type, t->term.UTerm.op, 0, NULL, NULL, t1, NULL);
            break;
        }
        case SMT_NiaBTerm: {
            SmtTerm* t1 = term_purify(t->term.BTerm.t1, data);
            SmtTerm* t2 = term_purify(t->term.BTerm.t2, data);
            t1 = updateSmtTerm(t1, data, SMT_NiaBTerm);
            t2 = updateSmtTerm(t2, data, SMT_NiaBTerm);
            res = newSmtTerm(t->type, t->term.BTerm.op, 0, NULL, NULL, t1, t2);
            break;
        }  
        case SMT_UFTerm: {
            res = copy_SmtTerm(t);
            for(int i = 0; i < t->term.UFTerm->numArgs; i++){
                SmtTerm* argi = term_purify(t->term.UFTerm->args[i], data);
                argi = updateSmtTerm(argi, data, SMT_UFTerm);
                freeSmtTerm(res->term.UFTerm->args[i]);
                res->term.UFTerm->args[i] = argi;
            }
            break;
        }
        case SMT_VarName: {
            int len = strlen(t->term.Variable);
            Hash_val* tmp_val = get_value_from_hstable(data->var_table, t->term.Variable, len);
            if(tmp_val == NULL){
                tmp_val = initHashVal();
                strcpy(tmp_val->name, t->term.Variable);
                tmp_val->num = ++(data->var_cnt);
                add_node2HashTable(data->var_table, t->term.Variable, len, tmp_val);
            }
            res = copy_SmtTerm(t);
            break;
        }
        case SMT_ConstNum:
        case SMT_VarNum:
        default:
            res = copy_SmtTerm(t);
            break;
    }
    return res;
}

SmtProp* prop_purify(SmtProp* p, PreData* data){
    SmtProp* res = NULL;
    switch(p->type){
        case SMTB_PROP:{
            SmtProp* prop1 = prop_purify(p->prop.Binary_prop.prop1, data);
            SmtProp* prop2 = prop_purify(p->prop.Binary_prop.prop2, data);
            res = newSmtProp(SMTB_PROP, p->prop.Binary_prop.op, prop1, prop2, NULL, NULL, true);
            break;
        }
        case SMTU_PROP:{
            SmtProp* prop1 = prop_purify(p->prop.Unary_prop.prop1, data);
            res = newSmtProp(SMTU_PROP, p->prop.Unary_prop.op, prop1, NULL, NULL, NULL, true);
            break;
        }
        case SMTAT_PROP_LIA:{
            SmtTerm* term1 = term_purify(p->prop.Atomic_prop.term1, data);
            SmtTerm* term2 = term_purify(p->prop.Atomic_prop.term2, data);
            term1 = updateSmtTerm(term1, data, SMT_LiaBTerm);
            term2 = updateSmtTerm(term2, data, SMT_LiaBTerm);
            res = newSmtProp(SMTAT_PROP_LIA, p->prop.Atomic_prop.op, NULL, NULL, term1, term2, true);
            break;
        }
        case SMTAT_PROP_EQ:{
            SmtTerm* term1 = term_purify(p->prop.Atomic_prop.term1, data);
            SmtTerm* term2 = term_purify(p->prop.Atomic_prop.term2, data);
            term1 = updateSmtTerm(term1, data, SMT_UFTerm);
            term2 = updateSmtTerm(term2, data, SMT_UFTerm);
            res = newSmtProp(SMTAT_PROP_EQ, p->prop.Atomic_prop.op, NULL, NULL, term1, term2, true);
            if(term1->type == SMT_UFTerm || term2->type == SMT_UFTerm)
                res->type = SMTAT_PROP_UF_EQ;
            break;
        }
        case SMTAT_PROP_UF_EQ:
        case SMTAT_PROP_LIA_EQ:
        case SMTAT_PROP_NIA_EQ:
            printf("in prop purify ,should't have type : \"SMTAT_PROP_UF_EQ\" or \"SMTAT_PROP_LIA_EQ\" or \"SMTAT_PROP_NIA_EQ\"\n");
            break;
        default:
            break;
    }
    return res;
}

void NiaTermIdentify(SmtTerm* t){
    //因为只改变liaBterm_type,所以可以直接在原本语法树上做修改
    switch(t->type){
        case SMT_LiaBTerm:{
            SmtTerm* t1 = t->term.BTerm.t1;
            SmtTerm* t2 = t->term.BTerm.t2;
            NiaTermIdentify(t1);
            NiaTermIdentify(t2);
            if(t->term.BTerm.op == LIA_DIV || (t->term.BTerm.op == LIA_MULT && t1->type != SMT_ConstNum && t2->type != SMT_ConstNum)){
                    t->type = SMT_NiaBTerm;
            }
            break;
        }
        case SMT_LiaUTerm:
            NiaTermIdentify(t->term.UTerm.t);
            break;
        case SMT_UFTerm:
            for(int i = 0; i < t->term.UFTerm->numArgs; i++){
                NiaTermIdentify(t->term.UFTerm->args[i]);
            }
            break;
        case SMT_NiaBTerm:
            printf("error in NiaTermIdentify, should not have SMT_NiaBTerm in this stage\n");
            exit(-1);
        default:
            break;
    }
    return;
}

void NiaPropIdentify(SmtProp* p){
    switch (p->type)
    {
    case SMTB_PROP:
        NiaPropIdentify(p->prop.Binary_prop.prop1);
        NiaPropIdentify(p->prop.Binary_prop.prop2);
        break;
    case SMTU_PROP:
        NiaPropIdentify(p->prop.Unary_prop.prop1);
        break;
    case SMTAT_PROP_EQ:
    case SMTAT_PROP_LIA:
        NiaTermIdentify(p->prop.Atomic_prop.term1);
        NiaTermIdentify(p->prop.Atomic_prop.term2);
        break;
    case SMTAT_PROP_LIA_EQ:
    case SMTAT_PROP_UF_EQ:
    case SMTAT_PROP_NIA_EQ:
        printf("in NiaPropIdentify ,should't have type : \"SMTAT_PROP_UF_EQ\" or \"SMTAT_PROP_LIA_EQ\" or \"SMTAT_PROP_NIA_EQ\"\n");
        break;
    default:
        break;
    }
}

SmtTerm* termCurryfy(SmtTerm* t){
    SmtTerm* res = NULL;
    switch(t->type){
        case SMT_LiaBTerm:{
            SmtTerm* t1 = termCurryfy(t->term.BTerm.t1);
            SmtTerm* t2 = termCurryfy(t->term.BTerm.t2);
            res = newSmtTerm(SMT_LiaBTerm, t->term.BTerm.op, 0, NULL, NULL, t1, t2);
            break;
        }
        case SMT_LiaUTerm:{
            SmtTerm* t1 = termCurryfy(t->term.UTerm.t);
            res = newSmtTerm(SMT_LiaUTerm, t->term.UTerm.op, 0, NULL, NULL, t1, NULL);
            break;
        }
        case SMT_UFTerm:
            if(t->term.UFTerm->numArgs == 0) res = newSmtTerm(SMT_VarName, 0, 0, t->term.UFTerm->name, NULL, NULL, NULL);
            else {
                int num = t->term.UFTerm->numArgs;
                UFunction* res1 = (UFunction*)malloc(sizeof(UFunction));
                res1->numArgs = 2;
                res1->args = (SmtTerm**)malloc(sizeof(SmtTerm*)*2);
                res1->name = "UF";
                res1->args[1] = termCurryfy(t->term.UFTerm->args[num-1]);
                t->term.UFTerm->numArgs--;
                res1->args[0] = termCurryfy(t);
                t->term.UFTerm->numArgs++;
                res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, res1, NULL, NULL);
            }
            break;
        default:{
            res = copy_SmtTerm(t);
            break;
        }
    }
    return res;
}

//对已经进行curryfy和purify的ufterm做变量替代
SmtTerm* term_replace(SmtTerm* t, PreData* data){
    SmtTerm* res = NULL;
    switch(t->type){
        case SMT_UFTerm:{
            char* s = (char*)malloc(sizeof(char)*(strlen(t->term.UFTerm->name)+1));
            memset(s, 0, sizeof(char)*(strlen(t->term.UFTerm->name)+1));
            strcpy(s, t->term.UFTerm->name);
            SmtTerm* t1 =  term_replace(t->term.UFTerm->args[0], data);
            SmtTerm* t2 =  term_replace(t->term.UFTerm->args[1], data); 
            UFunction* f = newUFunction(s, 2, t1, t2, NULL);
            SmtTerm* tmp = newSmtTerm(SMT_UFTerm, 0, 0, NULL, f, NULL, NULL);
            if(t1->type != SMT_VarName || t2->type != SMT_VarName){
                printf("error in term_replace, here should have type : SMT_VarName\n");
                exit(-1);
            }
            res = new_name_UFterm(tmp, data, 1);
            freeSmtTerm(tmp);
            break;
        }
        case SMT_VarName: {
            res = copy_SmtTerm(t);
            int len = strlen(t->term.Variable);
            Hash_val* tmp_val = get_value_from_hstable(data->var_table, t->term.Variable, len);
            if(tmp_val == NULL){
                tmp_val = initHashVal();
                strcpy(tmp_val->name, t->term.Variable);
                tmp_val->num = ++(data->var_cnt);
                add_node2HashTable(data->var_table, t->term.Variable, len, tmp_val);
            }
            break;
        }
        default:
            break;
    }
    return res;
}

//同时完成curryfy和flatten
SmtProp* prop_currfy_flatten(SmtProp* p, PreData* data){
    SmtProp* res = NULL;
    switch(p->type){
        case SMTB_PROP: {
            SmtProp* p1 = prop_currfy_flatten(p->prop.Binary_prop.prop1, data);
            SmtProp* p2 = prop_currfy_flatten(p->prop.Binary_prop.prop2, data);
            res = newSmtProp(SMTB_PROP, p->prop.Binary_prop.op, p1, p2, NULL, NULL, true);
            break;
        }
        case SMTU_PROP:{
            SmtProp* p1 = prop_currfy_flatten(p->prop.Unary_prop.prop1, data);
            res = newSmtProp(SMTU_PROP, p->prop.Unary_prop.op, p1, NULL, NULL, NULL, true);
            break;
        }
        case SMTAT_PROP_EQ:{
            //经过purify处理之后，此处应该两边都是变量，这里可以顺便统计变量的数量并编号
            if(p->prop.Atomic_prop.term1->type != SMT_VarName || p->prop.Atomic_prop.term2->type != SMT_VarName){
                printf("error in prop_currfy, here should be variable equation\n");
                exit(-1);
            }
            SmtTerm* t1 = term_replace(p->prop.Atomic_prop.term1, data);
            SmtTerm* t2 = term_replace(p->prop.Atomic_prop.term2, data);
            res = newSmtProp(SMTAT_PROP_EQ, p->prop.Atomic_prop.op, NULL, NULL, t1, t2, true);
            break;
        }
        case SMTAT_PROP_UF_EQ: {
            SmtTerm* t1 = termCurryfy(p->prop.Atomic_prop.term1);
            SmtTerm* t2 = termCurryfy(p->prop.Atomic_prop.term2);
            SmtTerm* t3 = term_replace(t1, data);
            SmtTerm* t4 = term_replace(t2, data);
            freeSmtTerm(t1);
            freeSmtTerm(t2);
            res = newSmtProp(SMTAT_PROP_EQ, p->prop.Atomic_prop.op, NULL, NULL, t3, t4, true);
            break;
        }
        case SMTAT_PROP_LIA:{
            SmtTerm* t1 = term_replace(p->prop.Atomic_prop.term1, data);
            SmtTerm* t2 = term_replace(p->prop.Atomic_prop.term2, data);
            res = newSmtProp(SMTAT_PROP_LIA, p->prop.Atomic_prop.op, NULL, NULL, t1, t2, true);
            break;
        }
        default:
            break;
    }
    return res;
}

//除了对prop做curryfy&&flatten以外，还对purify生成的新约束做curryfy&&flatten
SmtProp* currfy_flatten(SmtProp* p, PreData* data){
    SmtProp* tmp1 = prop_currfy_flatten(p, data);
    freeSmtProp(p);
    p = tmp1;
    SmtProplist* tmp = data->uf_purify_list;
    while(tmp->next != NULL){
        SmtProp* tmp2 = prop_currfy_flatten(tmp->prop, data);
        freeSmtProp(tmp->prop);
        tmp->prop = tmp2;
        tmp = tmp->next;
    }
    return p;
}

void proplist_currfy_flatten(SmtProplist* list, PreData* data){
    SmtProplist* tmp = list;
    while(tmp->next != NULL){
        tmp->prop = prop_currfy_flatten(tmp->prop, data);
        tmp =tmp->next;
    }
}

void init_Varlist_term(SmtTerm* t, PreData* data){
    switch(t->type){
        case SMT_LiaBTerm:
            init_Varlist_term(t->term.BTerm.t1, data);
            init_Varlist_term(t->term.BTerm.t2, data);
            break;
        case SMT_LiaUTerm:
            init_Varlist_term(t->term.UTerm.t, data);
            break;
        case SMT_UFTerm:
            for(int i = 0; i < t->term.UFTerm->numArgs; i++){
                init_Varlist_term(t->term.UFTerm->args[i], data);
            }
            break;
        case SMT_VarName: {
            char* s = t->term.Variable;
            Hash_val* hval = get_value_from_hstable(data->var_table, s, strlen(s));
            if(hval == NULL){
                printf("variable: %s isn't in var_table\n", s);
                exit(-1);
            }
            else if(data->var_list[hval->num] == NULL){
                // printf("add var to list : %s, id : %d\n", s, hval->num);
                data->var_list[hval->num] = (char*)malloc(sizeof(char)*64);
                memset(data->var_list[hval->num], 0, sizeof(char)*64);
                strcpy(data->var_list[hval->num], s);
            }
            //else printf("have var: %s\n", data->var_list[hval->num]);
            break;
        }
        default:
            break;
    }
}

void init_Varlist_prop(SmtProp* p, PreData* data){
    switch(p->type){
        case SMTB_PROP:
            init_Varlist_prop(p->prop.Binary_prop.prop1, data);
            init_Varlist_prop(p->prop.Binary_prop.prop2, data); 
            break;
        case SMTU_PROP:
            init_Varlist_prop(p->prop.Unary_prop.prop1, data);
            break;
        case SMTAT_PROP_EQ:
        case SMTAT_PROP_LIA:
        case SMTAT_PROP_UF_EQ: 
        case SMTAT_PROP_LIA_EQ:
            init_Varlist_term(p->prop.Atomic_prop.term1, data);
            init_Varlist_term(p->prop.Atomic_prop.term2, data);
            break;
        default:
            break;
    }
}

void init_Varlist_proplist(SmtProplist* p, PreData* data){
    SmtProplist* tmp = p;
    while(tmp->next != NULL){
        init_Varlist_prop(tmp->prop, data);
        tmp = tmp->next;
    }
}
//生成编号与变量的对应列表
void init_Varlist(SmtProp* p, PreData* data){
    data->var_list = (char**)malloc(sizeof(char*)*((data->var_cnt)+1));
    memset(data->var_list, 0, sizeof(char*)*((data->var_cnt)+1));
    init_Varlist_prop(p, data);
    init_Varlist_proplist(data->uf_purify_list, data);
    init_Varlist_proplist(data->lia_purify_list, data);
    init_Varlist_proplist(data->nia_purify_list, data);
    init_Varlist_proplist(data->replace_list, data);
}

void printVarlist(PreData* data){
    for(int i = 1; i <= data->var_cnt; i++){
        if(data->var_list[i] != NULL)
            printf("VarName : %s\nVarId : %d\n", data->var_list[i], i);
    }
}

void printVarlist_uf(PreData* data){
    for(int i = 1; i <= data->var_cnt_uf; i++){
        if(data->var_list[i] != NULL)
            printf("VarName : %s\nVarId : %d\n", data->var_list[i], i);
    }
}

//只打印原子命题列表
void printSmtProplist_2(SmtProplist* p){
    SmtProplist* tmp = p;
    while(tmp->next != NULL){
        char* s = AtomicProp_str(tmp->prop);
        printf("prop : %s\n", s);
        tmp = tmp->next;
    }
}

void add_prop2HashTable(SmtProp* p, PreData* data){
    switch(p->type){
        case SMTB_PROP:
            add_prop2HashTable(p->prop.Binary_prop.prop1, data);
            add_prop2HashTable(p->prop.Binary_prop.prop2, data);
            break;
        case SMTU_PROP:
            add_prop2HashTable(p->prop.Unary_prop.prop1, data);
            break;
        case SMTAT_PROP_EQ:
        case SMTAT_PROP_LIA:
        case SMTAT_PROP_UF_EQ:
        case SMTAT_PROP_LIA_EQ: 
        case SMTAT_PROP_NIA_EQ:{
            char* key = AtomicProp_str(p);
            int len = strlen(key);
            Hash_val* hval = get_value_from_hstable(data->prop_table, key, len);
            if(hval == NULL){
                hval = initHashVal();
                free(hval->name);
                hval->name = NULL;
                hval->num = ++(data->prop_cnt);
                #ifdef PREPROCESS_DEBUG
                    printf("atomic prop : %s\n", key);
                    printf("data->prop_cnt: %d\n", data->prop_cnt);
                #endif
                add_node2HashTable(data->prop_table, key, len, hval);
            }
            free(key);
            break;
        }
        default:
            break;
    }
}

void add_proplist2HashTable(SmtProplist* p, PreData* data){
    SmtProplist* tmp = p;
    while(tmp->next != NULL){
        add_prop2HashTable(tmp->prop, data);
        tmp = tmp->next;
    }
}

void init_propvar(SmtProp* p, PreData* data){
    switch(p->type){
        case SMTB_PROP:
            init_propvar(p->prop.Binary_prop.prop1, data);
            init_propvar(p->prop.Binary_prop.prop2, data);
            break;
        case SMTU_PROP:
            init_propvar(p->prop.Unary_prop.prop1, data);
            break;
        case SMTAT_PROP_EQ:
        case SMTAT_PROP_LIA:
        case SMTAT_PROP_UF_EQ:
        case SMTAT_PROP_LIA_EQ: 
        case SMTAT_PROP_NIA_EQ: {
            char* key = AtomicProp_str(p);
            int len = strlen(key);
            Hash_val* hval = get_value_from_hstable(data->prop_table, key, len);
            if(hval == NULL){
                printf("error in init_propvar, every atomic prop should have be stored in this stage\n");
                exit(-1);
            }
            free(key);
            data->prop_list[hval->num] = copy_SmtProp(p);
            p->type = SMT_PROPVAR;
            p->prop.Propvar = hval->num;
            break;
        }
        default:
            break;
    }
}

void init_propvar_list(SmtProplist* p, PreData* data){
    SmtProplist* tmp = p;
    while(tmp->next != NULL){
        init_propvar(tmp->prop, data);
        tmp = tmp->next;
    }
}

void init_proplist(SmtProp* p, PreData* data){
    add_prop2HashTable(p, data);
    add_proplist2HashTable(data->lia_purify_list, data);
    add_proplist2HashTable(data->uf_purify_list, data);
    add_proplist2HashTable(data->nia_purify_list, data);
    add_proplist2HashTable(data->replace_list, data);
    data->prop_list = (SmtProp**)malloc(sizeof(SmtProp*)*(data->prop_cnt + 1));
    memset(data->prop_list, 0, sizeof(SmtProp*)*(data->prop_cnt + 1));
    init_propvar(p, data);
    init_propvar_list(data->lia_purify_list, data);
    init_propvar_list(data->uf_purify_list, data);
    init_propvar_list(data->nia_purify_list, data);
    init_propvar_list(data->replace_list, data);
}

//生成p3<->(p1 op p2)对应的cnf中的clause
//p3<->not p2 (op为 not时， 此时p1缺省为0)
void clause_gen(int p1, int p2, int p3, int op, PreData* data){
    int size = 3;
    int *clause1 = (int *)malloc(sizeof(int) * (size + 1));
    int *clause2 = (int *)malloc(sizeof(int) * (size + 1));
    int *clause3 = (int *)malloc(sizeof(int) * (size + 1));
    int *clause4 = (int *)malloc(sizeof(int) * (size + 1));
    memset(clause1, 0, sizeof(int) * (size + 1));
    memset(clause2, 0, sizeof(int) * (size + 1));
    memset(clause3, 0, sizeof(int) * (size + 1));
    memset(clause4, 0, sizeof(int) * (size + 1));
    // 完成 SET_PROP: p3<->(p1 op p2) / p3<->not p2
    int cnt = 0;
    switch (op)
    {
    case SMTPROP_OR:
    {
        // p3\/非p1
        clause1[0] = -p1;
        clause1[1] = p3;
        // p3\/非p2
        clause2[0] = -p2;
        clause2[1] = p3;
        if (p1 != p2)
        {
            // 非p3\/p1\/p2
            clause3[0] = p1;
            clause3[1] = p2;
            clause3[2] = -p3;
        }
        else
        {
            clause3[0] = p1;
            clause3[1] = -p3;
        }
        cnt += 3;
        break;
    }
    case SMTPROP_AND:
    {
        // 非p3\/p1
        clause1[0] = p1;
        clause1[1] = -p3;
        // 非p3\/p2
        clause2[0] = p2;
        clause2[1] = -p3;
        if (p1 != p2)
        {
            // p3\/非p1\/非p2
            clause3[0] = -p1;
            clause3[1] = -p2;
            clause3[2] = p3;
        }
        else
        {
            clause3[0] = -p1;
            clause3[1] = p3;
        }
        cnt += 3;
        break;
    }
    case SMTPROP_IMPLY:
    {
        if (p1 != p2)
        {
            // p3\/p1
            clause1[0] = p1;
            clause1[1] = p3;
            // p3\/非p2
            clause2[0] = -p2;
            clause2[1] = p3;
            // 非p3\/非p1\/p2
            clause3[0] = -p1;
            clause3[1] = p2;
            clause3[2] = -p3;
            cnt += 3;
        }
        else
        {
            clause1[0] = p3;
            cnt += 1;
        }
        break;
    }
    case SMTPROP_IFF:
    {
        if (p1 != p2)
        {
            // p3\/p1\/p2
            clause1[0] = p1;
            clause1[1] = p2;
            clause1[2] = p3;
            // p3\/非p1\/非p2
            clause2[0] = -p1;
            clause2[1] = -p2;
            clause2[2] = p3;
            // 非p3\/p1\/非p2
            clause3[0] = p1;
            clause3[1] = -p2;
            clause3[2] = -p3;
            // 非p3\/非p1\/p2
            clause4[0] = -p1;
            clause4[1] = p2;
            clause4[2] = -p3;
            cnt += 4;
        }
        else
        {
            clause1[0] = p3;
            cnt += 1;
        }
        break;
    }
    case SMTPROP_NOT:
    {
        // p3\/p2
        clause1[0] = p2;
        clause1[1] = p3;
        // 非p3\/非p2
        clause2[0] = -p2;
        clause2[1] = -p3;
        cnt += 2;
        break;
    }
    default:
    {
        printf("error in clause_gen, invalid SMTPROP_OP\n");
        exit(-1);
        break;
    }
    }
    cnf_list *list1 = (cnf_list *)malloc(sizeof(cnf_list));
    memset(list1, 0, sizeof(cnf_list));
    cnf_list *list2 = (cnf_list *)malloc(sizeof(cnf_list));
    memset(list2, 0, sizeof(cnf_list));
    cnf_list *list3 = (cnf_list *)malloc(sizeof(cnf_list));
    memset(list3, 0, sizeof(cnf_list));
    cnf_list *list4 = (cnf_list *)malloc(sizeof(cnf_list));
    memset(list4, 0, sizeof(cnf_list));
    list1->size = size;
    list2->size = size;
    list3->size = size;
    list4->size = size;
    list1->clause = clause1;
    list2->clause = clause2;
    list3->clause = clause3;
    list4->clause = clause4;
    if (cnt == 1)
    {
        list1->next = data->cnf_res;
        data->cnf_res = list1;
        data->clause_cnt += 1;
        free(clause2);
        free(clause3);
        free(clause4);
        free(list2);
        free(list3);
        free(list4);
    }
    else if (cnt == 2)
    {
        list1->next = list2;
        list2->next = data->cnf_res;
        data->cnf_res = list1;
        data->clause_cnt += 2;
        free(clause3);
        free(clause4);
        free(list3);
        free(list4);
    }
    else if (cnt == 3)
    {
        list1->next = list2;
        list2->next = list3;
        list3->next = data->cnf_res;
        data->cnf_res = list1;
        data->clause_cnt += 3;
        free(clause4);
        free(list4);
    }
    else
    {
        list1->next = list2;
        list2->next = list3;
        list3->next = list4;
        list4->next = data->cnf_res;
        data->cnf_res = list1;
        data->clause_cnt += 4;
    }
}

int prop2cnf(SmtProp* p, PreData* data){
    int res = 0;
    switch(p->type){
        case SMTB_PROP: {
            int p1 = prop2cnf(p->prop.Binary_prop.prop1, data);
            int p2 = prop2cnf(p->prop.Binary_prop.prop2, data);
            res = ++(data->prop_cnt);
            #ifdef PREPROCESS_DEBUG
                printf("P%d = P%d op P%d\n", res, p1, p2);
            #endif
            clause_gen(p1, p2, res, p->prop.Binary_prop.op, data);
            break;
        }
        case SMTU_PROP: {
            int p1 = prop2cnf(p->prop.Unary_prop.prop1, data);
            res = ++(data->prop_cnt);
            #ifdef PREPROCESS_DEBUG
                printf("P%d = NOT P%d\n", res, p1);
            #endif
            clause_gen(0, p1, res, p->prop.Binary_prop.op, data);
            break;
        }
        case SMT_PROPVAR:
            res = p->prop.Propvar;
            break;
        default:
            printf("invalid prop type in prop2cnf\n");
            exit(-1);
            break;
    }
    return res;
}

clause_data* cnf_trans(SmtProp* p, PreData* data){
    int prop_num = prop2cnf(p, data);
    data->clause_cnt++;
    data->clause_cnt += data->ufunc_cnt;
    data->clause_cnt += data->purify_cnt;
    int** value = (int**)malloc(sizeof(int*)*(data->clause_cnt)*2);
    memset(value, 0, sizeof(int*)*(data->clause_cnt)*2);
    for(int i = 0; i < data->clause_cnt; i++){
        value[i] = (int*)malloc(sizeof(int)*data->prop_cnt);
        memset(value[i], 0, sizeof(int)*data->prop_cnt);
    }
    int* unassign_num = (int*)malloc(sizeof(int)*(data->clause_cnt)*2);
    memset(unassign_num, 0, sizeof(int)*(data->clause_cnt)*2);
    int* state = (int*)malloc(sizeof(int)*(data->clause_cnt)*2);
    memset(state, 0, sizeof(int)*(data->clause_cnt)*2);
    value[0][prop_num-1] = 1;
    unassign_num[0] = 1;
    state[0] = 2;
    int cnt = 1;
    cnf_list* tmp1 = data->cnf_res;
    while(tmp1->next != NULL){
        int size = tmp1->size;
        for(int i = 0; i < size; i++){
            if(tmp1->clause[i] > 0){
                value[cnt][tmp1->clause[i]-1] = 1;    
                unassign_num[cnt]++;  
            }
            else if(tmp1->clause[i] < 0){
                value[cnt][-tmp1->clause[i]-1] = -1;  
                unassign_num[cnt]++;
            }
        }
        if(unassign_num[cnt] == 1) state[cnt] = 2;
        else state[cnt] = -unassign_num[cnt];
        tmp1 = tmp1->next;
        cnt++;
    }
    SmtProplist* tmp2 = data->uf_purify_list;
    while(tmp2->next != 0){
        if(tmp2->prop->type != SMT_PROPVAR){
            printf("error in cnf_trans, invalid prop type\n");
            exit(-1);
        }
        value[cnt][tmp2->prop->prop.Propvar-1] = 1;
        unassign_num[cnt] = 1; 
        state[cnt] = 2;
        tmp2 = tmp2->next;
        cnt++;
    }
    tmp2 = data->lia_purify_list;
    while(tmp2->next != 0){
        if(tmp2->prop->type != SMT_PROPVAR){
            printf("error in cnf_trans, invalid prop type\n");
            exit(-1);
        }
        value[cnt][tmp2->prop->prop.Propvar-1] = 1;
        unassign_num[cnt] = 1; 
        state[cnt] = 2;
        tmp2 = tmp2->next;
        cnt++;
    }
    tmp2 = data->nia_purify_list;
    while(tmp2->next != 0){
        if(tmp2->prop->type != SMT_PROPVAR){
            printf("error in cnf_trans, invalid prop type\n");
            exit(-1);
        }
        value[cnt][tmp2->prop->prop.Propvar-1] = 1;
        unassign_num[cnt] = 1; 
        state[cnt] = 2;
        tmp2 = tmp2->next;
        cnt++;
    }
    tmp2 = data->replace_list;
    while(tmp2->next != 0){
        if(tmp2->prop->type != SMT_PROPVAR){
            printf("error in cnf_trans, invalid prop type\n");
            exit(-1);
        }
        value[cnt][tmp2->prop->prop.Propvar-1] = 1;
        unassign_num[cnt] = 1; 
        state[cnt] = 2;
        tmp2 = tmp2->next;
        cnt++;
    }
    if(cnt != data->clause_cnt){
        printf("something error in cnf_trans\n");
        printf("cnt : %d, data->clause_cnt : %d\n", cnt, data->clause_cnt);
        exit(-1);
    }
    clause_data* res = (clause_data*)malloc(sizeof(clause_data));
    memset(res, 0, sizeof(clause_data));
    res->value = value;
    res->unassign_num = unassign_num;
    res->state = state;
    res->lit_state = (int*)malloc(sizeof(int)*data->clause_cnt*2);
    memset(res->lit_state, 0, sizeof(int)*data->clause_cnt*2);
    return res;
}

sat_data* initCDCL(SmtProp* p, PreData* data){
    sat_data* s = (sat_data*)malloc(sizeof(sat_data));
    s->cl_data = cnf_trans(p, data);
    s->v_size = data->prop_cnt;
    s->cl_size = data->clause_cnt;
    s->cl_maxsize = 2*(s->cl_size);
    s->cur_dl = 0;
    int n = s->v_size;
    s->v_data = (var_data*)malloc(sizeof(var_data));
    s->v_data->value = (int*)malloc(n*sizeof(int));
    s->v_data->dl = (int*)malloc(n*sizeof(int));
    s->v_data->ancient = (int*)malloc(n*sizeof(int));
    memset(s->v_data->value, -1, sizeof(int)*n);
    memset(s->v_data->dl, -1, sizeof(int)*n);
    memset(s->v_data->ancient, -1, sizeof(int)*n);
    return s;
}


SmtProp* preprocess_data(SmtProp* p, PreData* data){
    #ifdef PREPROCESS_DEBUG
        printf("origin prop :\n");
        printSmtProp(p);
        printf("\n\n");
    #endif
    NiaPropIdentify(p);
    SmtProp* tmp = prop_purify(p, data);
    freeSmtProp(p);
    p = tmp;
    #ifdef PREPROCESS_DEBUG
        printf("prop after purify:\n");
        printSmtProp(p);
        printf("\n");
        printf("uf_purify_list:\n");
        printSmtProplist(data->uf_purify_list);
        printf("lia_purify_list:\n");
        printSmtProplist(data->lia_purify_list);
        printf("nia_purify_list:\n");
        printSmtProplist(data->nia_purify_list);
    #endif
    char* s1 = "SMT_INT8_MAX";
    char* s2 = "SMT_INT16_MAX";
    char* s3 = "SMT_INT32_MAX";
    char* s4 = "SMT_INT64_MAX";
    Hash_val* hval_1 = get_value_from_hstable(data->var_table, s1, strlen(s1));
    Hash_val* hval_2 = get_value_from_hstable(data->var_table, s2, strlen(s2));
    Hash_val* hval_3 = get_value_from_hstable(data->var_table, s3, strlen(s3));
    Hash_val* hval_4 = get_value_from_hstable(data->var_table, s4, strlen(s4));
    if(hval_1 != NULL) data->int8_max = hval_1->num;
    if(hval_2 != NULL) data->int16_max = hval_2->num;
    if(hval_3 != NULL) data->int32_max = hval_3->num;
    if(hval_4 != NULL) data->int64_max = hval_4->num;
    #ifdef PREPROCESS_DEBUG
    printf("INT8_MAX VALUE: %d\n", data->int8_max);
    printf("INT16_MAX VALUE: %d\n", data->int16_max);
    printf("INT32_MAX VALUE: %d\n", data->int32_max);
    printf("INT64_MAX VALUE: %d\n", data->int64_max);
    #endif
    init_Varlist(p, data);   
    init_proplist(p, data);
    #ifdef PREPROCESS_DEBUG
        printf("prop after prop_abstract:\n");
        printSmtProp(p);
        printf("\n");
        printf("uf_purify_list:\n");
        printSmtProplist(data->uf_purify_list);
        printf("lia_purify_list:\n");
        printSmtProplist(data->lia_purify_list);
        printf("nia_purify_list:\n");
        printSmtProplist(data->nia_purify_list);
        printf("replace_list:\n");
        printSmtProplist(data->replace_list);
    #endif
    data->at_prop_cnt = data->prop_cnt;
    #ifdef PREPROCESS_DEBUG
        for(int i = 1; i <= data->at_prop_cnt; i++){
            printSmtProp(data->prop_list[i]);
            printf("\n");
        }
    #endif
    return p;
}

sat_data* preprocess(SmtProp* p, PreData* data){
    p = preprocess_data(p, data);
    sat_data* s = initCDCL(p, data);
    return s;
}

// int main(int argc, char **argv) {
    
//     // char* x1 = "x1";
//     // char* x2 = "x2";
//     // SmtTerm* t1 = newSmtTerm(SMT_VarName, 0, 0, x1, NULL, NULL, NULL);
//     // SmtTerm* t2 = newSmtTerm(SMT_VarName, 0, 0, x2, NULL, NULL, NULL);
//     // SmtProp* p = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, t1, t2, true);
//     // printSmtProp(p);
// 	char s[80] = "input.txt";
// 	if(argc == 2)
// 	{
// 		printf("manual decided input file\n");
// 		strcpy(s,argv[1]);
// 	}
	 
// 	FILE *fp; // = the file in.
// 	fp=fopen(s, "rb");
// 	if (fp == NULL)
// 	{
// 		printf("File %s can't be opened.\n", s);
// 		exit(1);
// 	}
// 	else 
// 	{
// 		yyin = fp;
// 	}

// 	yyparse();
//     extern struct SmtProp* root;
// 	printf("\n PARSING FINISHED. \n");
//     PreData* data = initPreData();
//     sat_data* sdata = preprocess(root, data);
//     for(int i = 0; i < sdata->cl_size; i++){
//         for(int j = 0; j < sdata->v_size; j++){
//             if(sdata->cl_data->value[i][j] > 0){
//                 printf("%d ", j+1);
//             }
//             if(sdata->cl_data->value[i][j] < 0){
//                 printf("-%d ", j+1);
//             }
//         }
//         printf("\n");
//     }

// 	fclose(fp);
// }

