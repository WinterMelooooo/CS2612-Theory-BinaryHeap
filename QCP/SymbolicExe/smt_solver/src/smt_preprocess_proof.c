#include "smt_preprocess_proof.h"

//保留了vtable传递给proof
void freePredata_proof(PreData* data){
    if(data == NULL) return;
    hash_table_delete(data->ufun_table);
    hash_table_delete_trans(data->fun_var_table);
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

ProofTerm *SmtTerm2ProofTerm(SmtTerm *t, Hash_Table *vtable)
{
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    switch (t->type)
    {
    case SMT_LiaBTerm:
    case SMT_NiaBTerm:
    {
        ProofTerm *t1 = SmtTerm2ProofTerm(t->term.BTerm.t1, vtable);
        ProofTerm *t2 = SmtTerm2ProofTerm(t->term.BTerm.t2, vtable);
        res->arg_num = 2;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *)*2);
        res->args[0] = t1;
        res->args[1] = t2;
        switch (t->term.BTerm.op)
        {
        case LIA_ADD:
        {
            res->type = FUNC_ADD;
            break;
        }
        case LIA_MINUS:
        {
            res->type = FUNC_MINUS;
            break;
        }
        case LIA_MULT:
        {
            res->type = FUNC_MULT;
            break;
        }
        case LIA_DIV:
        {
            res->type = FUNC_DIV;
            break;
        }
        }
        break;
    }
    case SMT_LiaUTerm:
    {
        ProofTerm *t1 = SmtTerm2ProofTerm(t->term.UTerm.t, vtable);
        res->arg_num = 1;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *));
        res->args[0] = t1;
        res->type = FUNC_NEG;
        break;
    }
    case SMT_UFTerm:
    {
        UFunction *uf = t->term.UFTerm;
        res->arg_num = uf->numArgs;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * uf->numArgs);
        for (int i = 0; i < res->arg_num; i++)
        {
            res->args[i] = SmtTerm2ProofTerm(t->term.UFTerm->args[i], vtable);
        }
        res->func_name.name = (char *)malloc(sizeof(char) * (strlen(uf->name) + 1));
        strcpy(res->func_name.name, uf->name);
        res->type = FUNC_N;
        break;
    }
    case SMT_ConstNum:
    {
        res->arg_num = 0;
        res->args = NULL;
        res->type = INT_CONST;
        res->func_name.const_val = t->term.ConstNum;
        break;
    }
    case SMT_VarNum:
    {
        res->arg_num = 0;
        res->args = NULL;
        res->type = VAR;
        res->func_name.node_number = t->term.ConstNum;
        break;
    }
    case SMT_VarName:
    {
        char *s = t->term.Variable;
        Hash_val *hval = get_value_from_hstable(vtable, s, strlen(s));
        if (hval == NULL)
        {
            printf("error in SmtTerm2ProofTerm, null hash val\n");
            exit(-1);
        }
        res->args = NULL;
        res->type = VAR;
        res->func_name.node_number = hval->num;
        break;
    }
    default:
    {
        printf("error in SmtTerm2ProofTerm, invalid type\n");
        exit(-1);
    }
    }
    return res;
}

ProofTerm *SmtProp2ProofTerm(SmtProp *p, Hash_Table *vtable)
{
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    switch (p->type)
    {
    case SMTB_PROP:
    {
        res->arg_num = 2;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * 2);
        res->args[0] = SmtProp2ProofTerm(p->prop.Binary_prop.prop1, vtable);
        res->args[1] = SmtProp2ProofTerm(p->prop.Binary_prop.prop2, vtable);
        switch (p->prop.Binary_prop.op)
        {
        case SMTPROP_AND:
        {
            res->type = FUNC_AND;
            break;
        }
        case SMTPROP_OR:
        {
            res->type = FUNC_OR;
            break;
        }
        case SMTPROP_IMPLY:
        {
            res->type = FUNC_IMPLY;
            break;
        }
        case SMTPROP_IFF:
        {
            res->type = FUNC_IFF;
            break;
        }
        }
        break;
    }
    case SMTU_PROP:
    {
        res->arg_num = 1;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *));
        res->args[0] = SmtProp2ProofTerm(p->prop.Unary_prop.prop1, vtable);
        res->type = FUNC_NOT;
        break;
    }
    case SMTAT_PROP_EQ:
    case SMTAT_PROP_UF_EQ:
    case SMTAT_PROP_LIA_EQ:
    case SMTAT_PROP_NIA_EQ:
    {
        res->arg_num = 2;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * 2);
        res->args[0] = SmtTerm2ProofTerm(p->prop.Atomic_prop.term1, vtable);
        res->args[1] = SmtTerm2ProofTerm(p->prop.Atomic_prop.term2, vtable);
        res->type = FUNC_EQ;
        break;
    }
    case SMTAT_PROP_LIA:
    {
        res->arg_num = 2;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * 2);
        res->args[0] = SmtTerm2ProofTerm(p->prop.Atomic_prop.term1, vtable);
        res->args[1] = SmtTerm2ProofTerm(p->prop.Atomic_prop.term2, vtable);
        switch (p->prop.Atomic_prop.op)
        {
        case SMT_EQ:
        {
            res->type = FUNC_EQ;
            break;
        }
        case SMT_LE:
        {
            res->type = FUNC_LE;
            break;
        }
        case SMT_LT:
        {
            res->type = FUNC_LT;
            break;
        }
        case SMT_GE:
        {
            res->type = FUNC_GE;
            break;
        }
        case SMT_GT:
        {
            res->type = FUNC_GT;
            break;
        }
        }
        break;
    }
    case SMT_PROPVAR:
    {
        res->arg_num = 0;
        res->args = NULL;
        res->type = PROP_VAR;
        res->func_name.node_number = p->prop.Propvar;
        break;
    }
    case SMTTF_PROP:
    {
        res->arg_num = 0;
        res->args = NULL;
        if (p->prop.TF)
            res->type = PROP_TRUE;
        else
            res->type = PROP_FALSE;
        break;
    }
    default:
    {
        printf("error in SmtProp2Proofterm, invalid type\n");
        exit(-1);
    }
    }
    return res;
}

// 在purify时，给UFterm起新的变量名，并且增加新的约束，返回新的变量名
// 在做uf相关的变量替代(flatten)时，作用类似
//  mode = 0 => purify
//  mode = 1 => uf_flatten
SmtTerm *new_name_UFterm_proof(SmtTerm *t, PreData *data, ProofData *pdata, int mode)
{
    SmtTerm *res = NULL;
    if (t->type != SMT_UFTerm)
    {
        printf("\ninvalid term : \n");
        printSmtTerm(t);
        printf("\ninvalid type in new_name_UFterm\n");
        exit(-1);
    }
    char *key1 = UFunction_str(t->term.UFTerm);
    Hash_val *tmp_val = get_value_from_hstable(data->uf_purify_table, key1, strlen(key1));
    if (tmp_val == NULL)
    {
        tmp_val = initHashVal();
        Hash_val *var_val = initHashVal();
        data->var_cnt++;
        tmp_val->num = data->var_cnt;
        var_val->num = data->var_cnt;
        if (mode == 1)
        {
            ++data->ufunc_cnt;
            sprintf(var_val->name, "f_e%d", data->ufunc_cnt);
            char *arg1 = t->term.UFTerm->args[0]->term.Variable;
            char *arg2 = t->term.UFTerm->args[1]->term.Variable;
            Hash_val *v1 = get_value_from_hstable(data->var_table, arg1, strlen(arg1));
            Hash_val *v2 = get_value_from_hstable(data->var_table, arg2, strlen(arg2));
            if (v1 == NULL || v2 == NULL)
            {
                printf("error in new_uf_name, null hashval\n");
                exit(-1);
            }
            UF_Hash *uf_val = (UF_Hash *)malloc(sizeof(UF_Hash));
            uf_val->arg1 = v1->num;
            uf_val->arg2 = v2->num;
            char *key = var_val->name;
            add_node2HashTable(data->ufun_table, key, strlen(key), uf_val);
        }
        else
        {
            ++data->purify_cnt;
            sprintf(var_val->name, "v_a%d", data->purify_cnt);
            // 生成 set uf = v_ai 的证明
            ProofTerm *t1 = SmtTerm2ProofTerm(t, data->var_table);
            SET_VAR_gen(t1, data->var_cnt, pdata);
        }
        strcpy(tmp_val->name, var_val->name);
        add_node2HashTable(data->uf_purify_table, key1, strlen(key1), tmp_val);
        add_node2HashTable(data->var_table, var_val->name, strlen(var_val->name), var_val);
        // 添加新约束
        SmtTerm *new_var = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
        SmtProp *new_prop = newSmtProp(SMTAT_PROP_UF_EQ, SMT_EQ, NULL, NULL, copy_SmtTerm(t), new_var, true);
        SmtProplist *new_constrain = (SmtProplist *)malloc(sizeof(SmtProplist));
        memset(new_constrain, 0, sizeof(SmtProplist));
        new_constrain->prop = new_prop;
        if (mode == 0)
        {
            new_constrain->next = data->uf_purify_list;
            data->uf_purify_list = new_constrain;
        }
        else if (mode == 1)
        {
            new_constrain->next = data->replace_list;
            data->replace_list = new_constrain;
        }
        res = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
    }
    else
    {
        res = newSmtTerm(SMT_VarName, 0, 0, tmp_val->name, NULL, NULL, NULL);
    }
    return res;
}

// 在purify时，给Niaterm起新的变量名，并且增加新的约束，返回新的变量名
SmtTerm *new_name_Niaterm_proof(SmtTerm *t, PreData *data, ProofData *pdata)
{
    SmtTerm *res = NULL;
    if (t->type != SMT_NiaBTerm)
    {
        printf("\ninvalid term : \n");
        printSmtTerm(t);
        printf("\ninvalid type in new_name_Niaterm\n");
        exit(-1);
    }
    char *key1 = LiaTerm_str(t);
    Hash_val *tmp_val = get_value_from_hstable(data->nia_purify_table, key1, strlen(key1));
    if (tmp_val == NULL)
    {
        tmp_val = initHashVal();
        Hash_val *var_val = initHashVal();
        data->var_cnt++;
        data->purify_cnt++;
        tmp_val->num = data->var_cnt;
        var_val->num = data->var_cnt;
        sprintf(tmp_val->name, "v_a%d", data->purify_cnt);
        sprintf(var_val->name, "v_a%d", data->purify_cnt);
        add_node2HashTable(data->nia_purify_table, key1, strlen(key1), tmp_val);
        add_node2HashTable(data->var_table, var_val->name, strlen(var_val->name), var_val);
        // 添加新约束
        SmtTerm *new_var = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
        SmtProp *new_prop = newSmtProp(SMTAT_PROP_NIA_EQ, SMT_EQ, NULL, NULL, copy_SmtTerm(t), new_var, true);
        SmtProplist *new_constrain = (SmtProplist *)malloc(sizeof(SmtProplist));
        memset(new_constrain, 0, sizeof(SmtProplist));
        new_constrain->prop = new_prop;
        new_constrain->next = data->nia_purify_list;
        data->nia_purify_list = new_constrain;
        res = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
        // 生成 SET t = new_var的证明
        ProofTerm *t1 = SmtTerm2ProofTerm(t, data->var_table);
        SET_VAR_gen(t1, data->var_cnt, pdata);
    }
    else
    {
        res = newSmtTerm(SMT_VarName, 0, 0, tmp_val->name, NULL, NULL, NULL);
    }
    return res;
}

// 在purify时，给Liaterm起新的变量名，并且增加新的约束，返回新的变量名
SmtTerm *new_name_Liaterm_proof(SmtTerm *t, PreData *data, ProofData *pdata)
{
    SmtTerm *res = NULL;
    if (t->type != SMT_LiaBTerm && t->type != SMT_LiaUTerm && t->type != SMT_ConstNum)
    {
        printf("\ninvalid term : \n");
        printSmtTerm(t);
        printf("\ninvalid type in new_name_Liaterm\n");
        exit(-1);
    }
    char *key1 = LiaTerm_str(t);
    Hash_val *tmp_val = get_value_from_hstable(data->lia_purify_table, key1, strlen(key1));
    if (tmp_val == NULL)
    {
        tmp_val = initHashVal();
        Hash_val *var_val = initHashVal();
        data->var_cnt++;
        data->purify_cnt++;
        tmp_val->num = data->var_cnt;
        var_val->num = data->var_cnt;
        sprintf(tmp_val->name, "v_a%d", data->purify_cnt);
        sprintf(var_val->name, "v_a%d", data->purify_cnt);
        add_node2HashTable(data->lia_purify_table, key1, strlen(key1), tmp_val);
        add_node2HashTable(data->var_table, var_val->name, strlen(var_val->name), var_val);
        // 添加新约束
        SmtTerm *new_var = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
        SmtProp *new_prop = newSmtProp(SMTAT_PROP_LIA_EQ, SMT_EQ, NULL, NULL, copy_SmtTerm(t), new_var, true);
        SmtProplist *new_constrain = (SmtProplist *)malloc(sizeof(SmtProplist));
        memset(new_constrain, 0, sizeof(SmtProplist));
        new_constrain->prop = new_prop;
        new_constrain->next = data->lia_purify_list;
        data->lia_purify_list = new_constrain;
        res = newSmtTerm(SMT_VarName, 0, 0, var_val->name, NULL, NULL, NULL);
        // 生成 SET t = new_var的证明
        ProofTerm *t1 = SmtTerm2ProofTerm(t, data->var_table);
        SET_VAR_gen(t1, data->var_cnt, pdata);
    }
    else
    {
        res = newSmtTerm(SMT_VarName, 0, 0, tmp_val->name, NULL, NULL, NULL);
    }
    return res;
}

SmtTerm *updateSmtTerm_proof(SmtTerm *t, PreData *data, int mode, ProofData *pdata)
{
    if (mode == SMT_LiaBTerm || mode == SMT_LiaUTerm)
    {
        // 用于lia运算符(+,-)两边
        if (t->type == SMT_UFTerm)
        {
            SmtTerm *tmp = new_name_UFterm_proof(t, data, pdata, 0);
            freeSmtTerm(t);
            t = tmp;
        }
        else if (t->type == SMT_NiaBTerm)
        {
            SmtTerm *tmp = new_name_Niaterm_proof(t, data, pdata);
            freeSmtTerm(t);
            t = tmp;
        }
    }
    else if (mode == SMT_UFTerm)
    {
        // 用于uf的参数
        if (t->type == SMT_LiaBTerm || t->type == SMT_LiaUTerm || t->type == SMT_ConstNum)
        {
            SmtTerm *tmp = new_name_Liaterm_proof(t, data, pdata);
            freeSmtTerm(t);
            t = tmp;
        }
        else if (t->type == SMT_NiaBTerm)
        {
            SmtTerm *tmp = new_name_Niaterm_proof(t, data, pdata);
            freeSmtTerm(t);
            t = tmp;
        }
    }
    else if (mode == SMT_NiaBTerm)
    {
        // 用于nia运算符(*,/)两边
        if (t->type == SMT_UFTerm)
        {
            SmtTerm *tmp = new_name_UFterm_proof(t, data, pdata, 0);
            freeSmtTerm(t);
            t = tmp;
        }
        else if (t->type == SMT_LiaBTerm || t->type == SMT_LiaUTerm)
        {
            SmtTerm *tmp = new_name_Liaterm_proof(t, data, pdata);
            freeSmtTerm(t);
            t = tmp;
        }
    }
    return t;
}

SmtTerm *term_purify_proof(SmtTerm *t, PreData *data, ProofData *pdata)
{
    SmtTerm *res = NULL;
    switch (t->type)
    {
    case SMT_LiaBTerm:
    {
        SmtTerm *t1 = term_purify_proof(t->term.BTerm.t1, data, pdata);
        SmtTerm *t2 = term_purify_proof(t->term.BTerm.t2, data, pdata);
        t1 = updateSmtTerm_proof(t1, data, SMT_LiaBTerm, pdata);
        t2 = updateSmtTerm_proof(t2, data, SMT_LiaBTerm, pdata);
        res = newSmtTerm(t->type, t->term.BTerm.op, 0, NULL, NULL, t1, t2);
        break;
    }
    case SMT_LiaUTerm:
    {
        SmtTerm *t1 = term_purify_proof(t->term.BTerm.t1, data, pdata);
        t1 = updateSmtTerm_proof(t1, data, SMT_LiaUTerm, pdata);
        res = newSmtTerm(t->type, t->term.UTerm.op, 0, NULL, NULL, t1, NULL);
        break;
    }
    case SMT_NiaBTerm:
    {
        SmtTerm *t1 = term_purify_proof(t->term.BTerm.t1, data, pdata);
        SmtTerm *t2 = term_purify_proof(t->term.BTerm.t2, data, pdata);
        t1 = updateSmtTerm_proof(t1, data, SMT_NiaBTerm, pdata);
        t2 = updateSmtTerm_proof(t2, data, SMT_NiaBTerm, pdata);
        res = newSmtTerm(t->type, t->term.BTerm.op, 0, NULL, NULL, t1, t2);
        break;
    }
    case SMT_UFTerm:
    {
        res = copy_SmtTerm(t);
        for (int i = 0; i < t->term.UFTerm->numArgs; i++)
        {
            SmtTerm *argi = term_purify_proof(t->term.UFTerm->args[i], data, pdata);
            argi = updateSmtTerm_proof(argi, data, SMT_UFTerm, pdata);
            freeSmtTerm(res->term.UFTerm->args[i]);
            res->term.UFTerm->args[i] = argi;
        }
        int len = strlen(t->term.UFTerm->name);
        Hash_val *tmp_val = get_value_from_hstable(data->fun_var_table, t->term.UFTerm->name, len);
        if(tmp_val == NULL){
            tmp_val = initHashVal();
            strcpy(tmp_val->name, t->term.UFTerm->name);
            tmp_val->num = 1;
            add_node2HashTable(data->fun_var_table, t->term.UFTerm->name, len, tmp_val);
            ProofNode* node = newDeclareNode(0, t->term.UFTerm->name);
            pdata->declare_num++;
            updata_DeclareData(node, pdata);
        }
        break;
    }
    case SMT_VarName:
    {
        int len = strlen(t->term.Variable);
        Hash_val *tmp_val = get_value_from_hstable(data->var_table, t->term.Variable, len);
        if (tmp_val == NULL)
        {
            tmp_val = initHashVal();
            strcpy(tmp_val->name, t->term.Variable);
            tmp_val->num = ++(data->var_cnt);
            add_node2HashTable(data->var_table, t->term.Variable, len, tmp_val);
            //此处进行变量声明
            ProofNode* node = newDeclareNode(data->var_cnt, t->term.Variable);
            pdata->declare_num++;
            updata_DeclareData(node, pdata);
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

SmtProp *prop_purify_proof(SmtProp *p, PreData *data, ProofData *pdata)
{
    SmtProp *res = NULL;
    switch (p->type)
    {
    case SMTB_PROP:
    {
        SmtProp *prop1 = prop_purify_proof(p->prop.Binary_prop.prop1, data, pdata);
        SmtProp *prop2 = prop_purify_proof(p->prop.Binary_prop.prop2, data, pdata);
        res = newSmtProp(SMTB_PROP, p->prop.Binary_prop.op, prop1, prop2, NULL, NULL, true);
        break;
    }
    case SMTU_PROP:
    {
        SmtProp *prop1 = prop_purify_proof(p->prop.Unary_prop.prop1, data, pdata);
        res = newSmtProp(SMTU_PROP, p->prop.Unary_prop.op, prop1, NULL, NULL, NULL, true);
        break;
    }
    case SMTAT_PROP_LIA:
    {
        SmtTerm *term1 = term_purify_proof(p->prop.Atomic_prop.term1, data, pdata);
        SmtTerm *term2 = term_purify_proof(p->prop.Atomic_prop.term2, data, pdata);
        term1 = updateSmtTerm_proof(term1, data, SMT_LiaBTerm, pdata);
        term2 = updateSmtTerm_proof(term2, data, SMT_LiaBTerm, pdata);
        res = newSmtProp(SMTAT_PROP_LIA, p->prop.Atomic_prop.op, NULL, NULL, term1, term2, true);
        break;
    }
    case SMTAT_PROP_EQ:
    {
        SmtTerm *term1 = term_purify_proof(p->prop.Atomic_prop.term1, data, pdata);
        SmtTerm *term2 = term_purify_proof(p->prop.Atomic_prop.term2, data, pdata);
        term1 = updateSmtTerm_proof(term1, data, SMT_UFTerm, pdata);
        term2 = updateSmtTerm_proof(term2, data, SMT_UFTerm, pdata);
        res = newSmtProp(SMTAT_PROP_EQ, p->prop.Atomic_prop.op, NULL, NULL, term1, term2, true);
        if (term1->type == SMT_UFTerm || term2->type == SMT_UFTerm)
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

// 生成purify时set a = b的证明
// 生成purify前后的证明 p |- purify(p)
SmtProp *preprocess_data_proof(SmtProp *p, PreData *data, ProofData *pdata)
{
#ifdef PREPROCESS_DEBUG
    printf("origin prop :\n");
    printSmtProp(p);
    printf("\n\n");
#endif
    NiaPropIdentify(p);
    SmtProp *tmp = copy_SmtProp(p);
    pdata->cur_num++; // 预留第一个位置用于原始假设
    SmtProp* tmp1 = prop_purify_proof(p, data, pdata);
    freeSmtProp(p);
    p = tmp1;
    // 生成 p |- purify(p)的证明
    ProofTerm *origin_p = SmtProp2ProofTerm(tmp, data->var_table);
    #ifdef SMT_PROOF_DEBUG
    printProofTerm(origin_p);
    printf("end print\n");
    #endif
    freeSmtProp(tmp);
    ProofTerm *new_p = SmtProp2ProofTerm(p, data->var_table);
    int *plist = (int *)malloc(sizeof(int));
    plist[0] = preprocess_assume(origin_p, pdata);
    pdata->cur_num++;
    #ifdef SMT_PROOF_DEBUG
    printf("cur_num : %d\n", pdata->cur_num);
    #endif
    ProofNode *node = newProofNode(plist, pdata->cur_num, SUB_VAR, new_p, NULL, 1);
    int ans = updata_proofdata_preprocess(pdata, node);
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
    char *s1 = "SMT_INT8_MAX";
    char *s2 = "SMT_INT16_MAX";
    char *s3 = "SMT_INT32_MAX";
    char *s4 = "SMT_INT64_MAX";
    Hash_val *hval_1 = get_value_from_hstable(data->var_table, s1, strlen(s1));
    Hash_val *hval_2 = get_value_from_hstable(data->var_table, s2, strlen(s2));
    Hash_val *hval_3 = get_value_from_hstable(data->var_table, s3, strlen(s3));
    Hash_val *hval_4 = get_value_from_hstable(data->var_table, s4, strlen(s4));
    if (hval_1 != NULL)
        data->int8_max = hval_1->num;
    if (hval_2 != NULL)
        data->int16_max = hval_2->num;
    if (hval_3 != NULL)
        data->int32_max = hval_3->num;
    if (hval_4 != NULL)
        data->int64_max = hval_4->num;
#ifdef PREPROCESS_DEBUG
    printf("INT8_MAX VALUE: %d\n", data->int8_max);
    printf("INT16_MAX VALUE: %d\n", data->int16_max);
    printf("INT32_MAX VALUE: %d\n", data->int32_max);
    printf("INT64_MAX VALUE: %d\n", data->int64_max);
#endif
    init_Varlist(p, data);
    // 完成给原子命题起编号，并生成对应证明
    init_proplist_proof(p, data, pdata);
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
    for (int i = 1; i <= data->at_prop_cnt; i++)
    {
        printSmtProp(data->prop_list[i]);
        printf("\n");
    }
#endif
    return p;
}

// 给原子命题编号
// SET_PROP atomic_p = Pvar
int add_prop2HashTable_proof(SmtProp *p, PreData *data, ProofData *pdata)
{
    switch (p->type)
    {
    case SMTB_PROP:
        add_prop2HashTable_proof(p->prop.Binary_prop.prop1, data, pdata);
        add_prop2HashTable_proof(p->prop.Binary_prop.prop2, data, pdata);
        break;
    case SMTU_PROP:
        add_prop2HashTable_proof(p->prop.Unary_prop.prop1, data, pdata);
        break;
    case SMTAT_PROP_EQ:
    case SMTAT_PROP_LIA:
    case SMTAT_PROP_UF_EQ:
    case SMTAT_PROP_LIA_EQ:
    case SMTAT_PROP_NIA_EQ:
    {
        char *key = AtomicProp_str(p);
        int len = strlen(key);
        Hash_val *hval = get_value_from_hstable(data->prop_table, key, len);
        if (hval == NULL)
        {
            hval = initHashVal();
            free(hval->name);
            hval->name = NULL;
            hval->num = ++(data->prop_cnt);
#ifdef PREPROCESS_DEBUG
            printf("atomic prop : %s\n", key);
            printf("data->prop_cnt: %d\n", data->prop_cnt);
#endif
            add_node2HashTable(data->prop_table, key, len, hval);
            // 证明生成
            ProofTerm *t1 = SmtProp2ProofTerm(p, data->var_table);
            ProofTerm *t2 = newPropVarTerm(hval->num);
            ProofTerm *t = newEqProofTerm2(t1, t2);
            ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
            arg->type = PTERM;
            arg->args.pterm = t;
            pdata->cur_num++;
            ProofNode *node = newProofNode(NULL, pdata->cur_num, SET_PROP, copy_ProofTerm(t), arg, 0);
            #ifdef SMT_PROOF_DEBUG
            printProofNode(pdata, node);
            #endif
            return updata_proofdata_preprocess(pdata, node);
        }
        break;
    }
    default:
        break;
    }
    return 0;
}

// 由 atomic_p , atomic_p = Pvar |- Pvar
void add_proplist2HashTable_proof(SmtProplist *p, PreData *data, ProofData *pdata)
{
    SmtProplist *tmp = p;
    while (tmp->next != NULL)
    {
        ProofTerm *p = SmtProp2ProofTerm(tmp->prop, data->var_table);
        char *s = ProofTerm2str(p);
        int *hval = get_value_from_hstable(pdata->global_table, s, strlen(s));
        if (hval == NULL)
        {
            printf("error in add_proplist2HashTable_proof, atomic_p should have been added\n");
            exit(-1);
        }
        int *plist = (int *)malloc(sizeof(int) * 2);
        plist[0] = *hval;
        plist[1] = add_prop2HashTable_proof(tmp->prop, data, pdata);
        if (plist[1] == 0)
        {
            printf("error in add_proplist2HashTable_proof, add_prop2HashTable_proof fail\n");
            exit(-1);
        }
        pdata->cur_num++;
        ProofTerm *concl = newPropVarTerm(data->prop_cnt);
        ProofNode *node = newProofNode(plist, pdata->cur_num, EQUALITY_RESOLUTION, concl, NULL, 2);
        updata_proofdata_preprocess(pdata, node);
        tmp = tmp->next;
    }
}

// 生成SUB_PROP P |-- 将P中原子命题用编号替代后的结果
// 其他purify list中的命题，对应的步骤由add_proplist2HashTable_proof生成
// 返回SUB_PROP步骤的编号
int init_proplist_proof(SmtProp *p, PreData *data, ProofData *pdata)
{
    add_prop2HashTable_proof(p, data, pdata);
    add_proplist2HashTable_proof(data->lia_purify_list, data, pdata);
    add_proplist2HashTable_proof(data->uf_purify_list, data, pdata);
    add_proplist2HashTable_proof(data->nia_purify_list, data, pdata);
    add_proplist2HashTable_proof(data->replace_list, data, pdata);
    data->prop_list = (SmtProp **)malloc(sizeof(SmtProp *) * (data->prop_cnt + 1));
    memset(data->prop_list, 0, sizeof(SmtProp *) * (data->prop_cnt + 1));
    int num = search_prop(p, data, pdata->global_table);
    int *plist = (int *)malloc(sizeof(int));
    plist[0] = num;
    init_propvar(p, data);
    ProofTerm *concl = SmtProp2ProofTerm(p, data->var_table);
    pdata->cur_num++;
    ProofNode *node = newProofNode(plist, pdata->cur_num, SUB_PROP, concl, NULL, 1);
    int ans = updata_proofdata_preprocess(pdata, node);
    init_propvar_list(data->lia_purify_list, data);
    init_propvar_list(data->uf_purify_list, data);
    init_propvar_list(data->nia_purify_list, data);
    init_propvar_list(data->replace_list, data);
}

// 生成p3<->(p1 op p2)对应的cnf中的clause
// p3<->not p2 (op为 not时， 此时p1缺省为0)
// 生成证明：SET_PROP: p3<->(p1 op p2) / p3<->not p2
// 生成证明：p3<->(p1 op p2) |— cnf格式 (...\/...) /\ (...\/...) /\ (...\/...)
// 生成证明：AND_ELIM: (...\/...) /\ (...\/...) /\ (...\/...) |-- ...\/...
void clause_gen_proof(int p1, int p2, int p3, int op, PreData *data, ProofData *pdata)
{
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
    int snode = SET_PROP_gen(p1, p2, p3, op, pdata);
    int cnt = 0;
    switch (op)
    {
    case SMTPROP_OR:
    {
        ProofTerm *t1 = newOrProp(-p1, p3, 0, 2);
        ProofTerm *t2 = newOrProp(-p2, p3, 0, 2);
        ProofTerm *t3 = NULL;
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
            t3 = newOrProp(p1, p2, -p3, 3);
        }
        else
        {
            clause3[0] = p1;
            clause3[1] = -p3;
            t3 = newOrProp(p1, -p3, 0, 2);
        }
        cnt += 3;
        ProofTerm *cnfp = newAndProp(t1, t2, t3, NULL, 3);
        int ans = cnf_trans_proofgen(snode, cnfp, pdata);
        AND_ELIM_proof(ans, cnfp, pdata);
        break;
    }
    case SMTPROP_AND:
    {
        ProofTerm *t1 = newOrProp(p1, -p3, 0, 2);
        ProofTerm *t2 = newOrProp(p2, -p3, 0, 2);
        ProofTerm *t3 = NULL;
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
            t3 = newOrProp(-p1, -p2, p3, 3);
        }
        else
        {
            clause3[0] = -p1;
            clause3[1] = p3;
            t3 = newOrProp(-p1, p3, 0, 2);
        }
        cnt += 3;
        ProofTerm *cnfp = newAndProp(t1, t2, t3, NULL, 3);
        int ans = cnf_trans_proofgen(snode, cnfp, pdata);
        AND_ELIM_proof(ans, cnfp, pdata);
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
            ProofTerm *t1 = newOrProp(p1, p3, 0, 2);
            ProofTerm *t2 = newOrProp(-p2, p3, 0, 2);
            ProofTerm *t3 = newOrProp(-p1, p2, -p3, 3);
            ProofTerm *cnfp = newAndProp(t1, t2, t3, NULL, 3);
            int ans = cnf_trans_proofgen(snode, cnfp, pdata);
            AND_ELIM_proof(ans, cnfp, pdata);
            cnt += 3;
        }
        else
        {
            clause1[0] = p3;
            ProofTerm *t = newNotProp(p3);
            int ans = cnf_trans_proofgen(snode, t, pdata);
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
            ProofTerm *t1 = newOrProp(p1, p2, p3, 3);
            ProofTerm *t2 = newOrProp(-p1, -p2, p3, 3);
            ProofTerm *t3 = newOrProp(p1, -p2, -p3, 3);
            ProofTerm *t4 = newOrProp(-p1, p2, -p3, 3);
            ProofTerm *cnfp = newAndProp(t1, t2, t3, t4, 4);
            int ans = cnf_trans_proofgen(snode, cnfp, pdata);
            AND_ELIM_proof(ans, cnfp, pdata);
            cnt += 4;
        }
        else
        {
            clause1[0] = p3;
            ProofTerm *t = newNotProp(p3);
            int ans = cnf_trans_proofgen(snode, t, pdata);
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
        ProofTerm *t1 = newOrProp(p2, p3, 0, 2);
        ProofTerm *t2 = newOrProp(-p2, -p3, 0, 2);
        ProofTerm *cnfp = newAndProp(t1, t2, NULL, NULL, 2);
        int ans = cnf_trans_proofgen(snode, cnfp, pdata);
        AND_ELIM_proof(ans, cnfp, pdata);
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

int prop2cnf_proof(SmtProp *p, PreData *data, ProofData *pdata)
{
    int res = 0;
    switch (p->type)
    {
    case SMTB_PROP:
    {
        int p1 = prop2cnf_proof(p->prop.Binary_prop.prop1, data, pdata);
        int p2 = prop2cnf_proof(p->prop.Binary_prop.prop2, data, pdata);
        res = ++(data->prop_cnt);
#ifdef PREPROCESS_DEBUG
        printf("P%d = P%d op P%d\n", res, p1, p2);
#endif
        clause_gen_proof(p1, p2, res, p->prop.Binary_prop.op, data, pdata);
        break;
    }
    case SMTU_PROP:
    {
        int p1 = prop2cnf_proof(p->prop.Unary_prop.prop1, data, pdata);
        res = ++(data->prop_cnt);
#ifdef PREPROCESS_DEBUG
        printf("P%d = NOT P%d\n", res, p1);
#endif
        clause_gen_proof(0, p1, res, p->prop.Binary_prop.op, data, pdata);
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

clause_data *cnf_trans_proof(SmtProp *p, PreData *data, ProofData *pdata)
{
    int prop_num = prop2cnf_proof(p, data, pdata);
    data->clause_cnt++;
    data->clause_cnt += data->ufunc_cnt;
    data->clause_cnt += data->purify_cnt;
    int **value = (int **)malloc(sizeof(int *) * (data->clause_cnt) * 2);
    memset(value, 0, sizeof(int *) * (data->clause_cnt) * 2);
    for (int i = 0; i < data->clause_cnt; i++)
    {
        value[i] = (int *)malloc(sizeof(int) * data->prop_cnt);
        memset(value[i], 0, sizeof(int) * data->prop_cnt);
    }
    int *unassign_num = (int *)malloc(sizeof(int) * (data->clause_cnt) * 2);
    memset(unassign_num, 0, sizeof(int) * (data->clause_cnt) * 2);
    int *state = (int *)malloc(sizeof(int) * (data->clause_cnt) * 2);
    memset(state, 0, sizeof(int) * (data->clause_cnt) * 2);
    value[0][prop_num - 1] = 1;
    unassign_num[0] = 1;
    state[0] = 2;
    int cnt = 1;
    cnf_list *tmp1 = data->cnf_res;
    while (tmp1->next != NULL)
    {
        int size = tmp1->size;
        for (int i = 0; i < size; i++)
        {
            if (tmp1->clause[i] > 0)
            {
                value[cnt][tmp1->clause[i] - 1] = 1;
                unassign_num[cnt]++;
            }
            else if (tmp1->clause[i] < 0)
            {
                value[cnt][-tmp1->clause[i] - 1] = -1;
                unassign_num[cnt]++;
            }
        }
        if (unassign_num[cnt] == 1)
            state[cnt] = 2;
        else
            state[cnt] = -unassign_num[cnt];
        tmp1 = tmp1->next;
        cnt++;
    }
    SmtProplist *tmp2 = data->uf_purify_list;
    while (tmp2->next != 0)
    {
        if (tmp2->prop->type != SMT_PROPVAR)
        {
            printf("error in cnf_trans, invalid prop type\n");
            exit(-1);
        }
        value[cnt][tmp2->prop->prop.Propvar - 1] = 1;
        unassign_num[cnt] = 1;
        state[cnt] = 2;
        tmp2 = tmp2->next;
        cnt++;
    }
    tmp2 = data->lia_purify_list;
    while (tmp2->next != 0)
    {
        if (tmp2->prop->type != SMT_PROPVAR)
        {
            printf("error in cnf_trans, invalid prop type\n");
            exit(-1);
        }
        value[cnt][tmp2->prop->prop.Propvar - 1] = 1;
        unassign_num[cnt] = 1;
        state[cnt] = 2;
        tmp2 = tmp2->next;
        cnt++;
    }
    tmp2 = data->nia_purify_list;
    while (tmp2->next != 0)
    {
        if (tmp2->prop->type != SMT_PROPVAR)
        {
            printf("error in cnf_trans, invalid prop type\n");
            exit(-1);
        }
        value[cnt][tmp2->prop->prop.Propvar - 1] = 1;
        unassign_num[cnt] = 1;
        state[cnt] = 2;
        tmp2 = tmp2->next;
        cnt++;
    }
    tmp2 = data->replace_list;
    while (tmp2->next != 0)
    {
        if (tmp2->prop->type != SMT_PROPVAR)
        {
            printf("error in cnf_trans, invalid prop type\n");
            exit(-1);
        }
        value[cnt][tmp2->prop->prop.Propvar - 1] = 1;
        unassign_num[cnt] = 1;
        state[cnt] = 2;
        tmp2 = tmp2->next;
        cnt++;
    }
    if (cnt != data->clause_cnt)
    {
        printf("something error in cnf_trans\n");
        printf("cnt : %d, data->clause_cnt : %d\n", cnt, data->clause_cnt);
        exit(-1);
    }
    clause_data *res = (clause_data *)malloc(sizeof(clause_data));
    memset(res, 0, sizeof(clause_data));
    res->value = value;
    res->unassign_num = unassign_num;
    res->state = state;
    res->lit_state = (int *)malloc(sizeof(int) * data->clause_cnt * 2);
    memset(res->lit_state, 0, sizeof(int) * data->clause_cnt * 2);
    return res;
}

sat_data *initCDCL_proof(SmtProp *p, PreData *data, ProofData *pdata)
{
    sat_data *s = (sat_data *)malloc(sizeof(sat_data));
    s->cl_data = cnf_trans_proof(p, data, pdata);
    s->v_size = data->prop_cnt;
    s->cl_size = data->clause_cnt;
    s->cl_maxsize = 2 * (s->cl_size);
    s->cur_dl = 0;
    int n = s->v_size;
    s->v_data = (var_data *)malloc(sizeof(var_data));
    s->v_data->value = (int *)malloc(n * sizeof(int));
    s->v_data->dl = (int *)malloc(n * sizeof(int));
    s->v_data->ancient = (int *)malloc(n * sizeof(int));
    memset(s->v_data->value, -1, sizeof(int) * n);
    memset(s->v_data->dl, -1, sizeof(int) * n);
    memset(s->v_data->ancient, -1, sizeof(int) * n);
    return s;
}

sat_data *preprocess_proof(SmtProp *p, PreData *data, ProofData *pdata)
{
    p = preprocess_data_proof(p, data, pdata);
    int num = pdata->cur_num; // 此时cur_num应该为SUB_PROP的证明步骤
    sat_data *s = initCDCL_proof(p, data, pdata);
    ProofTerm *concl = newPropVarTerm(data->prop_cnt); // 此时prop_cnt应该为转cnf时最后set的命题变元的编号
    pdata->cur_num++;
    int *plist = (int *)malloc(sizeof(int));
    plist[0] = num;
    ProofNode *node = newProofNode(plist, pdata->cur_num, SUB_PROP_IFF, concl, NULL, 1);
    updata_proofdata_preprocess(pdata, node);
    return s;
}

// SET t1 = var_id
int SET_VAR_gen(ProofTerm *t1, int id, ProofData *pdata)
{
    ProofTerm *t2 = newVarTerm(id);
    ProofTerm *t3 = newEqProofTerm2(t1, t2);
    ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
    arg->type = PTERM;
    arg->args.pterm = t3;
    pdata->cur_num++;
    ProofNode *node = newProofNode(NULL, pdata->cur_num, SET_VAR, copy_ProofTerm(t3), arg, 0);
    return updata_proofdata_preprocess(pdata, node);
}

// p3 <-> p1 op p2
// p3 <-> not p2
int SET_PROP_gen(int p1, int p2, int p3, int op, ProofData *pdata)
{
    ProofTerm *t1 = newPropVarTerm(p1);
    ProofTerm *t2 = newPropVarTerm(p2);
    ProofTerm *t3 = newPropVarTerm(p3);
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->arg_num = 2;
    res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * 2);
    res->args[1] = t3;
    res->type = FUNC_IFF;
    switch (op)
    {
    case SMTPROP_NOT:
        freeProofTerm(t1);
        res->args[0] = newPropTerm(t2, NULL, FUNC_NOT);
        break;
    case SMTPROP_AND:
        res->args[0] = newPropTerm(t1, t2, FUNC_AND);
        break;
    case SMTPROP_OR:
        res->args[0] = newPropTerm(t1, t2, FUNC_OR);
        break;
    case SMTPROP_IMPLY:
        res->args[0] = newPropTerm(t1, t2, FUNC_IMPLY);
        break;
    case SMTPROP_IFF:
        res->args[0] = newPropTerm(t1, t2, FUNC_IFF);
        break;
    default:
        printf("error in SET_PROP_gen, invalid type: %d\n", op);
        exit(-1);
        break;
    }
    pdata->cur_num++;
    ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
    arg->type = PTERM;
    arg->args.pterm = copy_ProofTerm(res);
    ProofNode *node = newProofNode(NULL, pdata->cur_num, SET_PROP_IFF, res, arg, 0);
    return updata_proofdata_preprocess(pdata, node);
}

// 由 p<-> p1 op p2 |-- cnf格式
int cnf_trans_proofgen(int pnode, ProofTerm *concl, ProofData *pdata)
{
    int *plist = (int *)malloc(sizeof(int));
    plist[0] = pnode;
    pdata->cur_num++;
    ProofNode *node = newProofNode(plist, pdata->cur_num, CNF_TRANS, concl, NULL, 1);
    return updata_proofdata_preprocess(pdata, node);
}

// p0 /\ p1 /\  ... /\ Pn |-- Pi
// node为推出cnfp的证明步骤的编号
void AND_ELIM_proof(int node, ProofTerm *cnfp, ProofData *pdata)
{
    for (int i = 0; i < cnfp->arg_num; i++)
    {
        pdata->cur_num++;
        int *plist = (int *)malloc(sizeof(int));
        plist[0] = node;
        ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
        arg->type = NUM;
        arg->args.number = i;
        ProofTerm *concl = copy_ProofTerm(cnfp->args[i]);
        ProofNode *node = newProofNode(plist, pdata->cur_num, AND_ELIM, concl, arg, 1);
        updata_proofdata_preprocess(pdata, node);
    }
}

// 将concl更新到global_table中
int updata_proofdata_preprocess(ProofData *pdata, ProofNode *node)
{
    if (pdata->cur_num > pdata->max_num)
    {
        // 扩容node_table
        pdata->max_num *= 2;
        ProofNode **res = (ProofNode **)realloc(pdata->node_table, (pdata->max_num + 1) * sizeof(ProofNode *));
        if (res == NULL)
        {
            printf("memory is not enough\n");
            exit(-1);
        }
        pdata->node_table = res;
    }
    char *s = ProofTerm2str(node->concl);
    int *hval = get_value_from_hstable(pdata->global_table, s, strlen(s));
    if (hval == NULL)
    {
        hval = (int *)malloc(sizeof(int));
        *hval = node->node_number;
        pdata->node_table[node->node_number] = node;
        add_node2HashTable(pdata->global_table, s, strlen(s), hval);
        free(s);
        return node->node_number;
    }
    else
    {
        pdata->cur_num--;
        free(s);
        freeProofNode(node);
        return *hval;
    }
}

int updata_proofdata_theory(ProofData *pdata, ProofNode *node)
{
    if (pdata->cur_num > pdata->max_num)
    {
        // 扩容node_table
        pdata->max_num *= 2;
        ProofNode **res = (ProofNode **)realloc(pdata->node_table, (pdata->max_num + 1) * sizeof(ProofNode *));
        if (res == NULL)
        {
            printf("memory is not enough\n");
            exit(-1);
        }
        pdata->node_table = res;
    }
    char *s = ProofTerm2str(node->concl);
    int *hval = get_value_from_hstable(pdata->theory_global_table, s, strlen(s));
    if (hval == NULL)
    {
        hval = (int *)malloc(sizeof(int));
        *hval = node->node_number;
        pdata->node_table[node->node_number] = node;
        add_node2HashTable(pdata->theory_global_table, s, strlen(s), hval);
        free(s);
        return node->node_number;
    }
    else
    {
        pdata->cur_num--;
        free(s);
        freeProofNode(node);
        return *hval;
    }
}

int preprocess_assume(ProofTerm *t, ProofData *pdata)
{
    ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
    arg->type = PTERM;
    arg->args.pterm = t;
    ProofNode *node = newProofNode(NULL, 1, ASSUME, copy_ProofTerm(t), arg, 0);
    char *s = ProofTerm2str(t);
    int *hval = get_value_from_hstable(pdata->global_table, s, strlen(s));
    if (hval == NULL)
    {
        hval = (int *)malloc(sizeof(int));
        *hval = 1;
        pdata->node_table[1] = node;
        add_node2HashTable(pdata->global_table, s, strlen(s), hval);
        free(s);
        return node->node_number;
    }
    else
    {
        printf("error in preprocess_assume, should have unique assumption in preprocess\n");
        exit(-1);
    }
}

int search_prop(SmtProp *p, PreData *data, Hash_Table *table)
{
    ProofTerm *t = SmtProp2ProofTerm(p, data->var_table);
    char *s = ProofTerm2str(t);
    int *hval = get_value_from_hstable(table, s, strlen(s));
    if (hval == NULL)
    {
        printf("cannot search prop1\n");
        printProofTerm(t);
        freeProofTerm(t);
        free(s);
        exit(-1);
    }
    freeProofTerm(t);
    free(s);
    return *hval;
}

int search_prop2(ProofTerm *t, Hash_Table *table)
{
    char *s = ProofTerm2str(t);
    int *hval = get_value_from_hstable(table, s, strlen(s));
    if (hval == NULL)
    {
        printf("cannot search prop2\n");
        printProofTerm(t);
        printf("\n");
        freeProofTerm(t);
        free(s);
        exit(-1);
    }
    free(s);
    return *hval;
}

int search_prop_unsure(ProofTerm *t, Hash_Table *table)
{
    char *s = ProofTerm2str(t);
    int *hval = get_value_from_hstable(table, s, strlen(s));
    if (hval == NULL)
    {
        free(s);
        return -1;
    }
    free(s);
    return *hval;
}

// n = atomic_prop_cnt
void assign_assum_proof(int *value, int n, PreData *data, ProofData *pdata)
{
    for (int i = 1; i <= n; i++)
    {
        ProofTerm *concl = newPropVarTerm(i);
        ProofTerm *t = SmtProp2ProofTerm(data->prop_list[i], data->var_table);
        ProofTerm *tmp = newEqProofTerm2(copy_ProofTerm(t), copy_ProofTerm(concl));
        char *s = ProofTerm2str(tmp);
        int *hval = get_value_from_hstable(pdata->global_table, s, strlen(s));
        if (hval == NULL)
        {
            printf("error in assign_assum_proof, cannot find atomic_p = Pi\n");
            exit(-1);
        }
        int num1 = *hval;
        free(s);
        freeProofTerm(tmp);

        if (value[i] == 0)
        {
            concl = newPropTerm(concl, NULL, FUNC_NOT);
            t = newPropTerm(t, NULL, FUNC_NOT);
        }
        // ASSUME Pi // ASSUME (NOT Pi)
        pdata->cur_num++;
        ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
        arg->type = PTERM;
        arg->args.pterm = copy_ProofTerm(concl);
        ProofNode *node = newProofNode(NULL, pdata->cur_num, ASSUME, concl, arg, 0);
        int num2 = updata_proofdata_theory(pdata, node);

        // Pi  atomix_p = Pi |- atomix_p  //  NOT(Pi)  atomix_p = Pi |- NOT atomix_p
        pdata->cur_num++;
        int *plist = (int *)malloc(sizeof(int)*2);
        plist[0] = num2;
        plist[1] = num1;
        ProofNode *node1 = NULL;
        if (value[i] == 1)
            node1 = newProofNode(plist, pdata->cur_num, EQUALITY_RESOLUTION, t, NULL, 2);
        else
            node1 = newProofNode(plist, pdata->cur_num, FUNC_REWRITE, t, NULL, 2);
        int ans = updata_proofdata_theory(pdata, node1);
    }
}
