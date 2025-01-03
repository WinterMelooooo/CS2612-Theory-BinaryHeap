#include "nelson_oppen_proof.h"
#include "uf_proof.h"
#include "lia_proof.h"
#include "smt_preprocess_proof.h"
// #define NELSON_OPPEN_DEBUG

void init_theory_assume(CombineData *cdata, PreData *data, ProofData *pdata)
{
    uf_proof_assume_pos(cdata->uf_data->data.uflist->equ_list, pdata, data);
// uf_proof_assume_neg(cdata->uf_data->data.uflist->inequ_list, pdata, data);
// lia_proof_assume(cdata->lia_data->data.lialist->equ_list, pdata, FUNC_EQ0, data->var_cnt, 1);
// lia_proof_assume(cdata->lia_data->data.lialist->inequ_list, pdata, FUNC_LE0, data->var_cnt, 1);
// proof assum gen debug:
#ifdef NELSON_OPPEN_DEBUG
    printf("proof assume gen : cur_num: %d\n", pdata->cur_num);
    for (int i = 1; i <= pdata->cur_num; i++)
    {
        printProofNode(pdata, pdata->node_table[i]);
    }
    printf("proof assume gen end\n");
#endif
}

int lia_prop_trans_proof(int node, int *coef, int n, TermType type, ProofData *pdata)
{
    ProofTerm *concl = inequ_trans_proofterm(coef, n, type);
    int *plist = (int *)malloc(sizeof(int));
    plist[0] = node;
    pdata->cur_num++;
    ProofNode *anode = newProofNode(plist, pdata->cur_num, LIA_TRANS, concl, NULL, 1);
    return updata_proofdata_lia(pdata, anode, 1);
}

err proplist_trans_coef_proof(SmtProplist *prop_list, PreData *data, int *value, lia_list *list, ProofData *pdata)
{
    SmtProplist *tmp = prop_list;
    while (tmp->next != NULL)
    {
        InequList *equ = (InequList *)malloc(sizeof(InequList));
        memset(equ, 0, sizeof(InequList));
        char *s = AtomicProp_str(tmp->prop);
        Hash_val *hval = get_value_from_hstable(data->prop_table, s, strlen(s));
        free(s);
        if (hval == NULL)
        {
            printf("error in proplist_trans_coef, null hash_val\n");
            exit(-1);
        }
        int node = -1;
        if (value[hval->num] == 1)
        {
            node = search_prop(tmp->prop, data, pdata->theory_global_table);
        }
        else
        {
            SmtProp *p1 = newSmtProp(SMTU_PROP, SMTPROP_NOT, copy_SmtProp(tmp->prop), NULL, NULL, NULL, true);
            node = search_prop(p1, data, pdata->theory_global_table);
            freeSmtProp(p1);
        }
        int *coef = prop_trans_coef(tmp->prop, data);
        if (coef == NULL)
            return MULT_nia;
        if (value[hval->num] == 0)
        {
            for (int i = 0; i <= data->var_cnt; i++)
                coef[i] = -coef[i];
            coef[0]++;
        }
        equ->strict = -1;
        equ->coef = coef;
        if (value[hval->num] == 1 && tmp->prop->prop.Atomic_prop.op == SMT_EQ)
        {
            equ->strict = 0;
            equ->next = list->equ_list;
            list->equ_list = equ;
            lia_prop_trans_proof(node, coef, data->var_cnt, FUNC_EQ0, pdata);
        }
        else if (value[hval->num] == 0 && tmp->prop->prop.Atomic_prop.op == SMT_EQ)
        {
            // lia不处理 a!=b的情况
            free(coef);
            free(equ);
        }
        else
        {
            equ->next = list->inequ_list;
            list->inequ_list = equ;
            lia_prop_trans_proof(node, coef, data->var_cnt, FUNC_LE0, pdata);
        }
        tmp = tmp->next;
    }
    return OKAY;
}

CombineData *initCombineData_proof(PreData *data, int *value, ProofData *pdata)
{
    CombineData *cdata = (CombineData *)malloc(sizeof(CombineData));
    memset(cdata, 0, sizeof(CombineData));
    cdata->var_cnt = data->var_cnt;
    cdata->var_pair = (int **)malloc(sizeof(int *) * (data->var_cnt + 1));
    for (int i = 0; i <= data->var_cnt; i++)
    {
        cdata->var_pair[i] = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
        memset(cdata->var_pair[i], 0, sizeof(int) * (data->var_cnt + 1));
    }
    cdata->lia_data = (TheoryData *)malloc(sizeof(TheoryData));
    memset(cdata->lia_data, 0, sizeof(TheoryData));
    cdata->lia_data->type = LIA_THEORY;
    cdata->uf_data = (TheoryData *)malloc(sizeof(TheoryData));
    memset(cdata->uf_data, 0, sizeof(TheoryData));
    cdata->uf_data->type = UF_THEORY;
    cdata->lia_data->value = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
    memset(cdata->lia_data->value, 0, sizeof(int) * (data->var_cnt + 1));
    cdata->uf_data->value = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
    memset(cdata->uf_data->value, 0, sizeof(int) * (data->var_cnt + 1));
    cdata->lia_data->prop_list = (SmtProplist *)malloc(sizeof(SmtProplist));
    memset(cdata->lia_data->prop_list, 0, sizeof(SmtProplist));
    cdata->uf_data->prop_list = (SmtProplist *)malloc(sizeof(SmtProplist));
    memset(cdata->uf_data->prop_list, 0, sizeof(SmtProplist));

    for (int i = 1; i <= data->at_prop_cnt; i++)
    {
        SmtProp *p = data->prop_list[i];
        switch (p->type)
        {
            SmtProplist *p1;
            SmtProplist *p2;
        case SMTAT_PROP_EQ:
            cdata->lia_data->prop_cnt++;
            cdata->uf_data->prop_cnt++;
            p1 = (SmtProplist *)malloc(sizeof(SmtProplist));
            p1->prop = copy_SmtProp(data->prop_list[i]);
            p1->next = cdata->lia_data->prop_list;
            cdata->lia_data->prop_list = p1;
            p2 = (SmtProplist *)malloc(sizeof(SmtProplist));
            p2->prop = copy_SmtProp(data->prop_list[i]);
            p2->next = cdata->uf_data->prop_list;
            cdata->uf_data->prop_list = p2;
            SmtTerm *t1 = p->prop.Atomic_prop.term1;
            SmtTerm *t2 = p->prop.Atomic_prop.term2;
            if (t1->type != SMT_VarName || t2->type != SMT_VarName)
            {
                printf("error in initCombineData_proof, invalid type of SMTAT_PROP_EQ\n");
                exit(-1);
            }
            char *s1 = t1->term.Variable;
            char *s2 = t2->term.Variable;
            Hash_val *hval_1 = get_value_from_hstable(data->var_table, s1, strlen(s1));
            Hash_val *hval_2 = get_value_from_hstable(data->var_table, s2, strlen(s2));
            if (hval_1 == NULL || hval_2 == NULL)
            {
                printf("error in initCombineData_proof, hash_val should't be null\n");
                exit(-1);
            }
            cdata->var_pair[hval_1->num][hval_2->num] = EQ_PAIR;
            cdata->var_pair[hval_2->num][hval_1->num] = EQ_PAIR;
            break;
        case SMTAT_PROP_LIA_EQ:
        case SMTAT_PROP_LIA:
            cdata->lia_data->prop_cnt++;
            p1 = (SmtProplist *)malloc(sizeof(SmtProplist));
            p1->prop = copy_SmtProp(data->prop_list[i]);
            p1->next = cdata->lia_data->prop_list;
            cdata->lia_data->prop_list = p1;
            break;
        case SMTAT_PROP_UF_EQ:
            cdata->uf_data->prop_cnt++;
            p2 = (SmtProplist *)malloc(sizeof(SmtProplist));
            p2->prop = copy_SmtProp(data->prop_list[i]);
            p2->next = cdata->uf_data->prop_list;
            cdata->uf_data->prop_list = p2;
            break;
        case SMTAT_PROP_NIA_EQ:
            break;
        default:
            printf("error in initCombineData_proof, invalid type\n");
            exit(-1);
            break;
        }
    }

    // 完成theorydata中的value初始化, 此时还未进行curryfy
    var_in_proplist(cdata->lia_data, data);
    var_in_proplist(cdata->uf_data, data);
    for (int i = 1; i <= data->var_cnt; i++)
    {
        if (cdata->lia_data->value[i] == 0 || cdata->uf_data->value[i] == 0)
            continue;
        cdata->common_cnt++;
        for (int j = i + 1; j <= data->var_cnt; j++)
        {
            if (cdata->lia_data->value[j] == 0 || cdata->uf_data->value[j] == 0)
                continue;
            cdata->var_pair[i][j] = SHARE_PAIR;
        }
    }

    lia_list *list = (lia_list *)malloc(sizeof(lia_list));
    InequList *equ_list = (InequList *)malloc(sizeof(InequList));
    InequList *inequ_list = (InequList *)malloc(sizeof(InequList));
    memset(list, 0, sizeof(lia_list));
    memset(equ_list, 0, sizeof(InequList));
    memset(inequ_list, 0, sizeof(InequList));
    list->equ_list = equ_list;
    list->inequ_list = inequ_list;
    err code = proplist_trans_coef_proof(cdata->lia_data->prop_list, data, value, list, pdata);
    if (code != 0)
    {
        freeCombineData(cdata);
        cdata = NULL;
        printf("err re_code number: %d\n", code);
        return NULL;
    }
    cdata->lia_data->data.lialist = list;

    uf_list *ulist = (uf_list *)malloc(sizeof(uf_list));
    EquationNode *uf_equ_list = (EquationNode *)malloc(sizeof(EquationNode));
    EquationNode *uf_inequ_list = (EquationNode *)malloc(sizeof(EquationNode));
    memset(ulist, 0, sizeof(uf_list));
    memset(uf_equ_list, 0, sizeof(EquationNode));
    memset(uf_inequ_list, 0, sizeof(EquationNode));
    ulist->equ_list = uf_equ_list;
    ulist->inequ_list = uf_inequ_list;
    // curryfy在转化过程中同时完成
    proplist_trans_EquationNode(cdata->uf_data->prop_list, data, value, ulist);
    cdata->uf_data->var_cnt = cdata->uf_data->var_cnt + data->var_cnt_uf - data->var_cnt;
    cdata->uf_data->data.uflist = ulist;
    // printf("uf_replace:\n");
    // printSmtProplist(data->replace_list);
    //printVarlist_uf(data);

    return cdata;
}
// value[i] = 1表示命题变元Pi在sat的结果中赋值为true
int theroy_deduction_lia_proof(TheoryData *tdata, PreData *data, ProofData *pdata)
{
#ifdef NELSON_OPPEN_DEBUG
    printf("theroy_deduction_lia : start\n");
#endif
    int *tmp_value = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
    memset(tmp_value, 0, sizeof(int) * (data->var_cnt + 1));
    for (int i = 0; i <= data->var_cnt; i++)
        tmp_value[i] = tdata->value[i];
    InequList *r1 = copy_InequList(tdata->data.lialist->equ_list, data->var_cnt);
    InequList *r2 = copy_InequList(tdata->data.lialist->inequ_list, data->var_cnt);
    int res = lia_theory_deduction(r1, r2, tmp_value, data->var_cnt, data->int8_max, data->int16_max, data->int32_max, data->int64_max);
    free_InequList(r1);
    if (res == 0)
    {
        // unsat时生成证明
        r1 = copy_InequList(tdata->data.lialist->equ_list, data->var_cnt);
        r2 = copy_InequList(tdata->data.lialist->inequ_list, data->var_cnt);
        int res2 = lia_theory_deduction_proof(r1, r2, tmp_value, pdata, data->var_cnt, data->int8_max, data->int16_max, data->int32_max, data->int64_max, 1);
        free_InequList(r1);
        if (res2 != res)
        {
            printf("error in theory_deduction_lia_proof, res1: %d, res2: %d\n", res, res2);
            exit(-1);
        }
    }
    free(tmp_value);
    return res;
}

// 返回1表示能推出vi=vj，返回0表示不能推出vi=vj
int lia_infer_proof(int vi, int vj, TheoryData *tdata, PreData *data, ProofData *pdata)
{
    InequList *equ1 = (InequList *)malloc(sizeof(InequList));
    memset(equ1, 0, sizeof(InequList));
    InequList *equ2 = (InequList *)malloc(sizeof(InequList));
    memset(equ2, 0, sizeof(InequList));
    equ1->coef = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
    memset(equ1->coef, 0, sizeof(int) * (data->var_cnt + 1));
    equ2->coef = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
    memset(equ2->coef, 0, sizeof(int) * (data->var_cnt + 1));
    // vi > vj 即 vj-vi+1 <= 0
    equ1->coef[vi] = -1;
    equ1->coef[vj] = 1;
    equ1->coef[0] = 1;
    equ1->strict = -1;
    // vj > vi 即 vi-vj+1 <= 0
    equ2->coef[vi] = 1;
    equ2->coef[vj] = -1;
    equ2->coef[0] = 1;
    equ2->strict = -1;
    int *tmp_value = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
    memset(tmp_value, 0, sizeof(int) * (data->var_cnt + 1));
    for (int i = 0; i <= data->var_cnt; i++)
        tmp_value[i] = tdata->value[i];
    InequList *tmp = tdata->data.lialist->inequ_list;
    equ1->next = copy_InequList(tmp, data->var_cnt);
    InequList* equ_list = copy_InequList(tdata->data.lialist->equ_list, data->var_cnt);
    InequList* Inequ_copy = copy_InequList(equ1, data->var_cnt);
    int res1 = lia_theory_deduction(equ_list, Inequ_copy, tmp_value, data->var_cnt, data->int8_max, data->int16_max, data->int32_max, data->int64_max);
    free_InequList(equ_list);
    equ_list = copy_InequList(tdata->data.lialist->equ_list, data->var_cnt);
    if(res1 == 1) {
      free(tmp_value);
      free_InequList(equ1);
      free_InequList(equ2);
      return 0;
    }
    equ2->next = copy_InequList(tmp, data->var_cnt);
    Inequ_copy = copy_InequList(equ2, data->var_cnt);
    int res2 = lia_theory_deduction(equ_list, Inequ_copy, tmp_value, data->var_cnt, data->int8_max, data->int16_max, data->int32_max, data->int64_max);
    free_InequList(equ_list);
    equ_list = copy_InequList(tdata->data.lialist->equ_list, data->var_cnt);
    if(res2 == 1) {
        free(tmp_value);
        free_InequList(equ1);
        free_InequList(equ2);
        return 0;
    }
    // 生成证明
    // 先假设vj-vi+1<=0
    int t1 = lia_infer_assume(equ1->coef, pdata, data->var_cnt);
    res1 = lia_theory_deduction_proof(equ_list, copy_InequList(equ1, data->var_cnt), tmp_value, pdata, data->var_cnt, data->int8_max, data->int16_max, data->int32_max, data->int64_max, 2);
    free_InequList(equ_list);
    equ_list = copy_InequList(tdata->data.lialist->equ_list, data->var_cnt);
    if (res1 == 1)
    {
        printf("error1 in lia_infer_proof, here should be false\n");
        exit(-1);
    }
    // 由false推出假设不成立，concl为not(vj-vi+1<=0)
    int node1 = SCOPE_END_LIA(pdata->cur_num, t1, pdata);
    // 清空theory_local_table
    hash_table_delete(pdata->local_table);
    pdata->local_table = creat_hash_table();
    // 消去concl中的not 得到vi-vj <= 0
    node1 = LIA_ARITH_NOT_ELIM(equ1->coef, data->var_cnt, node1, pdata);

    // 再假设 vi-vj+1 <= 0
    int t2 = lia_infer_assume(equ2->coef, pdata, data->var_cnt);
    res2 = lia_theory_deduction_proof(equ_list, copy_InequList(equ2, data->var_cnt), tmp_value, pdata, data->var_cnt, data->int8_max, data->int16_max, data->int32_max, data->int64_max, 2);
    if (res2 == 1)
    {
        printf("error2 in lia_infer_proof, here should be false\n");
        exit(-1);
    }
    // 由false推出假设不成立，concl为not(vi-vj+1<=0)
    int node2 = SCOPE_END_LIA(pdata->cur_num, t2, pdata);
    // 清空theory_local_table
    hash_table_delete(pdata->local_table);
    pdata->local_table = creat_hash_table();
    // 消去concl中的not 得到vj-vi <= 0
    node2 = LIA_ARITH_NOT_ELIM(equ2->coef, data->var_cnt, node2, pdata);

    // 由node1和node2推出vi = vj
    pdata->cur_num++;
    int *plist = (int *)malloc(sizeof(int) * 2);
    plist[0] = node1;
    plist[1] = node2;
    ProofTerm *concl = newEqProofTerm(vi, vj);
    ProofNode *anode = newProofNode(plist, pdata->cur_num, ARITH_EQ_INTRO, concl, NULL, 2);
    anode->args = (ArgTerm**)malloc(sizeof(ArgTerm*)*2);
    anode->args[0] = (ArgTerm*)malloc(sizeof(ArgTerm));
    anode->args[1] = (ArgTerm*)malloc(sizeof(ArgTerm));
    memset(anode->args[0], 0, sizeof(ArgTerm));
    memset(anode->args[1], 0, sizeof(ArgTerm));
    anode->args[0]->type = NUM;
    anode->args[1]->type = NUM;
    anode->args[0]->args.number = vi;
    anode->args[1]->args.number = vj;
    anode->arg_num = 2;
    int ans = updata_proofdata_lia(pdata, anode, 1);
    // vi = vj |- vi - vj = 0
    // vi = vj |- vj - vi = 0
    uf_infer_add(pdata, data->var_cnt, vi, vj, ans);
    uf_infer_add(pdata, data->var_cnt, vj, vi, ans);
    free(tmp_value);
    free_InequList(equ_list);
    free_InequList(equ1);
    free_InequList(equ2);
    return 1;
}

int theroy_deduction_uf_proof(TheoryData *tdata, PreData *data, ProofData *pdata)
{
    database *S = initialize(data->var_cnt_uf);
    merge(S, tdata->data.uflist->equ_list);
#ifdef NELSON_OPPEN_DEBUG
    printf("merge success\n");
#endif
    EquationNode *tmp = tdata->data.uflist->inequ_list;
    while (tmp->next != NULL)
    {
        bool ans = areCongruent(S, tmp->left1, tmp->right);
        // test uf_proof
        if (ans)
        {
            uf_false_gen(S, pdata, data, tmp->left1, tmp->right);
            freeMemory(S, data->var_cnt_uf);
            return 0;
        }
        tmp = tmp->next;
    }
    freeMemory(S, data->var_cnt_uf);
    return 1;
}

int uf_infer_proof(int vi, int vj, TheoryData *tdata, PreData *data, ProofData *pdata)
{
    database *S = initialize(data->var_cnt_uf);
    merge(S, tdata->data.uflist->equ_list);
    bool ans = areCongruent(S, vi, vj);
    if (ans)
    {
        int node = explain_proof(S, pdata, data, vi, vj);
        uf_infer_add(pdata, data->var_cnt, vi, vj, node);
        freeMemory(S, data->var_cnt_uf);
        return 1;
    }
    else{
        freeMemory(S, data->var_cnt_uf);
        return 0;
    }
}

int nelson_oppen_convex_proof(CombineData *cdata, PreData *data, ProofData *pdata)
{
    init_theory_assume(cdata, data, pdata);
    int res1 = theroy_deduction_lia_proof(cdata->lia_data, data, pdata);
    if (res1 == 0)
        return 0;
    int res2 = theroy_deduction_uf_proof(cdata->uf_data, data, pdata);
    if (res2 == 0)
        return 0;
    int roll_cnt = 0;
    while (true)
    {
        roll_cnt++;
#ifdef NELSON_OPPEN_DEBUG
        printf("roll_cnt : %d\n", roll_cnt);
#endif
        bool new_equation = false;
        // 遍历所有的共享变量对，如果能被uf_theory推出，则在uf_theory和lia_theory中加入这个等式
        for (int vi = 1; vi <= cdata->var_cnt; vi++)
        {
            for (int vj = vi + 1; vj <= cdata->var_cnt; vj++)
            {
                if (cdata->var_pair[vi][vj] != SHARE_PAIR)
                    continue;
                else if (uf_infer_proof(vi, vj, cdata->uf_data, data, pdata))
                {
                    new_equation = true;
#ifdef NELSON_OPPEN_DEBUG
                    printf("uf_infer : %s = %s\n", data->var_list[vi], data->var_list[vj]);
#endif
                    add_equation_uf(vi, vj, cdata->uf_data);
                    add_equation_lia(vi, vj, cdata->lia_data, data);
                    cdata->var_pair[vi][vj] = EQ_PAIR;
                    cdata->var_pair[vj][vi] = EQ_PAIR;
                }
            }
        }
        if (new_equation && theroy_deduction_lia_proof(cdata->lia_data, data, pdata) == 0)
        {
            return 0;
        }
        else
        {
            for (int vi = 1; vi <= cdata->var_cnt && new_equation == false; vi++)
            {
                for (int vj = vi + 1; vj <= cdata->var_cnt; vj++)
                {
                    if (cdata->var_pair[vi][vj] != SHARE_PAIR)
                        continue;
                    else
                    {
#ifdef NELSON_OPPEN_DEBUG
                        printf("try to infer %d = %d in lia\n", vi, vj);
#endif
                        if (lia_infer_proof(vi, vj, cdata->lia_data, data, pdata))
                        {
                            new_equation = true;
#ifdef NELSON_OPPEN_DEBUG
                            printf("lia_infer : %s = %s\n", data->var_list[vi], data->var_list[vj]);
#endif
                            add_equation_uf(vi, vj, cdata->uf_data);
                            add_equation_lia(vi, vj, cdata->lia_data, data);
                            cdata->var_pair[vi][vj] = EQ_PAIR;
                            cdata->var_pair[vj][vi] = EQ_PAIR;
                            break;
                        }
                    }
                }
            }
        }
        if (new_equation && theroy_deduction_uf_proof(cdata->uf_data, data, pdata) == 0)
        {
            return 0;
        }
        if (!new_equation)
            break;
    }
    return 1;
}