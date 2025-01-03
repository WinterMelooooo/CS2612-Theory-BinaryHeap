#include "smt_lang.h"
#include "nelson_oppen.h"
#include "uf_proof.h"
//#define NELSON_OPPEN_DEBUG 1

void printEquationNode(EquationNode *list, PreData *data)
{
    EquationNode *tmp = list;
    while (tmp->next != NULL)
    {
        if (tmp->left2 == -1)
            printf("%s = %s\n", data->var_list[tmp->left1], data->var_list[tmp->right]);
        else
            printf("UF(%s, %s) = %s\n", data->var_list[tmp->left1], data->var_list[tmp->left2], data->var_list[tmp->right]);
        tmp = tmp->next;
    }
}
void var_in_term(TheoryData *tdata, PreData *data, SmtTerm *t)
{
    switch (t->type)
    {
    case SMT_LiaBTerm:
        var_in_term(tdata, data, t->term.BTerm.t1);
        var_in_term(tdata, data, t->term.BTerm.t2);
        break;
    case SMT_LiaUTerm:
        var_in_term(tdata, data, t->term.UTerm.t);
        break;
    case SMT_UFTerm:
    {
        for (int i = 0; i < t->term.UFTerm->numArgs; i++)
        {
            var_in_term(tdata, data, t->term.UFTerm->args[i]);
        }
        break;
    }
    case SMT_VarName:
    {
        char *s = t->term.Variable;
        Hash_val *hval = get_value_from_hstable(data->var_table, s, strlen(s));
        if (hval == NULL)
        {
            printf("error in var_in_term, hash_val should't be null\n");
            exit(-1);
        }
        else if (tdata->value[hval->num] == 0)
        {
            tdata->value[hval->num] = 1;
            tdata->var_cnt++;
        }
        break;
    }
    case SMT_ConstNum:
        break;
    default:
        printf("error in var_in_term, invalid term type\n");
        exit(-1);
        break;
    }
}

void var_in_prop(TheoryData *tdata, PreData *data, SmtProp *p)
{
    switch (p->type)
    {
    case SMTAT_PROP_EQ:
    case SMTAT_PROP_LIA:
    case SMTAT_PROP_UF_EQ:
    case SMTAT_PROP_LIA_EQ:
        var_in_term(tdata, data, p->prop.Atomic_prop.term1);
        var_in_term(tdata, data, p->prop.Atomic_prop.term2);
        break;
    default:
        printf("error in var_in_prop, invalid prop type\n");
        exit(-1);
        break;
    }
}

void var_in_proplist(TheoryData *tdata, PreData *data)
{
    SmtProplist *tmp = tdata->prop_list;
    while (tmp->next != NULL)
    {
        var_in_prop(tdata, data, tmp->prop);
        tmp = tmp->next;
    }
}

CombineData *initCombineData(PreData *data, int *value)
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
                printf("error in initCombineData, invalid type of SMTAT_PROP_EQ\n");
                exit(-1);
            }
            char *s1 = t1->term.Variable;
            char *s2 = t2->term.Variable;
            Hash_val *hval_1 = get_value_from_hstable(data->var_table, s1, strlen(s1));
            Hash_val *hval_2 = get_value_from_hstable(data->var_table, s2, strlen(s2));
            if (hval_1 == NULL || hval_2 == NULL)
            {
                printf("error in initCombineData, hash_val should't be null\n");
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
            printf("error in initCombineData, invalid type\n");
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
    err code = proplist_trans_coef(cdata->lia_data->prop_list, data, value, list);
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
    // printVarlist_uf(data);

    return cdata;
}

void add_equation_lia(int vi, int vj, TheoryData *tdata, PreData *data)
{
    InequList *equ1 = (InequList *)malloc(sizeof(InequList));
    memset(equ1, 0, sizeof(InequList));
    equ1->coef = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
    memset(equ1->coef, 0, sizeof(int) * (data->var_cnt + 1));
    equ1->coef[vi] = 1;
    equ1->coef[vj] = -1;
    equ1->strict = 0;
    equ1->next = tdata->data.lialist->equ_list;
    tdata->data.lialist->equ_list = equ1;
}

void add_equation_uf(int vi, int vj, TheoryData *tdata)
{
    EquationNode *equ1 = (EquationNode *)malloc(sizeof(EquationNode));
    memset(equ1, 0, sizeof(EquationNode));
    equ1->left1 = vi;
    equ1->left2 = -1;
    equ1->right = vj;
    equ1->next = tdata->data.uflist->equ_list;
    tdata->data.uflist->equ_list = equ1;
}

// 将表达式转换成系数数组
int *term_coef_trans(SmtTerm *t, PreData *data)
{
    int *coef = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
    memset(coef, 0, sizeof(int) * (data->var_cnt + 1));
    switch (t->type)
    {
    case SMT_ConstNum:
        coef[0] = t->term.ConstNum;
        break;
    case SMT_VarName:
    {
        char *s = t->term.Variable;
        Hash_val *hval = get_value_from_hstable(data->var_table, s, strlen(s));
        if (hval == NULL)
        {
            printf("error in term_coef_trans, null hash_val\n");
            exit(-1);
        }
        coef[hval->num] = 1;
        break;
    }
    case SMT_LiaBTerm:
    {
        int *left_coef = term_coef_trans(t->term.BTerm.t1, data);
        int *right_coef = term_coef_trans(t->term.BTerm.t2, data);
        if (left_coef == NULL || right_coef == NULL)
            return NULL;
        switch (t->term.BTerm.op)
        {
        case LIA_ADD:
            for (int i = 0; i <= data->var_cnt; i++)
                coef[i] = left_coef[i] + right_coef[i];
            break;
        case LIA_MINUS:
            for (int i = 0; i <= data->var_cnt; i++)
            {
                coef[i] = left_coef[i] - right_coef[i];
            }
            break;
        case LIA_MULT:
            if (t->term.BTerm.t1->type != SMT_ConstNum && t->term.BTerm.t2->type != SMT_ConstNum)
            {
                return NULL;
                // printf("error in term_coef_trans, invalid lia_expression\n");
                // exit(-1);
            }
            if (t->term.BTerm.t1->type == SMT_ConstNum)
            {
                for (int i = 0; i <= data->var_cnt; i++)
                {
                    coef[i] = left_coef[0] * right_coef[i];
                }
            }
            else
            {
                for (int i = 0; i <= data->var_cnt; i++)
                {
                    coef[i] = right_coef[0] * left_coef[i];
                }
            }
            break;
        default:
            printf("error in term_coef_trans, invalid lia_op\n");
            exit(-1);
            break;
        }
        free(left_coef);
        free(right_coef);
        break;
    }
    case SMT_LiaUTerm:
    {
        int *u_coef = term_coef_trans(t->term.UTerm.t, data);
        if (u_coef == NULL)
            return NULL;
        for (int i = 0; i <= data->var_cnt; i++)
        {
            coef[i] = -u_coef[i];
        }
        free(u_coef);
        break;
    }
    default:
        printf("error in term_coef_trans, invalid SmtTerm in lia");
        exit(-1);
        break;
    }
    return coef;
}

int *prop_trans_coef(SmtProp *p, PreData *data)
{
    int *coef = (int *)malloc(sizeof(int) * (data->var_cnt + 1));
    memset(coef, 0, sizeof(int) * (data->var_cnt + 1));
    switch (p->type)
    {
    case SMTAT_PROP_EQ:
    case SMTAT_PROP_LIA_EQ:
    case SMTAT_PROP_LIA:
    {
        int *left_coef = term_coef_trans(p->prop.Atomic_prop.term1, data);
        int *right_coef = term_coef_trans(p->prop.Atomic_prop.term2, data);
        if (left_coef == NULL || right_coef == NULL)
            return NULL;
        switch (p->prop.Atomic_prop.op)
        {
        case SMT_LE:
            for (int i = 0; i <= data->var_cnt; i++)
            {
                coef[i] = left_coef[i] - right_coef[i];
            }
            break;
        case SMT_LT:
            for (int i = 0; i <= data->var_cnt; i++)
            {
                coef[i] = left_coef[i] - right_coef[i];
            }
            // 整数离散性
            coef[0]++;
            break;
        case SMT_GE:
            for (int i = 0; i <= data->var_cnt; i++)
            {
                coef[i] = right_coef[i] - left_coef[i];
            }
            break;
        case SMT_GT:
            for (int i = 0; i <= data->var_cnt; i++)
            {
                coef[i] = right_coef[i] - left_coef[i];
            }
            // 整数离散性
            coef[0]++;
            break;
        case SMT_EQ:
            for (int i = 0; i <= data->var_cnt; i++)
            {
                coef[i] = left_coef[i] - right_coef[i];
            }
            break;
        default:
            printf("error in prop_trans_coef, invalid prop op\n");
            exit(-1);
        }
        free(left_coef);
        free(right_coef);
        break;
    }
    default:
        printf("error in prop_trans_coef, invalid prop type\n");
        exit(-1);
        break;
    }
    return coef;
}

err proplist_trans_coef(SmtProplist *prop_list, PreData *data, int *value, lia_list *list)
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
        }
        tmp = tmp->next;
    }
    return OKAY;
}

EquationNode *prop_trans_EquationNode(SmtProp *p, PreData *data)
{
    EquationNode *res = (EquationNode *)malloc(sizeof(EquationNode));
    memset(res, 0, sizeof(EquationNode));
    switch (p->type)
    {
    case SMTAT_PROP_EQ:
    {
        char *s1 = p->prop.Atomic_prop.term1->term.Variable;
        char *s2 = p->prop.Atomic_prop.term2->term.Variable;
        Hash_val *hval1 = get_value_from_hstable(data->var_table, s1, strlen(s1));
        Hash_val *hval2 = get_value_from_hstable(data->var_table, s2, strlen(s2));
        if (hval1 == NULL || hval2 == NULL)
        {
            printf("error in prop_trans_EquationNode, case SMTAT_PROP_EQ, null hashval\n");
            exit(-1);
        }
        res->left1 = hval1->num;
        res->left2 = -1;
        res->right = hval2->num;
        break;
    }
    case SMTAT_PROP_UF_EQ:
    {
        // UF(a,b) = c, t1表示UF(a,b), t2表示c
        SmtTerm *t1 = p->prop.Atomic_prop.term1;
        SmtTerm *t2 = p->prop.Atomic_prop.term2;
        if (t1->type != SMT_VarName && t2->type != SMT_VarName)
        {
            printf("error in prop_trans_EquationNode, invalid uf_prop\n");
            exit(-1);
        }
        if (t1->type == SMT_VarName && t2->type == SMT_UFTerm)
        {
            t2 = t1;
            t1 = p->prop.Atomic_prop.term2;
        }
        char *rkey = t2->term.Variable;
        char *left1 = t1->term.UFTerm->args[0]->term.Variable;
        char *left2 = t1->term.UFTerm->args[1]->term.Variable;
        Hash_val *rhval = get_value_from_hstable(data->var_table, rkey, strlen(rkey));
        Hash_val *left1_hval = get_value_from_hstable(data->var_table, left1, strlen(left1));
        Hash_val *left2_hval = get_value_from_hstable(data->var_table, left2, strlen(left2));
        if (rhval == NULL || left1_hval == NULL || left2_hval == NULL)
        {
            printf("error in prop_trans_EquationNode, case SMTAT_PROP_UF_EQ, null hashval\n");
            exit(-1);
        }
        res->left1 = left1_hval->num;
        res->left2 = left2_hval->num;
        res->right = rhval->num;
        break;
    }
    default:
        printf("error in prop_trans_EquationNode, invalid prop type\n");
        exit(-1);
        break;
    }
    return res;
}

void proplist_trans_EquationNode(SmtProplist *prop_list, PreData *data, int *value, uf_list *list)
{
    SmtProplist *tmp = prop_list;
    int var_cnt = data->var_cnt;
    while (tmp->next != NULL)
    {
        char *s = AtomicProp_str(tmp->prop);
        Hash_val *hval = get_value_from_hstable(data->prop_table, s, strlen(s));
        free(s);
        if (hval == NULL)
        {
            printf("error in proplist_trans_EquationNode, null hash_val\n");
            exit(-1);
        }
        SmtProp* tmp1 = prop_currfy_flatten(tmp->prop, data);
        freeSmtProp(tmp->prop);
        tmp->prop = tmp1;
        EquationNode *equ = prop_trans_EquationNode(tmp->prop, data);
        if (value[hval->num] == 0)
        {
            equ->next = list->inequ_list;
            list->inequ_list = equ;
        }
        else
        {
            equ->next = list->equ_list;
            list->equ_list = equ;
        }
        tmp = tmp->next;
    }
    data->var_cnt_uf = data->var_cnt;
    data->var_cnt = var_cnt;
    char **var_list = (char **)malloc(sizeof(char *) * (data->var_cnt_uf + 1));
    memset(var_list, 0, sizeof(char *) * (data->var_cnt_uf + 1));
#ifdef NELSON_OPPEN_DEBUG
    printf("var_cnt_uf : %d\nvar_cnt : %d\n", data->var_cnt_uf, data->var_cnt);
#endif
    for (int i = 1; i <= data->var_cnt; i++)
    {
        var_list[i] = data->var_list[i];
    }
    free(data->var_list);
    data->var_list = var_list;
    init_Varlist_proplist(data->replace_list, data);
    tmp = data->replace_list;
    while (tmp->next != NULL)
    {
        EquationNode *equ = prop_trans_EquationNode(tmp->prop, data);
        equ->next = list->equ_list;
        list->equ_list = equ;
        tmp = tmp->next;
    }
}

// value[i] = 1表示命题变元Pi在sat的结果中赋值为true
int theroy_deduction_lia(TheoryData *tdata, PreData *data)
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
    free(tmp_value);
    return res;
}

//返回1表示能推出vi=vj，返回0表示不能推出vi=vj
int lia_infer(int vi, int vj, TheoryData* tdata, PreData* data){
    InequList* equ1 = (InequList*)malloc(sizeof(InequList));
    memset(equ1, 0, sizeof(InequList));
    InequList* equ2 = (InequList*)malloc(sizeof(InequList));
    memset(equ2, 0, sizeof(InequList));
    equ1->coef = (int*)malloc(sizeof(int)*(data->var_cnt+1));
    memset(equ1->coef, 0, sizeof(int)*(data->var_cnt+1));
    equ2->coef = (int*)malloc(sizeof(int)*(data->var_cnt+1));
    memset(equ2->coef, 0, sizeof(int)*(data->var_cnt+1));
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
    int* tmp_value = (int*)malloc(sizeof(int)*(data->var_cnt+1));
    memset(tmp_value, 0, sizeof(int)*(data->var_cnt+1));
    for(int i = 0; i <= data->var_cnt; i++) tmp_value[i] = tdata->value[i];
    InequList* tmp = tdata->data.lialist->inequ_list;
    equ1->next = copy_InequList(tmp, data->var_cnt);
    InequList* equ_list = copy_InequList(tdata->data.lialist->equ_list, data->var_cnt);
    InequList* equ_copy = copy_InequList(equ1, data->var_cnt);
    int res1 = lia_theory_deduction(equ_list, equ_copy, tmp_value, data->var_cnt, data->int8_max, data->int16_max, data->int32_max, data->int64_max);
    free_InequList(equ_list);
    equ_list = copy_InequList(tdata->data.lialist->equ_list, data->var_cnt);
    if(res1 == 1) {
      free(tmp_value);
      free_InequList(equ1);
      free_InequList(equ2);
      return 0;
    }
    equ2->next = copy_InequList(tmp, data->var_cnt);
    equ_copy = copy_InequList(equ2, data->var_cnt);
    int res2 = lia_theory_deduction(equ_list, equ_copy, tmp_value, data->var_cnt, data->int8_max, data->int16_max, data->int32_max, data->int64_max);
    free_InequList(equ_list);
    free(tmp_value);
    free_InequList(equ1);
    free_InequList(equ2);
    if(res2 == 1) return 0;
    return 1;
}

int theroy_deduction_uf(TheoryData *tdata, PreData *data)
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
        if(ans) {
          freeMemory(S, data->var_cnt_uf);
          return 0;
        }
        tmp = tmp->next;
    }
    freeMemory(S, data->var_cnt_uf);
    return 1;
}

int uf_infer(int vi, int vj, TheoryData *tdata, PreData *data)
{
    database *S = initialize(data->var_cnt_uf);
    merge(S, tdata->data.uflist->equ_list);
    bool ans = areCongruent(S, vi, vj);
    freeMemory(S, data->var_cnt_uf);
    if (ans)
        return 1;
    else
        return 0;
}

int nelson_oppen_convex(CombineData *cdata, PreData *data)
{
    int res1 = theroy_deduction_lia(cdata->lia_data, data);
    if (res1 == 0)
        return 0;
    int res2 = theroy_deduction_uf(cdata->uf_data, data);
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
                else if (uf_infer(vi, vj, cdata->uf_data, data))
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
        if (new_equation && theroy_deduction_lia(cdata->lia_data, data) == 0)
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
                        if (lia_infer(vi, vj, cdata->lia_data, data))
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
        if (new_equation && theroy_deduction_uf(cdata->uf_data, data) == 0)
        {
            return 0;
        }
        if (!new_equation)
            break;
    }
    return 1;
}

void freeTheoryData(TheoryData *tdata)
{
    if (tdata == NULL)
        return;
    free(tdata->value);
    tdata->value = NULL;
    freeSmtProplist(tdata->prop_list);
    tdata->prop_list = NULL;
    if (tdata->type == LIA_THEORY && tdata->data.lialist != NULL)
    {
        free_InequList(tdata->data.lialist->equ_list);
        free_InequList(tdata->data.lialist->inequ_list);
        tdata->data.lialist->equ_list = NULL;
        tdata->data.lialist->inequ_list = NULL;
        if (tdata->data.lialist != NULL)
            free(tdata->data.lialist);
        ;
        tdata->data.lialist = NULL;
    }
    else if (tdata->type == UF_THEORY && tdata->data.uflist != NULL)
    {
        freeEquationlist(tdata->data.uflist->equ_list);
        freeEquationlist(tdata->data.uflist->inequ_list);
        tdata->data.uflist->equ_list = NULL;
        tdata->data.uflist->inequ_list = NULL;
        free(tdata->data.uflist);
        tdata->data.uflist = NULL;
    }
    free(tdata);
}

void freeCombineData(CombineData *cdata)
{
    if (cdata == NULL)
        return;
    freeTheoryData(cdata->lia_data);
    freeTheoryData(cdata->uf_data);
    cdata->lia_data = NULL;
    cdata->uf_data = NULL;
    for (int i = 0; i <= cdata->var_cnt; i++)
    {
        free(cdata->var_pair[i]);
        cdata->var_pair[i] = NULL;
    }
    free(cdata->var_pair);
    cdata->var_pair = NULL;
    free(cdata);
}

/*
int main(int argc, char **argv) {

    char s[80] = "input.txt";
    if(argc == 2)
    {
        printf("manual decided input file\n");
        strcpy(s,argv[1]);
    }

    FILE *fp; // = the file in.
    fp=fopen(s, "rb");
    if (fp == NULL)
    {
        printf("File %s can't be opened.\n", s);
        exit(1);
    }
    else
    {
        yyin = fp;
    }

    yyparse();
    extern struct SmtProp* root;
    printf("\n PARSING FINISHED. \n");
    PreData* data = initPreData();
    sat_data* sdata = preprocess(root, data);
    //initCombineData test:
    int* value = (int*)malloc(sizeof(int)*(data->var_cnt+1));
    memset(value, 0, sizeof(int)*(data->prop_cnt+1));
    for(int i = 0; i <= data->prop_cnt; i++) value[i] = 1;
    value[4] = 0;
    CombineData* cdata =  initCombineData(data, value);
    printf("lia_SmtProp_cnt: %d\n", cdata->lia_data->prop_cnt);
    printf("lia_SmtProplist:\n");
    printSmtProplist(cdata->lia_data->prop_list);
    printf("lia_var_cnt : %d\n", cdata->lia_data->var_cnt);
    for(int i = 1; i <= data->var_cnt; i++){
        if(cdata->lia_data->value[i] != 0){
            printf("%s  ", data->var_list[i]);
        }
    }
    printf("\nlia_equ_list:\n");
    printInequlist(cdata->lia_data->data.lialist->equ_list, data->var_cnt);
    printf("lia_inequ_list:\n");
    printInequlist(cdata->lia_data->data.lialist->inequ_list, data->var_cnt);
    printf("\nuf_SmtProp_cnt: %d\n", cdata->uf_data->prop_cnt);
    printf("uf_SmtProplist:\n");
    printSmtProplist(cdata->uf_data->prop_list);
    printf("uf_var_cnt : %d\n", cdata->uf_data->var_cnt);
    for(int i = 1; i <= data->var_cnt; i++){
        if(cdata->uf_data->value[i] != 0){
            printf("%s  ", data->var_list[i]);
        }
    }
    printf("\nuf_equ_list:\n");
    printEquationNode(cdata->uf_data->data.uflist->equ_list, data);
    printf("\nuf_inequ_list:\n");
    printEquationNode(cdata->uf_data->data.uflist->inequ_list, data);
    printf("\n");
    printf("var_cnt : %d,  common_cnt : %d\n", cdata->var_cnt, cdata->common_cnt);
    for(int i = 1; i <= data->var_cnt; i++){
        for(int j = i+1; j <= data->var_cnt; j++){
            if(cdata->var_pair[i][j] == SHARE_PAIR)
                printf("SHARE_PAIR: %s, %s\n", data->var_list[i], data->var_list[j]);
            else if(cdata->var_pair[i][j] == EQ_PAIR)
                printf("EQ_PAIR: %s, %s\n", data->var_list[i], data->var_list[j]);

        }
    }
    int res = theroy_deduction_lia(cdata->lia_data, data);
    if(res == 0) printf("unsat\n");
    else printf("sat\n");
    //add_equation_lia(4, 5, cdata->lia_data, data);
    //add_equation_uf(1,2,cdata->uf_data);
    printf("lia_equ_list:\n");
    printInequlist(cdata->lia_data->data.lialist->equ_list, data->var_cnt);
    printf("lia_inequ_list:\n");
    printInequlist(cdata->lia_data->data.lialist->inequ_list, data->var_cnt);
    // int res1 = lia_infer(3, 6, cdata->lia_data, data);
    // if(res1 == 0) printf("cannot infer\n");
    int res2 = uf_infer(4,5,cdata->uf_data, data);
    if(res2 == 0) printf("cannot infer\n");
    else printf("can infer\n");
    int res3 = nelson_oppen_convex(cdata, data);
    if(res3 == 0) printf("unsat");
    else printf("sat");

    fclose(fp);
}
*/
