#include "lia_theory.h"
#include "lia_proof.h"
#include "proof_lang.h"

// r1中全为等式，r2中为不等式
//返回NULL表示已经证出了false
InequList *eliminate_equa_constraint_proof(InequList *r1, InequList *r2, int *value, ProofData *pdata, MaxVar *table, int num, int level)
{
    InequList *cur = r1;
    while (cur->next != NULL)
    {
        InequList *equ = cur->next;
        InequList *tmp = r2;
        while (equ->next != NULL)
        {   
            int *res = equ_eliminate_simplify_proof(cur->coef, equ->coef, value, pdata, table, num, FUNC_EQ0, level);
            if (res == NULL)
                return NULL;
            free(equ->coef);
            equ->coef = res;
            equ = equ->next;
        }
        while (tmp->next != NULL)
        {   
            int *res = equ_eliminate_simplify_proof(cur->coef, tmp->coef, value, pdata, table, num, FUNC_LE0, level);
            if (res == NULL)
                return NULL;
            free(tmp->coef);
            tmp->coef = res;
            tmp = tmp->next;
        }
        if (equ->next == NULL && tmp->next == NULL)
        {
            // 即lia读入的是等式组，此时消元只剩一个等式
            bool res = equation_true(cur->coef, num, FUNC_EQ0, table);
            if (!res)
            {
                ProofNode *node = lia_FALSE(cur->coef, num, pdata, FUNC_EQ0, level);
                return NULL;
            }
        }
        cur = cur->next;
#ifdef LIA_THEORY_DEBUG
        printf("elimata once: \n");
        printInequlist(r1, num);
        printInequlist(r2, num);
        printf("elimate end\n");
#endif
    }
    return r2;
}

// r1 : a0 + a1*x1 + .. + an-1*xn-1 + an*xn = 0
// r2 : b0 + b1*x1 + .. + bn-1*xn-1 - bn*xn </<= 0
//返回NULL表示已经证出了false
int *equ_eliminate_simplify_proof(int *r1, int *r2, int *value, ProofData *pdata, MaxVar *table, int size, TermType op, int level)
{
    int num = 0;
    // 找出编号最大的系数不为0的变元
    for (int i = size; i >= 0; i--)
    {
        if (r1[i] != 0 && i != table->int8_max && i != table->int16_max && i != table->int32_max && i != table->int64_max)
        {
            num = i;
            value[i] = 0;
            break;
        }
    }
    if (num == 0 && !equation_true(r1, size, FUNC_EQ0, table))
    {
        ProofNode *node = lia_FALSE(r1, size, pdata, FUNC_EQ0, level);
        return NULL;
    }
    int *res = (int *)malloc(sizeof(int) * (size + 1));
    memset(res, 0, sizeof(int) * (size + 1));
    if (num == 0 || r2[num] == 0)
    {
        for (int i = 0; i <= size; i++)
            res[i] = r2[i];
        return res;
    }
    int an = r1[num];
    int bn = -r2[num];
    int lcm = (an * bn) / gcd(an, bn);
    int m1 = lcm / an;
    int m2 = lcm / bn;
    if (m2 < 0)
    {
        m2 = -m2;
        m1 = -m1;
    }
    for (int i = 0; i <= size; i++)
    {
        if (m1 > 0 && (r1[i] < LIA_INT_MIN / m1 || r1[i] > LIA_INT_MAX / m1))
        {
            printf("mul overflow1\n");
            exit(-1);
        }
        else if(m1 != -1 && m1 < 0 && (r1[i] > LIA_INT_MIN / m1 || r1[i] < LIA_INT_MAX / m1)){
            printf("mul overflow1.5\n");
            exit(-1);
        }
        else if (m1 == -1 && r1[i] == LIA_INT_MIN)
        {
            printf("mul overflow2\n");
            exit(-1);
        }
        if (r2[i] < LIA_INT_MIN / m2 || r2[i] > LIA_INT_MAX / m2)
        {
            printf("mul overflow3\n");
            exit(-1);
        }
        int x = m2 * r2[i];
        int y = m1 * r1[i];
        if (!check_add_safe(x, y))
        {
            printf("add overflow\n");
            free(res);
            exit(-1);
        }
        res[i] = x + y;
    }
    ProofNode *node = lia_proof_FME(r1, r2, res, size, pdata, num, op, ARITH_EQ_ELIM, level, table);
    if (node != NULL && node->concl->type == PROP_FALSE)
    {
        free(res);
        return NULL;
    }
    return res;
}

// r1中xn系数为正，r2中xn系数为负, num = n
// r1 : a0 + a1*x1 + .. + an-1*xn-1 + an*xn <= 0
// r2 : b0 + b1*x1 + .. + bn-1*xn-1 - bn*xn <= 0
// 此时an, bn 均大于0
// 生成的新约束 : c0 + c1*x1 + .. + cn-1*xn-1 <= 0
//返回NULL表示已经证出了false
int *generate_new_constraint_proof(int *r1, int *r2, ProofData *pdata, MaxVar *table, int num, int cur_num, int level)
{
    int an = r1[cur_num];
    int bn = -r2[cur_num];
    int g = gcd(an, bn);
    int m1 = bn / g;
    int m2 = an / g;
    int ub1, ub2, lb1, lb2;
    ub1 = LIA_INT_MAX / m1;
    lb1 = LIA_INT_MIN / m1;
    ub2 = LIA_INT_MAX / m2;
    lb2 = LIA_INT_MIN / m2;
    for (int i = 0; i <= num; i++)
    {
        if (r1[i] < lb1 || r1[i] > ub1)
        {
            printf("mul overflow5\n");
            exit(-1);
        }
        if (r2[i] < lb2 || r2[i] > ub2)
        {
            printf("mul overflow6\n");
            exit(-1);
        }
    }
    int *res = (int *)malloc(sizeof(int) * (num + 1));
    memset(res, 0, sizeof(int) * (num + 1));
    for (int i = 0; i <= num; i++)
    {
        // ci = m1*ai + m2*bi
        int x = m2 * r2[i];
        int y = m1 * r1[i];
        if (!check_add_safe(x, y))
        {
            printf("add overflow\n");
            free(res);
            exit(-1);
        }
        res[i] = x + y;
    }
    ProofNode *node = lia_proof_FME(r1, r2, res, num, pdata, cur_num, FUNC_LE0, ARITH_FME, level, table);
    if (node != NULL && node->concl->type == PROP_FALSE)
    {
        free(res);
        return NULL;
    }
    return res;
}

// r1和r2都有不存储信息的尾指针
// r1中所有不等式xn系数为正，r2所有不等式中xn系数为负
//返回NULL表示已经证出了false
InequList *generate_new_constraint_list_proof(InequList *r1, InequList *r2, ProofData *pdata, MaxVar *table, int num, int cur_num, int level)
{
    if (r1 == NULL || r2 == NULL)
    {
        printf("error in generate_new_constraint_list, should have tail pointer\n");
        exit(-1);
    }
    InequList *res = initInequList();
    if (r1->next == NULL || r2->next == NULL)
    {
        // 表明xn是一个unbounded的变元，直接删去其所有相关约束，不需要增加新的约束
        return res;
    }
    InequList *p1 = r1;
    while (p1->next != NULL)
    {
        InequList *p2 = r2;
        while (p2->next != NULL)
        {
            InequList *tmp = initInequList();
            tmp->coef = generate_new_constraint_proof(p1->coef, p2->coef, pdata, table, num, cur_num, level);
            if (tmp->coef == NULL)
            {
                free_InequList(tmp);
                free_InequList(res);
                return NULL;
            }
            tmp->next = res;
            res = tmp;
            p2 = p2->next;
        }
        p1 = p1->next;
    }
    return res;
}

// 消去x1,x2,...xn,得到常数不等关系
// real shadow没有解，原问题必没有整数解，若有整数解，原问题未必有
//返回NULL表示已经证出了false
InequList *real_shadow_proof(InequList *r, int *value, ProofData *pdata, MaxVar *table, int n, int level)
{
    int cnt = n;
    #ifdef LIA_THEORY_DEBUG
    printInequlist(r, n);
    #endif
    while (cnt >= 1)
    {
        if (value[cnt] == 0 || cnt == table->int8_max || cnt == table->int16_max || cnt == table->int32_max || cnt == table->int64_max)
        {
            cnt--;
            continue;
        }
        #ifdef LIA_THEORY_DEBUG
        printf("eliminate x%d\n", cnt);
        #endif
        BoundPair *res = eliminate_xn(r, cnt);
        r = res->remain;
        #ifdef LIA_THEORY_DEBUG
        printf("r after elimate:\n");
        printInequlist(r, n);
        printf("upper bound:\n");
        printInequlist(res->upper, n);
        printf("lower bound:\n");
        printInequlist(res->lower, n);
        #endif
        InequList *new_cons = generate_new_constraint_list_proof(res->upper, res->lower, pdata, table, n, cnt, level);
        #ifdef LIA_THEORY_DEBUG
        printf("new general cons: \n");
        printInequlist(new_cons, n);
        #endif
        free_InequList(res->upper);
        free_InequList(res->lower);
        free(res);
        if (new_cons == NULL)
        {   
            free_InequList(r);
            return NULL;
        }
        InequList *p = r;
        if (p->next == NULL)
        {
            free(r);
            r = new_cons;
        }
        else
        {
            while (p->next->next != NULL)
                p = p->next; // 寻找尾指针前一个指针
            free(p->next);
            p->next = new_cons;
        }
        #ifdef LIA_THEORY_DEBUG
        printf("new cons: \n");
        printInequlist(r, n);
        #endif
        cnt--;
    }
    return r;
}

int lia_theory_deduction_proof(InequList *r1, InequList *r2, int *value, ProofData *pdata, int n, int int8_max, int int16_max, int int32_max, int int64_max, int level)
{
#ifdef LIA_THEORY_DEBUG
    printf("lia_theory_deduction:\n");
#endif
    MaxVar *table = (MaxVar *)malloc(sizeof(MaxVar));
    table->int8_max = int8_max;
    table->int16_max = int16_max;
    table->int32_max = int32_max;
    table->int64_max = int64_max;
    if (r1->next != NULL)
    {
        r2 = eliminate_equa_constraint_proof(r1, r2, value, pdata, table, n, level);
        if (r2 == NULL){
            free(table);
            return 0;
        }
    }
    InequList *res = real_shadow_proof(r2, value, pdata, table, n, level);
    if (res == NULL){   
        free(table);
        return 0;
    }
    InequList* p = res;
    while(p->next != NULL){
        //只要int64_max系数为正，在不等式系数不超过int32范围的情况下
        // a1*int_max + a2*ll_max + c <= 0 恒不成立
        //若int64_max系数为负，则上式恒成立
        if(int64_max != -1 && p->coef[int64_max] > 0) {
            ProofNode* node = lia_FALSE(p->coef, n, pdata, FUNC_LE0, level);
            free(table);
            free_InequList(res);
            return 0;
        }
        if(int64_max == -1 || (int64_max != -1 && p->coef[int64_max] == 0)) {
            long long cons = (long long)(p->coef[0]);
            //由于系数范围不超过int32，所以下面的计算在极端情况下也不会超过int64的范围
            if(int8_max != -1 && p->coef[int8_max] != 0) cons = cons + ((long long)(p->coef[int8_max]))*((long long)INT8_MAX);
            if(int16_max != -1 && p->coef[int16_max] != 0) cons = cons + ((long long)(p->coef[int16_max]))*((long long)INT16_MAX);
            if(int32_max != -1 && p->coef[int32_max] != 0) cons = cons + ((long long)(p->coef[int32_max]))*((long long)INT32_MAX);
            if(cons > 0) {
                #ifdef LIA_THEORY_DEBUG
                printf("cons : %lld\n", cons);
                #endif
                ProofNode* node = lia_FALSE(p->coef, n, pdata, FUNC_LE0, level);
                free(table);
                free_InequList(res);
                return 0;
            }
        }
        p = p->next;
    }
    free_InequList(res);
    return 1;
}

// n个变元,带上常数一共有n+1个系数
ProofTerm *inequ_trans_proofterm(int *coef, int n, TermType type)
{
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = type;
    res->arg_num = n + 1;
    res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * (n + 1));
    memset(res->args, 0, sizeof(ProofTerm *) * (n + 1));
    for (int i = 0; i <= n; i++)
    {
        res->args[i] = (ProofTerm *)malloc(sizeof(ProofTerm));
        memset(res->args[i], 0, sizeof(ProofTerm));
        res->args[i]->type = INT_CONST;
        res->args[i]->func_name.const_val = coef[i];
        res->args[i]->arg_num = 0;
        res->args[i]->args = NULL;
    }
    return res;
}

// 用于在混合理论求解的最开始，将所有assign的情况做assum, 使用theory_global_table
// 在lia_infer时要推a=b，分别对a>b以及a<b做假设，使用theroy_local_table
void lia_proof_assume(InequList *r, ProofData *pdata, TermType type, int n, int level)
{
    InequList *tmp1 = r;
    while (tmp1->next != NULL)
    {
        ProofTerm *t = inequ_trans_proofterm(tmp1->coef, n, type);
        ++(pdata->cur_num);
        ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
        arg->type = PTERM;
        arg->args.pterm = t;
        ProofNode *anode = newProofNode(NULL, pdata->cur_num, ASSUME, copy_ProofTerm(t), arg, 0);
        updata_proofdata_lia(pdata, anode, level);
        tmp1 = tmp1->next;
    }
}

int lia_infer_assume(int* coef, ProofData *pdata, int n){
    ProofTerm *t = inequ_trans_proofterm(coef, n, FUNC_LE0);
    ++(pdata->cur_num);
    ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
    arg->type = PTERM;
    arg->args.pterm = t;
    ProofNode *anode = newProofNode(NULL, pdata->cur_num, ASSUME, copy_ProofTerm(t), arg, 0);
    return updata_proofdata_lia(pdata, anode, 2);
}

// 检查当前等式或不等式是否成立
bool equation_true(int *coef, int n, TermType op, MaxVar *table)
{
    int int8_max = table->int8_max;
    int int16_max = table->int16_max;
    int int32_max = table->int32_max;
    int int64_max = table->int64_max;
    for (int i = 1; i <= n; i++)
    {
        if (i == table->int8_max || i == table->int16_max || i == table->int32_max || i == table->int64_max)
            continue;
        if (coef[i] != 0)
            return true;
    }
    if (int64_max != -1 && coef[int64_max] != 0)
        return false;
    long long cons = (long long)coef[0];
    // 由于系数范围不超过int32，所以下面的计算在极端情况下也不会超过int64的范围
    if (int8_max != -1 && coef[int8_max] != 0)
        cons = cons + ((long long)coef[int8_max]) * ((long long)INT8_MAX);
    if (int16_max != -1 && coef[int16_max] != 0)
        cons = cons + ((long long)coef[int16_max]) * ((long long)INT16_MAX);
    if (int32_max != -1 && coef[int32_max] != 0)
        cons = cons + ((long long)coef[int32_max]) * ((long long)INT32_MAX);
    if (op == FUNC_EQ0 && cons != 0)
        return false;
    if (op == FUNC_LE0 && cons > 0)
        return false;
    return true;
}

// 用等式left在right中消去val，得到res，right的关系符是op(=或者<=)
//  两个不等式left和right傅里叶消去val产生res, 此时op恒为<=
ProofNode *lia_proof_FME(int *left, int *right, int *res, int n, ProofData *pdata, int val, TermType op, ProofRule rule, int level, MaxVar *table)
{
    ProofTerm *t1 = NULL;
    if (rule == ARITH_EQ_ELIM)
        t1 = inequ_trans_proofterm(left, n, FUNC_EQ0);
    else
        t1 = inequ_trans_proofterm(left, n, FUNC_LE0);
    ProofTerm *t2 = inequ_trans_proofterm(right, n, op);
    int n1 = ProofTerm2Num(t1, pdata->theory_global_table, pdata->local_table);
    int n2 = ProofTerm2Num(t2, pdata->theory_global_table, pdata->local_table);
    if (n1 == -1 || n2 == -1)
    {   
        printf("error in lia_proof_FME, use prop without proof\n");
        printf("premise:\n");
        printProofTerm(t1);
        printf(" , ");
        printProofTerm(t2);
        printf("\nconcl:\n");
        printProofTerm(inequ_trans_proofterm(res, n, op));
        printf("\n");

        exit(-1);
    }
    freeProofTerm(t1);
    freeProofTerm(t2);
    int *plist = (int *)malloc(sizeof(int) * 2);
    plist[0] = n1;
    plist[1] = n2;
    ProofTerm *concl = inequ_trans_proofterm(res, n, op);
    // 检查是否是false
    bool flag = equation_true(res, n, op, table);
    ++(pdata->cur_num);
    ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
    memset(arg, 0, sizeof(ArgTerm));
    arg->type = NUM;
    arg->args.number = val;
    ProofNode *rnode = newProofNode(plist, pdata->cur_num, rule, concl, arg, 2);
    int re = updata_proofdata_lia(pdata, rnode, level);
    if (!flag)
    {
        rnode = lia_FALSE(res, n, pdata, op, level);
    }
    return rnode;
}

ProofNode *lia_FALSE(int *coef, int n, ProofData *pdata, TermType op, int level)
{
    ProofTerm *t1 = inequ_trans_proofterm(coef, n, op);
    int n1 = ProofTerm2Num(t1, pdata->theory_global_table, pdata->local_table);
    freeProofTerm(t1);
    if (n1 == -1)
    {
        printf("error in lia_FALSE, use prop without proof\n");
        exit(-1);
    }
    int *plist = (int *)malloc(sizeof(int));
    plist[0] = n1;
    ProofTerm *concl = newFalseTerm();
    ++(pdata->cur_num);
    ProofNode *rnode = newProofNode(plist, pdata->cur_num, ARITH_FALSE, concl, NULL, 1);
    updata_proofdata_lia(pdata, rnode, level);
    return rnode;
}

// 用结论和证明步骤更新proofdata
//  若当前可用结论里已经存在该结论，并返回对应结论的编号
//  在theroy判断sat时level为1, 在lia_infer时为2
int updata_proofdata_lia(ProofData *pdata, ProofNode *node, int level)
{
    if (pdata->cur_num > pdata->max_num)
    {
        // 扩容node_table
        pdata->max_num *= 2;
        ProofNode** res = (ProofNode**)realloc(pdata->node_table, (pdata->max_num + 1) * sizeof(ProofNode*));
        if (res == NULL) {
            printf("memory is not enough\n");
            exit(-1);
        }
        //printf("extend in lia\n");
        pdata->node_table = res;
    }
    // pdata->node_table[node->node_number] = node;
    char *s = ProofTerm2str(node->concl);
    Hash_Table *table = pdata->theory_global_table;
    if (level == 2)
        table = pdata->local_table;
    int *hval = get_value_from_hstable(table, s, strlen(s));
    if (hval == NULL)
    {
        hval = (int *)malloc(sizeof(int));
        *hval = node->node_number;
        pdata->node_table[node->node_number] = node;
        add_node2HashTable(table, s, strlen(s), hval);
        free(s);
        return node->node_number;;
    }
    else
    {
        free(s);
        pdata->cur_num--;
        return *hval;
    }
}

//lia_infer_proof中使用
int SCOPE_END_LIA(int fnode, int anode, ProofData* data){
    //由false推出假设anode不成立，concl为not(vj-vi+1<=0)
    data->cur_num++;
    int* plist = (int*)malloc(sizeof(int));
    plist[0] = fnode;
    ProofTerm* t = copy_ProofTerm(data->node_table[anode]->concl);
    ProofTerm* concl = (ProofTerm*)malloc(sizeof(ProofTerm));
    concl->arg_num = 1;
    concl->type = FUNC_NOT;
    concl->args = (ProofTerm**)malloc(sizeof(ProofTerm*));
    concl->args[0] = t;
    ArgTerm* arg = (ArgTerm*)malloc(sizeof(ArgTerm));
    arg->type = NUM;
    arg->args.number = anode;
    ProofNode* node = newProofNode(plist, data->cur_num, SCOPE, concl, arg, 1);
    return updata_proofdata_lia(data, node, 1);

}

int LIA_ARITH_NOT_ELIM(int* coef, int n, int node, ProofData* data){
    int* rcoef = (int*)malloc(sizeof(int)*(n+1));
    for(int i = 0; i <= n; i++){
        rcoef[i] = -coef[i];
    }
    rcoef[0]++;
    ProofTerm* concl = inequ_trans_proofterm(rcoef, n, FUNC_LE0);
    free(rcoef);
    data->cur_num++;
    int* plist = (int*)malloc(sizeof(int));
    plist[0] = node;
    ProofNode* anode = newProofNode(plist, data->cur_num, ARITH_NOT_ELIM, concl, NULL, 1);
    return updata_proofdata_lia(data, anode, 1);
}