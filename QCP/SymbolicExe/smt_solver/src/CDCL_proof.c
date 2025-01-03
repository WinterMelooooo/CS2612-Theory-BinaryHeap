#include "proof_lang.h"
#include "CDCL.h"
#include "CDCL_proof.h"
#include "smt_preprocess_proof.h"
//#define CDCL_DEBUG
int *clause_resolution_proof(int *wi, int *wj, sat_data *s, ProofData *data)
{
    int *res = malloc(sizeof(int) * (s->v_size));
    memset(res, 0, sizeof(int) * (s->v_size));
    int resol_var = -1;
    for (int i = 0; i < s->v_size; i++)
    {
        if ((wi[i] == 1 && wj[i] == -1) || (wi[i] == -1 && wj[i] == 1))
        {
            res[i] = 0;
            resol_var = wi[i] * (i + 1);
            continue;
        }
        else
        {
            if (wi[i] != 0)
                res[i] = wi[i];
            else
                res[i] = wj[i];
        }
    }
    ProofTerm *pi = clause2ProofTerm(wi, s->v_size);
    ProofTerm *pj = clause2ProofTerm(wj, s->v_size);
    int *plist = (int *)malloc(sizeof(int) * 2);
    plist[0] = search_prop2(pi, data->global_table);
    plist[1] = search_prop2(pj, data->global_table);
    freeProofTerm(pi);
    freeProofTerm(pj);
    ProofTerm *concl = clause2ProofTerm(res, s->v_size);
    ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
    memset(arg, 0, sizeof(ArgTerm));
    arg->type = NUM;
    arg->args.number = resol_var;
    data->cur_num++;
    ProofNode *node = newProofNode(plist, data->cur_num, RESOLUTION, concl, arg, 2);
    updata_proofdata_preprocess(data, node);
    return res;
}

int *clause_learning_proof(int wi, sat_data *s, ProofData *data)
{ // 返回学习到的子句
    bool flag = true;
    int *res = (int *)malloc(sizeof(int) * (s->v_size));
    memset(res, 0, sizeof(int) * (s->v_size));
    for (int i = 0; i < s->v_size; i++)
    {
        res[i] = s->cl_data->value[wi][i];
    }
    while (flag)
    {
#ifdef CDCL_DEBUG
// for(int i = 0; i < s->v_size; i++){
//     if(res[i] > 0){
//         fprintf(fp, "%d ", i+1);
//     }
//     else if(res[i] < 0){
//         fprintf(fp, "-%d ", i+1);
//     }
// }
// fprintf(fp, "\n");
#endif
        flag = false;
        for (int i = 0; i < s->v_size; i++)
        {
            if (res[i] == 0)
                continue;
            if (s->v_data->dl[i] == s->cur_dl && s->v_data->ancient[i] != -1)
            {
                // fprintf(fp,"resol var : %d, its ancient : %d\n", i+1,  s->v_data->ancient[i] +1);
                int wj = s->v_data->ancient[i];
                int *tmp = res;
                res = clause_resolution_proof(res, s->cl_data->value[wj], s, data);
                free(tmp);
                flag = true;
                break;
            }
        }
    }
    return res;
}

int cdcl_solver_proof(sat_data *s, ProofData *data)
{   
    #ifdef CDCL_DEBUG
    for(int i = 0; i < s->cl_size; i++){
        for(int j = 0; j < s->v_size; j++){
            if(s->cl_data->value[i][j] > 0){
                printf("%d ", j+1);
            }
            if(s->cl_data->value[i][j] < 0){
                printf("-%d ", j+1);
            }
        }
        printf("\n");
    }
    #endif
    s->cur_dl = 0;
    local_ProofData *pdata = init_local_ProofData(s->cl_size * 3);
    while (true)
    {
        int conflict_cl = -1;
        if (s->cur_dl == 0)
            conflict_cl = bcp_proof(s, pdata, data);
        else
            conflict_cl = bcp(s);
        while (conflict_cl != -1)
        { // 即bcp产生了冲突
            #ifdef CDCL_DEBUG
            printf("conflict_cl: %d \n", conflict_cl + 1);
            #endif
            if (s->cur_dl == 0)
            {
                // 将local_ProofData中的数据合并到ProofData
                mergelocal_ProofData(pdata, data);
                return 0;
            }
            int *new_cl = clause_learning_proof(conflict_cl, s, data);
            if (s->cl_size == s->cl_maxsize)
            {
                printf("too many clause");
                freelocal_ProofData(pdata);
                return -2;
            }
            else
                s->cl_size++;
            s->cl_data->value[s->cl_size - 1] = new_cl;
            s->cl_data->state[s->cl_size - 1] = 1;
            s->cl_data->lit_state[s->cl_size - 1] = 0;
            s->cl_data->unassign_num[s->cl_size - 1] = 0;
            s->cur_dl = conflict_analysis(new_cl, s);
            if (s->cur_dl < 0)
                return 0; // 表示unsat
            backtrack(s->cur_dl, s);
            if (s->cur_dl == 0)
                conflict_cl = bcp_proof(s, pdata, data);
            else
                conflict_cl = bcp(s);
        }
        if (decide(s) == -1){
            freelocal_ProofData(pdata);
            //printf("cdcl sat\n");
            return 1;
        }
    }
}

int bcp_proof(sat_data *s, local_ProofData *pdata, ProofData *data)
{
    int unitcl = -1;
    for (int i = 0; i < s->cl_size; i++)
    {
        if (s->cl_data->state[i] == 2)
        {
            unitcl = i;
            break;
        }
    }
    if (unitcl == -1)
        return -1;
#ifdef CDCL_DEBUG
    printf("unitcl : %d\n", unitcl + 1);
#endif
    int bcpvar = -1;
    for (int i = 0; i < s->v_size; i++)
    {
        if (s->v_data->value[i] == -1 && s->cl_data->value[unitcl][i] != 0)
        {
            bcpvar = i;
            break;
        }
    }
    if (bcpvar == -1)
        printf("error in bcp\n"), exit(0);
    // 已知bcpvar，unitcl，unitcl中其他所有命题变元应该都是已经推导出来的结果
    // 假设unitcl = p1\/p2\/p3 ,bcpvar = p2, 则此处该生成证明：(not p1)  p1\/p2\/p3 |-- p2 \/ p3  (not)p3 |-- p2
    // 知道unitcl的变量个数
#ifdef CDCL_DEBUG
    printf("bcpvar : %d\n", bcpvar + 1);
#endif    
    int ans1 = bcp_resol_proof(bcpvar, s->cl_data->value[unitcl], s->v_size, pdata, data);
    s->cl_data->state[unitcl] = 0;
    s->cl_data->lit_state[unitcl] = 1;
    s->cl_data->unassign_num[unitcl]--;
    if (s->cl_data->unassign_num[unitcl] != 0)
        printf("error, here should be 0\n"), exit(0);
    if (s->cl_data->value[unitcl][bcpvar] == 1)
    {
        s->v_data->value[bcpvar] = 1;
#ifdef CDCL_DEBUG
        printf("bcpvar = true\n");
#endif
    }
    else
    {
        s->v_data->value[bcpvar] = 0;
#ifdef CDCL_DEBUG
        printf("bcpvar = false\n");
#endif
    }
    s->v_data->ancient[bcpvar] = unitcl;
    s->v_data->dl[bcpvar] = s->cur_dl;
    int conflict = -1;
    for (int i = 0; i < s->cl_size; i++)
    {
        if (s->cl_data->value[i][bcpvar] == 0 || i == unitcl)
            continue;
        if (s->cl_data->state[i] == 0)
        {
            if ((s->cl_data->value[i][bcpvar] == 1 && s->v_data->value[bcpvar] == 1) ||
                (s->cl_data->value[i][bcpvar] == -1 && s->v_data->value[bcpvar] == 0))
            {
                s->cl_data->lit_state[i]++;
            }
        }
        else if (s->cl_data->state[i] == 1)
        {
            printf("error in bcp , shouldn't have unsat clause in bcp\n");
            exit(0);
        }
        else if (s->cl_data->state[i] == 2)
        {
            if ((s->cl_data->value[i][bcpvar] == 1 && s->v_data->value[bcpvar] == 1) ||
                (s->cl_data->value[i][bcpvar] == -1 && s->v_data->value[bcpvar] == 0))
            {
                s->cl_data->state[i] = 0;
                s->cl_data->lit_state[i]++;
            }
            else
            {
                s->cl_data->state[i] = 1;
                if (conflict == -1)
                    conflict = i;
                // 生成冲突false的证明，即整个smt证明生成过程中，最后一步证明
                int ans2 = bcp_resol_proof(bcpvar, s->cl_data->value[i], s->v_size, pdata, data);
                ProofTerm *concl = newFalseTerm();
                int *plist = (int *)malloc(sizeof(int) * 2);
                plist[0] = ans1;
                plist[1] = ans2;
                ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
                arg->type = NUM;
                arg->args.number = bcpvar + 1;
                if (s->v_data->value[bcpvar] == 0)
                    arg->args.number = -bcpvar - 1;
                pdata->cur_num++;
                ProofNode *node = newProofNode(plist, pdata->cur_num + data->cur_num, RESOLUTION, concl, arg, 2);
                updata_proofdata_cdcl_local(pdata, node);
            }
        }
        else
        {
            if ((s->cl_data->value[i][bcpvar] == 1 && s->v_data->value[bcpvar] == 1) ||
                (s->cl_data->value[i][bcpvar] == -1 && s->v_data->value[bcpvar] == 0))
            {
                s->cl_data->state[i] = 0;
                s->cl_data->lit_state[i] = 1;
            }
            else
            {
                s->cl_data->state[i]++;
                if (s->cl_data->state[i] == -1)
                    s->cl_data->state[i] = 2;
            }
        }
        s->cl_data->unassign_num[i]--;
    }
    if (conflict != -1)
        return conflict;
    else
        return bcp_proof(s, pdata, data);
}

// 目前的实现为多步的resolution， 也可以考虑生成一步的chain resolution，由于3cnf，所以其实最多两步
int bcp_resol_proof(int bcpvar, int *value, int n, local_ProofData *pdata, ProofData *data)
{
    int *value2 = (int *)malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++)
        value2[i] = value[i];
    // 生成 (NOT)Pi  Pi\/ Pi+1\/....\/Pn |-- Pi+1 \/ Pi+2\/...\/Pn
    ProofTerm *unitcl = clause2ProofTerm(value2, n);
    int node2 = search_prop_unsure(unitcl, pdata->local_table);
    if (node2 == -1){
        node2 = search_prop2(unitcl, data->global_table);
    }
    freeProofTerm(unitcl);
    for (int i = 0; i < n; i++)
    {
        if (value2[i] == 0 || i == bcpvar)
            continue;
        ProofTerm *t = NULL;
        if (value2[i] > 0)
            t = newNotProp(-i - 1);
        else
            t = newNotProp(i + 1);
        int node1 = search_prop_unsure(t, pdata->local_table);
        if (node1 == -1){
            node1 = search_prop2(t, data->global_table);
        }
        freeProofTerm(t);
        int *plist = (int *)malloc(sizeof(int) * 2);
        plist[0] = node1;
        plist[1] = node2;
        ArgTerm *arg = (ArgTerm *)malloc(sizeof(ArgTerm));
        memset(arg, 0, sizeof(ArgTerm));
        arg->type = NUM;
        arg->args.number = i + 1;
        if (value2[i] > 0)
            arg->args.number = -i - 1;
        value2[i] = 0;
        ProofTerm *concl = clause2ProofTerm(value2, n);
        pdata->cur_num++;
        ProofNode *node = newProofNode(plist, data->cur_num + pdata->cur_num, RESOLUTION, concl, arg, 2);
        node2 = updata_proofdata_cdcl_local(pdata, node);
    }
    free(value2);
    // node2->concl 应为 Pi其中i=bcpvar
    return node2;
}

ProofTerm *clause2ProofTerm(int *value, int n)
{
    int cl_var_cnt = 0;
    for (int i = 0; i < n; i++)
    {
        if (value[i] != 0)
            cl_var_cnt++;
    }
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->arg_num = cl_var_cnt;
    res->type = FUNC_OR;
    res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * (res->arg_num));
    memset(res->args, 0, sizeof(ProofTerm *) * (res->arg_num));
    int cnt = 0;
    for (int i = 0; i < n; i++)
    {
        if (value[i] == 0)
            continue;
        if (value[i] > 0)
            res->args[cnt] = newNotProp(i + 1);
        else
            res->args[cnt] = newNotProp(-i - 1);
        cnt++;
    }
    if (cnt != cl_var_cnt)
    {
        printf("error in clause2ProofTerm, cnt: %d, cl_var_cnt: %d\n", cnt, cl_var_cnt);
        exit(-1);
    }
    if (cl_var_cnt == 1)
    {
        ProofTerm *tmp = res->args[0];
        free(res);
        return tmp;
    }
    return res;
}

int updata_proofdata_cdcl_local(local_ProofData *pdata, ProofNode *node)
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
    int *hval = get_value_from_hstable(pdata->local_table, s, strlen(s));
    if (hval == NULL)
    {
        hval = (int *)malloc(sizeof(int));
        *hval = node->node_number;
        pdata->node_table[pdata->cur_num] = node;
        add_node2HashTable(pdata->local_table, s, strlen(s), hval);
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

local_ProofData *init_local_ProofData(int n)
{
    local_ProofData *pdata = (local_ProofData *)malloc(sizeof(local_ProofData));
    memset(pdata, 0, sizeof(local_ProofData));
    pdata->cur_num = 0;
    pdata->max_num = n;
    pdata->local_table = creat_hash_table();
    pdata->node_table = (ProofNode **)malloc(sizeof(ProofNode *) * (n + 1));
    memset(pdata->node_table, 0, sizeof(ProofNode *) * (n + 1));
    return pdata;
}

void mergelocal_ProofData(local_ProofData *pdata, ProofData *data)
{
    for (int i = 1; i <= pdata->cur_num; i++)
    {
        data->cur_num++;
        updata_proofdata(data, pdata->node_table[i]);
    }
    free(pdata->node_table);
    hash_table_delete(pdata->local_table);
}

void freelocal_ProofData(local_ProofData *pdata)
{
    for (int i = 1; i <= pdata->cur_num; i++)
    {
        freeProofNode(pdata->node_table[i]);
    }
    free(pdata->node_table);
    hash_table_delete(pdata->local_table);
}