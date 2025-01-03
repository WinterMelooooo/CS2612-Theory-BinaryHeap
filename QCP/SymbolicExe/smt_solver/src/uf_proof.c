#include"uf_proof.h"

//trans时出现的uf变量，则该变量对应的原函数必是一个全函数
//cong时出现的uf变量，其对应的原函数必为一个偏函数
//所有的uf函数其第二个参数一定对应原本的变量或者原本的函数，第一个参数对应原本函数名或者偏函数
//返回a = b对应的证明步骤的编号
int explain_proof(database* S, ProofData* data, PreData* pdata, int a, int b){
    if(a == b){
        ProofTerm* t1 = uf_eq_recover(a, b, pdata);
        data->cur_num++;
        ArgTerm* arg = (ArgTerm*)malloc(sizeof(ArgTerm));
        memset(arg, 0, sizeof(ArgTerm));
        arg->type = PTERM;
        arg->args.pterm = copy_ProofTerm(t1->args[0]);
        ProofNode* node = newProofNode(NULL, data->cur_num, REFL, t1, arg, 0);
        printProofNode(data, node);
        return update_proofdata_uf(data, node);
    }
    else if(S->edgelist[a].vertex == b){
        if(S->edgelist[a].labelType == 2){
            //a和b对应的原函数相等应该已经在前提中
            ProofTerm* t1 = uf_eq_recover(a, b, pdata);
            int res = ProofTerm2Num(t1, data->theory_global_table, NULL);
            if(res == -1) {
                ProofTerm* tmp = t1;
                t1 = uf_eq_recover(b, a, pdata);
                res = ProofTerm2Num(t1, data->theory_global_table, NULL);
                freeProofTerm(t1);
                if(res == -1){
                    printf("error in explain_proof, %d = %d should have been in assume\n", a, b);
                    exit(-1);
                }
                int* plist = (int*)malloc(sizeof(int));
                plist[0] = res;
                data->cur_num++;
                ProofNode* node = newProofNode(plist, data->cur_num, SYMM, tmp, NULL, 1);
                res = update_proofdata_uf(data, node);
            }
            return res;
        }
        else if (S->edgelist[a].labelType == 1){
            //此时a=b 由 uf(x1,y1) = a ,和uf(x2, y2) = b推出
            //由curryfy&&replace的过程可知此时a和b分别是两个uf函数在replace时起的名字
            //所以将这一推导步骤还原(隐藏curryfy)，应该是先将ab还原成完整的原函数，然后由cong规则推出两个原函数相等
            //y1和y2必然是原始变量或者原始函数，x1和x2则是原始函数名或者偏函数
            val_linklist* pnode = (val_linklist*)malloc(sizeof(val_linklist));
            pnode->val = explain_proof(S, data, pdata, S->edgelist[a].label.pair.lleft2, S->edgelist[a].label.pair.rleft2);
            pnode->next = NULL;
            char* s1 = pdata->var_list[S->edgelist[a].label.pair.lleft1];
            char* s2 = pdata->var_list[S->edgelist[a].label.pair.rleft1];
            UF_Hash* hval1 = get_value_from_hstable(pdata->ufun_table, s1, strlen(s1));
            UF_Hash* hval2 = get_value_from_hstable(pdata->ufun_table, s2, strlen(s2));
            int premise_num = 1;
            while(hval1 != NULL){
                if(hval2 == NULL){
                    printf("error in explain_proof, should have same curryfy depth\n");
                    exit(-1);
                }
                premise_num++;
                val_linklist* tmp = (val_linklist*)malloc(sizeof(val_linklist));
                tmp->val = explain_proof(S, data, pdata, hval1->arg2, hval2->arg2);
                tmp->next = pnode;
                pnode = tmp;
                s1 = pdata->var_list[hval1->arg1];
                s2 = pdata->var_list[hval2->arg1];
                hval1 = get_value_from_hstable(pdata->ufun_table, s1, strlen(s1));
                hval2 = get_value_from_hstable(pdata->ufun_table, s2, strlen(s2));
            }
            if(hval2 != NULL){
                printf("error in explain_proof, should have same curryfy depth\n");
                exit(-1);
            }
            int* premise = (int*)malloc(sizeof(int)*premise_num);
            for(int i = 0; i < premise_num; i++){
                premise[i] = pnode->val;
                val_linklist* tmp = pnode;
                pnode = pnode->next;
                free(tmp);
            }
            data->cur_num++;
            ProofTerm* concl = uf_eq_recover(a, b, pdata);
            ArgTerm* arg = (ArgTerm*)malloc(sizeof(ArgTerm));
            arg->type = N_FUNC;
            arg->args.func_name = (char*)malloc(sizeof(char)*(strlen(s1)+1));
            memset(arg->args.func_name, 0, sizeof(char)*(strlen(s1)+1));
            strcpy(arg->args.func_name, s1); 
            ProofNode* node = newProofNode(premise, data->cur_num, CONG, concl, arg,premise_num);
            return update_proofdata_uf(data, node);
        }
    }
    else{
        int com = nearestCommonAncestor(S, a, b);
        if(com == a){
            int num1 =  explain_trans_chain(S, data, pdata, a, b);
            //由于生成的是b=a，所以要利用等号对称性规则得到a=b
            ProofTerm* concl = uf_eq_recover(a, b, pdata);
            int* plist = (int*)malloc(sizeof(int));
            plist[0] = num1;
            data->cur_num++;
            ProofNode* node = newProofNode(plist, data->cur_num, SYMM, concl, NULL, 1);
            return update_proofdata_uf(data, node);
        }
        else if(com == b){
            return explain_trans_chain(S, data, pdata, b, a);
        }
        else {
            int node1 = explain_proof(S, data, pdata, a, com);
            int node2 = explain_proof(S, data, pdata, com, b);
            ProofTerm* concl = uf_eq_recover(a, b, pdata);
            int* plist = (int*)malloc(sizeof(int)*2);
            plist[0] = node1;
            plist[1] = node2;
            data->cur_num++;
            ProofNode* node = newProofNode(plist, data->cur_num, TRANS, concl, NULL, 2);
            //printProofNode(node);
            return update_proofdata_uf(data, node);
        }
    }
}

//由b->b1->b2->...->a的等价链，利用传递性规则生成b = a的证明
int explain_trans_chain(database* S, ProofData* data, PreData* pdata, int a, int b){
    int next = S->edgelist[b].vertex;
    int num1 = explain_proof(S, data, pdata, b, next);
    while(next != a){
        int num2 = explain_proof(S, data, pdata, next, S->edgelist[next].vertex);
        next = S->edgelist[next].vertex;
        ProofTerm* concl = uf_eq_recover(b, next, pdata);
        int* plist = (int*)malloc(sizeof(int)*2);
        plist[0] = num1;
        plist[1] = num2;
        data->cur_num++;
        ProofNode* node = newProofNode(plist, data->cur_num, TRANS, concl, NULL, 2);
        num1 = update_proofdata_uf(data, node);
    }
    return num1;
}

//将f还原成全函数
ProofTerm* uf_recover(int f, PreData* pdata){
    if(f <= pdata->var_cnt){
        ProofTerm* res = (ProofTerm*)malloc(sizeof(ProofTerm));
        memset(res, 0, sizeof(ProofTerm));
        res->type = VAR;
        res->arg_num = 0;
        res->func_name.node_number = f;
        return res;
    }
    else {
        val_linklist* arg_list = NULL;
        char* s = pdata->var_list[f];
        UF_Hash* hval = get_value_from_hstable(pdata->ufun_table, s, strlen(s));
        int arg_num = 0;
        while(hval != NULL){
            arg_num++;
            val_linklist* node = (val_linklist*)malloc(sizeof(val_linklist));
            node->val = hval->arg2;
            node->next = arg_list;
            arg_list = node;
            f = hval->arg1;
            s = pdata->var_list[f];
            hval = get_value_from_hstable(pdata->ufun_table, s, strlen(s));
        }
        //此时剩下的f和s应为原本全函数的函数名
        ProofTerm* res = (ProofTerm*)malloc(sizeof(ProofTerm));
        memset(res, 0, sizeof(ProofTerm));
        res->type = FUNC_N;
        res->func_name.name = (char*)malloc(strlen(s) + 1);
        memset(res->func_name.name, 0, strlen(s) + 1);
        if (res->func_name.name != NULL) {
            strcpy(res->func_name.name, s);
        }
        res->arg_num = arg_num;
        res->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*arg_num);
        for(int i = 0; i < arg_num; i++){
            res->args[i] = uf_recover(arg_list->val, pdata);
            val_linklist* tmp = arg_list;
            arg_list = arg_list->next;
            free(tmp);
        }
        return res;
    }
}

ProofTerm* uf_eq_recover(int f1, int f2, PreData* pdata){
    ProofTerm* res = (ProofTerm*)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = FUNC_EQ;
    res->arg_num = 2;
    res->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*2);
    res->args[0] = uf_recover(f1, pdata);
    res->args[1] = uf_recover(f2, pdata);
    return res;
}

int update_proofdata_uf(ProofData* pdata, ProofNode* node){
    if(pdata->cur_num > pdata->max_num){
        //扩容node_table
        pdata->max_num *= 2;
        ProofNode** res = (ProofNode**)realloc(pdata->node_table, (pdata->max_num + 1) * sizeof(ProofNode*));
        if (res == NULL) {
            printf("memory is not enough\n");
            exit(-1);
        }
        pdata->node_table = res;
    }
    char* s = ProofTerm2str(node->concl);
    int* hval = get_value_from_hstable(pdata->theory_global_table, s, strlen(s));
    if(hval == NULL){
        hval = (int*)malloc(sizeof(int));
        *hval = node->node_number;
        pdata->node_table[node->node_number] = node;
        add_node2HashTable(pdata->theory_global_table, s, strlen(s), hval);
        free(s);
        return node->node_number;
    }
    else{
        pdata->cur_num --;
        if(node->rule == UF_CONTRA_FALSE){
            printf("error in uf_false_gen, false should not appear twice\n");
        }
        free(s);
        freeProofNode(node);
        return *hval;
    }
}

ProofTerm* uf_trans_ProofTerm(SmtTerm* t, PreData* pdata){
    if(t->type == SMT_UFTerm){
        ProofTerm* res = (ProofTerm*)malloc(sizeof(ProofTerm));
        memset(res, 0, sizeof(ProofTerm));
        res->type = FUNC_N;
        res->arg_num = t->term.UFTerm->numArgs;
        res->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*res->arg_num);
        memset(res->args, 0, sizeof(ProofTerm*)*res->arg_num);
        res->func_name.name = (char*)malloc(strlen(t->term.UFTerm->name)+1);
        memset(res->func_name.name, 0, strlen(t->term.UFTerm->name)+1);
        strcpy(res->func_name.name, t->term.UFTerm->name);
        for(int i = 0; i < res->arg_num; i++){
            res->args[i] = uf_trans_ProofTerm(t->term.UFTerm->args[i], pdata);
        }
        return res;
    }
    else if(t->type == SMT_VarName){
        ProofTerm* res = (ProofTerm*)malloc(sizeof(ProofTerm));
        memset(res, 0, sizeof(ProofTerm));
        res->type = VAR;
        Hash_val* hval = get_value_from_hstable(pdata->var_table, t->term.Variable, strlen(t->term.Variable));
        if(hval == NULL){
            printf("error in UF2ProofTerm, %s should be in hash table\n", t->term.Variable);
            exit(-1);
        }
        res->func_name.node_number = hval->num;
        return res;
    }
    else {
        printf("error in UF2ProofTerm, in this stage , uf should have been purified\n");
        exit(-1);
    }
}

ProofTerm* ufeq_trans_ProofTerm(SmtProp* p, PreData* pdata){
    if(p->type != SMTAT_PROP_UF_EQ && p->type != SMTAT_PROP_EQ){
        printf("error in ufeq_trans_ProofTerm, invalid prop type\n");
        printSmtProp(p);
        exit(-1);
    }
    ProofTerm* res = (ProofTerm*)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = FUNC_EQ;
    res->arg_num = 2;
    res->args = (ProofTerm**)malloc(sizeof(ProofTerm*));
    res->args[0] = uf_trans_ProofTerm(p->prop.Atomic_prop.term1, pdata);
    res->args[1] = uf_trans_ProofTerm(p->prop.Atomic_prop.term2, pdata);
    return res;
}

int uf_proof_assume(SmtProp* p, ProofData* data, PreData* pdata){
        ProofTerm* t = ufeq_trans_ProofTerm(p, pdata);
        data->cur_num++;
        ArgTerm* arg = (ArgTerm*)malloc(sizeof(ArgTerm));
        arg->type = PTERM;
        arg->args.pterm = t;
        ProofNode* anode = newProofNode(NULL, data->cur_num, ASSUME, copy_ProofTerm(t), arg, 0);
        return update_proofdata_uf(data, anode);
}

//只处理a=b的等式，将其还原后加入assum
//若还原后等式两边都是变量：x1 = x2，则进行一步推导：x1-x2 = 0
void uf_proof_assume_pos(EquationNode* list, ProofData* data, PreData* pdata){
    while(list->next != NULL){
        if(list->left2 != -1){
            list = list->next;
            continue;
        }
        ProofTerm* t = uf_eq_recover(list->left1, list->right, pdata);
        data->cur_num++;
        ArgTerm* arg = (ArgTerm*)malloc(sizeof(ArgTerm));
        arg->type = PTERM;
        arg->args.pterm = t;
        ProofNode* anode = newProofNode(NULL, data->cur_num, ASSUME, copy_ProofTerm(t), arg, 0);
        int ans = update_proofdata_uf(data, anode);
        //由a=b推出a-b = 0
        t = data->node_table[ans]->concl;
        if(t->args[0]->type == VAR && t->args[1]->type == VAR){
            uf_infer_add(data, pdata->var_cnt, list->left1, list->right, ans);
            uf_infer_add(data, pdata->var_cnt, list->right, list->left1, ans);
        }
        list = list->next;
    }
}

//处理a！=b，将其加入假设
void uf_proof_assume_neg(EquationNode* list, ProofData* data, PreData* pdata){
    while(list->next != NULL){
        if(list->left2 != -1){
            printf("error in uf_proof_assume_neg\n");
            exit(-1);
            //理论上不应该进入该分支
            list = list->next;
            continue;
        }
        ProofTerm* t = (ProofTerm*)malloc(sizeof(ProofTerm));
        memset(t, 0, sizeof(ProofTerm));
        t->type = FUNC_NOT;
        t->arg_num = 1;
        t->args = (ProofTerm**)malloc(sizeof(ProofTerm*));
        t->args[0] = uf_eq_recover(list->left1, list->right, pdata);
        data->cur_num++;
        ArgTerm* arg = (ArgTerm*)malloc(sizeof(ArgTerm));
        arg->type = PTERM;
        arg->args.pterm = t;
        ProofNode* anode = newProofNode(NULL, data->cur_num, ASSUME, copy_ProofTerm(t), arg, 0);
        update_proofdata_uf(data, anode);
        list = list->next;
    }
}

int uf_false_gen(database* S, ProofData* data, PreData* pdata, int x, int y){
    int p1 = explain_proof(S, data, pdata, x, y);
    ProofTerm* t = (ProofTerm*)malloc(sizeof(ProofTerm));
    memset(t, 0, sizeof(ProofTerm));
    t->type = FUNC_NOT;
    t->arg_num = 1;
    t->args = (ProofTerm**)malloc(sizeof(ProofTerm*));
    t->args[0] = uf_eq_recover(x, y, pdata);
    char* s = ProofTerm2str(t);
    int* hval = get_value_from_hstable(data->theory_global_table, s, strlen(s));
    freeProofTerm(t);
    free(s);
    int p2 = *hval;    
    int *plist = (int*)malloc(sizeof(int)*2);
    plist[0] = p1;
    plist[1] = p2;
    ProofTerm* concl = newFalseTerm();
    data->cur_num++;
    ProofNode* node = newProofNode(plist, data->cur_num, UF_CONTRA_FALSE, concl , NULL, 2);
    return update_proofdata_uf(data, node);
}

//由x=y推出x-y = 0
int uf_infer_add(ProofData* data, int n, int x, int y, int pnode){
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = FUNC_EQ0;
    res->arg_num = n + 1;
    res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * (n + 1));
    memset(res->args, 0, sizeof(ProofTerm *) * (n + 1));
    for (int i = 0; i <= n; i++)
    {
        res->args[i] = (ProofTerm *)malloc(sizeof(ProofTerm));
        memset(res->args[i], 0, sizeof(ProofTerm));
        res->args[i]->type = INT_CONST;
        res->args[i]->func_name.const_val = 0;
        res->args[i]->arg_num = 0;
        res->args[i]->args = NULL;
    }
    res->args[x]->func_name.const_val = 1;
    res->args[y]->func_name.const_val = -1;
    data->cur_num++;
    int* plist = (int*)malloc(sizeof(int));
    plist[0] = pnode;
    ProofNode* node = newProofNode(plist, data->cur_num, ARITH_TRANS, res, NULL, 1);
    return update_proofdata_uf(data, node);
}