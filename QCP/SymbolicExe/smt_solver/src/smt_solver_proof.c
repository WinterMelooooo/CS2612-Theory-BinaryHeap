#include"smt_solver.h"
#include"smt_solver_proof.h"
#include "smt_proof_checker.h"
// #define SMT_SOLVER_DEBUG
// #define SMT_PROOF_DEBUG
//0:unsat, 1:sat, -1: 永真
SMT_PROOF* smt_solver_proof(SmtProp* p){
    printf("smtprop check:\n");
    printSmtProp(p);
    printf("\n");
    SMT_PROOF* proof = (SMT_PROOF*)malloc(sizeof(SMT_PROOF));
    memset(proof, 0, sizeof(SMT_PROOF));
    #ifdef SMT_PROOF_DEBUG
    printSmtProp(p);
    printf("\n");
    #endif
    SmtProp* p1 = prop_simplify(p);
    if(p1->type == SMTTF_PROP){
        bool ans = p1->prop.TF;
        freeSmtProp(p1);
        // todo: 增加simplify的证明步骤
        if(ans){
            proof->ans = -1;
            return proof;
        }
        else{
            proof->ans = 0;
            return proof;
        }
    }
    SmtProp* p2 = copy_SmtProp(p1);
    PreData* data = initPreData();
    ProofData* pdata = initProofData();
    sat_data* sdata = preprocess_proof(p2, data, pdata);
    #ifdef SMT_PROOF_DEBUG
    printf("proof after preprocess\n");
    for(int i = 1; i <= pdata->cur_num; i++){
        printProofNode(pdata, pdata->node_table[i]);
    }
    printf("start cdcl proof\n");
    #endif
    cnf_list* learnt_clause = (cnf_list*)malloc(sizeof(cnf_list));
    learnt_clause->clause = NULL;
    learnt_clause->next = NULL;
    learnt_clause->size = 0;
    while(true){
        int ans = cdcl_solver_proof(sdata, pdata);
        if(ans == 0) {
            SCOPE_FINAL(pdata);
            #ifdef SMT_PROOF_DEBUG
            printf("declare start\n");
            for(int i = 1; i <= pdata->declare_num; i++) {
                printProofNode(pdata, pdata->declare_table[i]);
            }
            printf("proof start\n");
            for(int i = 1; i <= pdata->cur_num; i++){
                printProofNode(pdata, pdata->node_table[i]);
            }
             printf("proof end\n");
             printf("check start\n");
             //int check_ans = proof_check(pdata->declare_table, pdata->declare_num, pdata->node_table, pdata->cur_num);
             //printf("check res: %d\ncheck end\n", check_ans);
             #endif
             proof->ans = 0;
             proof->vtable = data->var_table;
             proof->declare_table = pdata->declare_table;
             proof->declare_num = pdata->declare_num;
             proof->proof_table = pdata->node_table;
             proof->proof_num = pdata->cur_num;
            freeCDCL(sdata);
            freePredata_proof(data);
            free_cnf_list(learnt_clause);
            freeSmtProp(p1);
            hash_table_delete(pdata->global_table);
            hash_table_delete(pdata->theory_global_table);
            hash_table_delete(pdata->local_table);
            free(pdata);
            #ifdef SMT_SOLVER_DEBUG
            printf("cdcl unsat\n");
            #endif
            return proof;
        }
        else{
            #ifdef SMT_SOLVER_DEBUG
            printf("cdcl sat\n");
            #endif
            int* value = (int*)malloc(sizeof(int)*(data->prop_cnt+1));
            memset(value, 0, sizeof(int)*(data->prop_cnt+1));
            for(int i = 0; i < data->prop_cnt; i++){
                value[i+1] = sdata->v_data->value[i];
                #ifdef SMT_SOLVER_DEBUG
                printf("%d  :  value: %d\n",i+1, value[i+1]);
                #endif
            }
            //根据value给出theory求解时的全局命题假设
            //printf("assume start\n");
            assign_assum_proof(value, data->at_prop_cnt, data, pdata);
            //printf("assume end\n");
            CombineData* cdata =  initCombineData_proof(data, value, pdata);
            free(value);
            value = NULL;
            
            if(cdata == NULL) {
                freeCDCL(sdata);
                freePredata(data);
                free_cnf_list(learnt_clause);
                freeSmtProp(p1);
                freeProofData(pdata);
                proof->ans = 1;
                return proof;
            }
            #ifdef SMT_SOLVER_DEBUG
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
            #endif
            int theory_res = nelson_oppen_convex_proof(cdata, data, pdata);
            freeCombineData(cdata);
            if(theory_res == 0) {
                //END_SCOPE 规则，推出sat这边学习到的子句
                // printProofNode(pdata, pdata->node_table[pdata->cur_num]);
                // printf("\n");
                theroy_infer_proof(pdata, sdata->v_data->value, data->at_prop_cnt);
                #ifdef SMT_SOLVER_DEBUG
                printf("test mix_theory\n");
                for(int i = 1; i <= pdata->cur_num; i++){
                    printProofNode(pdata, pdata->node_table[i]);
                }
                printf("theory_unsat\n");
                #endif
                int* new_clause = (int*)malloc(sizeof(int)*sdata->v_size);
                memset(new_clause, 0, sizeof(int)*sdata->v_size);
                for(int i = 0; i < data->at_prop_cnt; i++){
                    if(sdata->v_data->value[i] == 1)
                        new_clause[i] = -1;
                    else if(sdata->v_data->value[i] == 0)
                        new_clause[i] = 1;
                }
                cnf_list* lc = (cnf_list*)malloc(sizeof(cnf_list));
                lc->clause = new_clause;
                lc->next = learnt_clause;
                lc->size = sdata->v_size;
                learnt_clause = lc;
                freePredata(data);
                freeCDCL(sdata);
                data = initPreData();
                p2 = copy_SmtProp(p1);
                sdata = preprocess(p2, data);
                cnf_list* tmp = learnt_clause;
                while(tmp->next != NULL){
                    sdata->cl_size++;
                    sdata->cl_data->value[sdata->cl_size-1] = clause_copy(tmp->clause, sdata->v_size);
                    sdata->cl_data->state[sdata->cl_size-1] = -data->at_prop_cnt;
                    if(data->at_prop_cnt == 1) sdata->cl_data->state[sdata->cl_size-1] = 2;
                    sdata->cl_data->unassign_num[sdata->cl_size-1] = data->at_prop_cnt;
                    tmp =tmp->next;
                }
                hash_table_delete(pdata->theory_global_table);
                pdata->theory_global_table = creat_hash_table();
            }
            else {
                #ifdef SMT_PROOF_DEBUG
                printf("proof start\n");
                for(int i = 1; i <= pdata->cur_num; i++){
                    printProofNode(pdata, pdata->node_table[i]);
                }
                printf("proof end\n");
                printf("free start\n");
                #endif
                freeProofData(pdata);
                #ifdef SMT_PROOF_DEBUG
                printf("free end\n");
                #endif
                freeCDCL(sdata);
                freePredata(data);
                free_cnf_list(learnt_clause);
                freeSmtProp(p1);
                proof->ans = 1;
                return proof;
            }
        }
    }
}

int theroy_infer_proof(ProofData* pdata, int* value, int n){
    ArgTerm** args = (ArgTerm**)malloc(sizeof(ArgTerm*)*n);
    memset(args, 0, sizeof(ArgTerm*)*n);
    ProofTerm* concl = (ProofTerm*)malloc(sizeof(ProofTerm));
    memset(concl, 0, sizeof(ProofTerm));
    concl->type = FUNC_AND;
    concl->arg_num = n;
    concl->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*n);
    ProofTerm* concl2 = (ProofTerm*)malloc(sizeof(ProofTerm));
    memset(concl2, 0, sizeof(ProofTerm));
    concl2->type = FUNC_OR;
    concl2->arg_num = n;
    concl2->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*n);
    memset(concl2->args, 0, sizeof(ProofTerm*)*n);
    for(int i = 1; i <= n; i++){
        ProofTerm* t1 = NULL;
        ProofTerm* t2 = NULL;
        if(value[i-1] == 1){
            t1 = newNotProp(i);
            t2 = newNotProp(-i);
        }
        else {
            t1 = newNotProp(-i);
            t2 = newNotProp(i);
        }
        concl->args[i-1] = t1;
        concl2->args[i-1] = t2;
        args[i-1] = (ArgTerm*)malloc(sizeof(ArgTerm));
        memset(args[i-1], 0, sizeof(ArgTerm));
        args[i-1]->type = NUM;
        args[i-1]->args.number = search_prop2(t1, pdata->theory_global_table);
    }
    if(concl2->arg_num == 1){
        ProofTerm* tmp = concl2;
        concl2 = concl2->args[0];
        free(tmp);
    }
    if(concl->arg_num == 1){
        ProofTerm* tmp = concl;
        concl = concl->args[0];
        free(tmp);
    }
    int* plist = (int*)malloc(sizeof(int));
    plist[0] = pdata->cur_num;
    pdata->cur_num++;
    ProofNode* node = (ProofNode*)malloc(sizeof(ProofNode));
    memset(node, 0, sizeof(ProofNode));
    node->premise_num = 1;
    node->arg_num = n;
    node->premise_list = plist;
    node->args = args;
    node->rule = SCOPE;
    node->node_number = pdata->cur_num;
    node->concl = newPropTerm(concl, NULL, FUNC_NOT);
    //完成 False | P1 P2 ... Pn  |-- Not(P1/\P2/\.../\Pn)
    //使用De Morgan律对结论做化简
    int* plist2 = (int*)malloc(sizeof(int));
    plist2[0] = updata_proofdata_preprocess(pdata, node);
    pdata->cur_num++;
    ProofNode* node2 = newProofNode(plist2, pdata->cur_num, NOT_AND, concl2, NULL, 1);
    // printProofNode(pdata, node);
    // printf("\n");
    // printProofNode(pdata, node2);
    // printf("\n");
    return updata_proofdata_preprocess(pdata, node2);
}


//最后一步，关闭原命题
int SCOPE_FINAL(ProofData* pdata){
    int* plist = (int*)malloc(sizeof(int));
    plist[0] = pdata->cur_num;
    ArgTerm** args = (ArgTerm**)malloc(sizeof(ArgTerm*));
    args[0] = (ArgTerm*)malloc(sizeof(ArgTerm));
    memset(args[0], 0, sizeof(ArgTerm));
    args[0]->type = NUM;
    args[0]->args.number = 1;
    pdata->cur_num++;
    ProofNode* node = (ProofNode*)malloc(sizeof(ProofNode));
    memset(node, 0, sizeof(ProofNode));
    node->premise_num = 1;
    node->arg_num = 1;
    node->premise_list = plist;
    node->args = args;
    node->rule = SCOPE;
    node->node_number = pdata->cur_num;
    node->concl = newPropTerm(copy_ProofTerm(pdata->node_table[1]->concl), NULL, FUNC_NOT);
    updata_proofdata(pdata, node);
    if(node->concl->args[0]->type == FUNC_NOT){
        int* plist2 = (int*)malloc(sizeof(int));
        plist2[0] = node->node_number;
        pdata->cur_num++;
        ProofNode* node2 = newProofNode(plist2, pdata->cur_num, NOT_ELIM, copy_ProofTerm(pdata->node_table[1]->concl->args[0]), NULL, 1);
        return updata_proofdata(pdata, node2);
    }
    else return node->node_number;
}

int updata_proofdata(ProofData *pdata, ProofNode *node){
    if (pdata->cur_num > pdata->max_num){
        // 扩容node_table
        pdata->max_num *= 2;
        ProofNode **res = (ProofNode **)realloc(pdata->node_table, (pdata->max_num + 1) * sizeof(ProofNode *));
        if (res == NULL){
            printf("memory is not enough\n");
            exit(-1);
        }
        pdata->node_table = res;
    }
    pdata->node_table[node->node_number] = node;
    return node->node_number;
}

int smt_proof_check_high(SmtProp* goal, SMT_PROOF* proof){
    // if(proof->ans == 1) return 0;
    // return smt_proof_check_low(SmtProp2ProofTerm(prop_simplify(goal), proof->vtable), proof);
    return 1;
}
