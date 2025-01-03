#include "coq_proofgen.h"

enum VAR_COQ_TYPE var_type_search(char* v, int type){
    if(type == 0) return COQ_Z;
    else if(type == 1) return COQ_Z_Z;
}


PropTable* initPropTable(){
    PropTable* res = (PropTable*)malloc(sizeof(PropTable));
    memset(res, 0, sizeof(PropTable));
    res->purify_table = creat_hash_table();
    res->clause_table = creat_hash_table();
    res->local_table = NULL;
    res->env = GLOBAL_ENV;
    res->atom_num = 0;
    res->new_cl_num = 0;
    res->local_num = 0;
    res->resol_num = 0;
    res->purify_num = 0;
    return res;
}

void printCoqProofTerm(ProofTerm* t, MaxTable* mt, FILE* fp){
    if (t == NULL){
        printf("error in printCoqProofTerm, null t\n");
        return;
    }
    switch (t->type)
    {
    case FUNC_EQ0:
    case FUNC_LE0:
    {   
        int flag = 0;
        for (int i = 1; i <= t->arg_num - 1; i++)
        {   
            if(i == mt->int8_max || i == mt->int16_max || i == mt->int32_max || i == mt->int64_max) continue;
            if(flag == 0) {
                fprintf(fp, "%d*x%d", t->args[i]->func_name.const_val, i);
                flag = 1;
            }
            fprintf(fp, "+%d*x%d", t->args[i]->func_name.const_val, i);
        }
        if (t->type == FUNC_EQ0)
            fprintf(fp, " = -%d ", t->args[0]->func_name.const_val);
        else if (t->type == FUNC_LE0)
            fprintf(fp, " <= -%d ", t->args[0]->func_name.const_val);
        if(mt->int8_max != -1){
           fprintf(fp, "-%d*127", t->args[mt->int8_max]->func_name.const_val);
        } 
        if(mt->int16_max != -1){
           fprintf(fp, "-%d*32767", t->args[mt->int16_max]->func_name.const_val);
        } 
        if(mt->int32_max != -1){
           fprintf(fp, "-%d*2147483647", t->args[mt->int32_max]->func_name.const_val);
        } 
        if(mt->int64_max != -1){
           fprintf(fp, "-%d*9223372036854775807", t->args[mt->int64_max]->func_name.const_val);
        } 
        break;
    }
    case VAR:
    {   
        if(t->func_name.node_number != mt->int8_max && t->func_name.node_number != mt->int16_max 
        && t->func_name.node_number != mt->int32_max && t->func_name.node_number != mt->int64_max){
            fprintf(fp, "x%d", t->func_name.node_number);
        }
        else if(t->func_name.node_number == mt->int8_max) fprintf(fp, "127");
        else if(t->func_name.node_number == mt->int16_max) fprintf(fp, "32767");
        else if(t->func_name.node_number == mt->int32_max) fprintf(fp, "2147483647");
        else if(t->func_name.node_number == mt->int64_max) fprintf(fp, "9223372036854775807");
        break;
    }
    case PROP_VAR:
    {
        fprintf(fp, "P%d", t->func_name.node_number);
        break;
    }
    case INT_CONST:
    {
        fprintf(fp, "%d", t->func_name.const_val);
        break;
    }
    case FUNC_AND:
    {
        fprintf(fp, "(");
        for (int i = 0; i < t->arg_num - 1; i++)
        {
            printCoqProofTerm(t->args[i], mt, fp);
            fprintf(fp, " /\\ ");
        }
        printCoqProofTerm(t->args[t->arg_num - 1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_OR:
    {
        fprintf(fp, "(");
        for (int i = 0; i < t->arg_num - 1; i++)
        {
            printCoqProofTerm(t->args[i], mt, fp);
            fprintf(fp, " \\/ ");
        }
        printCoqProofTerm(t->args[t->arg_num - 1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_IMPLY:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " -> ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_IFF:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " <-> ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_LE:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " <= ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_LT:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " < ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_GE:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " >= ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_GT:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " > ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_EQ:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " = ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_ADD:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " + ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_MINUS:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " - ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_MULT:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " * ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_DIV:
    {
        fprintf(fp, "(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, " / ");
        printCoqProofTerm(t->args[1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_NEG:
    {
        fprintf(fp, "( -");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_N:
    {
        fprintf(fp, "%s(", t->func_name.name);
        for (int i = 0; i < t->arg_num - 1; i++)
        {
            printCoqProofTerm(t->args[i], mt, fp);
            fprintf(fp, ",");
        }
        printCoqProofTerm(t->args[t->arg_num - 1], mt, fp);
        fprintf(fp, ")");
        break;
    }
    case FUNC_NOT:
    {
        fprintf(fp, "(~(");
        printCoqProofTerm(t->args[0], mt, fp);
        fprintf(fp,"))");
        break;
    }
    case PROP_FALSE:
    {
        printf("FALSE");
        break;
    }
    case PROP_TRUE:
    {
        printf("TRUE");
        break;
    }
    default:
        break;
    }
}

void printCoqProof(SMT_PROOF* proof, FILE* fp){
    PropTable* ptable = initPropTable();
    MaxTable* mt = (MaxTable*)malloc(sizeof(MaxTable));
    mt->int8_max = -1;
    mt->int16_max = -1;
    mt->int32_max = -1;
    mt->int64_max = -1;
    ptable->mt = mt;
    char* s1 = "SMT_INT8_MAX";
    char* s2 = "SMT_INT16_MAX";
    char* s3 = "SMT_INT32_MAX";
    char* s4 = "SMT_INT64_MAX";
    fprintf(fp, "Theorem smt_proof : \nforall ");
    for(int i = 1; i <= proof->declare_num; i++){
        ProofNode* node = proof->declare_table[i];
        if(node->arg_num == 1){
            enum VAR_COQ_TYPE type = var_type_search(node->args[0]->args.func_name, 1);
            if(type == COQ_Z_Z){
                fprintf(fp, "(%s: Z->Z) ", node->args[0]->args.func_name);
            }
        }
        else if(node->arg_num == 2){
            char* s5 = node->args[1]->args.func_name;
            if(strcmp(s1, s5) == 0) {
                mt->int8_max = node->args[0]->args.number;
                continue;
            }
            else if(strcmp(s2, s5) == 0) {
                mt->int16_max = node->args[0]->args.number;
                continue;
            }
            else if(strcmp(s3, s5) == 0) {
                mt->int32_max = node->args[0]->args.number;
                continue;
            }
            else if(strcmp(s4, s5) == 0) {
                mt->int64_max = node->args[0]->args.number;
                continue;
            }
            enum VAR_COQ_TYPE type = var_type_search(node->args[1]->args.func_name, 0);
            if(type == COQ_Z){
                fprintf(fp, "(x%d: Z) ", node->args[0]->args.number);
            }
        }
    }
    fprintf(fp, ",\n");
    printCoqProofTerm(proof->proof_table[proof->proof_num]->concl, mt, fp);
    fprintf(fp, ".\nProof.\nintros. unfold not. intros. \n");
    int step_id = 1;
    while(step_id <= proof->proof_num){
        step_id = printCoqProofStep(proof, ptable, fp, step_id);
    }
    // for(int i = 1; i<= proof->proof_num; i++){
    //     switch(proof->proof_table[i]->rule){
    //         case SUB_VAR:
    //         case SUB_PROP:
    //         case SUB_PROP_IFF:
    //         case CNF_TRANS:
    //         case AND_ELIM:{
    //             break;
    //         }
    //         case ASSUME:{
    //             break;
    //         }
    //         case SET_VAR:{
    //             fprintf(fp, "remember ");
    //             printCoqProofTerm(proof->proof_table[i]->args[0]->args.pterm->args[0], mt, fp);
    //             int vnum = proof->proof_table[i]->args[0]->args.pterm->args[1]->func_name.node_number;
    //             fprintf(fp, " as x%d eqn: Purify_x%d.\n", vnum, vnum);
    //             char* key = ProofTerm2str(proof->proof_table[i]->args[0]->args.pterm);
    //             int* hval = get_value_from_hstable(ptable->purify_table, key, strlen(key));
    //             if(hval == NULL){
    //                 hval = (int*)malloc(sizeof(int));
    //                 *hval = -1; 
    //                 add_node2HashTable(ptable->purify_table, key, strlen(key), hval);
    //                 free(key);
    //             }
    //             else{
    //                 printf("error in printCoqProof, set the same var twice: %s\n", key);
    //                 free(key);
    //             }
    //             break;
    //         }
    //         case SET_PROP:{
    //             fprintf(fp, "remember ");
    //             ProofTerm* pterm = proof->proof_table[i]->args[0]->args.pterm;
    //             printCoqProofTerm(pterm->args[0], mt, fp);
    //             fprintf(fp, " as P%d .\n", pterm->args[1]->func_name.node_number);
    //             if(pterm->args[0]->type == FUNC_EQ && pterm->args[0]->args[1]->type == VAR){
    //                 char* key = ProofTerm2str(pterm->args[0]);
    //                 int* hval = get_value_from_hstable(ptable->purify_table, key, strlen(key));
    //                 if(hval != NULL){
    //                     *hval = pterm->args[1]->func_name.node_number;
    //                     fprintf(fp, "assert(P%d).\n{ subst P%d. rewrite Purify_x%d. reflexivity. }\n", *hval, *hval, pterm->args[0]->args[1]->func_name.node_number);
    //                 }
    //                 free(key);
    //             }
    //             break;
    //         }
    //         case SET_PROP_IFF:{
    //             ProofTerm* pterm = proof->proof_table[i]->concl;
    //             int num = pterm->args[1]->func_name.node_number;
    //             if(pterm->args[0]->type == FUNC_NOT){
    //                 fprintf(fp, "fold (~P%d) in H.\n", pterm->args[0]->args[0]->func_name.node_number);
    //             }
    //             fprintf(fp, "remember ");
    //             printCoqProofTerm(pterm->args[0], mt, fp);
    //             fprintf(fp, " as P%d.\n", num);
    //             fprintf(fp, "assert(HPP%d: P%d <-> ", num, num);
    //             printCoqProofTerm(pterm->args[0], mt, fp);
    //             fprintf(fp, "). {\nsubst P%d.\nsplit.\n+ intro H1. exact H1.\n+ intro H2. exact H2.\n}\n", num);
    //             ProofTerm* lpterm = pterm->args[0];
    //             if(pterm->args[0]->type == FUNC_AND){
    //                 fprintf(fp, "pose proof cnf_trans_and2 _ _ _ HPP%d as HP%d.\ndestruct HP%d as [HP%d1 [HP%d2 HP%d3]].\n", num, num, num, num, num, num);
    //             }
    //             else if(pterm->args[0]->type == FUNC_OR){
    //                 fprintf(fp, "pose proof cnf_trans_or2 _ _ _ HPP%d as HP%d.\ndestruct HP%d as [HP%d1 [HP%d2 HP%d3]].\n", num, num, num, num, num, num);
    //             }
    //             else if(pterm->args[0]->type == FUNC_IMPLY){
    //                 fprintf(fp, "pose proof cnf_trans_imply2 _ _ _ HPP%d as HP%d.\ndestruct HP%d as [HP%d1 [HP%d2 HP%d3]].\n", num, num, num, num, num, num);
    //             }
    //             else if(pterm->args[0]->type == FUNC_NOT){
    //                 fprintf(fp, "pose proof cnf_trans_not2 _ _  HPP%d as HP%d.\ndestruct HP%d as [HP%d1 HP%d2].\n", num, num, num, num, num);
    //             }
    //             break;
    //         }
    //         default: {break;}
    //     }
    // }
}

int printCoqProofStep(SMT_PROOF* proof, PropTable* ptable, FILE* fp, int step_id){
    switch(proof->proof_table[step_id]->rule){
        case SUB_VAR:
        case CNF_TRANS:
        case ARITH_TRANS:
        case LIA_TRANS: {
            break;
        }
        case AND_ELIM:{
            int n1 = proof->proof_table[step_id]->args[0]->args.number; //第n1个clause
            ProofTerm* pterm = proof->proof_table[step_id]->concl;
            int n2 = 0;
            if(pterm->args[pterm->arg_num-1]->type == FUNC_NOT) n2 = pterm->args[pterm->arg_num-1]->args[0]->func_name.node_number;
            else n2 = pterm->args[pterm->arg_num-1]->func_name.node_number;
            char* hval = (char*)malloc(sizeof(char)*16);
            memset(hval, 0, sizeof(char)*16);
            sprintf(hval, "HP%d%d", n2, n1+1);
            updata_clause_table(ptable->clause_table, hval, step_id);
            break;
        }
        case SUB_PROP:{
            int* assign = (int*)malloc(sizeof(int)*(ptable->atom_num+1));
            memset(assign, 0, sizeof(int)*(ptable->atom_num+1));
            ptable->assign = assign;
            break;
        }
        case SUB_PROP_IFF:{
            char* hval = (char*)malloc(sizeof(char)*16);
            memset(hval, 0, sizeof(char)*16);
            sprintf(hval, "H");
            updata_clause_table(ptable->clause_table, hval, step_id);
            break;
        }
        case SYMM: 
        case TRANS: {
            ptable->local_num++;
            fprintf(fp, "assert(LP%d: ", ptable->local_num);
            printCoqProofTerm(proof->proof_table[step_id]->concl, ptable->mt, fp);
            fprintf(fp, ") by lia. \n");
            updata_local_table(proof->proof_table[step_id]->concl, ptable->local_table, ptable->local_num);
            break;
        }
        case EQUALITY_RESOLUTION:{
            if(ptable->env == GLOBAL_ENV){
                int num = proof->proof_table[step_id]->concl->func_name.node_number;
                char* hval = (char*)malloc(sizeof(char)*16);
                memset(hval, 0, sizeof(char)*16);
                sprintf(hval, "H_purify%d", num);
                updata_clause_table(ptable->clause_table, hval, step_id);   
            }
            break;
        }
        case ASSUME:{
            if(step_id != 1){
                if(ptable->env == GLOBAL_ENV){
                    ptable->env = THEORY_ENV;
                    ptable->local_table = creat_hash_table();
                    int i = step_id;
                    ProofNode* node = proof->proof_table[step_id];
                    while(node->rule == ASSUME){
                        if(node->concl->type == PROP_VAR){
                            int pid = node->concl->func_name.node_number;
                            if(pid > ptable->atom_num){
                                printf("error in printCoqProofStep, pid overflow\n");
                                exit(-1);
                            }
                            ptable->assign[pid] = 1;
                        }
                        else if(node->concl->type == FUNC_NOT){
                            int pid = node->concl->args[0]->func_name.node_number;
                            if(pid > ptable->atom_num){
                                printf("error in printCoqProofStep, pid overflow\n");
                                exit(-1);
                            }
                            ptable->assign[pid] = -1;
                        }
                        step_id += 2;
                        node = proof->proof_table[step_id];
                    }
                    ptable->new_cl_num++;
                    fprintf(fp, "assert(TP%d: (", ptable->new_cl_num);
                    for(int i = 1; i < ptable->atom_num; i++){
                        if(ptable->assign[i] == -1) fprintf(fp, "~");
                        fprintf(fp,"P%d /\\ ", i);
                    }
                    if(ptable->assign[ptable->atom_num] == -1) fprintf(fp, "~");
                    fprintf(fp, "P%d)->False). {\nintros H1.\ndestruct H1 as ", ptable->atom_num);
                    for(int i = 1; i < ptable->atom_num; i++) fprintf(fp, "[H%d ", i);
                    fprintf(fp, "H%d", ptable->atom_num);
                    for(int i = 1; i < ptable->atom_num; i++) fprintf(fp, "]");
                    fprintf(fp, ".\n");
                    for(int i = 1; i <= ptable->atom_num; i++){
                        fprintf(fp, "rewrite HeqP%d in H%d.\n", i, i);
                    }
                }
                if(ptable->env == THEORY_ENV){
                    while(proof->proof_table[step_id]->rule != ARITH_EQ_INTRO) step_id++;
                    ptable->local_num++;
                    fprintf(fp, "assert(LP%d: ", ptable->local_num);
                    printCoqProofTerm(proof->proof_table[step_id]->concl, ptable->mt, fp);
                    fprintf(fp, ") by lia. \n");
                    updata_local_table(proof->proof_table[step_id]->concl, ptable->local_table, ptable->local_num);
                    step_id++;
                }
                return step_id;
            }
            break;
        }
        case SCOPE: {
            if(ptable->env == THEORY_ENV){
                ptable->env = GLOBAL_ENV;
                hash_table_delete(ptable->local_table);
                ptable->local_num = 0;
            }
            break;
        }
        case NOT_AND: {
            fprintf(fp, "assert(RTP%d: ", ptable->new_cl_num);
            printCoqProofTerm(proof->proof_table[step_id]->concl, ptable->mt, fp);
            fprintf(fp, " ). {\n");
            for(int i = 1; i < ptable->atom_num; i++){
                fprintf(fp, "pose proof demogan (");
                if(ptable->assign[i] == -1) fprintf(fp, "~");
                fprintf(fp, "P%d) (", i);
                for(int j = i + 1; j < ptable->atom_num; j++){
                    if(ptable->assign[j] == -1) fprintf(fp, "~");
                    fprintf(fp, "P%d /\\", j);
                }
                if(ptable->assign[ptable->atom_num] == -1) fprintf(fp, "~");
                fprintf(fp, "P%d) as DP%d. rewrite DP%d in TP%d.\n", ptable->atom_num, i, i, ptable->new_cl_num);
                if(ptable->assign[i] == -1){
                    fprintf(fp, "pose proof NN_Elim P%d as NDP%d. rewrite NDP%d in TP%d.\n", i, i, i, ptable->new_cl_num);
                }
            }
            fprintf(fp, "exact TP%d.\n}\n", ptable->new_cl_num);
            char* hval = (char*)malloc(sizeof(char)*16);
            memset(hval, 0, sizeof(char)*16);
            sprintf(hval, "RTP%d", ptable->new_cl_num);
            updata_clause_table(ptable->clause_table, hval, step_id);
            break;
        }
        case SET_VAR:{
            fprintf(fp, "remember ");
            ProofTerm* pterm = proof->proof_table[step_id]->args[0]->args.pterm;
            printCoqProofTerm(pterm->args[0], ptable->mt, fp);
            int vnum = pterm->args[1]->func_name.node_number;
            fprintf(fp, " as x%d eqn: Purify_x%d.\n", vnum, vnum);
            char* key = ProofTerm2str(pterm);
            int* hval = get_value_from_hstable(ptable->purify_table, key, strlen(key));
            if(hval == NULL){
                hval = (int*)malloc(sizeof(int));
                *hval = -1; 
                add_node2HashTable(ptable->purify_table, key, strlen(key), hval);
                free(key);
            }
            else{
                printf("error in printCoqProof, set the same var twice: %s\n", key);
                free(key);
            }
            break;
        }
        case SET_PROP:{
            fprintf(fp, "remember ");
            ProofTerm* pterm = proof->proof_table[step_id]->args[0]->args.pterm;
            printCoqProofTerm(pterm->args[0], ptable->mt, fp);
            int num = pterm->args[1]->func_name.node_number;
            fprintf(fp, " as P%d eqn: HeqP%d.\n", num, num);
            if(pterm->args[0]->type == FUNC_EQ && pterm->args[0]->args[1]->type == VAR){
                char* key = ProofTerm2str(pterm->args[0]);
                int* hval = get_value_from_hstable(ptable->purify_table, key, strlen(key));
                if(hval != NULL){
                    ptable->resol_num++;
                    *hval = num;
                    fprintf(fp, "assert(H_purify%d: P%d).\n{ subst P%d. rewrite Purify_x%d. reflexivity. }\n", *hval, *hval, *hval, pterm->args[0]->args[1]->func_name.node_number);
                }
                free(key);
            }
            ptable->atom_num++;
            break;
        }
        case SET_PROP_IFF:{
            ProofTerm* pterm = proof->proof_table[step_id]->concl;
            int num = pterm->args[1]->func_name.node_number;
            if(pterm->args[0]->type == FUNC_NOT){
                fprintf(fp, "fold (~P%d) in H.\n", pterm->args[0]->args[0]->func_name.node_number);
            }
            fprintf(fp, "remember ");
            printCoqProofTerm(pterm->args[0], ptable->mt, fp);
            fprintf(fp, " as P%d.\n", num);
            fprintf(fp, "assert(HPP%d: P%d <-> ", num, num);
            printCoqProofTerm(pterm->args[0], ptable->mt, fp);
            fprintf(fp, "). {\nsubst P%d.\nsplit.\n+ intro H1. exact H1.\n+ intro H2. exact H2.\n}\n", num);
            ProofTerm* lpterm = pterm->args[0];
            if(pterm->args[0]->type == FUNC_AND){
                fprintf(fp, "pose proof cnf_trans_and2 _ _ _ HPP%d as HP%d.\ndestruct HP%d as [HP%d1 [HP%d2 HP%d3]].\n", num, num, num, num, num, num);
            }
            else if(pterm->args[0]->type == FUNC_OR){
                fprintf(fp, "pose proof cnf_trans_or2 _ _ _ HPP%d as HP%d.\ndestruct HP%d as [HP%d1 [HP%d2 HP%d3]].\n", num, num, num, num, num, num);
            }
            else if(pterm->args[0]->type == FUNC_IMPLY){
                fprintf(fp, "pose proof cnf_trans_imply2 _ _ _ HPP%d as HP%d.\ndestruct HP%d as [HP%d1 [HP%d2 HP%d3]].\n", num, num, num, num, num, num);
            }
            else if(pterm->args[0]->type == FUNC_NOT){
                fprintf(fp, "pose proof cnf_trans_not2 _ _  HPP%d as HP%d.\ndestruct HP%d as [HP%d1 HP%d2].\n", num, num, num, num, num);
            }
            break;
        }
        case CONG:{
            ProofNode* node = proof->proof_table[step_id];
            int nary = node->premise_num;
            ptable->local_num++;
            fprintf(fp, "assert(LP%d: ", ptable->local_num);
            printCoqProofTerm(node->concl, ptable->mt, fp);
            fprintf(fp, "). {\nassert (H_UF0: %s = %s) by reflexivity.\n", node->args[0]->args.func_name, node->args[0]->args.func_name);
            int* premise = (int*)malloc(sizeof(int)*(nary));
            memset(premise, 0, sizeof(int)*(nary));
            for(int i = 0; i < nary; i++){
                ProofTerm* pterm = proof->proof_table[node->premise_list[i]]->concl;
                fprintf(fp, "assert(H_P%d: ", i);
                printCoqProofTerm(pterm, ptable->mt, fp);
                fprintf(fp, ") by lia.\n");
                fprintf(fp, "pose proof uf_congurence2 _ _ _ _ _ _ H_P%d H_UF%d as H_UF%d.\n", i, i, i+1);
            }
            fprintf(fp, "exact H_UF%d.\n}\n", nary);
            updata_local_table(proof->proof_table[step_id]->concl, ptable->local_table, ptable->local_num);
            break;
        }
        case RESOLUTION:{
            int p1 = proof->proof_table[step_id]->premise_list[0];
            int p2 = proof->proof_table[step_id]->premise_list[1];
            int resol_var = proof->proof_table[step_id]->args[0]->args.number;
            char* h1 = search_clause_table(ptable->clause_table, p1);
            char* h2 = search_clause_table(ptable->clause_table, p2);
            if(h1 == NULL || h2 == NULL){
                printf("error in printCoqProofStep in case resolution, no premise\n");
                exit(-1);
            }
            ProofTerm* pterm1 = proof->proof_table[p1]->concl;
            ProofTerm* pterm2 = proof->proof_table[p2]->concl;
            fprintf(fp, "pose proof resol_");
            if(proof->proof_table[step_id]->concl->type == PROP_FALSE){
                if(resol_var > 0) fprintf(fp, "false1 _ _ %s %s as Hend.\napply Hend.\nQed.", h1, h2);
                else fprintf(fp, "false2 _ _ %s %s as Hend.\napply Hend.\nQed.", h1, h2);
            }
            else{
                ptable->resol_num++;
                if(resol_var > 0){
                    if(pterm2->args[0]->type == FUNC_NOT && pterm2->args[0]->args[0]->func_name.node_number == resol_var){
                        fprintf(fp,"pos1 _ _ %s %s as H_resol%d.\n", h1, h2, ptable->resol_num);
                    }
                    else fprintf(fp, "pos2 _ _ %s %s as H_resol%d.\n", h1, h2, ptable->resol_num);
                }
                else{
                    if(pterm2->args[0]->type == PROP_VAR && pterm2->args[0]->func_name.node_number == -resol_var){
                        fprintf(fp, "neg1 _ _ %s %s as H_resol%d.\n", h1, h2, ptable->resol_num);
                    }
                    else fprintf(fp, "neg2 _ _ %s %s as H_resol%d.\n", h1, h2, ptable->resol_num);
                }
                char* hval = (char*)malloc(sizeof(char)*16);
                memset(hval, 0, sizeof(char)*16);
                sprintf(hval, "H_resol%d", ptable->resol_num);
                updata_clause_table(ptable->clause_table, hval, step_id);
            }
            break;
        }
        case UF_CONTRA_FALSE:{
            fprintf(fp, "contradiction.\n}\n");
            break;
        }
        default: {break;}
    }
    return step_id+1;
}

void updata_local_table(ProofTerm* t, Hash_Table* table, int value){
    char* key = ProofTerm2str(t);
    int* hval = get_value_from_hstable(table, key, strlen(key));
    if(hval == NULL){
        hval = (int*)malloc(sizeof(int));
        *hval = value;
    }
    free(key);
}

void updata_clause_table(Hash_Table* table, char* hval, int step_id){
    char* key = (char*)malloc(sizeof(char)*16);
    memset(key, 0, sizeof(char)*16);
    sprintf(key,"@p%d", step_id);
    char* val = get_value_from_hstable(table, key, strlen(key));
    if(val == NULL){
        add_node2HashTable(table, key, strlen(key), hval);
    } else free(hval);
    free(key);
}

char* search_clause_table(Hash_Table* table, int step_id){
    char* key = (char*)malloc(sizeof(char)*16);
    memset(key, 0, sizeof(char)*16);
    sprintf(key,"@p%d", step_id);
    char* val = get_value_from_hstable(table, key, strlen(key));
    free(key);
    return val;
}