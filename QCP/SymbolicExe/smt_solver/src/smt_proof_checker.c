#include "smt_proof_checker.h"
// #define CHECK_INFO
//相等返回1，不等返回0
int ProofTerm_eqb(ProofTerm* t1, ProofTerm* t2){
    if(t1 == NULL || t2 == NULL){
        printf("error in ProofTerm_eqb, nullptr\n");
        exit(-1);
    }
    if(t1->type != t2->type || t1->arg_num != t2->arg_num) return 0;
    else{
        switch(t1->type){
            case PROP_VAR:
            case VAR:{
                if(t1->func_name.node_number == t2->func_name.node_number) return 1;
                else return 0;
            }
            case INT_CONST:{
                if(t1->func_name.const_val == t2->func_name.const_val) return 1;
                else return 0;
            }
            case FUNC_N:{
                if(strcmp(t1->func_name.name, t2->func_name.name)!= 0) return 0;
                //不需要break
            }
            default:{
                for(int i = 0; i < t1->arg_num; i++){
                    if(ProofTerm_eqb(t1->args[i], t2->args[i]) == 0) return 0;
                }
                return 1;
            }
  
        }
    }   
}

CheckData* initCheckData(){
    CheckData* cdata = (CheckData*)malloc(sizeof(CheckData));
    MaxVar* table = (MaxVar*)malloc(sizeof(MaxVar));
    table->int8_max = -1;
    table->int16_max = -1;
    table->int32_max = -1;
    table->int64_max = -1;
    cdata->max_table = table;
    cdata->max_plen = 20;
    cdata->prop_cnt = 0;
    cdata->v_table = creat_hash_table();
    cdata->p_list = (ProofTerm**)malloc(sizeof(ProofTerm*)*(cdata->max_plen+1));
    memset(cdata->p_list, 0, sizeof(ProofTerm*)*(cdata->max_plen+1));
    return cdata;
}

void updata_CheckData(CheckData* cdata){
    if(cdata->prop_cnt >= cdata->max_plen){
        int old_plen = cdata->max_plen;
        cdata->max_plen *= 2;
        ProofTerm **res = (ProofTerm**)realloc(cdata->p_list, sizeof(ProofTerm*)*(cdata->max_plen+1));
        if (res == NULL)
        {
            printf("memory is not enough\n");
            exit(-1);
        }
        memset((ProofTerm**)res + old_plen + 1, 0, sizeof(ProofTerm*) * (cdata->max_plen - old_plen));
        cdata->p_list = res;
    }
}

int* ProofTerm_trans_coef(ProofTerm* t, int n){
  //todo
  int* coef = (int*)malloc(sizeof(int)*(n+1));
  memset(coef, 0, sizeof(int)*(n+1));
  switch(t->type){
    case FUNC_ADD:
    case FUNC_MINUS:{
        int* left_coef = ProofTerm_trans_coef(t->args[0], n);
        int* right_coef = ProofTerm_trans_coef(t->args[1], n);
        if(t->type == FUNC_ADD){
            for(int i = 0; i <= n; i++){
                coef[i] = left_coef[i] + right_coef[i];
            }
        }
        else {
           for(int i = 0; i <= n; i++){
                coef[i] = left_coef[i] - right_coef[i];
            } 
        }
        free(left_coef);
        free(right_coef);
        break;
    }
    case FUNC_NEG:
    case INT_CONST:{
        coef[0] = t->func_name.const_val;
        break;
    }
    case VAR:{
        int num = t->func_name.node_number;
        if(num > n){
            printf("error in ProofTerm_trans_coef, unexpected var\n");
            exit(-1);
        }
        coef[num] = 1;
        break;
    }
  }
  return NULL;
}

ProofTerm* resubvar_prop(const ProofTerm* t, Hash_Table* vtable){
    ProofTerm* res = NULL;
    switch(t->type){
        case VAR:{
            int vid = t->func_name.node_number;
            char* s = (char*)malloc(sizeof(char)*16);
            memset(s, 0, sizeof(char)*16);
            sprintf(s, "v%d", vid);
            ProofTerm* t1 = get_value_from_hstable(vtable, s, strlen(s));
            free(s);
            if(t1 == NULL){
                printf("exist var without declare or define\n");
                return NULL;
            }
            if(t1->type == VAR) {
                res = copy_ProofTerm(t);
            }
            else{
                res = resubvar_prop(t1, vtable);
            }
            break;
        }
        case PROP_VAR:
        case INT_CONST:
        case PROP_FALSE:
        case PROP_TRUE:{
            res = copy_ProofTerm(t);
            break;
        }
        case FUNC_N:{
            res = (ProofTerm*)malloc(sizeof(ProofTerm));
            memset(res, 0, sizeof(ProofTerm));
            res->type = FUNC_N;
            res->arg_num = t->arg_num;
            res->func_name.name = (char*)malloc(sizeof(char)*(strlen(t->func_name.name)+1));
            memset(res->func_name.name, 0, sizeof(char)*(strlen(t->func_name.name)+1));
            strcpy(res->func_name.name, t->func_name.name);
            res->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*res->arg_num);
            memset(res->args, 0, sizeof(ProofTerm*)*res->arg_num);
            for(int i = 0; i < res->arg_num; i++){
                res->args[i] = resubvar_prop(t->args[i], vtable);
            }
            break;
        }
        default:{
            res = (ProofTerm*)malloc(sizeof(ProofTerm));
            memset(res, 0, sizeof(ProofTerm));
            res->type = t->type;
            res->arg_num = t->arg_num;
            res->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*res->arg_num);
            memset(res->args, 0, sizeof(ProofTerm*)*res->arg_num);
            for(int i = 0; i < res->arg_num; i++){
                res->args[i] = resubvar_prop(t->args[i], vtable);
            }
            break;
        }
    }
    return res;
}

ProofTerm* resub_prop(ProofTerm* t, ProofTerm** p_list){
    ProofTerm* res = NULL;
    switch(t->type){
        case PROP_VAR:{
            int pid = t->func_name.node_number;
            ProofTerm* p = p_list[pid];
            if(p == NULL){
                res = copy_ProofTerm(t);
            }
            else {
                res = resub_prop(p, p_list);
            }
            break;
        }
        case FUNC_AND:
        case FUNC_OR:
        case FUNC_IMPLY:
        case FUNC_IFF:
        case FUNC_NOT:{
            res = (ProofTerm*)malloc(sizeof(ProofTerm));
            memset(res, 0, sizeof(ProofTerm));
            res->type = t->type;
            res->arg_num = t->arg_num;
            res->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*res->arg_num);
            memset(res->args, 0, sizeof(ProofTerm*)*res->arg_num);
            for(int i = 0; i < res->arg_num; i++){
                res->args[i] = resub_prop(t->args[i], p_list);
            }
            break;
        }
        default:{
            res = copy_ProofTerm(t);
            break;
        }
    }
    return res;
}

//将OR连接的命题变为数组形式
int* ProofTerm2arr(ProofTerm* t, int n){
    int* res = (int*)malloc(sizeof(int)*(n+1));
    memset(res, 0, sizeof(int)*(n+1));
    //处理命题只有一个单命题的情况
    if(t->type == FUNC_NOT){
        int p = t->args[0]->func_name.node_number;
        res[p] = -1;
        return res;
    }
    else if(t->type == PROP_VAR){
        int p = t->func_name.node_number;
        res[p] = 1;
        return res;
    }
    //处理OR连接的情况
    for(int i = 0; i < t->arg_num; i++){
        if(t->args[i]->type == FUNC_NOT){
            int p = t->args[i]->args[0]->func_name.node_number;
            res[p] = -1;
        }
        else{
            int p = t->args[i]->func_name.node_number;
            res[p] = 1;
        }
    }
    return res;
}

ProofTerm* NegProofTerm(ProofTerm* t){
    ProofTerm* res = (ProofTerm*)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = FUNC_NOT;
    res->arg_num = 1;
    res->args = (ProofTerm**)malloc(sizeof(ProofTerm*));
    res->args[0] = t;
    return res;
}

int* LE0_ProofTerm2arr(ProofTerm* t){
    int n = t->arg_num;
    int* res = (int*)malloc(sizeof(int)*n);
    memset(res, 0, sizeof(int)*(n+1));
    for(int i = 0; i < n; i++){
        res[i] = t->args[i]->func_name.const_val;
    }
    return res;
}

//检查：node的premise_list中的命题编号是否小于当前命题，且是否可用
int basis_check(int node_number, int premise_num, int* plist, int* assum_list){
    for(int i = 0; i < premise_num; i++){
        int n = plist[i];
        if(n >= node_number || assum_list[n] == -1) return 0;
    }
    return 1;
}


int rule_DECLARE_CHECK(ProofNode* node, CheckData* cdata){
    if(node->arg_num == 1) return 1;
    if(node->arg_num != 2) return 0;
    if(node->args[0]->type != NUM || node->args[1]->type != N_FUNC) return 0;
    char* s1 = "SMT_INT8_MAX";
    char* s2 = "SMT_INT16_MAX";
    char* s3 = "SMT_INT32_MAX";
    char* s4 = "SMT_INT64_MAX";
    char* s5 = node->args[1]->args.func_name;
    if(strcmp(s1, s5) == 0) cdata->max_table->int8_max = node->args[0]->args.number;
    else if(strcmp(s2, s5) == 0) cdata->max_table->int16_max = node->args[0]->args.number;
    else if(strcmp(s3, s5) == 0) cdata->max_table->int32_max = node->args[0]->args.number;
    else if(strcmp(s4, s5) == 0) cdata->max_table->int64_max = node->args[0]->args.number;

    char* s = (char*)malloc(sizeof(char)*16);
    memset(s, 0, sizeof(char)*16);
    sprintf(s, "v%d", node->args[0]->args.number);
    ProofTerm* hval = get_value_from_hstable(cdata->v_table, s, strlen(s));
    if(hval == NULL){
        hval = (ProofTerm*)malloc(sizeof(ProofTerm));
        memset(hval, 0, sizeof(ProofTerm));
        hval->arg_num = 0;
        hval->type = VAR;
        hval->func_name.node_number = node->args[0]->args.number;
        //hval = newPropVarTerm(node->args[0]->args.number);
        add_node2HashTable(cdata->v_table, s, strlen(s), hval);
        free(s);
        return 1;
    }
    else{
        printf("v%d has been declared\n", node->args[0]->args.number);
        return 0;
    }
}

int rule_SCOPE_check(ProofNode* node, ProofNode** list, int* assum_list){
    int fn = node->premise_list[0];
    ProofTerm* t = list[fn]->concl;
    int min_assum = fn;
    if(t->type == PROP_FALSE ){
        ProofTerm* aterm = (ProofTerm*)malloc(sizeof(ProofTerm));
        memset(aterm, 0, sizeof(ProofTerm));
        if(node->arg_num > 1){
            aterm->type = FUNC_AND; 
            aterm->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*(node->arg_num));
            aterm->arg_num = node->arg_num;
            memset(aterm->args, 0, sizeof(ProofTerm*)*(node->arg_num));
            for(int i = 0; i < node->arg_num; i++){
                int num = node->args[i]->args.number;
                if(assum_list[num] != 1 || num >= fn) {
                    for(int j = 0; j < i; j++){
                        freeProofTerm(aterm->args[j]);
                    }
                    free(aterm->args);
                    free(aterm);
                    #ifdef CHECK_INFO
                    printf("error step: %d, non-exist assumption: %d\n", node->node_number, num);
                    #endif
                    return 0;
                }
                aterm->args[i] = copy_ProofTerm(list[num]->concl);
                if(num < min_assum) min_assum = num;
            }
        }
        else {
            int num = node->args[0]->args.number;
            aterm = copy_ProofTerm(list[num]->concl);
        }
        ProofTerm* concl = (ProofTerm*)malloc(sizeof(ProofTerm));
        memset(concl, 0, sizeof(ProofTerm));
        concl->type = FUNC_NOT;
        concl->arg_num = 1;
        concl->args = (ProofTerm**)malloc(sizeof(ProofTerm*));
        concl->args[0] =  aterm;
        if(ProofTerm_eqb(concl, node->concl)){
            for(int i = min_assum; i <= fn; i++){
                //关闭assumption作用域
                assum_list[i] = -1;
            }
            freeProofTerm(concl);
            return 1;
        }
        else {
            freeProofTerm(concl);
            return 0;
        }
    }
    else return 0;
}

int rule_SET_VAR_check(ProofNode* node, CheckData* cdata){
    if(node->premise_num != 0 || node->arg_num != 1 || node->args[0]->type != PTERM) return 0;
    ProofTerm* t = node->args[0]->args.pterm;
    if(t->type != FUNC_EQ || t->arg_num != 2 || t->args[1]-> type != VAR) return 0;
    ProofTerm* v1 = t->args[1];
    int num = v1->func_name.node_number;
    char* s = (char*)malloc(sizeof(char)*16);
    memset(s, 0, sizeof(char)*16);
    sprintf(s, "v%d", num);
    ProofTerm* hval = get_value_from_hstable(cdata->v_table, s, strlen(s));
    if(hval != NULL) {
        printf("v%d has been existed\n", num);
        free(s);
        return 0;
    }
    else if(ProofTerm_eqb(t, node->concl)){
        hval = copy_ProofTerm(t->args[0]);  //表示该变量已经出现
        add_node2HashTable(cdata->v_table, s, strlen(s), hval);
        free(s);
        return 1;
    }
    return 0;
}

//SET_PROP && SET_PROP_IFF
int rule_SET_PROP_check(ProofNode* node, CheckData* cdata){
    if(node->premise_num != 0 || node->arg_num != 1 || node->args[0]->type != PTERM) return 0;
    ProofTerm* t = node->args[0]->args.pterm;
    if( (t->type != FUNC_EQ && t->type != FUNC_IFF) || t->arg_num != 2 || t->args[1]->type != PROP_VAR) return 0;
    ProofTerm* v1 = t->args[1];
    int num = v1->func_name.node_number;
    if(cdata->p_list[num] != NULL) return 0;
    if(ProofTerm_eqb(t, node->concl)){
        cdata->p_list[num] = copy_ProofTerm(t->args[0]);  //表示该变量已经自由出现
        cdata->prop_cnt++;
        updata_CheckData(cdata);
        return 1;
    }
    return 0;
}

int rule_SUB_VAR_check(ProofNode* node, ProofNode** list, CheckData* cdata){
    if(node->premise_num != 1 || node->arg_num != 0 ) return 0;
    ProofTerm* t = list[node->premise_list[0]]->concl;
    ProofTerm* res = resubvar_prop(node->concl, cdata->v_table);
    if(res == NULL) return 0;
    if(ProofTerm_eqb(res, t)){
        freeProofTerm(res);
        return 1;
    }
    // printf("the concl:\n");
    // printProofTerm(t);
    // printf("\nactually should be:\n");
    // printProofTerm(res);
    // printf("\n");
    freeProofTerm(res);
    return 0;
}

// SUB_PROP && SUB_PROP_IFF
int rule_SUB_PROP_check(ProofNode* node, ProofNode** list, CheckData* cdata){
    if(node->premise_num != 1 || node->arg_num != 0 ) return 0;
    ProofTerm* t = list[node->premise_list[0]]->concl;
    ProofTerm* res = resub_prop(node->concl, cdata->p_list);
    t = resub_prop(t, cdata->p_list);
    if(ProofTerm_eqb(res, t)){
        freeProofTerm(t);
        freeProofTerm(res);
        return 1;
    }
    freeProofTerm(t);
    freeProofTerm(res);
    return 0;
}



int rule_CNF_TRANS_check(ProofNode* node, ProofNode** list){
    ProofTerm* t = list[node->premise_list[0]]->concl;
    if(t->type != FUNC_IFF || t->args[1]->type != PROP_VAR) {
        printf("t->type:%d\n t->args[0]->type:%d\n", t->type, t->args[0]->type);
        printProofTerm(t);
        printf("\n");
        return 0;
    }
    int p3 = t->args[1]->func_name.node_number;
    switch(t->args[0]->type){
        case FUNC_AND:{
            int p1 = t->args[0]->args[0]->func_name.node_number;
            int p2 = t->args[0]->args[1]->func_name.node_number;
            ProofTerm *t1 = newOrProp(p1, -p3, 0, 2);
            ProofTerm *t2 = newOrProp(p2, -p3, 0, 2);
            ProofTerm *t3 = NULL;
            if(p1 != p2){
                t3 = newOrProp(-p1, -p2, p3, 3);
            }
            else {
                t3 = newOrProp(-p1, p3, 0, 2);
            }
            ProofTerm *cnfp = newAndProp(t1, t2, t3, NULL, 3);
            if(ProofTerm_eqb(cnfp, node->concl)){
                freeProofTerm(cnfp);
                return 1;
            }
            else{
                freeProofTerm(cnfp);
                return 0;
            }
            break;
        }
        case FUNC_OR:{
            int p1 = t->args[0]->args[0]->func_name.node_number;
            int p2 = t->args[0]->args[1]->func_name.node_number;
            ProofTerm *t1 = newOrProp(-p1, p3, 0, 2);
            ProofTerm *t2 = newOrProp(-p2, p3, 0, 2);
            ProofTerm *t3 = NULL;
            if(p1 != p2){
                t3 = newOrProp(p1, p2, -p3, 3);
            }
            else {
                t3 = newOrProp(p1, -p3, 0, 2);
            }
            ProofTerm *cnfp = newAndProp(t1, t2, t3, NULL, 3);
            if(ProofTerm_eqb(cnfp, node->concl)){
                freeProofTerm(cnfp);
                return 1;
            }
            else{
                freeProofTerm(cnfp);
                return 0;
            }
            break;
        }
        case FUNC_IMPLY:{
            int p1 = t->args[0]->args[0]->func_name.node_number;
            int p2 = t->args[0]->args[1]->func_name.node_number;
            ProofTerm* cnfp = NULL;
            if(p1 != p2){
                ProofTerm *t1 = newOrProp(p1, p3, 0, 2);
                ProofTerm *t2 = newOrProp(-p2, p3, 0, 2);
                ProofTerm *t3 = newOrProp(-p1, p2, -p3, 3);
                cnfp = newAndProp(t1, t2, t3, NULL, 3);
            }
            else{
                cnfp = newNotProp(p3);
            }
            if(ProofTerm_eqb(cnfp, node->concl)){
                freeProofTerm(cnfp);
                return 1;
            }
            else{
                freeProofTerm(cnfp);
                return 0;
            }
            break;
        }
        case FUNC_IFF:{
            int p1 = t->args[0]->args[0]->func_name.node_number;
            int p2 = t->args[0]->args[1]->func_name.node_number;
            ProofTerm* cnfp = NULL;
            if(p1 != p2){
                ProofTerm *t1 = newOrProp(p1, p2, p3, 3);
                ProofTerm *t2 = newOrProp(-p1, -p2, p3, 3);
                ProofTerm *t3 = newOrProp(p1, -p2, -p3, 3);
                ProofTerm *t4 = newOrProp(-p1, p2, -p3, 3);
                cnfp = newAndProp(t1, t2, t3, t4, 4);
            }
            else{
                cnfp = newNotProp(p3);
            }
            if(ProofTerm_eqb(cnfp, node->concl)){
                freeProofTerm(cnfp);
                return 1;
            }
            else{
                freeProofTerm(cnfp);
                return 0;
            }
            break;
        }
        case FUNC_NOT:{
            int p2 = t->args[0]->args[0]->func_name.node_number;
            ProofTerm *t1 = newOrProp(p2, p3, 0, 2);
            ProofTerm *t2 = newOrProp(-p2, -p3, 0, 2);
            ProofTerm *cnfp = newAndProp(t1, t2, NULL, NULL, 2); 
            if(ProofTerm_eqb(cnfp, node->concl)){
                freeProofTerm(cnfp);
                return 1;
            }
            else{
                freeProofTerm(cnfp);
                return 0;
            }
            break;   
        }
        default:{
            #ifdef CHECK_INFO
            printf("error logic symbol: %d\n", t->args[1]->type);
            #endif
            return 0;
        }
    }
}

int rule_EQUALITY_RESOLUTION_check(ProofNode* node, ProofNode** list){
    ProofTerm* p = list[node->premise_list[0]]->concl;
    ProofTerm* rp = list[node->premise_list[1]]->concl;
    if(rp->type != FUNC_EQ){
        printf("error in rule_EQUALITY_RESOLUTION_check, right prop type is not func_eq : %d\n", rp->type);
        return 0;
    }
    ProofTerm* p1 = rp->args[0];
    ProofTerm* p2 = rp->args[1];
    if((ProofTerm_eqb(p, p1)&&ProofTerm_eqb(p2, node->concl)) || (ProofTerm_eqb(p, p2)&&ProofTerm_eqb(p1, node->concl))) return 1;
    else return 0;
}

int rule_RESOLUTION_check(ProofNode* node, ProofNode** list){
    int maxp = node->args[0]->args.number;
    ProofTerm* t1 = list[node->premise_list[0]]->concl;
    ProofTerm* t2 = list[node->premise_list[1]]->concl;
    if(node->concl->type == PROP_FALSE){
        if(maxp > 0){
            if(t1->type != PROP_VAR || t1->func_name.node_number != maxp) return 0;
            if(t2->type != FUNC_NOT || t2->args[0]->func_name.node_number != maxp) return 0;
            return 1;
        }
        else{
            if(t2->type != PROP_VAR || t2->func_name.node_number != -maxp) return 0;
            if(t1->type != FUNC_NOT || t1->args[0]->func_name.node_number != -maxp) return 0;
            return 1;
        }
    }
    else{
        if(maxp < 0) maxp = -maxp;
        int resol_var = maxp;
        ProofTerm* concl = node->concl;
        ProofTerm* p = NULL;
        if(concl->type == PROP_VAR){
            p = concl;
        }
        else p = concl->args[concl->arg_num-1];
        if(p->type == PROP_VAR) maxp = (maxp > p->func_name.node_number) ? maxp : p->func_name.node_number;
        else maxp = (maxp > p->args[0]->func_name.node_number) ? maxp : p->args[0]->func_name.node_number;
        int* arr1 = ProofTerm2arr(t1, maxp);
        int* arr2 = ProofTerm2arr(t2, maxp);
        int* res = (int*)malloc(sizeof(int)*(maxp+1));
        // printf("maxp:%d\nt1:", maxp);
        // printProofTerm(t1);
        // printf("\nt2: ");
        // printProofTerm(t2);
        // printf("\n");
        // printf("arr1[maxp]:%d, arr2[maxp]:%d\n", arr1[maxp], arr2[maxp]);
        memset(res, 0, sizeof(int)*(maxp+1));
        for(int i = 1; i <= maxp; i++){
            if((arr1[i] == -1 && arr2[i] == 1) || (arr1[i] == 1 && arr2[i] == -1)){
                res[i] = 0;
                if(i != resol_var){
                    free(arr1);
                    free(arr2);
                    free(res);
                    #ifdef CHECK_INFO
                    printf("more than one resol var\n");
                    #endif
                    return 0;
                }
            }
            else{
                if(arr1[i] != 0) res[i] = arr1[i];
                else if(arr2[i] != 0) res[i] = arr2[i];
            }
        }
        free(arr1);
        free(arr2);
        int* arr3 = ProofTerm2arr(concl, maxp);
        for(int i = 1; i <= maxp; i++){
            if(res[i] != arr3[i]) {
                free(arr3);
                free(res);
                return 0;
            }
        }
        free(arr3);
        free(res);
        return 1;
    }
}

int rule_AND_ELIM_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 1 || node->arg_num != 1) return 0;
    ProofTerm* p = list[node->premise_list[0]]->concl;
    int num = node->args[0]->args.number;
    if(p->type != FUNC_AND || p->arg_num < num) return 0;
    int ans =  ProofTerm_eqb(p->args[num], node->concl);
    return ans;
}

int rule_NOT_ELIM_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 1 || node->arg_num != 0) return 0;
    ProofTerm* p1 = list[node->premise_list[0]]->concl;
    if(p1->type != FUNC_NOT || p1->args[0]->type != FUNC_NOT) return 0;
    ProofTerm* p2 = p1->args[0]->args[0];
    return ProofTerm_eqb(p2, node->concl);
}

int rule_NOT_AND_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 1 || node->arg_num != 0) return 0;
    ProofTerm* p1 = list[node->premise_list[0]]->concl;
    if(p1->type != FUNC_NOT || p1->arg_num != 1) return 0;
    ProofTerm* p2 = p1->args[0];
    if(p2->type == FUNC_NOT) {
        return ProofTerm_eqb(p2->args[0],node->concl);
    }
    else if(p2->type != FUNC_AND) return 0;
    ProofTerm* concl = (ProofTerm*)malloc(sizeof(ProofTerm));
    memset(concl, 0, sizeof(ProofTerm));
    concl->type = FUNC_OR;
    concl->arg_num = p2->arg_num;
    concl->args = (ProofTerm**)malloc(sizeof(ProofTerm*)*(concl->arg_num));
    memset(concl->args, 0, sizeof(ProofTerm*)*(concl->arg_num));
    for(int i = 0; i < concl->arg_num; i++){
        if(p2->args[i]->type == FUNC_NOT){
            concl->args[i] = copy_ProofTerm(p2->args[i]->args[0]);
        }
        else{
            concl->args[i] = NegProofTerm(copy_ProofTerm(p2->args[i]));
        }
    }
    if(ProofTerm_eqb(concl, node->concl)){
        freeProofTerm(concl);
        return 1;
    }
    else {
        freeProofTerm(concl);
        return 0;
    }
}

int rule_REFL_check(ProofNode* node){
    if(node->premise_num != 0 || node->arg_num != 1) return 0;
    ProofTerm* t = node->args[0]->args.pterm;
    if(node->concl->type != FUNC_EQ || node->concl->arg_num != 2) return 0;
    return (ProofTerm_eqb(t, node->concl->args[0]) && ProofTerm_eqb(t, node->concl->args[1]));
}

int rule_SYMM_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 1 || node->arg_num != 0) return 0;
    ProofTerm* t = list[node->premise_list[0]]->concl;
    if(t->type != FUNC_EQ || t->arg_num != 2 || node->concl->type != FUNC_EQ || node->concl->arg_num != 2) return 0;
    return (ProofTerm_eqb(t->args[0], node->concl->args[1]) && ProofTerm_eqb(t->args[1], node->concl->args[0]));
}

int rule_TRANS_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 2 || node->arg_num != 0) return 0;
    ProofTerm* t1 = list[node->premise_list[0]]->concl;
    ProofTerm* t2 = list[node->premise_list[1]]->concl;
    if(node->concl->type != FUNC_EQ || node->concl->arg_num != 2) return 0;
    if(t1->type != FUNC_EQ || t1->arg_num != 2 || t2->type != FUNC_EQ || t2->arg_num != 2) return 0;
    return (ProofTerm_eqb(t1->args[1], t2->args[0]) && ProofTerm_eqb(t1->args[0], node->concl->args[0]) && ProofTerm_eqb(t2->args[1], node->concl->args[1]));
}

int rule_CONG_check(ProofNode* node, ProofNode** list){
    if(node->arg_num != 1 || node->args[0]->type != N_FUNC) return 0;
    char* f = node->args[0]->args.func_name;
    int n = node->premise_num;
    if(node->concl->type != FUNC_EQ || node->concl->arg_num != 2) return 0;
    ProofTerm* p1 = node->concl->args[0];
    ProofTerm* p2 = node->concl->args[1];
    if(p1->type != FUNC_N || p2->type != FUNC_N || p1->arg_num != n || p2->arg_num != n) return 0;
    if(strcmp(p1->func_name.name, p2->func_name.name) != 0) return 0;
    for(int i = 0; i < n; i++){
        ProofTerm* t = list[node->premise_list[i]]->concl;
        ProofTerm* t1 = p1->args[i];
        ProofTerm* t2 = p2->args[i];
        if(t->type != FUNC_EQ || t->arg_num != 2) return 0;
        if((!ProofTerm_eqb(t->args[0], t1))||(!ProofTerm_eqb(t->args[1], t2))) return 0;
    }
    return 1;
}

int rule_FUNC_REWRITE_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 2 || node->arg_num != 0) return 0;
    ProofTerm* t1 = list[node->premise_list[0]]->concl;
    ProofTerm* t2 = list[node->premise_list[1]]->concl;
    if(t1->type != node->concl->type) return 0;
    if(t2->type != FUNC_EQ || t2->arg_num != 2) return 0;
    if(ProofTerm_eqb(t1->args[0], t2->args[1]) && ProofTerm_eqb(node->concl->args[0], t2->args[0])) return 1;
    else if(ProofTerm_eqb(t1->args[0], t2->args[0]) && ProofTerm_eqb(node->concl->args[0], t2->args[1])) return 1;
    return 0;
}

int rule_ARITH_FME_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 2 || node->arg_num != 1 || node->args[0]->type != NUM) return 0;
    ProofTerm* t1 = list[node->premise_list[0]]->concl;
    ProofTerm* t2 = list[node->premise_list[1]]->concl;
    if(t1->type != FUNC_LE0 || t2->type != FUNC_LE0 || t1->arg_num != t2->arg_num) return 0;
    int n = t1->arg_num - 1;
    int elim_v = node->args[0]->args.number;
    int* r1 = LE0_ProofTerm2arr(t1);
    int* r2 = LE0_ProofTerm2arr(t2);
    int* res = generate_new_constraint(r1, r2, n, elim_v);
    free(r1);
    free(r2);
    if(node->concl->type != FUNC_LE0 || node->concl->arg_num != n+1) return 0;
    for(int i = 0; i <= n; i++){
        if(res[i] != node->concl->args[i]->func_name.const_val){
            free(res);
            return 0;
        }
    }
    free(res);
    return 1;
}

int rule_ARITH_EQ_ELIM_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 2 || node->arg_num != 1) return 0;
    ProofTerm* t1 = list[node->premise_list[0]]->concl;
    ProofTerm* t2 = list[node->premise_list[1]]->concl;
    if(t1->type != FUNC_EQ0 || t1->arg_num != t2->arg_num 
        || (t2->type != FUNC_LE0 && t2->type!= FUNC_EQ0)) return 0;
    int n = t1->arg_num - 1;
    int elim_v = node->args[0]->args.number;
    int* r1 = LE0_ProofTerm2arr(t1);
    int* r2 = LE0_ProofTerm2arr(t2);
    int* res = equ_eliminate(r1, r2, elim_v, n);
    free(r1);
    free(r2);
    if(node->concl->type != t2->type || node->concl->arg_num != n+1) return 0;
    for(int i = 0; i <= n; i++){
        if(res[i] != node->concl->args[i]->func_name.const_val){
            free(res);
            return 0;
        }
    }
    free(res);
    return 1;
}

int rule_ARITH_FALSE_check(ProofNode* node, ProofNode** list, CheckData* cdata){
    if(node->premise_num != 1 || node->arg_num != 0) return 0;
    ProofTerm* t1 = list[node->premise_list[0]]->concl;
    if(t1->type != FUNC_EQ0 && t1->type != FUNC_LE0) return 0;
    int n = t1->arg_num;
    int* coef = LE0_ProofTerm2arr(t1);
    bool flag = equation_true(coef, n-1, t1->type, cdata->max_table);
    free(coef);
    if(flag) return 0;
    else return 1;

}
int rule_ARITH_NOT_ELIM_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 1 || node->arg_num != 0) return 0;
    ProofTerm* t1 = list[node->premise_list[0]]->concl;
    if(t1->type != FUNC_NOT || t1->arg_num != 1 || t1->args[0]->type != FUNC_LE0) return 0;
    ProofTerm* t2 = t1->args[0];
    if(node->concl->type != FUNC_LE0 || node->concl->arg_num != t2->arg_num) return 0;
    for(int i = 1; i < t2->arg_num; i++){
        if(t2->args[i]->func_name.const_val != - node->concl->args[i]->func_name.const_val) return 0;
    }
    if(-(t2->args[0]->func_name.const_val) + 1 != node->concl->args[0]->func_name.const_val) return 0;
    else return 1;
}

int rule_ARITH_EQ_INTRO_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 2 || node->arg_num != 2) return 0;
    ProofTerm* t1 = list[node->premise_list[0]]->concl;
    ProofTerm* t2 = list[node->premise_list[1]]->concl;
    if(t1->type != FUNC_LE0 || t1->arg_num != t2->arg_num 
        || t2->type != FUNC_LE0 ) return 0;
    if(node->args[0]->type != NUM || node->args[1]->type != NUM) return 0;
    int a = node->args[0]->args.number;
    int b = node->args[0]->args.number;
    if(node->concl->type != FUNC_EQ || node->concl->arg_num != 2) return 0;
    if(node->args[0]->args.number != a || node->args[1]->args.number != b) return 0;
    for(int i = 0; i < t1->arg_num; i++){
        if(i == a){
            if(t1->args[i]->func_name.const_val != 1 || t2->args[i]->func_name.const_val != -1) return 0;
        }
        else if(i == b) {
            if(t1->args[i]->func_name.const_val != -1 || t2->args[i]->func_name.const_val != 1) return 0;
        }
        else {
            if(t1->args[i]->func_name.const_val != 0 || t2->args[i]->func_name.const_val != 0) return 0; 
        }
    }
    return 1;
}

int rule_ARITH_TRANS_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 1 || node->arg_num != 0) return 0;
    ProofTerm* t = list[node->premise_list[0]]->concl;
    if(t->type != FUNC_EQ || t->arg_num != 2) return 0;
    int a = t->args[0]->func_name.node_number;
    int b = t->args[1]->func_name.node_number;
    if(node->concl->type != FUNC_EQ0 || node->concl->arg_num <= a || node->concl->arg_num <= b) return 0;
    if(node->concl->args[a]->func_name.const_val != - node->concl->args[b]->func_name.const_val) return 0;
    for(int i = 0; i < node->concl->arg_num; i++){
        if(i == a || i == b || node->concl->args[i]->func_name.const_val == 0) continue;
        else return 0;
    }
    return 1;
}

int rule_LIA_TRANS_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 1 || node->arg_num != 0) return 0;
}

int rule_UF_CONTRA_FALSE_check(ProofNode* node, ProofNode** list){
    if(node->premise_num != 2 || node->arg_num != 0) return 0;
    ProofTerm* t1 = list[node->premise_list[0]]->concl;
    ProofTerm* t2 = list[node->premise_list[1]]->concl;
    if(t2->type != FUNC_NOT || t2->arg_num != 1 || node->concl->type != PROP_FALSE) return 0;
    return ProofTerm_eqb(t1, t2->args[0]);
}


int proof_check(ProofNode** dlist, int dn, ProofNode** list, int n){
    int* assum_list = (int*)malloc(sizeof(int)*(n+1));
    memset(assum_list, 0, sizeof(int)*(n+1));
    CheckData* cdata = initCheckData();
    for(int i = 1; i <= dn; i++){
        ProofNode* node = dlist[i];
        if(node->rule != DECLARE) return 0;
        if(!rule_DECLARE_CHECK(node, cdata)) return 0;
    }
    for(int i = 1; i <= n; i++){
        ProofNode* node = list[i];
        #ifdef CHECK_INFO
        printf("    check step%d\n    step rule:%d\n", i, node->rule);
        #endif
        if(!basis_check(node->node_number, node->premise_num, node->premise_list, assum_list)) {
            printf("basis check false\n");
            return 0;
        }
        switch (node->rule){
            case ASSUME:{
                assum_list[i] = 1;
                if(!ProofTerm_eqb(node->args[0]->args.pterm, node->concl)) return 0;
                break;
            }
            case SCOPE:{
                if(!rule_SCOPE_check(node, list, assum_list)) return 0;
                break;
            }
            case SET_VAR:{
                if(!rule_SET_VAR_check(node, cdata)) return 0;
                break;
            }
            case SET_PROP:
            case SET_PROP_IFF:{
                if(!rule_SET_PROP_check(node, cdata)) return 0;
                break;
            }
            case SUB_VAR:{
                if(!rule_SUB_VAR_check(node, list, cdata)) return 0;
                break;
            }
            case SUB_PROP:
            case SUB_PROP_IFF:{
                if(!rule_SUB_PROP_check(node, list, cdata)) return 0;
                break;
            }
            case CNF_TRANS:{
                if(!rule_CNF_TRANS_check(node, list)) return 0;
                break;
            }
            case EQUALITY_RESOLUTION:{
                if(!rule_EQUALITY_RESOLUTION_check(node, list)) return 0;
                break;
            }
            case RESOLUTION:{
                if(!rule_RESOLUTION_check(node, list)) return 0;
                break;
            }
            case AND_ELIM:{
                if(!rule_AND_ELIM_check(node, list)) return 0;
                break;
            }
            case NOT_ELIM:{
                if(!rule_NOT_ELIM_check(node, list)) return 0;
                break;
            }
            case NOT_AND:{
                if(!rule_NOT_AND_check(node, list)) return 0;
                break;
            }
            case REFL:{
                if(!rule_REFL_check(node)) return 0;
                break;
            }
            case SYMM:{
                if(!rule_SYMM_check(node, list)) return 0;
                break;
            }
            case TRANS:{
                if(!rule_TRANS_check(node, list)) return 0;
                break;
            }
            case CONG:{
                if(!rule_CONG_check(node, list)) return 0;
                break;
            }
            case FUNC_REWRITE:{
                if(!rule_FUNC_REWRITE_check(node, list)) return 0;
                break;
            }
            case ARITH_FME:{
                if(!rule_ARITH_FME_check(node, list)) return 0;
                break;
            }
            case ARITH_EQ_ELIM:{
                if(!rule_ARITH_EQ_ELIM_check(node, list)) return 0;
                break;
            }
            case ARITH_FALSE:{
                if(!rule_ARITH_FALSE_check(node, list, cdata)) return 0;
                break;
            }
            case ARITH_NOT_ELIM:{
                if(!rule_ARITH_NOT_ELIM_check(node, list)) return 0;
                break;
            }
            case ARITH_EQ_INTRO:{
                if(!rule_ARITH_EQ_INTRO_check(node, list)) return 0;
                break;
            }
            case ARITH_TRANS:{
                if(!rule_ARITH_TRANS_check(node, list)) return 0;
                break;
            }
            case LIA_TRANS:{
                break;
            }
            case UF_CONTRA_FALSE:{
                if(!rule_UF_CONTRA_FALSE_check(node, list)) return 0;
                break;
            }
            default:
                break;
        }
    }
    return 1;
}

// 0表示check结果为false或者proof不存在， 1表示true
int smt_proof_check(SMT_PROOF* proof){
    if(proof->ans == 1) return 0;
    return proof_check(proof->declare_table, proof->declare_num, proof->proof_table, proof->proof_num);
}

int smt_proof_check_low(ProofTerm* goal, SMT_PROOF* proof){
    if(proof->ans == 1) return 0;
    ProofTerm* concl = proof->proof_table[proof->proof_num]->concl;
    if(!ProofTerm_eqb(concl, goal)) return 0;
    return smt_proof_check(proof);
}




