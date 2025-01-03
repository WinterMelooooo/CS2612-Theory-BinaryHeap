#include"smt_solver.h"
// #define SMT_SOLVER_DEBUG 1
sat_data* sat_data_copy(sat_data* s){
    sat_data* res = (sat_data*)malloc(sizeof(sat_data));
    memset(res, 0, sizeof(sat_data));
    res->v_size = s->v_size;
    res->cl_size = s->cl_size;
    res->cl_maxsize = s->cl_maxsize;
    res->cur_dl = 0;
    int n = s->v_size;
    res->v_data = (var_data*)malloc(sizeof(var_data));
    res->v_data->value = (int*)malloc(n*sizeof(int));
    res->v_data->dl = (int*)malloc(n*sizeof(int));
    res->v_data->ancient = (int*)malloc(n*sizeof(int));
    memset(res->v_data->value, -1, sizeof(int)*n);
    memset(res->v_data->dl, -1, sizeof(int)*n);
    memset(res->v_data->ancient, -1, sizeof(int)*n);
    res->cl_data = (clause_data*)malloc(sizeof(clause_data));
    res->cl_data->state = (int*)malloc(sizeof(int)*res->cl_maxsize);
    memset(res->cl_data->state, 0, sizeof(int)*res->cl_maxsize);
    res->cl_data->lit_state = (int*)malloc(sizeof(int)*res->cl_maxsize);
    memset(res->cl_data->lit_state, 0, sizeof(int)*res->cl_maxsize);
    res->cl_data->unassign_num = (int*)malloc(sizeof(int)*res->cl_maxsize);
    memset(res->cl_data->unassign_num, 0, sizeof(int)*res->cl_maxsize);
    res->cl_data->value = (int**)malloc(sizeof(int*)*res->cl_maxsize);
    memset(res->cl_data->value, 0, sizeof(int*)*res->cl_maxsize);
    for(int i = 0; i < res->cl_size; i++){
        res->cl_data->value[i] = (int*)malloc(sizeof(int)*n);
        memset(res->cl_data->value[i], 0, sizeof(int)*n);
        for(int j = 0; j < n; j++) res->cl_data->value[i][j] = s->cl_data->value[i][j];
    }
    for(int i = 0; i < res->cl_size; i++){
        res->cl_data->state[i] = s->cl_data->state[i];
        res->cl_data->unassign_num[i] = s->cl_data->unassign_num[i];
    }
    return res;
}

int* clause_copy(int* cl, int n){
    int* res = (int*)malloc(sizeof(int)*n);
    memset(res, 0, sizeof(int)*n);
    for(int i = 0; i < n; i++)
        res[i] = cl[i];
    return res;
}

//0:unsat, 1:sat, -1: 永真
int smt_solver(SmtProp* p){
    SmtProp* p1 = prop_simplify(p);
    if(p1->type == SMTTF_PROP){
        bool ans = p1->prop.TF;
        freeSmtProp(p1);
        if(ans) return -1;
        else return 0;
    }
    
    SmtProp* p2 = copy_SmtProp(p1);
    PreData* data = initPreData();
    sat_data* sdata = preprocess(p2, data);
    cnf_list* learnt_clause = (cnf_list*)malloc(sizeof(cnf_list));
    learnt_clause->clause = NULL;
    learnt_clause->next = NULL;
    learnt_clause->size = 0;
    while(true){
        int ans = cdcl_solver(sdata);
        if(ans == 0) {
            freeCDCL(sdata);
            freePredata(data);
            free_cnf_list(learnt_clause);
            freeSmtProp(p1);
            #ifdef SMT_SOLVER_DEBUG
            printf("cdcl unsat\n");
            #endif
            return 0;
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
            ProofData* pdata = initProofData();
            CombineData* cdata =  initCombineData(data, value);
            free(value);
            value = NULL;
            if(cdata == NULL) {
                freeCDCL(sdata);
                freePredata(data);
                free_cnf_list(learnt_clause);
                freeSmtProp(p1);
                return 1;
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
            int theory_res = nelson_oppen_convex(cdata, data);
            freeCombineData(cdata);
            if(theory_res == 0) {
                #ifdef SMT_SOLVER_DEBUG
                printf("theory_unsat\n");
                #endif
                int* new_clause = (int*)malloc(sizeof(int)*sdata->v_size);
                memset(new_clause, 0, sizeof(int)*sdata->v_size);
                for(int i = 0; i < data->prop_cnt; i++){
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
                    sdata->cl_data->state[sdata->cl_size-1] = -sdata->v_size;
                    if(sdata->v_size == 1) sdata->cl_data->state[sdata->cl_size-1] = 2;
                    sdata->cl_data->unassign_num[sdata->cl_size-1] = sdata->v_size;
                    tmp =tmp->next;
                }
            }
            else {
                freeCDCL(sdata);
                freePredata(data);
                free_cnf_list(learnt_clause);
                freeSmtProp(p1);
                return 1;
            }
        }
    }
}


// #ifdef PARSER_DEBUG

// int main(int argc, char **argv) {
    
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
//     smt_solver(root);
//     // PreData* data = initPreData();
//     // sat_data* sdata = preprocess(root, data);
    
//     // int res3 = nelson_oppen_convex(cdata, data);
//     // if(res3 == 0) printf("unsat");
//     // else printf("sat");
    
// 	fclose(fp);
// }

// #endif
