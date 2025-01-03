#include"CDCL.h"
// #define CDCL_DEBUG 1
#ifdef CDCL_DEBUG
// FILE* fp;
#endif
int* clause_resolution(int* wi, int* wj, sat_data* s){
    int *res = malloc(sizeof(int)*(s->v_size));
    memset(res, 0, sizeof(int)*(s->v_size));
    for(int i = 0; i < s->v_size; i++){
        if((wi[i] == 1 && wj[i] == -1) || (wi[i] == -1 && wj[i] == 1) ){
            res[i] = 0;
            continue;
        }
        else{
            if(wi[i] != 0) res[i] = wi[i];
            else res[i] = wj[i];
        }
    }
    return res;
}

int* clause_learning(int wi, sat_data* s){   //返回学习到的子句
    bool flag = true;
    int* res = (int*)malloc(sizeof(int)*(s->v_size));
    memset(res, 0, sizeof(int)*(s->v_size));
    for(int i = 0; i < s->v_size; i++){
        res[i] = s->cl_data->value[wi][i];
    }
    while(flag){
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
        for(int i = 0; i < s->v_size; i++){
            if(res[i] == 0) continue;
            if(s->v_data->dl[i] == s->cur_dl && s->v_data->ancient[i] != -1){
                //fprintf(fp,"resol var : %d, its ancient : %d\n", i+1,  s->v_data->ancient[i] +1);
                int wj = s->v_data->ancient[i];
                int* tmp = res;
                res = clause_resolution(res, s->cl_data->value[wj],s);
                free(tmp);
                flag = true;
                break;
            }
        }
    }
    return res;
}



int conflict_analysis(int* clause, sat_data* s){   //返回回溯等级
    int max1, max2;     //最大值和第二大值
    max1 = -1;
    max2 = -1;
    for(int i = 0; i < s->v_size; i++){
        if(clause[i] == 0) continue;
        int dl = s->v_data->dl[i];
        if(dl > max1){
            max2 = max1;
            max1 = dl;
        }
        else if(dl > max2 && dl < max1){
            max2 = dl;
        }
    }
    if(max1 == -1){
        printf("error, empty learnt clause");
        return -1;
    }
    else if(max2 == -1) return 0;  //只有一个命题变元
    return max2;

}

int bcp(sat_data* s){
    int unitcl = -1;
    for(int i = 0; i < s->cl_size; i++){
        if(s->cl_data->state[i] == 2){
            unitcl = i;
            break;
        }
    }
    if(unitcl == -1) return -1;
    #ifdef CDCL_DEBUG
    printf("unitcl : %d\n", unitcl+1);
    #endif
    int bcpvar = -1;
    for(int i = 0; i < s->v_size; i++){
        if(s->v_data->value[i] == -1 && s->cl_data->value[unitcl][i] != 0){
            bcpvar = i;
            break;
        }
    }
    if(bcpvar == -1) printf("error in bcp\n") ,exit(0);
    #ifdef CDCL_DEBUG
    printf("bcpvar : %d\n", bcpvar+1);
    #endif
    s->cl_data->state[unitcl] = 0;
    s->cl_data->lit_state[unitcl] = 1;
    s->cl_data->unassign_num[unitcl]--;
    if(s->cl_data->unassign_num[unitcl]!=0) printf("error, here should be 0\n") ,exit(0);
    if(s->cl_data->value[unitcl][bcpvar] == 1) {
        s->v_data->value[bcpvar] = 1 ;
        #ifdef CDCL_DEBUG
        printf("bcpvar = true\n");
        #endif
        }
    else {
        s->v_data->value[bcpvar] = 0;
        #ifdef CDCL_DEBUG
        printf("bcpvar = false\n");
        #endif
        }
    s->v_data->ancient[bcpvar] = unitcl;
    s->v_data->dl[bcpvar] = s->cur_dl;
    int conflict = -1;
    for(int i = 0; i < s->cl_size; i++){
        if(s->cl_data->value[i][bcpvar] == 0 || i == unitcl) continue;
        if(s->cl_data->state[i] == 0){
            if((s->cl_data->value[i][bcpvar] == 1 && s->v_data->value[bcpvar] == 1)||
               (s->cl_data->value[i][bcpvar] == -1 && s->v_data->value[bcpvar] == 0)){
                    s->cl_data->lit_state[i]++;
              }
        }
        else if(s->cl_data->state[i] == 1){
            printf("error in bcp , shouldn't have unsat clause in bcp\n");
            exit(0);
        }
        else if(s->cl_data->state[i] == 2){
            if((s->cl_data->value[i][bcpvar] == 1 && s->v_data->value[bcpvar] == 1)||
               (s->cl_data->value[i][bcpvar] == -1 && s->v_data->value[bcpvar] == 0)){
                    s->cl_data->state[i] = 0;
                    s->cl_data->lit_state[i]++;
              }
              else {
                s->cl_data->state[i] = 1;
                if(conflict == -1)conflict = i;
              }
        }
        else {
            if((s->cl_data->value[i][bcpvar] == 1 && s->v_data->value[bcpvar] == 1)||
               (s->cl_data->value[i][bcpvar] == -1 && s->v_data->value[bcpvar] == 0)){
                    s->cl_data->state[i] = 0;
                    s->cl_data->lit_state[i] = 1;
              }
              else {
                s->cl_data->state[i] ++;
                if(s->cl_data->state[i] == -1) s->cl_data->state[i] = 2;
              }
        }
        s->cl_data->unassign_num[i]--;
    }
    if(conflict != -1) return conflict;
    else return bcp(s);

}




void backtrack(int back_dl, sat_data *s){
    for(int i = 0; i < s->v_size; i++){
        if(s->v_data->value[i] != -1 && s->v_data->dl[i] > back_dl){
            #ifdef CDCL_DEBUG
            printf("unpick %d in dl: %d\n", i+1, s->v_data->dl[i]);
            #endif
            for(int j = 0; j < s->cl_size; j++){
                if(s->cl_data->value[j][i] == 0) continue;
                if(s->cl_data->state[j] == 0){
                    if((s->cl_data->value[j][i] == 1 && s->v_data->value[i] == 1)||
                       (s->cl_data->value[j][i] == -1 && s->v_data->value[i] == 0)){
                            if(s->cl_data->lit_state[j] > 1) s->cl_data->lit_state[j]--;
                            else {
                                s->cl_data->lit_state[j]--;
                                if(s->cl_data->unassign_num[j] > 0) 
                                    s->cl_data->state[j] = -s->cl_data->unassign_num[j] - 1;
                                else{
                                    #ifdef CDCL_DEBUG
                                    printf("backtrack var : %d, get unit clause : %d\n", i+1, j+1);
                                    #endif
                                    s->cl_data->state[j] = 2;
                                }
                            }
                    }
                    
                }
                else if(s->cl_data->state[j] == 1){
                    if((s->cl_data->value[j][i] == 1 && s->v_data->value[i] == 0)||
                       (s->cl_data->value[j][i] == -1 && s->v_data->value[i] == 1)){
                            #ifdef CDCL_DEBUG
                            printf("backtrack var : %d, get unit clause : %d\n", i+1, j+1);
                            #endif
                            s->cl_data->state[j] = 2;
                       }
                    else printf("unexpected error in backtrack");
                }
                else if(s->cl_data->state[j] == 2){
                    if((s->cl_data->value[j][i] == 1 && s->v_data->value[i] == 0)||
                       (s->cl_data->value[j][i] == -1 && s->v_data->value[i] == 1)){
                            s->cl_data->state[j] = -2;
                       }
                    else printf("unexpected error in backtrack");
                }
                else if(s->cl_data->state[j] < 0){
                    s->cl_data->state[j] --;
                }
                s->cl_data->unassign_num[j]++;
            }
            s->v_data->dl[i] = -1;
            s->v_data->value[i] = -1;
            s->v_data->ancient[i] = -1;
        }
    }
}

int decide(sat_data* s){
    for(int i = 0; i < s->v_size; i++){
        if(s->v_data->value[i] == -1){
            s->v_data->value[i] = 1;
            #ifdef CDCL_DEBUG
            printf("decide %d = true\n", i+1);
            #endif
            for(int j = 0; j < s->cl_size; j++){
                if(s->cl_data->value[j][i] == 0) continue;
                s->cl_data->unassign_num[j]--;
                if(s->cl_data->state[j] == 0 && s->cl_data->value[j][i] == 1){
                    s->cl_data->lit_state[j]++;
                }
                else if(s->cl_data->state[j] < 0){
                    if(s->cl_data->value[j][i] == 1){
                        s->cl_data->state[j] = 0;
                        s->cl_data->lit_state[j] = 1;
                    }
                    else {
                        s->cl_data->state[j]++;
                        if(s->cl_data->state[j] == -1) s->cl_data->state[j] = 2;
                    }
                }
                else if(s->cl_data->state[j] == 1 || s->cl_data->state[j] == 2){  //decide的时候不应该存在unsat或unit的子句
                    printf("unexpected error in decide procedure");
                }
            }
            s->cur_dl++;
            s->v_data->dl[i] = s->cur_dl;
            s->v_data->ancient[i] = -1;
            return i;
        }
    }
    return -1;
}

int cdcl_solver(sat_data* s ){
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
    while(true){
        int conflict_cl = bcp(s);
        while(conflict_cl != -1){         //即bcp产生了冲突
            #ifdef CDCL_DEBUG
            printf("conflict_cl: %d \n",conflict_cl+1);
            #endif
            if(s->cur_dl == 0) return 0;
            #ifdef CDCL_DEBUG
            // fprintf(fp, "\nvalue state:\n");
            // for(int i = 0; i < s->v_size; i++){
            //     fprintf(fp, "x%d : dl = %d, ancient = %d \n",i+1, s->v_data->dl[i], s->v_data->ancient[i]+1);
            // }
            #endif
            int* new_cl = clause_learning(conflict_cl, s);
            #ifdef CDCL_DEBUG
            for(int i = 0; i < s->v_size; i++){
                if(new_cl[i] > 0){
                    printf("%d ", i+1);
                }
                else if(new_cl[i] < 0){
                    printf("-%d ", i+1);
                }
            }
            printf("\n");
            #endif
            if(s->cl_size == s->cl_maxsize){
                printf("too many clause");
                return -2;
            }
            else s->cl_size++;
            s->cl_data->value[s->cl_size-1] = new_cl;
            s->cl_data->state[s->cl_size-1] = 1;
            s->cl_data->lit_state[s->cl_size-1] = 0;
            s->cl_data->unassign_num[s->cl_size-1] = 0;
            s->cur_dl = conflict_analysis(new_cl, s);
            if(s->cur_dl < 0) return 0;   //表示unsat
            backtrack(s->cur_dl, s);
            #ifdef CDCL_DEBUG
            printf("backtrack res: ");
            // for(int i = 0; i < s->v_size; i++){
            //     if(s->v_data->value[i] == 1){
            //         printf("%d ", i+1);
            //     }
            //     else if(s->v_data->value[i] == 0){
            //         printf("-%d ", i+1);
            //     }
            // }
            printf("\n");
            #endif
            conflict_cl = bcp(s);
        }
        if(decide(s) == -1){
            #ifdef CDCL_DEBUG
            for(int i = 0; i < s->v_size; i++){
            if(s->v_data->value[i] == 1){
                printf("%d ",i+1);
            }
            else if(s->v_data->value[i] == 0){
                 printf("-%d ",i+1);
            }
            }
        printf("\n");
           #endif
        return 1;
        }

    }

}



sat_data* initCDCL_TEST(int n, int m){  //n表示变量数量，m表示clause数量
    sat_data* s = (sat_data*)malloc(sizeof(sat_data));
    s->v_size = n;
    s->cl_size = m;
    s->cl_maxsize = m*8;
    s->v_data = (var_data*)malloc(sizeof(var_data));
    s->cl_data = (clause_data*)malloc(sizeof(clause_data));

    s->v_data->value = (int*)malloc(n*sizeof(int));
    s->v_data->dl = (int*)malloc(n*sizeof(int));
    s->v_data->ancient = (int*)malloc(n*sizeof(int));
    memset(s->v_data->value, -1, sizeof(int)*n);
    memset(s->v_data->dl, -1, sizeof(int)*n);
    memset(s->v_data->ancient, -1, sizeof(int)*n);

    s->cl_data->state = (int*)malloc(s->cl_maxsize*sizeof(int));
    s->cl_data->lit_state = (int*)malloc(s->cl_maxsize*sizeof(int));
    s->cl_data->unassign_num = (int*)malloc(s->cl_maxsize*sizeof(int));
    s->cl_data->value = (int**)malloc(s->cl_maxsize*sizeof(int*));
    memset(s->cl_data->lit_state, 0, sizeof(int)*s->cl_maxsize);
    memset(s->cl_data->state, 0, sizeof(int)*s->cl_maxsize);
    memset(s->cl_data->unassign_num, 0, sizeof(int)*s->cl_maxsize);
    for(int i = 0; i < m; i++){
        s->cl_data->value[i] = (int*)malloc(n*sizeof(int));
        memset(s->cl_data->value[i], 0, sizeof(int)*n);
    }
    return s;
}

void free_vdata(var_data *v_data){
    free(v_data->value);
    free(v_data->dl);
    free(v_data->ancient);
    free(v_data);
}

void freeCDCL(sat_data* s){
    free_vdata(s->v_data);
    free(s->cl_data->state);
    free(s->cl_data->lit_state);
    free(s->cl_data->unassign_num);
    for(int i = 0; i < s->cl_size; i++){
        free(s->cl_data->value[i]);
    }
    free(s->cl_data->value);
    free(s->cl_data);
    free(s);
}



static void read_until_new_line (FILE * input) {
    int ch; 
    while ((ch = getc (input)) != '\n')
    if (ch == EOF) { 
        printf ("parse error: unexpected EOF"); 
        exit (1); 
    } 
}

// void Test_Sat_Solver(char* filename){
//     FILE* input = fopen(filename, "r");
//     #ifdef CDCL_DEBUG
//     fp = fopen("sqrt2809test.txt", "w");
//     #endif
//     int tmp;
//     int nvar, nclause;
//     while ((tmp = getc (input)) == 'c') read_until_new_line (input);
//     ungetc (tmp, input);
//     do { 
//         tmp = fscanf (input, " p cnf %i %i \n", &nvar, &nclause);  
//         if (tmp > 0 && tmp != EOF) break; 
//         tmp = fscanf (input, "%*s\n"); 
//     }    
//     while (tmp != 2 && tmp != EOF);
//     printf("%d %d\n",nvar, nclause);
//     sat_data* s = initCDCL_TEST(nvar, nclause);
//     int cl_num = 0;
//     while(cl_num < nclause){
//         //printf("clause_num %d\n",cl_num); 
//         int ch = getc (input);
//         if (ch == ' ' || ch == '\n') continue;
//         if (ch == 'c') { read_until_new_line (input); continue; }
//         ungetc (ch, input);
//         int lit = 0; 
//         tmp = fscanf (input, " %i ", &lit);
//         if (tmp == EOF) {
//             printf ("s parse error: header incorrect\n"); 
//             exit (0); 
//         }
//         if(lit != 0){
//             //printf("%d ",lit);
//             if(lit > 0){
//                 s->cl_data->value[cl_num][lit-1] = 1;
//             }
//             else{
//              s->cl_data->value[cl_num][-lit-1] = -1;
//             }
//              s->cl_data->state[cl_num]--;
//              s->cl_data->unassign_num[cl_num]++;
             
//         }
//         else{
//             if(s->cl_data->state[cl_num] == -1)
//                 s->cl_data->state[cl_num] = 2;
//             cl_num++;
//             printf("\n");
//         }
//         //printf("\n");
//     }
//     fclose(input);
//     #ifdef CDCL_DEBUG
//     for(int i = 0; i < s->cl_size; i++){
//         for(int j = 0; j < s->v_size; j++){
//             if(s->cl_data->value[i][j] > 0){
//                 printf("%d ", j+1);
//             }
//             if(s->cl_data->value[i][j] < 0){
//                 printf("-%d ", j+1);
//             }
//         }
//         printf("\n");
//     }
//     #endif
//     printf("parse success\n");
    
//     int ans = cdcl_solver(s);
//     if(ans == 0) {
//         printf("unsat\n");
//     }
//     else if(ans < 0){
//         printf("error : too many clause \n");
//     }
//     else if(ans == 1){
//         #ifdef CDCL_DEBUG
//         printf("sat\n");
//         #endif
//     }
//     #ifdef CDCL_DEBUG
//     fclose(fp);
//     #endif
// }

/* int main (int argc, char** argv){
    if(argc  <= 1) {
        printf("no input file provided\n"); 
        exit (0);
    } 
    else {
        Test_Sat_Solver(argv[1]);
    } 
    return 0;
}
*/
