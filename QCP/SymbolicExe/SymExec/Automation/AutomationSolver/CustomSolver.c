#include<string.h>
#include"CustomSolver.h"
#include"../../Paras.h"
#define QUOTE(name) #name
#define STR(macro) QUOTE(macro)

static struct GlobVarList *global_vars;
extern int exec_info;
struct GlobVarListNode *get_global_var_node(char *name);

void setIncludePath(){
    FILE *p = fopen(strategy_file,"r");
    if (p==NULL) return;
    char rel_path[500], abs_path[500];
    char var_name[100], var_value[100];
    while(true){
        if(fscanf(p,"add:%s\n",rel_path)==1){
            sprintf(abs_path,"%s%s",STR(PROJECT_ROOT_DIR),rel_path);
            if (exec_info)
            printf("Add include path:%s\n",rel_path);
            addIncludePath(abs_path);
            continue;
        }
        if(fscanf(p,"set:%s = %s\n",var_name,var_value)==2){
            continue;
        }
        break;        
    }
    fclose(p);
}

void initStrategyLibInScopesSingle(char * path, struct environment * env){
    char var_name[100], var_value[100];
    global_vars = GlobVarListNil();
    addCustomStrategyLib(path, env);
}

void initStrategyLibInScopes(struct environment * env){
    FILE *p = fopen(strategy_file,"r");
    global_vars = GlobVarListNil();
    if (p==NULL) return;
    char rel_path[500], abs_path[500];
    char var_name[100], var_value[100];
    while(true){
        if(fscanf(p,"add:%s\n",rel_path)==1){
            sprintf(abs_path,"%s/%s",STR(PROJECT_ROOT_DIR),rel_path);
            addCustomStrategyLib(abs_path,env);
            continue;
        }
        if(fscanf(p,"set:%s = %s\n",var_name,var_value)==2){
            struct GlobVarListNode *node = get_global_var_node(var_name);
            if(node!=NULL){
                GlobVarListRemove(global_vars,node);
            }
            GlobVarListCons(strdup(var_name),strdup(var_value),global_vars);
            continue;
        }
        break;
    }
    fclose(p);
}

void insertLib(struct StrategyLib * src,struct StrategyLib *dst,int i){
    if (src == NULL) return;
    for(int i = 0; i < STRATEGY_LIB_MAX_PRIORITY; i++){
        struct StrategyLibRuleListCell *cell = src->rules[i];
        struct StrategyLibRuleList * head = cell->head;
        while(head!=NULL){
            struct StrategyLibRule *arg = head->rule;
            arg->priority = 20*i+arg->priority;
            if(arg!=NULL){
                addStrategyLibRule(dst,arg);
            }
            head = head->next;
        }
    }
}

void isolateStrategyLib(struct StringList *scopes,struct StrategyLib * dst){
    int i=0;
    struct StringListNode *scope = scopes->head;
    struct StrategyLib *src = NULL;
    while(scope !=NULL){
        if (exec_info) {
          printf("try to find scope:%s\n",scope -> data);//Debug.
        }
        src = findLibByScope(scope ->data,true);
        if (exec_info) {
          printf("Get scope :%s (%p)\n",scope -> data,src);//Debug.
        }
        insertLib(src,dst,i);
        i=i+1; scope = scope->next;
    }
}

void freeIsolateLib(struct StrategyLib *lib){
    for(int i = 0; i < STRATEGY_LIB_MAX_PRIORITY; i++){
        struct StrategyLibRuleListCell *cell = lib->rules[i];
        struct StrategyLibRuleList * head = cell->head;
        while(head!=NULL){
            struct StrategyLibRuleList *next = head->next;
            struct StrategyLibRule *rule = head->rule;
            rule->priority = (rule->priority)%20;
            free(head);
            head = next;
        }
        free(cell);
    }
    free(lib);
}

void finiStrategyAll(){
    freeStrategyLibs();
    freeIncludePath();
    GlobVarListFree(global_vars);
}

struct EntailRetType * custom_solve(struct Assertion * pre, struct Assertion * post,struct environment * env, struct StringList * scope){
    struct StringList *scopes;
    if (scope == NULL) {
        scopes = StringListCons(strdup("core"), StringListNil());
    } else {
        scopes = StringListCons(strdup("core"), StringListDeepCopy(scope));
    }
    if (exec_info) {
    printf("=============================================================================================\n");
    printf("Try to solve entailment with scope: ");
    for (struct StringListNode *node = scopes->head; node != NULL; node = node->next) {
        printf("%s ", node->data);
    }
    printf("\n"); 
    }
    struct StrategyLib * lib = initStrategyLib();
    isolateStrategyLib(scopes,lib);
    struct EntailRetType * ret = solve(pre, post, lib, env);
    StringListFree(scopes);
    freeIsolateLib(lib);
    return ret;
}

struct EntailRetType * custom_solve_no_core(struct Assertion * pre, struct Assertion * post,struct environment * env, struct StringList * scope){
    struct StrategyLib * lib = initStrategyLib();
    isolateStrategyLib(scope,lib);
    struct EntailRetType * ret = solve(pre, post, lib, env);
    freeIsolateLib(lib);
    return ret;
}

struct EntailRetType *post_solve(struct Assertion * pre, struct Assertion * post, struct environment * env){
    struct StringList *scopes=StringListCons(strdup("post"),StringListNil());
    struct StrategyLib * lib = initStrategyLib();
    isolateStrategyLib(scopes,lib);
    struct EntailRetType * ret = solve(pre, post, lib, env);
    StringListFree(scopes);
    freeIsolateLib(lib);
    return ret;
}

struct EntailRetType *prop_cancel_solve(struct Assertion * pre, struct Assertion * post, struct environment * env){
    struct StringList *scopes=StringListCons(strdup("Pcancel"),StringListNil());
    struct StrategyLib * lib = initStrategyLib();
    isolateStrategyLib(scopes,lib);
    struct EntailRetType * ret = solve(pre, post, lib, env);
    StringListFree(scopes);
    freeIsolateLib(lib);
    return ret;
}

struct EntailRetType *tag_cancel_solve(struct Assertion * pre, struct Assertion * post, struct environment * env){
    struct StringList *scopes=StringListCons(strdup("Tagcancel"),StringListNil());
    struct StrategyLib * lib = initStrategyLib();
    isolateStrategyLib(scopes,lib);
    struct EntailRetType * ret = solve(pre, post, lib, env);
    StringListFree(scopes);
    freeIsolateLib(lib);
    return ret;
}

char *get_global_var(char *name){
    struct GlobVarListNode *node = global_vars->head;
    while(node!=NULL){
        if(!strcmp(node->name,name)){
            return node->value;
        }
        node = node->next;
    }
    return NULL;
}

struct GlobVarListNode *get_global_var_node(char *name){
    struct GlobVarListNode *node = global_vars->head;
    while(node!=NULL){
        if(!strcmp(node->name,name)){
            return node;
        }
        node = node->next;
    }
    return NULL; 
}

#undef STR
#undef QUOTE