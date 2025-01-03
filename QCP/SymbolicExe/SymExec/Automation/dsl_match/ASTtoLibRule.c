#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "ASTtoLibRule.h"


bool errorGenerated = false;

int cmd_env = 0; //value: 1-action; 0-others;

extern struct lang_rule_file *root;
static struct charMapping * type_mapping;
static struct StringList * paths;
extern int exec_info;
extern struct StringList *all_strategy_libs;
extern struct StringList *strategy_folder_list;

void appendStrategyLibRuleNode(struct StrategyLibRuleNode **head,char *scope,struct StrategyLibRule *strategy){
    struct StrategyLibRuleNode *newNode = (struct StrategyLibRuleNode*)malloc(sizeof(struct StrategyLibRuleNode));
    if(newNode ==NULL){
        fprintf(stderr, "Memory allocation failed for StrategyLibRuleNode.\n");
        return;
    }
    newNode->scope = scope;
    newNode->strategy = strategy;
    newNode->next = NULL;  
    if(*head == NULL){
        *head = newNode;
        return;
    }
    struct StrategyLibRuleNode *current = *head;
    while(current->next!=NULL){
        current = current->next;
    }
    current->next = newNode;
}

void freeStrategyLibRuleNode(struct StrategyLibRuleNode *head){
    struct StrategyLibRuleNode *current = head;
    struct StrategyLibRuleNode *next;
    while(current!=NULL){
        next = current->next;
        free(current->scope);
        free(current);
        current = next;
    }
}

void appendStrategyLibNode(struct StrategyLibNode **head,char *scope,struct StrategyLib *lib){
    struct StrategyLibNode *newNode=(struct StrategyLibNode*)malloc(sizeof(struct StrategyLibNode));
    if(newNode ==NULL){
        fprintf(stderr, "Memory allocation failed for StrategyLibNode.\n");
        return;
    }
    newNode->scope = scope;
    newNode->lib = lib;
    newNode->next = NULL;  
    if(*head == NULL){
        *head = newNode;
        return;
    }
    struct StrategyLibNode *current = *head;
    while(current->next!=NULL){
        current = current->next;
    }
    current->next = newNode;   
    if (exec_info)
    printf("New scope:%s(%p)\n",scope,newNode->lib);//Debug.
}

struct StrategyLib* findLibByScope(char *scope,bool search){
    // printf("head:%p\n",strategyLibInScopes);
    struct StrategyLibNode *current = strategyLibInScopes;
    while(current!=NULL){
        if(strcmp(current->scope, scope)==0){
            return current->lib;
        }
        current = current->next;
    }
    if(search==true){
        if (strcmp(scope,"Pcancel") == 0 || strcmp(scope,"core") == 0 || strcmp(scope, "post") == 0){
            return NULL;
        }
        fprintf(stderr,"Fail to find lib for scope:%s\n",scope);
        exit(1);
        return NULL;
    }
    else{
        struct StrategyLib *lib = initStrategyLib();
        appendStrategyLibNode((struct StrategyLibNode **)&strategyLibInScopes,strdup(scope),lib);
        if (exec_info) {
          printf("Add new strategy scope: %s\n",scope);
        }
        // printf("newHead:%p,address of head:%p\n",strategyLibInScopes,&strategyLibInScopes);
        return lib;
    }
}

void freeStrategyLibNode(struct StrategyLibNode *head){
    struct StrategyLibNode *current = head;
    struct StrategyLibNode *next;
    while(current!=NULL){
        next = current->next;
        free(current->scope);
        finiStrategyLib(current->lib);
        free(current);
        current = next;
    }
}

void freeStrategyLibs(){
    freeStrategyLibNode(strategyLibInScopes);
    strategyLibInScopes = NULL;
}

struct StrategyLibRule * AST_to_LibRule(struct lang_cmd * root,char * file,int prio,struct environment * env){
    int id = root -> ID, priority = prio;
    type_mapping = initCharMapping(1);
    struct StrategyLibPatternLList * pats = cmd_pattern_to_LList(root->patterns,env);
    if (errorGenerated) {
        fprintf(stderr, "Error occur in patten list (left and right).\n");
        return NULL;
    }
    struct StrategyLibCheckList * checks = cmd_check_to_CList(root->checks,env);
    if (errorGenerated) {
        fprintf(stderr, "Error occur in check.\n");
        return NULL;
    }
    struct StrategyLibActionList * actions = cmd_action_to_AList(root->actions,env);
    if (errorGenerated) {
        fprintf(stderr, "Error occur in action list.\n");
        return NULL;
    }
    if(PRINT_INFORMATION)printf("\n ------------------------------------------------------ \n");
    

    return type_infer(initStrategyLibRule(id, priority, strdup(file), pats, actions, checks, type_mapping), env);
}

struct StrategyLibPatternLList * cmd_pattern_to_LList(struct lang_pattern_list * pats,struct environment * env){
    struct lang_pattern_list * cur = pats;
    struct StrategyLibPatternLList * ret = NULL;
    if (cur != NULL) {
        if (cur -> head -> t == lang_T_UNKNOWN) {
            fprintf(stderr, "Unexpected unknown pattern type in cmd_pattern_to_LList.\n");
            lang_print_pattern(cur -> head);
            errorGenerated = true;
            return NULL;
        }
        if (cur -> head == NULL) {
            fprintf(stderr, "Unexpected NULL pattern in cmd_pattern_to_LList.\n");
            errorGenerated = true;
            return NULL;
        }
        if(PRINT_INFORMATION) printf("initStrategyLibPatternLList(\ninitStrategyLibPatternList(%s : ", cur->head->t == lang_T_LEFT ? "LEFT" : "RIGHT");
        struct StrategyLibPatternList * now = cmd_pattern_to_List(cur->head->expr,env);
        if(PRINT_INFORMATION) printf(")\n at %d)\n", cur->head->at_number);
        struct StrategyLibPatternLList * res = cmd_pattern_to_LList(cur->tail,env);
        ret = initStrategyLibPatternLList(now, res, cur->head->at_number, cur->head->t == lang_T_LEFT);        
        cur = cur->tail;
    }
    return ret;
}

void PolyTypeList_ValidCheck(struct PatternPolyTypeList *types, struct environment * env);

void PolyType_ValidCheck(struct PatternPolyType *type, struct environment * env){
    if (type == NULL) return;
    switch (type->ty) {
        case PATTERN_POLY_ARROW: {
            PolyType_ValidCheck(type->data.arrow->left, env);
            PolyType_ValidCheck(type->data.arrow->right, env);
            return;
        }
        case PATTERN_POLY_VAR: {
            struct atype_info * ty = find_atype_by_name(type->data.var, &(env->ephemer));
            if (ty != NULL) {
                if (PRINT_INFORMATION) printf("Change_PolyType(%s)\n", type->data.var);
                type->ty = PATTERN_POLY_CONST;
            }
            return;
        }
        case PATTERN_POLY_APP: {
            PolyTypeList_ValidCheck(type->data.app->args, env);
            return;
        }
        default: {
            return;
        }
    }
}

void PolyTypeList_ValidCheck(struct PatternPolyTypeList *types, struct environment * env){
    struct PatternPolyTypeList *cur = types;
    while (cur != NULL) {
        PolyType_ValidCheck(cur->head, env);
        cur = cur->next;
    }
}

void FuncExpr_ValidCheck(struct lang_expr *expr, struct environment * env){
    switch (expr->t) {
        case lang_T_FUNC: {
          if (expr->d.FUNC.name->t != lang_T_VAR) {
            fprintf(stderr, "Invalid Function Name Type.\n");
            lang_print_expr(expr->d.FUNC.name);
            errorGenerated = true;
            return;
          }
          if (expr->d.FUNC.typeNumber > 0 && expr->d.FUNC.name->d.VAR.type != NULL) {
            fprintf(stderr, "Invalid Function Structure (x : f){A}.\n");
            lang_print_expr(expr->d.FUNC.name);
            errorGenerated = true;
            return;
          }
          PolyType_ValidCheck(expr->d.FUNC.name->d.VAR.type, env);
          PolyTypeList_ValidCheck(expr->d.FUNC.types, env);
          return ;
        }
        default: {
            printf("Warning: Invalid input of FuncExpr_ValidCheck.\n");
            return;
        }
    }
}

int find_name(struct lang_expr *name, int typeNumber, int paraNumber, struct environment * env, char * funcname){
    if (name -> d.VAR.vt == PATTERN_VAR) {
        if (!charMappingIn(name->d.VAR.name, type_mapping))
        {
            if (name->d.VAR.type != NULL) charMappingInsert(name->d.VAR.name, initPatternPolyTypeMappingValue(PatternPolyTypeDeepCopy(name->d.VAR.type), 1), type_mapping);
            else charMappingInsert(name->d.VAR.name, initPatternPolyTypeMappingValue(NULL, 0), type_mapping);
        }
        return 0; // pattern function regard as prop
    }
    char * fname = strdup(name->d.VAR.name);
    struct mappingValue *mv = charMappingFind(fname, type_mapping);
    if (mv != NULL) {
        struct PatternPolyType *ptAtype = mv->val;
        if (ptAtype == NULL) {
          return 0;
        }
        int paras = 0;
        while(ptAtype->ty == PATTERN_POLY_ARROW){
          paras = paras+1;
          ptAtype = ptAtype->data.arrow->right;
        }
        // if (paras < paraNumber){
        //     fprintf(stderr, "%s:Expected paras(%d) ; Received paras(%d) in %s\n",fname,paras,paraNumber,funcname);
        //     errorGenerated = true; 
        //     return -1;
        // }        
        return (ptAtype->data.type == ASRT_TYPE);
    }
    else {
      struct var_scope_union *logic_var = find_logic_var_by_name(fname,&(env->ephemer));
      if (logic_var == NULL) {
        struct projection_info * projection_var = find_projection_by_name(fname,&(env->ephemer));
        if (projection_var == NULL) {
          fprintf(stderr, "Cannot find function %s in the environment.\n", fname);
          errorGenerated = true;
          return -1;
        }
        struct qvar_list *ptqv = projection_var->var->qv;
        int types = 0;
        while(ptqv!=NULL){
          types = types +1;
          ptqv = ptqv->next;
        }
        struct atype *ptAtype = projection_var->var->atype;
        int paras = 1;
        while(ptAtype->t ==AT_ARROW){
          paras = paras+1;
          ptAtype = ptAtype->d.ARROW.to;
        }
        // if (types!= typeNumber || paras < paraNumber){
        //   printf("%s:Expected paras(%d) types(%d); Received paras(%d) types(%d) in function %s\n",fname,paras,types,paraNumber,typeNumber, funcname);
        //   errorGenerated = true;
        //   return -1;
        // }         
        return !atype_is_prop(ptAtype); 
      }
      struct qvar_list *ptqv = logic_var->d.logic_var->qv;
      int types = 0;
      while(ptqv!=NULL){
        types = types +1;
        ptqv = ptqv->next;
      }
      struct atype *ptAtype = logic_var->d.logic_var->atype;
      int paras = 0;
      while(ptAtype->t ==AT_ARROW){
        paras = paras+1;
        ptAtype = ptAtype->d.ARROW.to;
      }
      // if (types!= typeNumber || paras < paraNumber){
      //   printf("%s:Expected paras(%d) types(%d); Received paras(%d) types(%d) in function %s\n",fname,paras,types,paraNumber,typeNumber, funcname);
      //   errorGenerated = true;
      //   return -1;
      // }         
      return !atype_is_prop(ptAtype);   
    }
}

struct StrategyLibPatternList * cmd_pattern_to_List(struct lang_expr * expr,struct environment * env){
    if (errorGenerated) return NULL;
    struct StrategyLibPatternList * ret = NULL;
    switch(expr->t){
        case lang_T_CONST:{
            fprintf(stderr,"Invalid LibPattern Type: single Const Value %llu.\n", expr->d.CONST.value);
            errorGenerated = true;
            break;   // at CONST
        }
        case lang_T_VAR:{
            fprintf(stderr,"Invalid LibPattern Type: single Var %s.\n", expr->d.VAR.name);
            errorGenerated = true;
            break;  
        }
        case lang_T_ARRINX:{
            fprintf(stderr,"Invalid LibPattern Type: single Array Index.\n");
            errorGenerated = true;
            break; // no case
        }
        case lang_T_BINOP:{
            switch (expr->d.BINOP.op) {
                case lang_T_OR: {
                   if (PRINT_INFORMATION) printf("initStrategyLibPatternList(");
                   struct StrategyLibPatternList * left = cmd_pattern_to_List(expr->d.BINOP.left,env);
                   if (PRINT_INFORMATION) printf("||");
                   struct StrategyLibPatternList * right = cmd_pattern_to_List(expr->d.BINOP.right,env);
                   ret = appendStrategyLibPatternList(left, right);
                   if (PRINT_INFORMATION) printf(")");
                   break;
                }
                case lang_T_EQ : 
                case lang_T_NEQ :
                case lang_T_LT :
                case lang_T_GT :
                case lang_T_LE :
                case lang_T_GE : {
                    ret = initStrategyLibPatternList(
                        getLibPattern(expr, env), ret);
                    break;
                }
                default : {
                    fprintf(stderr,"Invalid LibPattern Type: single BinOp expression.\n");
                    errorGenerated = true;
                    break;              
                }
            }
            break;
        }
        case lang_T_UNOP:{
            fprintf(stderr,"Invalid LibPattern Type: single unary expression.\n");
            errorGenerated = true;
            break; 
        }
        case lang_T_DATA_AT: {
          if (PRINT_INFORMATION) printf("initStrategyLibPatternList(initStrategyLibPatternSep(initPatternSepDataAt(");
          struct PatternExpr *addr = Get_Expr_expr(expr->d.DATA_AT.addr,env);
          if (PRINT_INFORMATION) printf(",");
          if (PRINT_INFORMATION) PatternCTypePrint(expr->d.DATA_AT.type);
          if (PRINT_INFORMATION) printf(",");
          struct PatternExpr *value = Get_Expr_expr(expr->d.DATA_AT.value,env);
          ret = initStrategyLibPatternList(
                        initStrategyLibPatternSep(
                            initPatternSepDataAt(addr, PatternCTypeDeepCopy(expr->d.DATA_AT.type), value)
                        ), ret);
          if (PRINT_INFORMATION) printf(")))");
          break;
        }
        case lang_T_UNDEF_DATA_AT: {
          if (PRINT_INFORMATION) printf("initStrategyLibPatternList(initStrategyLibPatternSep(initPatternSepUndefDataAt(");
          struct PatternExpr *addr = Get_Expr_expr(expr->d.UNDEF_DATA_AT.addr,env);
          if (PRINT_INFORMATION) printf(",");
          if (PRINT_INFORMATION) PatternCTypePrint(expr->d.UNDEF_DATA_AT.type);
          ret = initStrategyLibPatternList(
                        initStrategyLibPatternSep(
                            initPatternSepUndefDataAt(addr, PatternCTypeDeepCopy(expr->d.UNDEF_DATA_AT.type))
                        ), ret);
          if (PRINT_INFORMATION) printf(")))");
          break;
        }
        case lang_T_FUNC:{
            FuncExpr_ValidCheck(expr, env);
            int is_sep = find_name(expr->d.FUNC.name, expr->d.FUNC.typeNumber, expr->d.FUNC.paraNumber,env, "cmd_expr_to_List");
            int is_pat = charMappingFind(strdup(expr->d.FUNC.name->d.VAR.name), type_mapping) != NULL;
            if (errorGenerated) return NULL;
            if (is_sep) {
                if(PRINT_INFORMATION)printf("initStrategyLibPatternList(initStrategyLibPatternSep(initPatternSep%sPred(", is_pat ? "Pat"  : "");
                if (PRINT_INFORMATION) printf("%s,",strdup(expr->d.FUNC.name->d.VAR.name));
                if (PRINT_INFORMATION) PatternPolyTypeListPrint(expr->d.FUNC.types);
                if (PRINT_INFORMATION) printf(",");
                struct PatternExprList *args = expr_to_PExprList(expr->d.FUNC.args,env);
                if (is_pat) {
                  ret = initStrategyLibPatternList(
                    initStrategyLibPatternSep(
                        initPatternSepPatPred(strdup(expr->d.FUNC.name->d.VAR.name),args)
                    ), ret
                  );
                }
                else {
                ret = initStrategyLibPatternList(
                    initStrategyLibPatternSep(
                        initPatternSepPred(strdup(expr->d.FUNC.name->d.VAR.name),PatternPolyTypeListDeepCopy(expr->d.FUNC.types),args)
                    ), ret
                  );
                }
                if(PRINT_INFORMATION) printf(")))");
            }
            else {
                if(PRINT_INFORMATION)printf("initStrategyLibPatternList(initStrategyLibPatternProp(initPatternProp%sPred(", is_pat ? "Pat"  : "");
                if (PRINT_INFORMATION) printf("%s,",strdup(expr->d.FUNC.name->d.VAR.name));
                if (PRINT_INFORMATION) PatternPolyTypeListPrint(expr->d.FUNC.types);
                if (PRINT_INFORMATION) printf(",");
                struct PatternExprList *args = expr_to_PExprList(expr->d.FUNC.args,env); 
                if (is_pat) {
                  ret = initStrategyLibPatternList(
                    initStrategyLibPatternProp(
                        initPatternPropPatPred(strdup(expr->d.FUNC.name->d.VAR.name), args)
                    ), ret
                  );
                }
                else {
                ret = initStrategyLibPatternList(
                    initStrategyLibPatternProp(
                        initPatternPropPred(strdup(expr->d.FUNC.name->d.VAR.name), PatternPolyTypeListDeepCopy(expr->d.FUNC.types), args)
                    ), ret
                  );
                }
                if(PRINT_INFORMATION) printf(")))");
            }
            break;
        }
        case lang_T_TOKEN:{
            fprintf(stderr,"Invalid LibPattern Type: single Token.\n");
            errorGenerated = true;
            break;  
        }
        case lang_T_SIZEOF:{
            fprintf(stderr,"Invalid LibPattern Type: single Sizeof.\n");
            errorGenerated = true;
            break;  
        }
        default:{
            fprintf(stderr,"Invalid LibPattern Type: UnSupport Type.\n");
            errorGenerated = true;
            break; 
        }
    }
    return ret;
}

struct StrategyLibActionList * cmd_action_to_AList(struct lang_action_list * actions,struct environment * env){
    if (errorGenerated) return NULL;
    struct StrategyLibActionList *ret = NULL;
    if(actions!=NULL){ 
        if(PRINT_INFORMATION) printf("initStrategyLibActionList(");
        struct StrategyLibAction * now = actToLibAction(actions->head,env);
        if (PRINT_INFORMATION) printf(",");
        struct StrategyLibActionList * res = cmd_action_to_AList(actions->tail,env);
        ret = initStrategyLibActionList(now, res);
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else{
        if(PRINT_INFORMATION) printf("\nNULL\n");
        return NULL;
    }
}

struct StrategyLibCheckList * cmd_check_to_CList(struct lang_action_list * checks,struct environment * env){
    if (errorGenerated) return NULL;
    struct StrategyLibCheckList *ret = NULL;
    if(checks!=NULL){
        if(PRINT_INFORMATION) printf("initStrategyLibCheckList(");
        struct StrategyLibCheck * now = checkToLibCheck(checks->head,env);
        if (PRINT_INFORMATION) printf(",");
        struct StrategyLibCheckList * res = cmd_check_to_CList(checks->tail,env);
        ret = initStrategyLibCheckList(now,res);
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else{
        if(PRINT_INFORMATION) printf("\nNULL\n");
        return NULL;
    }
}

struct StrategyLibAction  *actToLibAction(struct lang_action *act,struct environment * env){
    if (errorGenerated) return NULL;
    struct StrategyLibAction  *ret = NULL;
    if((!strcmp(act->name,"left_erase"))||(!strcmp(act->name,"left_prop_erase"))||(!strcmp(act->name,"left_sep_erase"))){
        if((act->arg)->t != lang_T_CONST){
            errorGenerated = true;
            fprintf(stderr,"Incorrect Parameters Type for action:%s.\n", act->name);
            return NULL;
        }
        int pos = (act->arg)->d.CONST.value;
        if(PRINT_INFORMATION) printf("\ninitStrategyLibActionDelLeft(%d)",pos);
        return initStrategyLibActionDelLeft(pos);
    }
    else if((!strcmp(act->name,"right_erase"))||(!strcmp(act->name,"right_sep_erase"))||(!strcmp(act->name,"right_prop_erase"))){
        if((act->arg)->t != lang_T_CONST){
            errorGenerated = true;
            fprintf(stderr,"Incorrect Parameters Type for action:%s.", act->name);
            return NULL;
        }
        int pos = (act->arg)->d.CONST.value;
        if(PRINT_INFORMATION) printf("\ninitStrategyLibActionDelRight(%d)",pos);
        return initStrategyLibActionDelRight(pos);        
    }
    else if((!strcmp(act->name,"left_add"))||(!strcmp(act->name,"left_prop_add"))||(!strcmp(act->name,"left_sep_add"))){
        if(PRINT_INFORMATION) printf("\ninitStrategyLibActionAddLeft(");
        ret =  initStrategyLibActionAddLeft(getLibPattern(act->arg, env));
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else if((!strcmp(act->name,"right_add"))||(!strcmp(act->name,"right_prop_add"))||(!strcmp(act->name,"right_sep_add"))){
        if(PRINT_INFORMATION) printf("\ninitStrategyLibActionAddRight(");
        ret =  initStrategyLibActionAddRight(getLibPattern(act->arg, env));
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else if(!strcmp(act->name,"left_exist_add")){
        if((act->arg)->t!=lang_T_VAR || act->arg->d.VAR.vt!=NORMAL_VAR){
            fprintf(stderr,"Incorrect Parameters Type for action:left_exist_add.\n");
            errorGenerated = true;
            return NULL;
        }
        char *var = (act->arg)->d.VAR.name;
        if(PRINT_INFORMATION)printf("\ninitStrategyLibActionAddLeftExist(%s:",var);   
        if ((act->arg)->d.VAR.type != NULL) {
            if (PRINT_INFORMATION) PatternPolyTypePrint(stdout, (act->arg)->d.VAR.type);
            struct PatternPolyType * ty = PatternPolyTypeDeepCopy((act->arg)->d.VAR.type);
            ret = initStrategyLibActionAddLeftExist(initVarType(strdup(var), ty));
            charMappingInsert((act->arg)->d.VAR.name,
                               initPatternPolyTypeMappingValue(PatternPolyTypeDeepCopy(ty), 1), type_mapping);
        }
        else {
            ret = initStrategyLibActionAddLeftExist(initVarType(strdup(var), NULL));
            if (!charMappingIn((act->arg)->d.VAR.name, type_mapping))
                charMappingInsert((act->arg)->d.VAR.name, initPatternPolyTypeMappingValue(NULL, 0), type_mapping);
        }
        if(PRINT_INFORMATION) printf(")");
        return ret;

    }
    else if(!strcmp(act->name,"right_exist_add")){
        if((act->arg)->t!=lang_T_VAR || act->arg->d.VAR.vt!=NORMAL_VAR){
            fprintf(stderr,"Incorrect Parameters Type for action:right_exist_add.\n");
            errorGenerated = true;
            return NULL;
        }
        char *var = (act->arg)->d.VAR.name;
        if(PRINT_INFORMATION)printf("\ninitStrategyLibActionAddRightExist(%s:",var);   
        if ((act->arg)->d.VAR.type) {
            if (PRINT_INFORMATION) PatternPolyTypePrint(stdout, (act->arg)->d.VAR.type);
            struct PatternPolyType * ty = PatternPolyTypeDeepCopy((act->arg)->d.VAR.type);
            ret = initStrategyLibActionAddRightExist(initVarType(strdup(var), ty));
            charMappingInsert((act->arg)->d.VAR.name,
                               initPatternPolyTypeMappingValue(PatternPolyTypeDeepCopy(ty), 1), type_mapping);
        }
        else {
            ret = initStrategyLibActionAddRightExist(initVarType(strdup(var), NULL));
            if (!charMappingIn((act->arg)->d.VAR.name, type_mapping))
                charMappingInsert((act->arg)->d.VAR.name, initPatternPolyTypeMappingValue(NULL, 0), type_mapping);
        }
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else if(!strcmp(act->name,"instantiate")){
        if((act->arg)->t!=lang_T_BINOP){
            fprintf(stderr,"Incorrect Parameters Type for action:instantiate.\n");
            errorGenerated = true;
            return NULL;
        }
        struct lang_expr *ptExpr = act->arg;
        if(ptExpr->d.BINOP.op!=lang_T_FIELDOFPTR){
            fprintf(stderr,"Incorrect Parameters Type for action:instantiate.\n");
            errorGenerated = true;
            return NULL;
        }
        struct lang_expr *ptLExpr = ptExpr->d.BINOP.left;
        struct lang_expr *ptRExpr = ptExpr->d.BINOP.right;
        if(ptLExpr->t!=lang_T_VAR || ptLExpr->d.VAR.vt!=NORMAL_VAR){
            fprintf(stderr,"Incorrect Parameters Type for action:instantiate.\n");
            errorGenerated = true;
            return NULL;
        }
        if(PRINT_INFORMATION) printf("\ninitStrategyLibActionInst(strdup(%s),",ptLExpr->d.VAR.name);
        ret= initStrategyLibActionInst(strdup(ptLExpr->d.VAR.name),Get_Expr_expr(ptRExpr,env));
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else if(!strcmp(act->name,"substitute")){
        if((act->arg)->t!=lang_T_BINOP){
            fprintf(stderr,"\nIncorrect Parameters Type for action:substitute.\n");
            errorGenerated = true;
            return NULL;
        }
        struct lang_expr *ptExpr = act->arg;
        if(ptExpr->d.BINOP.op!=lang_T_FIELDOFPTR){
            fprintf(stderr,"Incorrect Parameters Type for action:substitute.\n");
            errorGenerated = true;
            return NULL;
        }
        struct lang_expr *ptLExpr = ptExpr->d.BINOP.left;
        struct lang_expr *ptRExpr = ptExpr->d.BINOP.right;
        if(ptLExpr->t!=lang_T_VAR || ptLExpr->d.VAR.vt!=NORMAL_VAR){
            fprintf(stderr,"Incorrect Parameters Type for action:substitute.\n");
            errorGenerated = true;
            return NULL;
        }
        if(PRINT_INFORMATION) printf("\nActionSubst(strdup(%s),",ptLExpr->d.VAR.name);
        ret = initStrategyLibActionSubst(strdup(ptLExpr->d.VAR.name),Get_Expr_expr(ptRExpr,env));
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else{
        fprintf(stderr,"Invalid action type: %s\n",act->name);
        errorGenerated = true;
        return NULL;
    }
}

struct StrategyLibCheck *checkToLibCheck(struct lang_action *act,struct environment * env){
    if (errorGenerated) return NULL;
    struct StrategyLibCheck *ret = NULL;
    if(!strcmp(act->name,"absense")){
        if(PRINT_INFORMATION) printf("\ninitStrategyLibCheckAbsense(");
        ret = initStrategyLibCheckAbsense(getPatternProp(act->arg,env));
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else if(!strcmp(act->name,"infer")){
        if(PRINT_INFORMATION) printf("\ninitStrategyLibCheckInfer(");
        ret = initStrategyLibCheckInfer(getPatternProp(act->arg,env));
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else{
        fprintf(stderr,"Invalid check type: %s\n",act->name);
        errorGenerated = true;
        return NULL;
    }
}

struct PatternExprList * expr_to_PExprList(struct lang_expr_list *args,struct environment * env){
    if (errorGenerated) return NULL;
    struct PatternExprList *ret = NULL;
    if(args!=NULL){
        if(PRINT_INFORMATION) printf("initPatternExprList(");
        struct PatternExpr * now = Get_Expr_expr(args->head,env);
        if (PRINT_INFORMATION) printf(",");
        struct PatternExprList * res = expr_to_PExprList(args->tail,env);
        ret = initPatternExprList(now, res);
        if(PRINT_INFORMATION) printf(")");
        return ret;
    }
    else{
        if(PRINT_INFORMATION) printf("NULL");
        return NULL;
    }
}

struct PatternExpr * Field_trans(struct lang_expr *expr, struct environment *env) {
  if (expr->d.FUNC.name->d.BINOP.op != lang_T_FIELDOF) {
    fprintf(stderr, "Invalid Function name Type.\n");
    errorGenerated = true;
    return NULL;
  }
  struct PatternExpr *ret;
  if (PRINT_INFORMATION)
    printf("initPatternExprApp(%s, ", expr->d.FUNC.name->d.BINOP.right->d.VAR.name);
  if (PRINT_INFORMATION) PatternPolyTypePrint(stdout, expr->d.FUNC.name->d.BINOP.right->d.VAR.type);
  if (PRINT_INFORMATION) PatternPolyTypeListPrint(expr->d.FUNC.types);
  if (PRINT_INFORMATION)
    printf(",");
  struct PatternPolyTypeList *type = PatternPolyTypeListDeepCopy(expr->d.FUNC.types);
  if (expr->d.FUNC.name->d.BINOP.right->d.VAR.type != NULL)
    type = initPatternPolyTypeList(PatternPolyTypeDeepCopy(expr->d.FUNC.name->d.BINOP.right->d.VAR.type), type);
  ret = initPatternExprApp(
      strdup(expr->d.FUNC.name->d.BINOP.right->d.VAR.name), type , expr_to_PExprList(lang_PLCons(expr->d.FUNC.name->d.BINOP.left, expr->d.FUNC.args), env));
  if(PRINT_INFORMATION)printf(")");
  return ret;
}

struct PatternExpr * Get_Expr_expr(struct lang_expr * expr,struct environment * env){
    if (errorGenerated) return NULL;
    struct PatternExpr * ret = NULL;
    switch(expr->t){
        case lang_T_CONST:{
            unsigned long long num = expr->d.CONST.value;
            if(PRINT_INFORMATION) printf("initPatternExprConst(%llu)",num);
            ret = initPatternExprConst(num);
            break;
        }
        case lang_T_VAR:{
            switch(expr->d.VAR.vt){
                case NORMAL_VAR:{
                    if (!charMappingIn(expr->d.VAR.name, type_mapping) && (find_logic_var_by_name(expr->d.VAR.name, &(env->ephemer)) == NULL))
                    {
                        struct var_scope_union * addr = find_prog_var_by_name(expr->d.VAR.name, &(env->ephemer));
                        if (addr != NULL) {
                          if(PRINT_INFORMATION) printf("initPatternExprGlobalVar(%s",expr->d.VAR.name);
                          ret = initPatternExprGlobalVar(strdup(expr->d.VAR.name));
                          charMappingInsert(expr->d.VAR.name, initPatternPolyTypeMappingValue(initPatternPolyTypeConst(strdup("Z")), 1), type_mapping);
                          if (PRINT_INFORMATION) printf(")");
                          return ret;
                        }
                        fprintf(stderr, "Cannot find variable %s in the pattern variable and in environment.\n", expr->d.VAR.name);
                        errorGenerated = true;
                        break;
                    }
                    if(PRINT_INFORMATION) printf("initPatternExprNormalVar(%s",expr->d.VAR.name);
                    ret = initPatternExprVar(strdup(expr->d.VAR.name));
                    break;
                }
                case EXISTS_VAR:{
                    if(PRINT_INFORMATION) printf("initPatternExprExistsVar(%s",expr->d.VAR.name);
                    ret = initPatternExprEVar(strdup(expr->d.VAR.name));
                    break;
                }
                case ATOM_VAR:{
                    if(PRINT_INFORMATION) printf("initPatternExprAtomVar(%s",expr->d.VAR.name);
                    ret = initPatternExprAtomVar(strdup(expr->d.VAR.name));
                    break;
                }
                case PATTERN_VAR:{
                    if(PRINT_INFORMATION) printf("initPatternExprPatternVar(%s",expr->d.VAR.name);
                    ret = initPatternExprVar(strdup(expr->d.VAR.name));
                    break;
                }
                default:{
                    fprintf(stderr,"Unrecognized variable:%s\n",expr->d.VAR.name);
                    errorGenerated = true;
                    break;
                }
            }
            if (expr->d.VAR.type != NULL) {
                if (PRINT_INFORMATION) printf(" : ");
                if (PRINT_INFORMATION) PatternPolyTypePrint(stdout, expr->d.VAR.type);
                struct PatternPolyType * ty = PatternPolyTypeDeepCopy(expr->d.VAR.type);
                charMappingInsert(expr->d.VAR.name, initPatternPolyTypeMappingValue(ty, 1), type_mapping);
            }
            else {
                if (!charMappingIn(expr->d.VAR.name, type_mapping))
                    charMappingInsert(expr->d.VAR.name, initPatternPolyTypeMappingValue(NULL, 0), type_mapping);
            }
            if (PRINT_INFORMATION) printf(")");
            break;
        }
        case lang_T_ARRINX:{
            if(PRINT_INFORMATION)printf("initPatternExprArridx(");
            ret = initPatternExprArridx(
                    Get_Expr_expr(expr->d.ARRINX.name,env), Get_Expr_expr(expr->d.ARRINX.index,env)
                  );
            if(PRINT_INFORMATION)printf(")");
            break; 
        }
        case lang_T_BINOP:{
            switch (expr->d.BINOP.op) {
              struct PatternExpr *left;
              struct PatternExpr *right;
              case lang_T_ADD: {
                if(PRINT_INFORMATION)printf("initPatternExprBinop(");
                left = Get_Expr_expr(expr->d.BINOP.left,env);
                if (PRINT_INFORMATION) printf("+");
                right = Get_Expr_expr(expr->d.BINOP.right,env);
                ret = initPatternExprBinop(Oadd, left, right);
                if(PRINT_INFORMATION)printf(")");
                break;
              }
              case lang_T_SUB: {
                if(PRINT_INFORMATION)printf("initPatternExprBinop(");
                left = Get_Expr_expr(expr->d.BINOP.left,env);
                if (PRINT_INFORMATION) printf("-");
                right = Get_Expr_expr(expr->d.BINOP.right,env);
                ret = initPatternExprBinop(Osub, left, right);
                if(PRINT_INFORMATION)printf(")");
                break;
              }
              case lang_T_MUL: {
                if(PRINT_INFORMATION)printf("initPatternExprBinop(");
                left = Get_Expr_expr(expr->d.BINOP.left,env);
                if (PRINT_INFORMATION) printf("*");
                right = Get_Expr_expr(expr->d.BINOP.right,env);
                ret = initPatternExprBinop(Omul, left, right);
                if(PRINT_INFORMATION)printf(")");
                break;
              }
              case lang_T_DIV: {
                if(PRINT_INFORMATION)printf("initPatternExprBinop(");
                left = Get_Expr_expr(expr->d.BINOP.left,env);
                if (PRINT_INFORMATION) printf("/");
                right = Get_Expr_expr(expr->d.BINOP.right,env);
                ret = initPatternExprBinop(Odiv, left, right);
                if(PRINT_INFORMATION)printf(")");
                break;
              }
              case lang_T_FIELDOF: {  // a.t --> t{?A}(a)
                if(PRINT_INFORMATION)printf("initPatternExprField(");
                left = Get_Expr_expr(expr->d.BINOP.left,env);
                if (PRINT_INFORMATION) printf(".");
                //lang_print_expr(expr->d.BINOP.right);
                struct projection_info *proj = find_projection_by_name(expr->d.BINOP.right->d.VAR.name, &(env->ephemer));
                if (proj == NULL) {
                  fprintf(stderr, "Cannot find projection %s in the environment.\n", expr->d.BINOP.right->d.VAR.name);
                  errorGenerated = true;
                  return NULL;
                }
                ret = initPatternExprApp(
                      strdup(expr->d.BINOP.right->d.VAR.name), NULL, initPatternExprList(left, NULL));
                if(PRINT_INFORMATION)printf("strdup(%s),NULL)",expr->d.BINOP.right->d.VAR.name);
                break;
              }
              default: {
                fprintf(stderr,"Invalid Expr Case \n");
                errorGenerated = true;
                return NULL; // no case etc.
              }
            }
            break;
        }
        case lang_T_UNOP:{
             if (PRINT_INFORMATION) printf("initPatternExprUnop(");
             if (PRINT_INFORMATION) printf("-");
             struct PatternExpr *val = Get_Expr_expr(expr->d.UNOP.arg,env);
             ret = initPatternExprUnop(Oneg, val);
             if(PRINT_INFORMATION)printf(")");
             return ret;
        }
        case lang_T_SIZEOF: {
          if(PRINT_INFORMATION)printf("initPatternExprSizeof(");
          ret = initPatternExprSizeof(PatternCTypeDeepCopy(expr->d.SIZEOF.type));
          if(PRINT_INFORMATION)printf(")");
          break;
        }
        case lang_T_FUNC:{
            if (expr->d.FUNC.name->t == lang_T_BINOP) {
              ret = Field_trans(expr, env);
              break;
            }
            FuncExpr_ValidCheck(expr, env);
            if(!strcmp(expr->d.FUNC.name->d.VAR.name, "field_addr")){
                struct lang_expr * Expr1 = expr->d.FUNC.args->tail->head;
                struct lang_expr * Expr2 = expr->d.FUNC.args->tail->tail->head;
                if(Expr1->t != lang_T_VAR || Expr1 -> d.VAR.vt != NORMAL_VAR) {
                    fprintf(stderr,"Incorrect struct name type for field_addr. Only Name expected.\n");
                    errorGenerated = true;
                    return NULL;
                }
                if(Expr2->t != lang_T_VAR || Expr2 -> d.VAR.vt != NORMAL_VAR) {
                    fprintf(stderr,"Incorrect field name type for field_addr. Only Name expected.\n");
                    errorGenerated = true;
                    return NULL;
                }
                if(PRINT_INFORMATION)printf("initPatternExprField(");
                ret = initPatternExprField(
                        Get_Expr_expr(expr->d.FUNC.args->head,env), strdup(Expr1->d.VAR.name), strdup(Expr2->d.VAR.name)
                      ); 
                if(PRINT_INFORMATION)printf("strdup(%s),strdup(%s)",Expr1->d.VAR.name,Expr2->d.VAR.name);
                break;
            }
            if (!strcmp(expr->d.FUNC.name->d.VAR.name, "sizeof")){
              fprintf(stderr,"Wrong parser result of sizeof.\n");
              errorGenerated = true;
              return NULL;
            }
            else{
                find_name(expr->d.FUNC.name, expr->d.FUNC.typeNumber, expr->d.FUNC.paraNumber,env, "Get_Expr_expr");
                if (errorGenerated) return NULL;
                if(PRINT_INFORMATION)printf("initPatternExprApp(%s, ",expr->d.FUNC.name->d.VAR.name);
                if (PRINT_INFORMATION) PatternPolyTypeListPrint(expr->d.FUNC.types);
                if (PRINT_INFORMATION) printf(",");
                ret = initPatternExprApp(
                      strdup(expr->d.FUNC.name->d.VAR.name),PatternPolyTypeListDeepCopy(expr->d.FUNC.types), expr_to_PExprList(expr->d.FUNC.args,env)
                      );
                if(PRINT_INFORMATION)printf(")");
            }
            break;
        }
        case lang_T_TOKEN:{
            switch(expr->d.TOKEN.tk){
                case lang_T_UPPER_NULL:
                case lang_T_LOWER_NULL:{
                    if(PRINT_INFORMATION)printf("initPatternExprConst(0)");
                    ret = initPatternExprConst(0);
                    break;
                }
                default:{
                    fprintf(stderr,"Unrecognized Token Type: %d in Get_Expr_expr\n",expr->d.TOKEN.tk);
                    errorGenerated = true;
                    return NULL;
                }
            }
            break;
        }
        default:{
            fprintf(stderr,"Unrecognized PatternExpr,ExprType = %d\n",expr->t);
            errorGenerated = true;
            return NULL;
        }
    }
    return ret;
}

struct StrategyLibPattern *getLibPattern(struct lang_expr * expr, struct environment * env){
    if (errorGenerated) return NULL;
    struct StrategyLibPattern *ret = NULL;
    switch(expr->t){
        case lang_T_BINOP: {
            switch(expr->d.BINOP.op){
                case lang_T_EQ:
                case lang_T_NEQ:
                case lang_T_LE:
                case lang_T_GE:
                case lang_T_LT:
                case lang_T_GT:
                    return Get_Expr_BinOP(expr,env);
                    break;  
                default:
                    fprintf(stderr,"Invalid type for LibPattern(exprType:BinOp -%d)\n",expr->d.BINOP.op);
                    errorGenerated = true;
                    return NULL;
            }
            break;
        }
        case lang_T_FUNC: {
            FuncExpr_ValidCheck(expr, env);
            int is_sep = find_name(expr->d.FUNC.name, expr->d.FUNC.typeNumber, expr->d.FUNC.paraNumber,env, "getLibPattern");
            if (errorGenerated) return NULL;
            if (is_sep) {
              if(PRINT_INFORMATION)printf("initStrategyLibPatternSep(");
              ret =  initStrategyLibPatternSep(getPatternSeq(expr,env));
              if(PRINT_INFORMATION)printf(")");
            }
            else {
              if(PRINT_INFORMATION)printf("initStrategyLibPatternProp(");
              ret =  initStrategyLibPatternProp(getPatternProp(expr, env));
              if(PRINT_INFORMATION)printf(")");
            }
            break;
        }
        case lang_T_DATA_AT: {
          if (PRINT_INFORMATION) printf("initStrategyLibPatternSep(initPatternSepDataAt(");
          struct PatternExpr *addr = Get_Expr_expr(expr->d.DATA_AT.addr,env);
          if (PRINT_INFORMATION) printf(",");
          if (PRINT_INFORMATION) PatternCTypePrint(expr->d.DATA_AT.type);
          if (PRINT_INFORMATION) printf(",");
          struct PatternExpr *value = Get_Expr_expr(expr->d.DATA_AT.value,env);
          ret = initStrategyLibPatternSep(
                  initPatternSepDataAt(addr, PatternCTypeDeepCopy(expr->d.DATA_AT.type), value)
                );
          if (PRINT_INFORMATION) printf("))");
          break;
        }
        case lang_T_UNDEF_DATA_AT: {
          if (PRINT_INFORMATION) printf("initStrategyLibPatternSep(initPatternSepUndefDataAt(");
          struct PatternExpr *addr = Get_Expr_expr(expr->d.UNDEF_DATA_AT.addr,env);
          if (PRINT_INFORMATION) printf(",");
          if (PRINT_INFORMATION) PatternCTypePrint(expr->d.UNDEF_DATA_AT.type);
          ret = initStrategyLibPatternSep(
                            initPatternSepUndefDataAt(addr, PatternCTypeDeepCopy(expr->d.UNDEF_DATA_AT.type))
                        );
          if (PRINT_INFORMATION) printf("))");
          break;
        }
        default:
            fprintf(stderr,"Invalid type for LibPattern(exprType: %d)\n",expr->t);
            errorGenerated = true;
            return NULL;
    }
    return ret;
}

struct StrategyLibPattern * Get_Expr_BinOP(struct lang_expr * expr,struct environment * env){
    if (errorGenerated) return NULL;
    struct StrategyLibPattern * ret = NULL;
    switch(expr->d.BINOP.op){
        struct PatternExpr *left;
        struct PatternExpr *right;
        case lang_T_EQ:{
            if(PRINT_INFORMATION)printf("initStrategyLibPatternProp(initPatternPropComp(");
            left = Get_Expr_expr(expr->d.BINOP.left,env);
            if (PRINT_INFORMATION) printf("==");
            right = Get_Expr_expr(expr->d.BINOP.right,env);
            ret = initStrategyLibPatternProp(initPatternPropComp(PROP_EQ, left, right));
            if(PRINT_INFORMATION)printf("))");
            break;
        }
        case lang_T_NEQ:{
            if(PRINT_INFORMATION)printf("initStrategyLibPatternProp(initPatternPropComp(");
            left = Get_Expr_expr(expr->d.BINOP.left,env);
            if (PRINT_INFORMATION) printf("!=");
            right = Get_Expr_expr(expr->d.BINOP.right,env);
            ret = initStrategyLibPatternProp(initPatternPropComp(PROP_NEQ, left, right));
            if(PRINT_INFORMATION)printf("))");
            break;
        }
        case lang_T_LE:{
            if(PRINT_INFORMATION)printf("initStrategyLibPatternProp(initPatternPropComp(");
            left = Get_Expr_expr(expr->d.BINOP.left,env);
            if (PRINT_INFORMATION) printf("<=");
            right = Get_Expr_expr(expr->d.BINOP.right,env);
            ret = initStrategyLibPatternProp(initPatternPropComp(PROP_LE, left, right));
            if(PRINT_INFORMATION)printf("))");
            break;
        }
        case lang_T_GE:{
            if(PRINT_INFORMATION)printf("initStrategyLibPatternProp(initPatternPropComp(");
            left = Get_Expr_expr(expr->d.BINOP.left,env);
            if (PRINT_INFORMATION) printf(">=");
            right = Get_Expr_expr(expr->d.BINOP.right,env);
            ret = initStrategyLibPatternProp(initPatternPropComp(PROP_GE, left, right));
            if(PRINT_INFORMATION)printf("))");
            break;
        }
        case lang_T_LT:{
            if(PRINT_INFORMATION)printf("initStrategyLibPatternProp(initPatternPropComp(");
            left = Get_Expr_expr(expr->d.BINOP.left,env);
            if (PRINT_INFORMATION) printf("<");
            right = Get_Expr_expr(expr->d.BINOP.right,env);
            ret = initStrategyLibPatternProp(initPatternPropComp(PROP_LT, left, right));
            if(PRINT_INFORMATION)printf("))");
            break;
        }
        case lang_T_GT:{
            if(PRINT_INFORMATION)printf("initStrategyLibPatternProp(initPatternPropComp(");
            left = Get_Expr_expr(expr->d.BINOP.left,env);
            if (PRINT_INFORMATION) printf(">");
            right = Get_Expr_expr(expr->d.BINOP.right,env);
            ret = initStrategyLibPatternProp(initPatternPropComp(PROP_GT, left, right));
            if(PRINT_INFORMATION)printf("))");
            break;
        }
        case lang_T_FIELDOFPTR:{
            fprintf(stderr,"Invalid case -> for strategy BinOp in Get_Expr_BinOP\n");
            errorGenerated = true;
            return NULL;
        }
        case lang_T_OR:{
            fprintf(stderr,"Invalid case || for strategy BinOp in Get_Expr_BinOP\n");
            errorGenerated = true;
            return NULL;
        }
        default:{
            fprintf(stderr,"This Case Not Support for strategy BinOp in Get_Expr_BinOP\n");
            errorGenerated = true;
            return NULL;
        }
    }

    return ret;
}

struct PatternProp *getPatternProp(struct lang_expr *expr,struct environment * env){
    if (errorGenerated) return NULL;
    struct PatternProp *ret = NULL;
    switch(expr->t){
        case lang_T_BINOP: {
            struct PatternExpr *left;
            struct PatternExpr *right;
            switch(expr->d.BINOP.op){
                case lang_T_EQ:
                    if(PRINT_INFORMATION)printf("initPatternPropComp(");
                    left = Get_Expr_expr(expr->d.BINOP.left,env);
                    if (PRINT_INFORMATION) printf("==");
                    right = Get_Expr_expr(expr->d.BINOP.right,env);
                    ret =  initPatternPropComp(PROP_EQ,left,right);
                    if(PRINT_INFORMATION)printf(")");
                    break;
                case lang_T_NEQ:
                    if(PRINT_INFORMATION)printf("initPatternPropComp(");
                    left = Get_Expr_expr(expr->d.BINOP.left,env);
                    if (PRINT_INFORMATION) printf("!=");
                    right = Get_Expr_expr(expr->d.BINOP.right,env);
                    ret = initPatternPropComp(PROP_NEQ,left,right);
                    if(PRINT_INFORMATION)printf(")");
                    break;
                case lang_T_LT:
                    if(PRINT_INFORMATION)printf("initPatternPropComp(");
                    left = Get_Expr_expr(expr->d.BINOP.left,env);
                    if (PRINT_INFORMATION) printf("<");
                    right = Get_Expr_expr(expr->d.BINOP.right,env);
                    ret = initPatternPropComp(PROP_LT,left,right);
                    if(PRINT_INFORMATION)printf(")");
                    break;
                case lang_T_GT:
                    if(PRINT_INFORMATION)printf("initPatternPropComp(");
                    left = Get_Expr_expr(expr->d.BINOP.left,env);
                    if (PRINT_INFORMATION) printf(">");
                    right = Get_Expr_expr(expr->d.BINOP.right,env);
                    ret = initPatternPropComp(PROP_GT,left,right);
                    if(PRINT_INFORMATION)printf(")");
                    break;
                case lang_T_LE:
                    if(PRINT_INFORMATION)printf("initPatternPropComp(");
                    left = Get_Expr_expr(expr->d.BINOP.left,env);
                    if (PRINT_INFORMATION) printf("<=");
                    right = Get_Expr_expr(expr->d.BINOP.right,env);
                    ret = initPatternPropComp(PROP_LE,left,right);
                    if(PRINT_INFORMATION)printf(")");
                    break;
                case lang_T_GE:
                    if(PRINT_INFORMATION)printf("initPatternPropComp(");
                    left = Get_Expr_expr(expr->d.BINOP.left,env);
                    if (PRINT_INFORMATION) printf(">=");
                    right = Get_Expr_expr(expr->d.BINOP.right,env);    
                    ret = initPatternPropComp(PROP_GE,left,right);
                    if(PRINT_INFORMATION)printf(")");
                    break;
                default:
                    fprintf(stderr,"Invalid type for PatternProp(exprType:BinOp -%d)\n",expr->d.BINOP.op);
                    errorGenerated = true;
                    return NULL;
            }
            break;
        }
        case lang_T_FUNC: {
              FuncExpr_ValidCheck(expr, env);
              find_name(expr->d.FUNC.name, expr->d.FUNC.typeNumber, expr->d.FUNC.paraNumber,env, "getPatternProp");
              int is_pat = charMappingFind(strdup(expr->d.FUNC.name->d.VAR.name), type_mapping) != NULL;
              if (errorGenerated) return NULL;
              if(PRINT_INFORMATION) printf("initPatternProp%sPred(%s,", is_pat ? "Pat" : "", expr->d.FUNC.name->d.VAR.name);
              if (PRINT_INFORMATION) PatternPolyTypeListPrint(expr->d.FUNC.types);
              if (PRINT_INFORMATION) printf(",");
              if (is_pat) {
                ret = initPatternPropPatPred(strdup(expr->d.FUNC.name->d.VAR.name),expr_to_PExprList(expr->d.FUNC.args,env));
              }
              else {
                ret = initPatternPropPred(strdup(expr->d.FUNC.name->d.VAR.name),PatternPolyTypeListDeepCopy(expr->d.FUNC.types),expr_to_PExprList(expr->d.FUNC.args,env));
              }
              if(PRINT_INFORMATION)printf(")");
              break;
        } 
        default:
            fprintf(stderr,"Invalid type:%d for PatternProp in getPatternProp\n", expr->t);
            errorGenerated = true;
            return NULL;
    }
    return ret;
}


struct PatternSep *getPatternSeq(struct lang_expr *expr, struct environment * env){
    if (errorGenerated) return NULL;
    struct PatternSep *ret = NULL;
    switch(expr->t){
        case lang_T_FUNC: {
          // Here is valid checked before   
          int is_pat = charMappingFind(strdup(expr->d.FUNC.name->d.VAR.name), type_mapping) != NULL;
          if(PRINT_INFORMATION) printf("initPatternSep%sPred(%s,", is_pat ? "Pat" : "", expr->d.FUNC.name->d.VAR.name);
          if (PRINT_INFORMATION) PatternPolyTypeListPrint(expr->d.FUNC.types);
          if (PRINT_INFORMATION) printf(",");
          if (is_pat) {
            ret = initPatternSepPatPred(strdup(expr->d.FUNC.name->d.VAR.name),expr_to_PExprList(expr->d.FUNC.args,env));
          }
          else {
            ret = initPatternSepPred(strdup(expr->d.FUNC.name->d.VAR.name),PatternPolyTypeListDeepCopy(expr->d.FUNC.types),expr_to_PExprList(expr->d.FUNC.args,env));
          }
          if(PRINT_INFORMATION)printf(")");
          return ret;
        }
        default:
            fprintf(stderr,"Invalid type for PatternSeq\n");
            errorGenerated = true;
            return NULL;
    }
}

void addStrategyLibRuleNode(struct lang_cmd *rule,char * file,struct environment * env){
    if (exec_info) {
      printf("Start to parse rule %d in file %s\n", rule ->ID, file);
    }
    struct lang_priority_list * prio = rule ->prio ;
    char *scope;
    int priority;
    while (prio != NULL)
    {
      if (prio -> head == NULL) {
        fprintf(stderr,"Empty priority in rule %d in file %s.\n", rule ->ID, file);
        exit(1);
      }
      priority = prio -> head->prio;
      scope = prio -> head->name;
      if (priority >= 20) {
        fprintf(stderr,"Priority value too large:%d in scope %s for rule %d in %s.\n",priority,scope, rule -> ID, file);
        exit(1);
      }
      struct StrategyLibRule *newRule = AST_to_LibRule(rule,file,priority,env);
      if(newRule==NULL || errorGenerated == true){
          fprintf(stderr,"Fail to generate rule %d in file %s.\n", rule -> ID, file);
          exit(1);
      }
      struct StrategyLib *lib = findLibByScope(scope,false);
      addStrategyLibRule(lib, newRule);
      prio = prio -> tail;
    }
}

static char * getFileName(char * file) {
    int len = strlen(file), l = len - 1;
    while (l >= 0 && file[l] != '/') l--;
    ++l;
    int r = l;
    while (r < len && file[r] != '.') r++;
    char * ret = malloc(r - l + 1);
    int i, j;
    for (i = 0, j = l; j < r; i++, j++)
        ret[i] = file[j];
    ret[i] = '\0';
    return ret;
}

void addIncludePath(char *path){
    FILE *p = fopen(path,"r");
    if(p==NULL){
        fprintf(stderr,"Fail to open the file %s.\n", path);
        exit(1);
    }
    if (paths!=NULL){
        StringListFree(paths);
    }
    llin = p;
    lllineno = 0;
    llparse();
    paths = StringListDeepCopy(root->Path);
    lang_print_include_paths(paths);
    fclose(p);
}

void addCustomStrategyLib(char *file,struct environment * env){
    FILE *p = fopen(file,"r");
    char * filename = getFileName(file);
    if (p == NULL) {
        for (struct StringListNode * i = strategy_folder_list->head; i != NULL; i = i->next) {
            char * path = malloc(strlen(i->data) + strlen(filename) + 12);
            sprintf(path, "%s%s.strategies", i->data, filename);
            p = fopen(path, "r");
            if (p != NULL) {
                file = path;
                break;
            }
            free(path);
        }
        if (p == NULL) {
            fprintf(stderr,"Fail to open the file %s.\n",file);
            exit(1);
        }
    } else {
        file = realpath(file, NULL);
    }
    printf("Start to parse strategies file %s\n", filename);
    printf("File Path: %s\n", file);
    llin = p;
    lllineno = 0;
    llparse();
    struct lang_rule_list *ptCmd = root->rules;
    while(ptCmd != NULL){
        addStrategyLibRuleNode(ptCmd->head,filename,env);
        ptCmd = ptCmd->tail;
    }
    printf("Finish parsing strategies file %s\n", filename);
    all_strategy_libs = StringListSnoc(file, all_strategy_libs);
    free(filename);
    fclose(p);
}

struct StringList *getIncludePath(){
    return paths;
}

void freeIncludePath(){
    StringListFree(paths);
}

void initIncludePaths(){
    paths = StringListNil();
}

void checkDSLFiles(char* file){
    FILE *p = fopen(file,"r");
    if(p == NULL){
        fprintf(stderr,"Cannot Open DSLFileLists %s\n", file);
        exit(1);
    }
}
