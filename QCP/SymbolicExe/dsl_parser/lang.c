#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "./lang.h"


struct lang_expr *lang_TConst(unsigned long long value){
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_CONST;
    res -> d.CONST.value = value;
    return res;
}

struct lang_expr *lang_TVar(char *name, struct PatternPolyType * type, enum lang_VarType vt){
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_VAR;
    res -> d.VAR.vt = vt;
    res -> d.VAR.name = name;
    res -> d.VAR.type = type;
    return res;
}

struct lang_expr *lang_TBinOp(enum lang_BinOpType op,struct lang_expr *left,struct lang_expr *right){
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_BINOP;
    res -> d.BINOP.op = op;
    res -> d.BINOP.left = left;
    res -> d.BINOP.right = right;
    return res;
}

struct lang_expr *lang_TUnOp(enum lang_UnOpType op,struct lang_expr *arg){
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_UNOP;
    res -> d.UNOP.op = op;
    res -> d.UNOP.arg = arg;
    return res;
}

struct lang_expr *lang_TFunc(struct lang_expr *name,struct PatternPolyTypeList *types,struct lang_expr_list *args){
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_FUNC;
    res -> d.FUNC.name = name;
    res ->d.FUNC.types = types;
    res -> d.FUNC.args = args;
    int number = 0;
    int typeNumber = 0;
    struct PatternPolyTypeList *ptTypes = types;
    while(ptTypes!=NULL){
        typeNumber = typeNumber + 1;
        ptTypes = ptTypes->next;
    }
    struct lang_expr_list *p = args;
    while(p!=NULL){
        number = number +1;
        p = p->tail;
    }
    res -> d.FUNC.paraNumber = number;
    res -> d.FUNC.typeNumber = typeNumber;
    return res;
}

struct lang_expr *lang_TToken(enum lang_Token tk){
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_TOKEN;
    res -> d.TOKEN.tk = tk;
    return res;
}

struct lang_expr *lang_TSizeof(struct PatternCType *type){
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_SIZEOF;
    res -> d.SIZEOF.type = type;
    return res;
}

struct lang_expr *lang_TArrinx(struct lang_expr *name,struct lang_expr *index){
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_ARRINX;
    res ->d.ARRINX.name = name;
    res ->d.ARRINX.index = index;
    return res;
}

struct lang_expr *lang_TDataAt(struct lang_expr *addr,struct PatternCType *type,struct lang_expr *value) {
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_DATA_AT;
    res -> d.DATA_AT.addr = addr;
    res -> d.DATA_AT.type = type;
    res -> d.DATA_AT.value = value;
    return res;
}

struct lang_expr *lang_TUndefDataAt(struct lang_expr *addr,struct PatternCType *type) {
    struct lang_expr *res = (struct lang_expr *)malloc(sizeof(struct lang_expr));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr.\n");
        exit(0);
    }
    res -> t = lang_T_UNDEF_DATA_AT;
    res -> d.UNDEF_DATA_AT.addr = addr;
    res -> d.UNDEF_DATA_AT.type = type;
    return res;
}

struct lang_cmd *lang_cmd(unsigned int ID,struct lang_priority_list *prio,struct lang_pattern_list *patterns,struct lang_action_list *actions,struct lang_action_list *checks){
    struct lang_cmd *res = (struct lang_cmd *)malloc(sizeof(struct lang_cmd));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_cmd.\n");
        exit(0);
    }
    res -> ID = ID;
    res -> prio = prio;
    res -> patterns = patterns;
    res -> actions = actions;
    res -> checks = checks;
    return res;
}

struct lang_pattern *lang_TPattern(struct lang_expr *expr, int at_number) {
    struct lang_pattern *res = (struct lang_pattern *)malloc(sizeof(struct lang_pattern));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_pattern.\n");
        exit(0);
    }
    res -> expr = expr;
    res -> t = lang_T_UNKNOWN;
    res -> at_number = at_number;
    return res;
}

struct lang_pattern_list *lang_TPatternList(struct lang_pattern_list *pat_list, enum lang_LEFTRIGHT_Type t) {
   struct lang_pattern_list *cur = pat_list;
   while (cur != NULL) {
      cur -> head -> t = t;
      cur = cur -> tail;
   }
   return pat_list;  
}

struct lang_pattern_list *lang_TPatternListApp(struct lang_pattern_list *a,struct lang_pattern_list *d) {
    if (a == NULL) return d;
    struct lang_pattern_list *res = (struct lang_pattern_list *)malloc(sizeof(struct lang_pattern_list));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_pattern_list.\n");
        exit(0);
    }
    res -> head = a -> head;
    res -> tail = lang_TPatternListApp(a -> tail, d);
    return res;

}

struct lang_pattern_list *lang_PTLNil() { return NULL; } 

struct lang_pattern_list *lang_PTLCons(struct lang_pattern *a,struct lang_pattern_list *d) {
    struct lang_pattern_list *res = (struct lang_pattern_list *)malloc(sizeof(struct lang_pattern_list));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_pattern_list.\n");
        exit(0);
    }
    res -> head = a;
    res -> tail = d;
    return res;
}

struct lang_priority *lang_PR(char *name,int prio) {
    struct lang_priority *res = (struct lang_priority *)malloc(sizeof(struct lang_priority));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_priority.\n");
        exit(0);
    }
    res -> name = name;
    res -> prio = prio;
    return res;
}

struct lang_priority_list *lang_PRNil() { return NULL; }

struct lang_priority_list *lang_PRCons(struct lang_priority *a,struct lang_priority_list *d) {
    struct lang_priority_list *res = (struct lang_priority_list *)malloc(sizeof(struct lang_priority_list));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_priority_list.\n");
        exit(0);
    }
    res -> head = a;
    res -> tail = d;
    return res;

}

struct lang_action *lang_TAction(char *name,struct lang_expr *arg){
    struct lang_action *res = (struct lang_action *)malloc(sizeof(struct lang_action));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_action.\n");
        exit(0);
    }
    res -> name = name;
    res -> arg = arg;
    return res;
}

struct lang_action_list *lang_ALNil(){return NULL;}

struct lang_action_list *lang_ALCons(struct lang_action *a,struct lang_action_list *d){
    struct lang_action_list *res = (struct lang_action_list *)malloc(sizeof(struct lang_action_list));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_action_list.\n");
        exit(0);
    }
    res -> head = a;
    res -> tail = d;
    return res;
}

struct lang_expr_list *lang_PLNil(){return NULL;}

struct lang_expr_list *lang_PLCons(struct lang_expr *a,struct lang_expr_list *d){
    struct lang_expr_list *res = (struct lang_expr_list *)malloc(sizeof(struct lang_expr_list));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_expr_list.\n");
        exit(0);
    }
    res -> head = a;
    res -> tail = d;
    return res;   
}

struct lang_rule_list *lang_RLNil(){return NULL;}

struct lang_rule_list *lang_RLCons(struct lang_cmd *a,struct lang_rule_list *d){
    struct lang_rule_list *res = (struct lang_rule_list *)malloc(sizeof(struct lang_rule_list));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_rule_list.\n");
        exit(0);
    }
    res -> head = a;
    res -> tail = d;
    return res;
}

struct lang_rule_file *lang_RF(struct StringList *include_paths,struct lang_rule_list *rules){
    struct lang_rule_file *res = (struct lang_rule_file*)malloc(sizeof(struct lang_rule_file));
    if (res == NULL) {
        fprintf(stderr, "Failure in malloc lang_rule_file.\n");
        exit(0);
    }
    res->Path = include_paths;
    res->rules = rules;
    return res;
}

void lang_print_BinOp(enum lang_BinOpType op){
    switch(op){
    case lang_T_EQ:  printf(" == ");break;
    case lang_T_NEQ: printf(" != ");break;
    case lang_T_LE:  printf(" <= ");break;
    case lang_T_GE:  printf(" >= ");break;
    case lang_T_LT:  printf(" < ");break;
    case lang_T_GT:  printf(" > ");break;
    case lang_T_OR:  printf(" || ");break;
    case lang_T_FIELDOFPTR:  printf(" -> ");break;
    case lang_T_FIELDOF:  printf(" . ");break;
    case lang_T_ADD: printf(" + ");break;
    case lang_T_SUB: printf(" - ");break;
    case lang_T_MUL: printf(" * ");break;
    case lang_T_DIV: printf(" / ");break;
    }
}

void lang_print_UnOp(enum lang_UnOpType op){
    switch(op){
    case lang_T_MINUS:   printf("-");break;
    }
}

void lang_print_Token(enum lang_Token tk){
    switch(tk){
    case lang_T_UPPER_NULL:printf("NULL");break;
    case lang_T_LOWER_NULL:printf("null");break;

    case lang_T_I16:printf("I16");break;
    case lang_T_U16:printf("U16");break;
    case lang_T_I32:printf("I32");break;
    case lang_T_U32:printf("U32");break;
    case lang_T_I64:printf("I64");break;
    case lang_T_U64:printf("U64");break;
    case lang_T_I8:printf("I8");break;
    case lang_T_U8:printf("U8");break;
    }
}


void lang_print_expr(struct lang_expr *e){
    switch(e->t){
    case lang_T_CONST:
        printf("CONST(%llu)",e->d.CONST.value);
        break;
    case lang_T_VAR:
        switch(e->d.VAR.vt){
            case NORMAL_VAR:
                printf("NormalVAR(%s : ",e->d.VAR.name);
                PatternPolyTypePrint(stdout, e->d.VAR.type);
                printf(")");
                break;
            case EXISTS_VAR:
                printf("ExistsVAR(%s : ",e->d.VAR.name);
                PatternPolyTypePrint(stdout, e->d.VAR.type);
                printf(")");
                break;
            case ATOM_VAR:
                printf("AtomVAR(%s : ",e->d.VAR.name);
                PatternPolyTypePrint(stdout, e->d.VAR.type);
                printf(")");
                break;
            case PATTERN_VAR:
                printf("PatternVAR(%s : ",e->d.VAR.name);
                PatternPolyTypePrint(stdout, e->d.VAR.type);
                printf(")");
                break;
        }
        break;
    case lang_T_BINOP:
        printf("(");
        lang_print_expr(e->d.BINOP.left);
        lang_print_BinOp(e->d.BINOP.op);
        lang_print_expr(e->d.BINOP.right);
        printf(")");
        break;
    case lang_T_UNOP:
        printf("(");
        lang_print_UnOp(e->d.UNOP.op);
        lang_print_expr(e->d.UNOP.arg);
        printf(")");
        break;
    case lang_T_FUNC:
        lang_print_expr(e->d.FUNC.name);
        printf("(");
        PatternPolyTypeListPrint(e->d.FUNC.types);
        lang_print_exprs(e->d.FUNC.args);
        printf(",number of types:%d",e->d.FUNC.typeNumber);
        printf(",number of paras:%d",e->d.FUNC.paraNumber);
        printf("))");
        break;
    case lang_T_TOKEN:
        lang_print_Token(e->d.TOKEN.tk);
        break;
    case lang_T_ARRINX:
        lang_print_expr(e->d.ARRINX.name);
        printf("[");
        lang_print_expr(e->d.ARRINX.index);
        printf("]");
        break;
    case lang_T_SIZEOF:
        printf("SIZEOF(");
        PatternCTypePrint(e->d.SIZEOF.type);
        printf(")");
        break;
    case lang_T_DATA_AT:
        printf("DATA_AT(");
        lang_print_expr(e->d.DATA_AT.addr);
        printf(",");
        PatternCTypePrint(e->d.DATA_AT.type);
        printf(",");
        lang_print_expr(e->d.DATA_AT.value);
        printf(")");
        break;
    case lang_T_UNDEF_DATA_AT:
        printf("UNDEF_DATA_AT(");
        lang_print_expr(e->d.UNDEF_DATA_AT.addr);
        printf(",");
        PatternCTypePrint(e->d.UNDEF_DATA_AT.type);
        printf(")");
        break;
    default :
        printf("Unknown expr type\n");
        break;
    }
}

void lang_print_action(struct lang_action *act){
    printf("(%s(",act->name);
    lang_print_expr(act->arg);
    printf("))");
}

void lang_print_pattern(struct lang_pattern *p) {
    switch (p->t) {
      case lang_T_LEFT:
        printf("LEFT(");
        break;
      case lang_T_RIGHT:
        printf("RIGHT(");
        break;
      case lang_T_UNKNOWN:
        printf("UNKNOWN(");
        break;
    }
    lang_print_expr(p->expr);
    printf("at %d)", p->at_number);
}


void lang_print_patterns(struct lang_pattern_list *ps) {
    struct lang_pattern_list *ptrP = ps;
    printf("pattern_list(");
    while (ptrP != NULL) {
        printf("\n");
        lang_print_pattern(ptrP->head);
        ptrP = ptrP->tail;
    }
    printf("\n )");

}

void lang_print_priority(struct lang_priority *p) {
    printf("priority(%s,%d)", p->name, p->prio);
}

void lang_print_priorities(struct lang_priority_list *ps) {
    struct lang_priority_list *ptrP = ps;
    printf("priority_list(");
    while (ptrP != NULL) {
        printf("\n");
        lang_print_priority(ptrP->head);
        ptrP = ptrP->tail;
    }
    printf("\n )");
}

void lang_print_cmd(struct lang_cmd *c) {
    printf("cmd(ID:%u\n", c->ID);
    lang_print_priorities(c->prio);
    lang_print_patterns(c->patterns);
    lang_print_actions(c->actions);
    lang_print_actions(c->checks);
}

void lang_print_exprs(struct lang_expr_list *e){
    struct lang_expr_list *ptrE = e;
    printf("expr_list{");
    while(ptrE!=NULL){
        printf("\n");
        lang_print_expr(ptrE->head);
        ptrE = ptrE->tail;
    }
    printf("\n }");
}

void lang_print_actions(struct lang_action_list *acts){
    struct lang_action_list *ptActs = acts;
    printf("action_list(\n");
    while(ptActs!=NULL){
        lang_print_action(ptActs->head);
        printf("\n ");
        ptActs = ptActs->tail;
    }
    printf(")\n");
}

void lang_print_rules(struct lang_rule_list *rules){
    struct lang_rule_list *ptRules = rules;
    printf("rule_lists:\n");
    printf("-----------------------------------------\n");
    while(ptRules!=NULL){
        lang_print_cmd(ptRules->head);
        printf("-----------------------------------------\n");
        ptRules = ptRules->tail;
    }
    printf("\n");
}

void lang_print_include_paths(struct StringList *path){
    struct StringListNode *node = path->head;
    while(node!=NULL){
        if(node->data!=NULL) {
          if (exec_info) {
            printf("add path:%s \n",node->data);
          }
        }
        else {
          fprintf(stderr, "Empty include path in File %s.\n", __FILE__);
          exit(0);
        }
        node = node ->next;
    }
}

char * str_to_lower (char *name) {
   char *ret = strdup(name);
    for (int i = 0; ret[i]; i++) {
      if (ret[i] >= 'A' && ret[i] <= 'Z') 
        ret[i] = ret[i] + 32;
    }
    return ret;
}

struct PatternPolyType * AlterPatternPolyTypeVar(char *name) {
  if (!strcmp(str_to_lower(name),"z")) return initPatternPolyTypeConst("Z");
  if (!strcmp(str_to_lower(name), "asrt")) return initPatternPolyTypeConst("Assertion");
  if (!strcmp(str_to_lower(name), "assertion")) return initPatternPolyTypeConst("Assertion");
  if (!strcmp(str_to_lower(name), "prop")) return initPatternPolyTypeConst("Prop");
  if (!strcmp(str_to_lower(name), "bool")) return initPatternPolyTypeConst("Bool");
  return initPatternPolyTypeVar(name);
}

struct PatternPolyType * AlterPatternPolyTypeConst(char *name) {
  if (!strcmp(str_to_lower(name),"z")) return initPatternPolyTypeConst("Z");
  if (!strcmp(str_to_lower(name), "asrt")) return initPatternPolyTypeConst("Assertion");
  if (!strcmp(str_to_lower(name), "assertion")) return initPatternPolyTypeConst("Assertion");
  if (!strcmp(str_to_lower(name), "prop")) return initPatternPolyTypeConst("Prop");
  if (!strcmp(str_to_lower(name), "bool")) return initPatternPolyTypeConst("Bool");
  return initPatternPolyTypeConst(name);
}

char *lang_new_str(char *str, int len) {
  int i = 0, j = 0;
  for (; j < len; ++i, ++j) {
    if (str[j] == ':')
    {
      j++;
    }
  }
  int real_len = i;
  char *res = (char *)malloc(sizeof(char) * (real_len + 1));
  if (res == NULL) {
    fprintf(stderr, "Failure in malloc.\n");
    exit(0);
  }
  i = 0;
  j = 0;
  for (; j < len; ++i, ++j) {
    if (str[j] == ':')
    {
      res[i] = '.';
      j++;
    }
    else res[i] = str[j];
  }
  res[i] = '\0';
  return res;
}

unsigned long long lang_build_nat(char *c, int len, int Signed, int type) {
  unsigned long long s = 0;
  int i = 0;
  for (i = 0; i < len; ++i) {
    /* 18446744073709551615 */
    if (s > 1844674407370955161ull || (s == 1844674407370955161ull && c[i] - '0' > 5)) {
      fprintf(stderr,"Integer literal is too large");
      exit(0);
    }
    s = s * 10 + (c[i] - '0');
  }
  if (Signed == 0 && type == 0 && s > 2147483648u) {
    fprintf(stderr,"Integer literal is too large for signed int");
    exit(0);
  }
  if (Signed == 0 && type == 1 && s > 9223372036854775808ull) {
    fprintf(stderr,"Integer literal is too large for signed long long");
    exit(0);
  }
  if (Signed == 1 && type == 0 && s > 4294967295u) {
    fprintf(stderr,"Integer literal is too large for unsigned int");
    exit(0);
  }
  if (Signed == 1 && type == 1 && s > 18446744073709551615ull) {
    fprintf(stderr,"Integer literal is too large for unsigned long long");
    exit(0);
  }
  return s;
}

unsigned int lang_build_hex(char *c, int len) {
  unsigned int s = 0;
  int i = 0;
  for (i = 0; i < len; ++i) {
    /* 4294967295 */
    if (s > 268435455) {
      fprintf(stderr, "Integer literal is too large.\n");
      exit(0);
    }
    s *= 16;
    if ('0' <= c[i] && c[i] <= '9')
      s += c[i] - '0';
    else if ('a' <= c[i] && c[i] <= 'f')
      s += c[i] - 'a' + 10;
    else
      s += c[i] - 'A' + 10;
  }
  return s;
}

struct lang_expr *lang_exprDeepCopy(struct lang_expr *e) {
  if (e == NULL)
    return NULL;
  switch (e -> t) {
    case lang_T_CONST:
      return lang_TConst(e->d.CONST.value);
    case lang_T_VAR:
      return lang_TVar(strdup(e->d.VAR.name), PatternPolyTypeDeepCopy(e->d.VAR.type), e->d.VAR.vt);
    case lang_T_BINOP:
      return lang_TBinOp(e->d.BINOP.op, lang_exprDeepCopy(e->d.BINOP.left), lang_exprDeepCopy(e->d.BINOP.right));
    case lang_T_UNOP:
      return lang_TUnOp(e->d.UNOP.op, lang_exprDeepCopy(e->d.UNOP.arg));
    case lang_T_FUNC:
      return lang_TFunc(lang_exprDeepCopy(e->d.FUNC.name), PatternPolyTypeListDeepCopy(e->d.FUNC.types), lang_PLDeepCopy(e->d.FUNC.args));
    case lang_T_TOKEN:
      return lang_TToken(e->d.TOKEN.tk);
    case lang_T_ARRINX:
      return lang_TArrinx(lang_exprDeepCopy(e->d.ARRINX.name), lang_exprDeepCopy(e->d.ARRINX.index));
    case lang_T_SIZEOF:
      return lang_TSizeof(PatternCTypeDeepCopy(e->d.SIZEOF.type));
    case lang_T_DATA_AT:
      return lang_TDataAt(lang_exprDeepCopy(e->d.DATA_AT.addr), PatternCTypeDeepCopy(e->d.DATA_AT.type), lang_exprDeepCopy(e->d.DATA_AT.value));
    case lang_T_UNDEF_DATA_AT:
      return lang_TUndefDataAt(lang_exprDeepCopy(e->d.UNDEF_DATA_AT.addr), PatternCTypeDeepCopy(e->d.UNDEF_DATA_AT.type));
    default :
        printf("Unknown expr type\n");
        break;
  }
  printf("unexpected deep copy case\n");
  exit(1);
}
struct lang_expr_list *lang_PLDeepCopy(struct lang_expr_list *e) {
  if (e == NULL)
    return NULL;
  return lang_PLCons(lang_exprDeepCopy(e->head), lang_PLDeepCopy(e->tail));
}

void free_lang_expr(struct lang_expr *e) {
  if (e == NULL)
    return;
  switch (e->t) {
    case lang_T_VAR: {
     // free(e->d.VAR.name);
      PatternPolyTypeFree(e->d.VAR.type);
    }
    case lang_T_BINOP: {
      free_lang_expr(e->d.BINOP.left);
      free_lang_expr(e->d.BINOP.right);
      break;
    }
    case lang_T_UNOP: {
      free_lang_expr(e->d.UNOP.arg);
      break;
    }
    case lang_T_FUNC: {
      free_lang_expr(e->d.FUNC.name);
      PatternPolyTypeListFree(e->d.FUNC.types);
      free_lang_expr_list(e->d.FUNC.args);
      break;
    }
    case lang_T_ARRINX: {
      free_lang_expr(e->d.ARRINX.name);
      free_lang_expr(e->d.ARRINX.index);
      break;
    }
    case lang_T_SIZEOF: {
      PatternCTypeFree(e->d.SIZEOF.type);
      break;
    }
    case lang_T_DATA_AT: {
      free_lang_expr(e->d.DATA_AT.addr);
      PatternCTypeFree(e->d.DATA_AT.type);
      free_lang_expr(e->d.DATA_AT.value);
      break;
    }
    case lang_T_UNDEF_DATA_AT: {
      free_lang_expr(e->d.UNDEF_DATA_AT.addr);
      PatternCTypeFree(e->d.UNDEF_DATA_AT.type);
      break;
    }
    default :
      break;
  }
  free(e);
}

void free_lang_expr_list(struct lang_expr_list *el) {
  if (el == NULL)
    return;
  free_lang_expr(el->head);
  free_lang_expr_list(el->tail);
  free(el);
}