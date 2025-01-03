#include "env.h"
#include "lang.h"
#include "utils.h"
#include "../SymExec/Utility/InnerAsrtPrinter.h"

#define create(name, ty)                                         \
  struct ty *name = (struct ty *)malloc(sizeof(struct ty));      \
  if (name == NULL) {                                            \
    fprintf(stderr, "Failure in malloc.\n");                     \
    exit(0);                                                     \
  }

struct qvar_list *qvar_list_cons(struct atype *qv, struct qvar_list *next) {
  create(res, qvar_list);
  ASSIGN_ATYPE(res->qv, qv);
  res->next = next;
  return res;
}

void free_qvar_list(struct qvar_list *qv) {
  if (qv == NULL)
    return;
  free_atype(qv->qv);
  struct qvar_list *n = qv->next;
  free(qv);
  free_qvar_list(n);
}

struct qvar_list *clone_qvar_list(struct qvar_list *qv) {
  if (qv == NULL)
    return NULL;
  return qvar_list_cons(qv->qv, clone_qvar_list(qv->next));
}

struct type *TBasic(enum BasicType ty) {
  create(res, type);
  res->refcnt = 0;
  res->t = T_BASIC;
  res->d.BASIC.ty = ty;
  return res;
}

struct type *TStruct(struct struct_union_info *info) {
  create(res, type);
  res->refcnt = 0;
  res->t = T_STRUCT;
  res->d.STRUCT.info = info;
  return res;
}

struct type *TUnion(struct struct_union_info *info) {
  create(res, type);
  res->refcnt = 0;
  res->t = T_UNION;
  res->d.UNION.info = info;
  return res;
}

struct type *TEnum(struct enum_info *info) {
  create(res, type);
  res->refcnt = 0;
  res->t = T_ENUM;
  res->d.ENUM.info = info;
  return res;
}

struct type *TPtr(struct type *ty) {
  create(res, type);
  res->refcnt = 0;
  res->t = T_PTR;
  ASSIGN_TYPE(res->d.PTR.ty, ty);
  return res;
}

struct type *TArray(struct type *ty, unsigned int size) {
  create(res, type);
  res->refcnt = 0;
  res->t = T_ARRAY;
  ASSIGN_TYPE(res->d.ARRAY.ty, ty);
  res->d.ARRAY.size = size;
  return res;
}

struct type *TFunction(struct type *ret, struct type_list *param) {
  create(res, type);
  res->refcnt = 0;
  res->t = T_FUNCTION;
  ASSIGN_TYPE(res->d.FUNCTION.ret, ret);
  res->d.FUNCTION.param = param;
  return res;
}

struct type *TTypeAlias(struct type_info *info) {
  create(res, type);
  res->refcnt = 0;
  res->t = T_TYPE_ALIAS;
  res->d.TYPE_ALIAS.info = info;
  return res;
}

struct type_list *TLNil() {
  return NULL;
}

struct type_list *TLCons(struct type *hd, struct type_list *tl) {
  create(res, type_list);
  res->hd = hd;
  res->tl = tl;
  hd->refcnt += 1;
  return res;
}

struct expr *TConst(unsigned long long value) {
  create(res, expr);
  res->t = T_CONST;
  res->d.CONST.value = value;
  return res;
}

struct expr *TString(char *string) {
  create(res, expr);
  res->t = T_STRING;
  res->d.STRING.str = string;
  return res;
}

struct expr *TVar(struct prog_var_info *info) {
  create(res, expr);
  res->t = T_VAR;
  res->d.VAR.info = info;
  return res;
}

struct expr *TBinop(enum BinOpType op, struct expr *left, struct expr *right) {
  create(res, expr);
  res->t = T_BINOP;
  res->d.BINOP.op = op;
  res->d.BINOP.left = left;
  res->d.BINOP.right = right;
  return res;
}

struct expr *TUnop(enum UnOpType op, struct expr *arg) {
  create(res, expr);
  res->t = T_UNOP;
  res->d.UNOP.arg = arg;
  res->d.UNOP.op = op;
  return res;
}

struct expr *TDeref(struct expr *arg) {
  create(res, expr);
  res->t = T_DEREF;
  res->d.DEREF.arg = arg;
  return res;
}

struct expr *TAddress(struct expr *arg) {
  create(res, expr);
  res->t = T_ADDRES;
  res->d.ADDRES.arg = arg;
  return res;
}

struct expr *TCast(struct type *ty, struct expr *arg) {
  create(res, expr);
  res->t = T_CAST;
  res->d.CAST.arg = arg;
  ASSIGN_TYPE(res->d.CAST.ty, ty);
  return res;
}

struct expr *TCall(struct expr *func, struct expr_list *args, struct virt_arg *vargs) {
  create(res, expr);
  res->t = T_CALL;
  res->d.CALL.args = args;
  res->d.CALL.func = func;
  res->d.CALL.vargs = vargs;
  return res;
}

struct expr *TSizeofType(struct type *ty) {
  create(res, expr);
  res->t = T_SIZEOFTYPE;
  ASSIGN_TYPE(res->d.SIZEOFTYPE.ty, ty);
  return res;
}

struct expr *TIndex(struct expr *arg, struct expr *pos) {
  create(res, expr);
  res->t = T_INDEX;
  res->d.INDEX.arg = arg;
  res->d.INDEX.pos = pos;
  return res;
}

struct expr *TFieldof(struct expr *arg, struct field_info *field) {
  create(res, expr);
  res->t = T_FIELDOF;
  res->d.FIELDOF.arg = arg;
  res->d.FIELDOF.field = field;
  return res;
}

struct expr *TFieldofptr(struct expr *arg, struct field_info *field) {
  create(res, expr);
  res->t = T_FIELDOFPTR;
  res->d.FIELDOFPTR.arg = arg;
  res->d.FIELDOFPTR.field = field;
  return res;
}

struct expr *TEnumLit(struct enumerator_info *info) {
  create(res, expr);
  res->t = T_ENUMLIT;
  res->d.ENUMLIT.info = info;
  return res;
}

struct expr *TCondition(struct expr *cond, struct expr *true, struct expr *false) {
  create(res, expr);
  res->t = T_CONDITION;
  res->d.CONDITION.cond = cond;
  res->d.CONDITION.btrue = true;
  res->d.CONDITION.bfalse = false;
  return res;
}

struct expr_list *ELNil() { return NULL; }
struct expr_list *ELCons(struct expr *head, struct expr_list *tail) {
  create(res, expr_list);
  res->head = head;
  res->tail = tail;
  return res;
}

struct simple_cmd *TComputation(struct expr *arg) {
  create(res, simple_cmd);
  res->t = T_COMPUTATION;
  res->d.COMPUTATION.arg = arg;
  return res;
}

struct simple_cmd *TAsgn(enum AssignType op, struct expr *left,
                         struct expr *right) {
  create(res, simple_cmd) res->t = T_ASGN;
  res->d.ASGN.left = left;
  res->d.ASGN.op = op;
  res->d.ASGN.right = right;
  return res;
}

struct simple_cmd *TIncDec(enum IncDecType op, struct expr *arg) {
  create(res, simple_cmd);
  res->t = T_INCDEC;
  res->d.INCDEC.arg = arg;
  res->d.INCDEC.op = op;
  return res;
}

struct cmd *TVarDecl(struct prog_var_info *info) {
  create(res, cmd);
  res->t = T_VARDECL;
  res->d.VARDECL.info = info;
  return res;
}

struct cmd *TTypedef(struct type_info *info) {
  create(res, cmd);
  res->t = T_TYPEDEF;
  res->d.TYPEDEF.info = info;
  return res;
}

struct cmd *TSimple(struct simple_cmd *scmd) {
  create(res, cmd);
  res->t = T_SIMPLE;
  res->d.SIMPLE.scmd = scmd;
  return res;
}

struct cmd *TSeq(struct cmd *left, struct cmd *right) {
  create(res, cmd);
  res->t = T_SEQ;
  res->d.SEQ.left = left;
  res->d.SEQ.right = right;
  return res;
}

struct cmd *TIf(struct expr *cond, struct cmd *left,
                struct cmd *right) {
  create(res, cmd);
  res->t = T_IF;
  res->d.IF.cond = cond;
  res->d.IF.left = left;
  res->d.IF.right = right;
  return res;
}

struct cmd *TSwitch(struct expr *cond, struct Case_list *body) {
  create(res, cmd);
  res->t = T_SWITCH;
  res->d.SWITCH.cond = cond;
  res->d.SWITCH.body = body;
  return res;
}

struct cmd *TWhile(struct AsrtList *inv, int is_partial, struct expr *cond,
                   struct cmd *body) {
  create(res, cmd);
  res->t = T_WHILE;
  res->d.WHILE.inv = inv;
  res->d.WHILE.is_partial = is_partial;
  res->d.WHILE.cond = cond;
  res->d.WHILE.body = body;
  return res;
}

struct cmd *TDoWhile(struct AsrtList *inv, int is_partial, struct expr *cond,
                     struct cmd *body) {
  create(res, cmd);
  res->t = T_DOWHILE;
  res->d.DOWHILE.inv = inv;
  res->d.DOWHILE.is_partial = is_partial;
  res->d.DOWHILE.cond = cond;
  res->d.DOWHILE.body = body;
  return res;
}

struct cmd *TFor(struct AsrtList *inv, int is_partial, struct simple_cmd *init,
                 struct expr *cond, struct simple_cmd *incr,
                 struct cmd *body) {
  create(res, cmd);
  res->t = T_FOR;
  res->d.FOR.inv = inv;
  res->d.FOR.is_partial = is_partial;
  res->d.FOR.init = init;
  res->d.FOR.cond = cond;
  res->d.FOR.incr = incr;
  res->d.FOR.body = body;
  return res;
}

struct cmd *TBreak() {
  create(res, cmd);
  res->t = T_BREAK;
  return res;
}

struct cmd *TContinue() {
  create(res, cmd);
  res->t = T_CONTINUE;
  return res;
}

struct cmd *TReturn(struct expr *arg) {
  create(res, cmd);
  res->t = T_RETURN;
  res->d.RETURN.arg = arg;
  return res;
}

struct cmd *TComment(struct AsrtList *asrt, int is_partial, char *mark) {
  create(res, cmd);
  res->t = T_COMMENT;
  res->d.COMMENT.asrt = asrt;
  res->d.COMMENT.is_partial = is_partial;
  res->d.COMMENT.mark = mark;
  return res;
}

struct cmd *TPartialComment(struct func_spec *specs) {
  create(res, cmd);
  res->t = T_PARTIAL_COMMENT;
  res->d.PARTIAL_COMMENT.specs = specs;
  return res;
}

struct cmd *TProof(char *proof) {
  create(res, cmd);
  res->t = T_PROOF;
  res->d.PROOF.proof = proof;
  return res;
}

struct cmd *TDoStrategy(char *name) {
  create(res, cmd);
  res->t = T_DO_STRATEGY;
  res->d.DO_STRATEGY.name = name;
  return res;
}

struct cmd *TSkip() {
  create(res, cmd);
  res->t = T_SKIP;
  return res;
}

struct cmd *TBlock(struct cmd *cmd) {
  create(res, cmd);
  res->t = T_BLOCK;
  res->d.BLOCK.cmd = cmd;
  return res;
}

struct cmd *TStructDef(struct struct_union_info *info) {
  create(res, cmd);
  res->t = T_STRUCT_DEF;
  res->d.STRUCT_DEF.info = info;
  return res;
}

struct cmd *TStructDec(struct struct_union_info *info) {
  create(res, cmd);
  res->t = T_STRUCT_DEC;
  res->d.STRUCT_DEC.info = info;
  return res;
}

struct cmd *TUnionDef(struct struct_union_info *info) {
  create(res, cmd);
  res->t = T_UNION_DEF;
  res->d.UNION_DEF.info = info;
  return res;
}

struct cmd *TUnionDec(struct struct_union_info *info) {
  create(res, cmd);
  res->t = T_UNION_DEC;
  res->d.UNION_DEC.info = info;
  return res;
}

struct cmd *TEnumDef(struct enum_info *info) {
  create(res, cmd);
  res->t = T_ENUM_DEF;
  res->d.ENUM_DEF.info = info;
  return res;
}

struct cmd *TEnumDec(struct enum_info *info) {
  create(res, cmd);
  res->t = T_ENUM_DEC;
  res->d.ENUM_DEC.info = info;
  return res;
}

struct Case *TCase(struct expr *cond, struct cmd *body) {
  create(res, Case);
  res->t = T_CASE;
  res->d.CASE.cond = cond;
  res->d.CASE.body = body;
  return res;
}

struct Case *TDefault(struct cmd *body) {
  create(res, Case);
  res->t = T_DEFAULT;
  res->d.DEFAULT.body = body;
  return res;
}

struct Case_list *CLNil() { return NULL; }

struct Case_list *CLCons(struct Case *head, struct Case_list *tail) {
  create(res, Case_list);
  res->head = head;
  res->tail = tail;
  return res;
}

#undef create

struct func_spec * func_spec_deep_copy(struct func_spec *spec) {
  if (spec == NULL) return NULL;
  struct func_spec * res = (struct func_spec *)malloc(sizeof(struct func_spec));
  if (res == NULL) {
    fprintf(stderr, "Failure in malloc.\n");
    exit(0);
  }
  res->qv = clone_qvar_list(spec->qv);
  res->pre = AsrtListDeepCopy(spec->pre);
  res->post = AsrtListDeepCopy(spec->post);
  res->with = ExistListDeepCopy(spec->with);
  res->witht = ExistListDeepCopy(spec->witht);
  res->__return = ExprValDeepCopy(spec->__return);
  if (spec->name != NULL) {
    res->name = malloc(strlen(spec->name) + 1);
    strcpy(res->name, spec->name);
  } else {
    res->name = NULL;
  }
  if (spec->derived_by != NULL) {
    res->derived_by = malloc(strlen(spec->derived_by) + 1);
    strcpy(res->derived_by, spec->derived_by);
  } else {
    res->derived_by = NULL;
  }
  return res;
}

void func_spec_free(struct func_spec *spec) {
  if (spec == NULL) return;
  free_qvar_list(spec->qv);
  AsrtListFree(spec->pre);
  AsrtListFree(spec->post);
  ExistListFree(spec->with);
  ExistListFree(spec->witht);
  ExprValFree(spec->__return);
  // free(spec->name);
  // free(spec->derived_by);
  free(spec);
}

struct type *type_unalias(struct type *ty) {
  if (ty == NULL)
    return NULL;
  if (ty->t == T_TYPE_ALIAS)
    return type_unalias(ty->d.TYPE_ALIAS.info->type);
  else
    return ty;
}

int type_list_equal(struct type_list *tl1, struct type_list *tl2) {
  if (tl1 == NULL && tl2 == NULL)
    return 1;
  else if (tl1 == NULL || tl2 == NULL)
    return 0;
  else
    return type_equal(tl1->hd, tl2->hd) && type_list_equal(tl1->tl, tl2->tl);
}

int type_size(struct type *t) {
  switch (t->t) {
  case T_BASIC:
    switch (t->d.BASIC.ty) {
    case T_VOID:
    case T_CHAR:
    case T_U8:     return 1;
    case T_SHORT:
    case T_U16:    return 2;
    case T_INT:
    case T_UINT:   return 4;
    case T_INT64:
    case T_UINT64: return 8;
    }
    return 0; // unreachable
  case T_STRUCT:
    return t->d.STRUCT.info->size;
  case T_UNION:
    return t->d.UNION.info->size;
  case T_ENUM:
    return 4;
  case T_PTR:
    return 8;
  case T_ARRAY:
    if (t->d.ARRAY.size == 0)
      return 0;
    return t->d.ARRAY.size * type_size(t->d.ARRAY.ty);
  case T_FUNCTION: {
    assert(0);
    return 0; // unreachable
  }
  case T_TYPE_ALIAS:
    return type_size(t->d.TYPE_ALIAS.info->type);
  }
}

int type_align(struct type *t) {
  switch (t->t) {
  case T_BASIC:
    switch (t->d.BASIC.ty) {
    case T_VOID:
    case T_CHAR:
    case T_U8:     return 1;
    case T_SHORT:
    case T_U16:    return 2;
    case T_INT:
    case T_UINT:   return 4;
    case T_INT64:
    case T_UINT64: return 8;
    }
    return 0; // unreachable
  case T_STRUCT:
    return t->d.STRUCT.info->alignment;
  case T_UNION:
    return t->d.UNION.info->alignment;
  case T_ENUM:
    return 4;
  case T_PTR:
    return 8;
  case T_ARRAY:
    return type_align(t->d.ARRAY.ty);
  case T_FUNCTION: {
    assert(0);
    return 0; // unreachable
  }
  case T_TYPE_ALIAS:
    return type_align(t->d.TYPE_ALIAS.info->type);
  }
}

int type_equal(struct type *t1, struct type *t2) {
  t1 = type_unalias(t1);
  t2 = type_unalias(t2);
  if (t1->t != t2->t)
    return 0;
  switch (t1->t) {
  case T_BASIC:
    return t1->d.BASIC.ty == t2->d.BASIC.ty;
  case T_STRUCT:
    return t1->d.STRUCT.info == t2->d.STRUCT.info;
  case T_UNION:
    return t1->d.UNION.info == t2->d.UNION.info;
  case T_ENUM:
    return t1->d.ENUM.info == t2->d.ENUM.info;
  case T_PTR:
    return type_equal(t1->d.PTR.ty, t2->d.PTR.ty);
  case T_ARRAY:
    return type_equal(t1->d.ARRAY.ty, t2->d.ARRAY.ty) &&
           t1->d.ARRAY.size == t2->d.ARRAY.size;
  case T_FUNCTION:
    return type_equal(t1->d.FUNCTION.ret, t2->d.FUNCTION.ret) &&
           type_list_equal(t1->d.FUNCTION.param, t2->d.FUNCTION.param);
  case T_TYPE_ALIAS:
    assert(0);
  }
}
int type_is_void(struct type *ty) {
  ty = type_unalias(ty);
  return ty->t == T_BASIC && ty->d.BASIC.ty == T_VOID;
}

void free_type_list(struct type_list *tl) {
  if (tl == NULL)
    return;
  struct type_list *tll = tl->tl;
  free_type(tl->hd);
  free(tl);
  free_type_list(tll);
}

void free_type(struct type *ty) {
  if (ty == NULL)
    return;
  ty->refcnt -= 1;
  if (ty->refcnt <= 0) {
    switch (ty->t) {
    case T_BASIC:
    case T_STRUCT:
    case T_UNION:
    case T_ENUM:
    case T_TYPE_ALIAS:
      break;
    case T_PTR:
      free_type(ty->d.PTR.ty);
      break;
    case T_ARRAY:
      free_type(ty->d.ARRAY.ty);
      break;
    case T_FUNCTION:
      free_type(ty->d.FUNCTION.ret);
      free_type_list(ty->d.FUNCTION.param);
      break;
    }
    free(ty);
  }
}

void free_expr(struct expr *e) {
  struct expr_list *el;
  struct expr_list *eln;
  
  switch (e->t) {
  case T_CONST:
  case T_VAR:
    break;
  case T_STRING:
    free(e->d.STRING.str);
    break;
  case T_BINOP:
    free_expr(e->d.BINOP.left);
    free_expr(e->d.BINOP.right);
    break;
  case T_UNOP:
    free_expr(e->d.UNOP.arg);
    break;
  case T_CAST:
    free_type(e->d.CAST.ty);
    free_expr(e->d.CAST.arg);
    break;
  case T_CALL:
    el = e->d.CALL.args;
    if (el == NULL)
      break;
    eln = el->tail;
    while (eln != NULL) {
      free_expr(el->head);
      free(el);
      el = eln;
      eln = eln->tail;
    }
    free_expr(el->head);
    free(el);
    break;
  case T_DEREF:
    free_expr(e->d.DEREF.arg);
    break;
  case T_ADDRES:
    free_expr(e->d.ADDRES.arg);
    break;
  case T_SIZEOFTYPE:
    free_type(e->d.SIZEOFTYPE.ty);
    break;
  case T_INDEX:
    free_expr(e->d.INDEX.arg);
    free_expr(e->d.INDEX.pos);
    break;
  case T_FIELDOF:
    free_expr(e->d.FIELDOF.arg);
    break;
  case T_FIELDOFPTR:
    free_expr(e->d.FIELDOFPTR.arg);
    break;
  case T_ENUMLIT:
    break;
  case T_CONDITION:
    free_expr(e->d.CONDITION.cond);
    free_expr(e->d.CONDITION.btrue);
    free_expr(e->d.CONDITION.bfalse);
    break;
  }
  free_type(e->type);
  free(e);
}

extern void* (*LocalFree)(void *);
void free_spec(struct func_spec *spec) {
  LocalFree = (void *(*)(void *))LocalLinkedHashMapFree;
  ExistListFree(spec->with);
  ExprValFree(spec->__return);
  AsrtListFree(spec->pre);
  AsrtListFree(spec->post);
  free(spec);
}

void print_type_list(struct type_list *param) {
  if (param == NULL)
    return;
  print_type(param->hd, NULL);
  if (param->tl == NULL)
    return;
  printf(", ");
  print_type_list(param->tl);
}

void print_type1(struct type *ty, char *ident) {
  switch (ty->t) {
  case T_PTR:
    printf("(*");
    print_type1(ty->d.PTR.ty, ident);
    printf(")"); break;
  case T_ARRAY:
    printf("(");
    print_type1(ty->d.ARRAY.ty, ident);
    printf("[%u])", ty->d.ARRAY.size);
    break;
  case T_FUNCTION:
    printf("(");
    print_type1(ty->d.FUNCTION.ret, ident);
    printf("(");
    print_type_list(ty->d.FUNCTION.param);
    printf("))");
    break;
  default:
    if (ident != NULL)
      printf("%s", ident);
    break;
  }
}

void free_type_stack(struct type *ty) {
  switch (ty->t) {
  case T_BASIC:
  case T_STRUCT:
  case T_UNION:
  case T_ENUM:
  case T_TYPE_ALIAS:
    break;
  case T_PTR:
    free_type_stack(ty->d.PTR.ty);
    break;
  case T_ARRAY:
    free_type_stack(ty->d.ARRAY.ty);
    break;
  case T_FUNCTION:
    free_type_stack(ty->d.FUNCTION.ret);
    break;
  }
  free(ty);
}

void print_type(struct type *ty, char *ident) {
  struct type *stack = TBasic(T_INT); // dummy

  while (ty->t == T_PTR || ty->t == T_ARRAY || ty->t == T_FUNCTION) {
    switch (ty->t) {
    case T_BASIC:
    case T_STRUCT:
    case T_UNION:
    case T_ENUM:
    case T_TYPE_ALIAS:
      break;
    case T_PTR:
      stack = TPtr(stack);
      ty = ty->d.PTR.ty;
      break;
    case T_ARRAY:
      stack = TArray(stack, ty->d.ARRAY.size);
      ty = ty->d.ARRAY.ty;
      break;
    case T_FUNCTION:
      stack = TFunction(stack, ty->d.FUNCTION.param);
      ty = ty->d.FUNCTION.ret;
      break;
    }
  }

  switch (ty->t) {
  case T_BASIC:
    switch (ty->d.BASIC.ty) {
    case T_VOID:   printf("void"); break;
    case T_CHAR:   printf("char"); break;
    case T_U8:     printf("unsigned char"); break;
    case T_SHORT:  printf("short"); break;
    case T_U16:    printf("unsigned short"); break;
    case T_INT:    printf("int"); break;
    case T_INT64:  printf("long long"); break;
    case T_UINT:   printf("unsigned int"); break;
    case T_UINT64: printf("unsigned long long"); break;
    }
    break;
  case T_STRUCT:      printf("struct %s", ty->d.STRUCT.info->name); break;
  case T_UNION:       printf("struct %s", ty->d.UNION.info->name); break;
  case T_ENUM:        printf("enum %s", ty->d.ENUM.info->name); break;
  case T_TYPE_ALIAS:  printf("%s", ty->d.TYPE_ALIAS.info->name); break;
  case T_PTR: break;
  case T_ARRAY: break;
  case T_FUNCTION: break;
  }
  if (ident != NULL || stack->t != T_BASIC)
    printf(" ");

  print_type1(stack, ident);

  free_type_stack(stack);
}

void print_expr_list(struct expr_list *el, char *sep, struct persistent_env *env) {
  if (el == NULL)
    return;
  else if (el->tail == NULL)
    print_expr(el->head, env);
  else {
    print_expr(el->head, env);
    printf("%s", sep);
    print_expr_list(el->tail, sep, env);
  }
}

void print_heap(struct Assertion *h, int addressable, struct persistent_env *env);

void print_expr(struct expr *e, struct persistent_env* env) {
  switch (e->t) {
  case T_CONST:
    printf("%llu", e->d.CONST.value);
    switch (e->type->d.BASIC.ty) {
    case T_VOID:
    case T_CHAR:
    case T_U8:
    case T_SHORT:
    case T_U16:
      assert(0);
    case T_INT:
      break;
    case T_INT64:
      printf("ll");
      break;
    case T_UINT:
      printf("u");
      break;
    case T_UINT64:
      printf("ull");
      break;
    }
    break;
  case T_STRING:
    printf("\"");
    print_escaped_str(e->d.STRING.str);
    printf("\"");
    break;
  case T_VAR:
    printf("%s", e->d.VAR.info->name);
    /* printf(".%u", e->d.VAR.id); */
    break;
  case T_BINOP:
    printf("(");
    print_expr(e->d.BINOP.left, env);
    printf(" ");
    print_BinOp(e->d.BINOP.op);
    printf(" ");
    print_expr(e->d.BINOP.right, env);
    printf(")");
    break;
  case T_UNOP:
    printf("(");
    print_UnOp(e->d.UNOP.op);
    print_expr(e->d.UNOP.arg, env);
    printf(")");
    break;
  case T_CAST:
    printf("((");
    print_type(e->d.CAST.ty, NULL);
    printf(")");
    print_expr(e->d.CAST.arg, env);
    printf(")");
    break;
  case T_CALL:
    printf("(");
    print_expr(e->d.CALL.func, env);
    printf("(");
    print_expr_list(e->d.CALL.args, ", ", env);
    printf(")");
    if (e->d.CALL.vargs != NULL) {
      printf("\n");
      print_space();
      nspace += 5;
      printf("/* under context:\n");
      print_assertion(e->d.CALL.vargs->ctx->pre, 1, env);
      nspace -= 2;
      print_space();
      printf("assign:\n");
      nspace += 2;
      struct virt_arg_list *i;
      for (i = e->d.CALL.vargs->arg; i != NULL; i = i->next) {
        print_space();
        printf("%s = ", i->name);
        print_exprval(i->val, env);
        printf("\n");
      }
      nspace -= 2;
      if (e->d.CALL.vargs->spec_name != NULL) {
        print_space();
        printf("calling spec: %s\n", e->d.CALL.vargs->spec_name);
      }
      nspace -= 3;
      print_space();
      printf("*/");
    }
    printf(")");
    break;
  case T_DEREF:
    printf("(*");
    print_expr(e->d.DEREF.arg, env);
    printf(")");
    break;
  case T_ADDRES:
    printf("(&");
    print_expr(e->d.ADDRES.arg, env);
    printf(")");
    break;
  case T_SIZEOFTYPE:
    printf("(sizeof(");
    print_type(e->d.SIZEOFTYPE.ty, NULL);
    printf("))");
    break;
  case T_INDEX:
    printf("(");
    print_expr(e->d.INDEX.arg, env);
    printf("[");
    print_expr(e->d.INDEX.pos, env);
    printf("])");
    break;
  case T_FIELDOF:
    printf("(");
    print_expr(e->d.FIELDOF.arg, env);
    printf(".%s)", e->d.FIELDOF.field->name);
    break;
  case T_FIELDOFPTR:
    printf("(");
    print_expr(e->d.FIELDOFPTR.arg, env);
    printf("->%s)", e->d.FIELDOFPTR.field->name);
    break;
  case T_ENUMLIT:
    printf("%s", e->d.ENUMLIT.info->name);
    break;
  case T_CONDITION:
    printf("(");
    print_expr(e->d.CONDITION.cond, env);
    printf(" ? ");
    print_expr(e->d.CONDITION.btrue, env);
    printf(" : ");
    print_expr(e->d.CONDITION.bfalse, env);
    printf(")");
    break;
  }
}

void print_scmd(struct simple_cmd *scmd, struct persistent_env *env) {
  switch (scmd->t) {
  case T_COMPUTATION:
    print_expr(scmd->d.COMPUTATION.arg, env);
    break;
  case T_ASGN:
    print_expr(scmd->d.ASGN.left, env);
    print_AsgnOp(scmd->d.ASGN.op);
    print_expr(scmd->d.ASGN.right, env);
    break;
  case T_INCDEC:
    switch (scmd->d.INCDEC.op) {
    case T_INC_F: printf("++"); print_expr(scmd->d.INCDEC.arg, env); break;
    case T_DEC_F: printf("--"); print_expr(scmd->d.INCDEC.arg, env); break;
    case T_INC_B: print_expr(scmd->d.INCDEC.arg, env); printf("++"); break;
    case T_DEC_B: print_expr(scmd->d.INCDEC.arg, env); printf("--"); break;
    }
  }
}

void print_case(struct Case *c, int full_asrt, struct persistent_env *env) {
  print_space();
  nspace += 2;

  switch (c->t) {
  case T_CASE:
    printf("case ");
    print_expr(c->d.CASE.cond, env);
    printf(":\n");
    print_cmd(c->d.CASE.body, full_asrt, env);
    break;
  case T_DEFAULT:
    printf("default:\n");
    print_cmd(c->d.DEFAULT.body, full_asrt, env);
    break;
  }

  nspace -= 2;
}

void print_cases(struct Case_list *cs, char *sep, int full_asrt, struct persistent_env *env) {
  if (cs == ((void *)0))
    return;
  while (cs->tail != ((void *)0)) {
    print_case(cs->head, full_asrt, env);
    printf("%s", sep);
    cs = cs->tail;
  }
  print_case(cs->head, full_asrt, env);
}

void print_cmd(struct cmd *c, int full_asrt, struct persistent_env *env) {
  if (c == NULL)
    return;
  switch (c->t) {
  case T_BLOCK:
    nspace -= 2;
    print_space();
    printf("{\n");
    nspace += 2;
    print_cmd(c->d.BLOCK.cmd, full_asrt, env);
    nspace -= 2;
    print_space();
    printf("}\n");
    nspace += 2;
    break;
  case T_VARDECL:
    print_space();
    print_type(c->d.VARDECL.info->type, c->d.VARDECL.info->name);
    printf(";\n");
    break;
  case T_TYPEDEF:
    print_space();
    printf("typedef ");
    print_type(c->d.TYPEDEF.info->type, c->d.TYPEDEF.info->name);
    printf(";\n");
    break;
  case T_SIMPLE:
    print_space();
    print_scmd(c->d.SIMPLE.scmd, env);
    printf(";\n");
    break;
  case T_SEQ:
    print_cmd(c->d.SEQ.left, full_asrt, env);
    print_cmd(c->d.SEQ.right, full_asrt, env);
    break;
  case T_SWITCH:
    print_space();
    nspace += 2;
    printf("switch (");
    print_expr(c->d.SWITCH.cond, env);
    printf(") {\n");
    print_cases(c->d.SWITCH.body, "", full_asrt, env);
    nspace -= 2;
    print_space();
    printf("}\n");
    break;
  case T_IF:
    print_space();
    nspace += 2;
    printf("if (");
    print_expr(c->d.IF.cond, env);
    printf(")\n");
    print_cmd(c->d.IF.left, full_asrt, env);
    if (c->d.IF.right != NULL) {
      nspace -= 2;
      print_space();
      printf("else\n");
      nspace += 2;
      print_cmd(c->d.IF.right, full_asrt, env);
    }
    nspace -= 2;
    break;
  case T_WHILE:
    if (c->d.WHILE.inv != NULL) {
      if (full_asrt) {
        print_space();
        printf("/**** loop invariant begin ");
        if (c->d.WHILE.is_partial)
          printf("(partial) ");
        printf("****\n");
        print_assertion(c->d.WHILE.inv, 1, env);
        print_space();
        printf(" ****  loop invariant end  ****/\n");
      } else {
        print_space();
        printf("/**** loop invariant here ****/\n");
      }
    }
    print_space();
    printf("while (");
    print_expr(c->d.WHILE.cond, env);
    printf(")\n");
    nspace += 2;
    print_cmd(c->d.WHILE.body, full_asrt, env);
    nspace -= 2;
    break;
  case T_DOWHILE:
    print_space();
    printf("do\n");
    nspace += 2;
    print_cmd(c->d.DOWHILE.body, full_asrt, env);
    nspace -= 2;
    if (c->d.DOWHILE.inv != NULL) {
      if (full_asrt) {
        print_space();
        printf("/**** loop invariant begin ");
        if (c->d.DOWHILE.is_partial)
          printf("(partial) ");
        printf("****\n");
        print_assertion(c->d.DOWHILE.inv, 1, env);
        print_space();
        printf(" ****  loop invariant end  ****/\n");
      } else {
        print_space();
        printf("/**** loop invariant here ****/\n");
      }
    }
    print_space();
    printf("while (");
    print_expr(c->d.DOWHILE.cond, env);
    printf(")\n");
    break;
  case T_FOR:
    if (c->d.FOR.inv != NULL) {
      if (full_asrt) {
        print_space();
        printf("/**** loop invariant begin ");
        if (c->d.FOR.is_partial)
          printf("(partial) ");
        printf("****\n");
        print_assertion(c->d.FOR.inv, 1, env);
        print_space();
        printf(" ****  loop invariant end  ****/\n");
      } else {
        print_space();
        printf("/**** loop invariant here ****/\n");
      }
    }
    print_space();
    printf("for (");
    if (c->d.FOR.init != NULL) { print_scmd(c->d.FOR.init, env); }
    printf("; ");
    if (c->d.FOR.cond != NULL) { print_expr(c->d.FOR.cond, env); }
    printf("; ");
    if (c->d.FOR.incr != NULL) { print_scmd(c->d.FOR.incr, env); }
    printf(")\n");
    nspace += 2;
    print_cmd(c->d.FOR.body, full_asrt, env);
    nspace -= 2;
    break;
  case T_BREAK:
    print_space();
    printf("break;\n");
    break;
  case T_CONTINUE:
    print_space();
    printf("continue;\n");
    break;
  case T_RETURN:
    print_space();
    printf("return");
    if (c->d.RETURN.arg != NULL) {
      printf(" ");
      print_expr(c->d.RETURN.arg, env);
    }
    printf(";\n");
    break;
  case T_COMMENT: {
    char *a_str;
    a_str = "assertion";
    if (full_asrt) {
      print_space();
      if (c->d.COMMENT.mark != NULL)
        printf("/**** %s %s begin ", a_str, c->d.COMMENT.mark);
      else
        printf("/**** %s begin ", a_str);
      if (c->d.COMMENT.is_partial)
        printf("(partial) ");
      printf("****\n");
      print_assertion(c->d.COMMENT.asrt, 1, env);
      print_space();
      if (c->d.COMMENT.mark != NULL)
        printf(" ****  %s %s end  ****/\n", a_str, c->d.COMMENT.mark);
      else
        printf(" ****  %s end  ****/\n", a_str);
    } else {
      print_space();
      printf("/**** %s here ****/\n", a_str);
    }
    break; }
  case T_PARTIAL_COMMENT: {
    if (full_asrt) {
      print_space();
      printf("/**** local spec begin ****\n");

      struct func_spec *i;
      int n = 0;
      for (i = c->d.PARTIAL_COMMENT.specs; i != NULL; i = i->next) {
        n += 1;
        print_space();
        printf("case %d:\n", n);
        nspace += 2;
        print_spec(i, env);
        nspace -= 2;
      }

      print_space();
      printf(" ****  local spec end  ****/\n");
    } else {
      print_space();
      printf("/**** partial here ****/");
    }
    break; }
  case T_DO_STRATEGY:
    print_space();
    printf("/*@ do %s */\n", c->d.DO_STRATEGY.name);
    break;
  case T_SKIP:
    print_space();
    printf(";\n");
    break;
  case T_PROOF:
    print_space();
    printf("/**** proof %s here ****/\n", c->d.PROOF.proof);
    break;
  case T_STRUCT_DEF: {
    print_space();
    printf("struct %s {\n", c->d.STRUCT_DEF.info->name);
    nspace += 2;
    struct field_info *it;
    for (it = c->d.STRUCT_DEF.info->first_field; it != NULL; it = it->next) {
      print_space();
      print_type(it->type, it->name);
      printf(";\n");
    }
    nspace -= 2;
    print_space();
    printf("};\n");
    break; }
  case T_STRUCT_DEC:
    print_space();
    printf("struct %s;\n", c->d.STRUCT_DEC.info->name);
    break;
  case T_UNION_DEF: {
    print_space();
    printf("union %s {\n", c->d.UNION_DEF.info->name);
    nspace += 2;
    struct field_info *it;
    for (it = c->d.UNION_DEF.info->first_field; it != NULL; it = it->next) {
      print_space();
      print_type(it->type, it->name);
      printf(";\n");
    }
    nspace -= 2;
    print_space();
    printf("};\n");
    break; }
  case T_UNION_DEC:
    print_space();
    printf("union %s;\n", c->d.UNION_DEC.info->name);
    break;
  case T_ENUM_DEF: {
    print_space();
    printf("enum %s {\n", c->d.ENUM_DEF.info->name);
    nspace += 2;
    struct enumerator_info *it;
    for (it = c->d.ENUM_DEF.info->first_rator; it != NULL; it = it->next) {
      print_space();
      printf("%s,\n", it->name);
    }
    nspace -= 2;
    print_space();
    printf("};\n");
    break; }
  case T_ENUM_DEC:
    print_space();
    printf("enum %s;\n", c->d.ENUM_DEC.info->name);
    break;
  }
}

/* another assertion printer */

struct type *type_of_simple_ctype(struct SimpleCtype *ct, struct persistent_env *env);

struct type_list *type_of_simple_ctype_list(struct SimpleCtypeListNode *ct, struct persistent_env *env) {
  if (ct == NULL)
    return NULL;
  return TLCons(type_of_simple_ctype(ct->data, env),
                type_of_simple_ctype_list(ct->next, env));
}

struct type *type_of_simple_ctype(struct SimpleCtype *ct, struct persistent_env *env) {
  switch (ct->t) {
  case C_void:     return TBasic(T_VOID);
  case C_int8:     return ct->d.CINT8.s == Signed ? TBasic(T_CHAR) : TBasic(T_U8);
  case C_int16:    return ct->d.CINT16.s == Signed ? TBasic(T_SHORT) : TBasic(T_U16);
  case C_int32:    return ct->d.CINT32.s == Signed ? TBasic(T_INT) : TBasic(T_UINT);
  case C_int64:    return ct->d.CINT64.s == Signed ? TBasic(T_INT64) : TBasic(T_UINT64);
  case C_pointer:  return TPtr(type_of_simple_ctype(ct->d.CPOINTER.type, env));
  case C_array:    return TArray(type_of_simple_ctype(ct->d.CARRAY.type, env),
                                 ct->d.CARRAY.length);
  case C_function: return TFunction(type_of_simple_ctype(ct->d.CFUNC.ret_type, env),
                                    type_of_simple_ctype_list(ct->d.CFUNC.arg_list->head, env));
  case C_struct:   return TStruct(find_struct_by_id(ct->d.CSTRUCT.struct_id, env));
  case C_union:    return TUnion(find_union_by_id(ct->d.CUNION.union_id, env));
  case C_enum:     return TEnum(find_enum_by_id(ct->d.CENUM.enum_id, env));
  }
}

struct atype *atype_of_polytype(struct PolyType *t, struct persistent_env *env) {
  switch (t->t) {
  case POLY_VAR:
    return ATAtom(find_atype_by_id(t->d.VAR.id, env));
  case POLY_FUNCAPP: {
    struct atype *ret = ATAtom(find_atype_by_id(t->d.FUNCAPP.func, env));
    for (struct PolyTypeListNode *i = t->d.FUNCAPP.args->tail;
         i != NULL; i = i->next)
      ret = ATApp(ret, atype_of_polytype(i->data, env));
    return ret;
  }
  case POLY_ARROW:
    return ATArrow(atype_of_polytype(t->d.ARROW.left, env),
                   atype_of_polytype(t->d.ARROW.right, env));
  }
}

int print_suffix = 1;

void print_atype_File(FILE *f, struct atype *ty) {
  switch (ty->t) {
  case AT_ARROW:
    fprintf(f,"(");
    print_atype_File(f, ty->d.ARROW.from);
    fprintf(f," → ");
    print_atype_File(f, ty->d.ARROW.to);
    fprintf(f,")");
    break;
  case AT_APP:
    if (atype_is_list(ty->d.APP.tfn)) {
      fprintf(f,"[");
      print_atype_File(f,ty->d.APP.rand);
      fprintf(f,"]");
      break;
    } else if (atype_is_app(ty->d.APP.tfn) &&
               atype_is_atom(ty->d.APP.tfn->d.APP.tfn)) {
      fprintf(f,"(");
      print_atype_File(f,ty->d.APP.tfn->d.APP.rand);
      fprintf(f," × ");
      print_atype_File(f,ty->d.APP.rand);
      fprintf(f,")");
      break;
    }
    fprintf(f,"(");
    print_atype_File(f,ty->d.APP.tfn);
    fprintf(f," ");
    print_atype_File(f,ty->d.APP.rand);
    fprintf(f,")");
    break;
  case AT_QVAR:
    fprintf(f,"?%s", ty->d.QVAR.name);
    break;
  case AT_TVAR:
    if (ty->d.TVAR.link != NULL)
      print_atype_File(f,ty->d.TVAR.link);
    else
      fprintf(f,"%s", ty->d.TVAR.name);
    break;
  case AT_ATOM:
    switch (ty->d.ATOM.info->id) {
    case BUILTINTYPE_Z:
      fprintf(f,"ℤ"); break;
    case BUILTINTYPE_NAT:
      fprintf(f,"ℕ"); break;
    case BUILTINTYPE_PROP:
      fprintf(f,"ℙℙ"); break;
    case BUILTINTYPE_ASSERTION:
      fprintf(f,"𝕊ℙ"); break;
    case BUILTINTYPE_BOOL:
      fprintf(f,"𝔹"); break;
    default:
      fprintf(f,"%s", ty->d.ATOM.info->name); break;
    }
    break;
  }
}

void print_atype(struct atype *ty) {
  print_atype_File(stdout, ty);
}

char * Get_atype_name(struct atype * ty) {
   if (ty == NULL) return NULL;
   switch (ty->t) {
     case AT_ARROW: {
        char *from = Get_atype_name(ty->d.ARROW.from);
        char *to = Get_atype_name(ty->d.ARROW.to);
        char *ret = (char *)malloc(strlen(from) + strlen(to) + 9);
        sprintf(ret, "_Imply_%s_%s", from, to);
        return ret;
     }
    case AT_APP:
      if (atype_is_list(ty->d.APP.tfn)) {
        char *rand = Get_atype_name(ty->d.APP.rand);
        char *ret = (char *)malloc(strlen(rand) + 7);
        sprintf(ret, "_List_%s", rand);
        return ret;
      } else if (atype_is_app(ty->d.APP.tfn) &&
                atype_is_atom(ty->d.APP.tfn->d.APP.tfn)) {
        char * rand = Get_atype_name(ty->d.APP.rand);
        char * tfn = Get_atype_name(ty->d.APP.tfn->d.APP.rand);
        char *ret = (char *)malloc(strlen(rand) + strlen(tfn) + 8);
        sprintf(ret, "_Prod_%s_%s", tfn, rand);
        return ret;
      }
      char * rand = Get_atype_name(ty->d.APP.rand);
      char * tfn = Get_atype_name(ty->d.APP.tfn);
      char * ret = (char *)malloc(strlen(rand) + strlen(tfn) + 7);
      sprintf(ret, "_App_%s_%s", tfn, rand);
      return ret;
    case AT_QVAR:
      return strdup(ty->d.QVAR.name);
    case AT_TVAR:
      if (ty->d.TVAR.link != NULL)
        return Get_atype_name(ty->d.TVAR.link);
      else
        return strdup(ty->d.TVAR.name);
      break;
    case AT_ATOM:
      switch (ty->d.ATOM.info->id) {
      case BUILTINTYPE_Z:
        return strdup("Z");
      case BUILTINTYPE_NAT:
        return strdup("nat");
      case BUILTINTYPE_PROP:
        return strdup("Prop");
      case BUILTINTYPE_ASSERTION:
        return strdup("Assertion");
      case BUILTINTYPE_BOOL:
        return strdup("bool");
      default:
        return strdup(ty->d.ATOM.info->name);
      }
      break;
    }
}

void print_Vvari(int id, int show_type, struct persistent_env *env) {
  struct logic_var_info *info = find_logic_var_by_id(id, env);
  if (show_type)
    printf("(");
  if (info != NULL)
    printf("%s", info->name);
  else
    printf("v");
  print_subscript(id);
  if (show_type) {
    printf(" : ");
    print_atype(info->atype);
    printf(")");
  }
}

void print_exprval(struct ExprVal *e, struct persistent_env *env);

void print_exprval_list(struct ExprValListNode *l, struct persistent_env *env) {
  if (l == NULL)
    return;
  print_exprval(l->data, env);
  if (l->next != NULL) {
    printf(", ");
    print_exprval_list(l->next, env);
  }
}

void print_polytype(struct PolyType *t, struct persistent_env *env);

void print_polytypelist(struct PolyTypeListNode *l, struct persistent_env *env,
                        int print_brace, int print_space) {
  if (l == NULL)
    return;
  if (print_brace)
    printf("{");
  print_polytype(l->data, env);
  if (print_brace)
    printf("}");
  if (l->next != NULL) {
    if (print_space)
      printf(" ");
    print_polytypelist(l->next, env, print_brace, print_space);
  }
}

void print_polytype(struct PolyType *t, struct persistent_env *env) {
  switch (t->t) {
  case POLY_VAR:
    printf("%s", find_atype_by_id(t->d.VAR.id, env)->name);
    break;
  case POLY_FUNCAPP:
    if (t->d.FUNCAPP.args->head == NULL) {
      printf("%s", find_atype_by_id(t->d.FUNCAPP.func, env)->name);
      break;
    }
    printf("(");
    printf("%s", find_atype_by_id(t->d.FUNCAPP.func, env)->name);
    printf(" ");
    print_polytypelist(t->d.FUNCAPP.args->head, env, 0, 1);
    printf(")");
    break;
  case POLY_ARROW:
    printf("(");
    print_polytype(t->d.ARROW.left, env);
    printf(" → ");
    print_polytype(t->d.ARROW.right, env);
    printf(")");
    break;
  }
}

void print_exprval(struct ExprVal *e, struct persistent_env *env) {
  switch (e->t) {
  case TIME_COST: printf("⏲");
                  break;
  case EZ_VAL: printf("%llu", e->d.EZ_VAL.number);
               break;
  case VFIELD_ADDRESS: printf("(");
                       printf("&");
                       print_exprval(e->d.VFIELD_ADDRESS.expr, env);
                       printf("→");
                       printf("{%s∷%s}",
                              find_field_by_id(e->d.VFIELD_ADDRESS.field_id, env)->parent->name,
                              find_field_by_id(e->d.VFIELD_ADDRESS.field_id, env)->name);
                       printf(")");
                       break;
  case LINDEX: print_exprval(e->d.LINDEX.list, env);
               printf("[");
               print_exprval(e->d.LINDEX.index, env);
               printf("]");
               break;
  case VUOP: printf("(");
             switch (e->d.VUOP.op) {
             case Oneg:  printf("-"); break;
             case Onint: printf("~"); break;
             case Onot:  printf("!"); break;
             }
             print_exprval(e->d.VUOP.expr, env);
             printf(")");
             break;
  case VBOP: printf("(");
             print_exprval(e->d.VBOP.expr1, env);
             switch (e->d.VBOP.op) {
             case Oadd: printf(" + "); break;
             case Osub: printf(" - "); break;
             case Omul: printf(" * "); break;
             case Odiv: printf(" / "); break;
             case Omod: printf(" %% "); break;
             case Oand: printf(" & "); break;
             case Oor:  printf(" | "); break;
             case Oxor: printf(" ^ "); break;
             case Oshl: printf(" ≪ "); break;
             case Oshr: printf(" ≫ "); break;
             }
             print_exprval(e->d.VBOP.expr2, env);
             printf(")");
             break;
  case FUNCAPP: print_Vvari(e->d.FUNCAPP.id, 0, env);
                print_polytypelist(e->d.FUNCAPP.types->head, env, 1, 0);
                if (e->d.FUNCAPP.args->head != NULL) {
                  printf("(");
                  print_exprval_list(e->d.FUNCAPP.args->head, env);
                  printf(")");
                }
                break;
  case SIZE_OF: { printf("sizeof(");
                  struct type *ty = type_of_simple_ctype(e->d.SIZE_OF.type, env);
                  print_type(ty, NULL);
                  free_type(ty);
                  printf(")"); }
  }
}

void print_prop(struct Proposition *p, struct persistent_env *env) {
  switch (p->t) {
  case T_PROP_TRUE: printf("⊤");
                    break;
  case T_PROP_FALSE: printf("⊥");
                     break;
  case T_PROP_UNARY: printf("¬");
    print_prop(p->d.UNARY.prop, env);
                     break;
  case T_PROP_BINARY: printf("(");
    print_prop(p->d.BINARY.prop1, env);
                      switch (p->d.BINARY.op) {
                      case PROP_AND:   printf(" ∧ "); break;
                      case PROP_OR:    printf(" ∨ "); break;
                      case PROP_IMPLY: printf(" ⇒ "); break;
                      case PROP_IFF:   printf(" ⇔ "); break;
                      }
                      print_prop(p->d.BINARY.prop2, env);
                      printf(")");
                      break;
  case T_PROP_PTR: print_exprval(p->d.PTR.expr, env);
                   switch (p->d.PTR.op) {
                   case PROP_NOT_NULL:   printf(" ≠ 0"); break;
                   case PROP_MAYBE_NULL: printf(" ≟ 0"); break;
                   case PROP_IS_NULL:    printf(" = 0"); break;
                   }
                   break;
  case T_PROP_COMPARE: print_exprval(p->d.COMPARE.expr1, env);
                       switch (p->d.COMPARE.op) {
                       case PROP_LE:  printf(" ≤ "); break;
                       case PROP_GE:  printf(" ≥ "); break;
                       case PROP_LT:  printf(" < "); break;
                       case PROP_GT:  printf(" > "); break;
                       case PROP_EQ:  printf(" = "); break;
                       case PROP_NEQ: printf(" ≠ "); break;
                       }
                       print_exprval(p->d.COMPARE.expr2, env);
                       break;
  case T_PROP_QUANTIFIER: printf("(");
                          switch (p->d.QUANTIFIER.op) {
                          case PROP_FORALL: printf("∀ "); break;
                          case PROP_EXISTS: printf("∃ "); break;
                          }
                          print_Vvari(p->d.QUANTIFIER.ident, 1, env);
                          printf(". ");
                          print_prop(p->d.QUANTIFIER.prop, env);
                          printf(")");
                          break;
  case T_PROP_OTHER: print_Vvari(p->d.OTHER.predicate, 0, env);
                     print_polytypelist(p->d.OTHER.types->head, env, 1, 0);
                     printf("(");
                     print_exprval_list(p->d.OTHER.args->head, env);
                     printf(")");
                     break;
  }
}

void print_sep(struct Separation *sep, struct persistent_env *env) {
  struct type *ty;
  switch (sep->t) {
  case T_DATA_AT: if (sep->d.DATA_AT.left->t == VFIELD_ADDRESS) {
                    print_exprval(sep->d.DATA_AT.left->d.VFIELD_ADDRESS.expr, env);
                    struct field_info *info = find_field_by_id(sep->d.DATA_AT.left->d.VFIELD_ADDRESS.field_id, env);
                    printf("→");
                    printf("{%s∷%s}", info->parent->name, info->name);
                    printf(" = ");
                  } else {
                    print_exprval(sep->d.DATA_AT.left, env);
                    printf(" ↦ ");
                  }
                  print_exprval(sep->d.DATA_AT.right, env);
                  printf(" : ");
                  ty = type_of_simple_ctype(sep->d.DATA_AT.ty, env);
                  print_type(ty, NULL);
                  free_type(ty);
                  break;
  case T_UNDEF_DATA_AT: print_exprval(sep->d.UNDEF_DATA_AT.left, env);
                        printf(" ↦ _ : ");
                        ty = type_of_simple_ctype(sep->d.UNDEF_DATA_AT.ty, env);
                        print_type(ty, NULL);
                        free_type(ty);
                        break;
  case T_ARR: print_exprval(sep->d.ARR.addr, env);
              printf(" ↦ ");
              print_exprval(sep->d.ARR.value, env);
              printf("[0 ⋯ ");
              print_exprval(sep->d.ARR.size, env);
              printf(") : list of ");
              ty = type_of_simple_ctype(sep->d.ARR.ty, env);
              print_type(ty, NULL);
              free_type(ty);
              break;
  case T_OTHER: print_Vvari(sep->d.OTHER.sep_id, 0, env);
                print_polytypelist(sep->d.OTHER.types->head, env, 1, 0);
                printf("(");
                print_exprval_list(sep->d.OTHER.exprs->head, env);
                printf(")");
                break;
  }
}

void print_fpspec(struct FPSpec *s, struct persistent_env *env) {
  print_space();
  print_exprval(s->fp_addr, env);
  printf(" : ");
  struct func_info *info = s->func_info;
  print_type(info->ret_type, NULL);
  printf("(");
  struct prog_var_info_list *i;
  for (i = info->param; i != NULL && i->tail != NULL; i = i->tail) {
    print_type(i->head->type, i->head->name);
    printf(", ");
  }
  if (i != NULL)
    print_type(i->head->type, i->head->name);
  printf(")");
  printf(" ⊨ \n");
  nspace += 2;
  print_spec(s->func_info->spec, env);
  nspace -= 2;
}

void print_heap(struct Assertion *h, int addressable, struct persistent_env *env) {
  if (h->exist_list != NULL) {
    print_space();
    printf("∃");
    struct ExistList *l;
    for (l = h->exist_list; l != NULL; l = l->next) {
      printf(" ");
      print_Vvari(l->id, 1, env);
    }
    printf("\n");
  }

  {
    struct LocalLinkedHashMap *local;
    local = h->local_list;
    struct LocalLinkedHashMapNode *in;
    for (in = local->head; in != NULL; in = in->next)
      if (in->state == 1)  {
        print_space();
        print_exprval(in->value, env);
        if (addressable)
          printf(" ← &");
        else
          printf(" ← ");
        struct prog_var_info *var = find_prog_var_by_id(in->id, env), *it;
        for (it = var->shadowing; it != NULL; it = it->shadowing)
          printf(".");
        printf("%s", var->name);
        printf("\n");
      }
  }

  if (h->sep_list != NULL) {
    struct SepList *l;
    print_space();
    printf("★\n");
    nspace += 2;
    for (l = h->sep_list; l != NULL; l = l->next) {
      print_space();
      print_sep(l->head, env);
      printf("\n");
    }
    nspace -= 2;
  }

  if (h->fp_spec_list->head != NULL) {
    struct FPSpecListNode *l;
    print_space();
    printf("＠\n");
    nspace += 2;
    for (l = h->fp_spec_list->head; l != NULL; l = l->next) {
      print_fpspec(l->data, env);
    }
    nspace -= 2;
  }

  if (h->prop_list != NULL) {
    struct PropList *l;
    print_space();
    printf("⋀\n");
    nspace += 2;
    for (l = h->prop_list; l != NULL; l = l->next) {
      print_space();
      print_prop(l->head, env);
      printf("\n");
    }
    nspace -= 2;
  }
}

void print_assertion(struct AsrtList *a, int addressable, struct persistent_env *env) {
  int i;

  for (i = 0; a != NULL; a = a->next) {
    print_space();
    printf("case %d:\n", i);
    nspace += 2;
    print_heap(a->head, addressable, env);
    nspace -= 2;
    i += 1;
  }
}

void print_kind(struct kind *k) {
  switch (k->t) {
  case K_STAR:
    printf("⋆");
    break;
  case K_ARROW:
    printf("(");
    print_kind(k->d.ARROW.from);
    printf(" ⇒ ");
    print_kind(k->d.ARROW.to);
    printf(")");
    break;
  case K_KVAR:
    print_kind(k->d.KVAR.link);
    break;
  }
}

void print_spec(struct func_spec *spec, struct persistent_env *env) {
  struct ExistList *i;
  if (spec->name != NULL) {
    print_space();
    printf("name: %s\n", spec->name);
    if (spec->derived_by != NULL) {
      print_space();
      printf("derived by: %s\n", spec->derived_by);
    }
  }
  if (spec->with != NULL) {
    print_space();
    printf("local variable:\n");
    nspace += 2;
    for (i = spec->with; i != NULL; i = i->next) {
      struct logic_var_info *info = find_logic_var_by_id(i->id, env);
      print_space();
      printf("%s", info->name);
      print_subscript(info->id);
      printf(" : ");
      print_atype(info->atype);
      printf("\n");
    }
    nspace -= 2;
  }
  if (spec->__return != NULL) {
    print_space();
    printf("return value:\n");
    printf("  ");
    print_space();
    print_exprval(spec->__return, env);
    printf("\n");
  }
  print_space();
  printf("precondition:\n");
  nspace += 2;
  print_assertion(spec->pre, 0, env);
  nspace -= 2;
  print_space();
  printf("postcondition:\n");
  nspace += 2;
  print_assertion(spec->post, 0, env);
  nspace -= 2;
}

/* assertion printer end */
