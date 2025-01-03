#include "plang.h"
#include "utils.h"

#define create(name, ty)                                         \
  struct ty *name = (struct ty *)malloc(sizeof(struct ty));      \
  if (name == NULL) {                                            \
    fprintf(stderr, "Failure in malloc.\n");                     \
    exit(0);                                                     \
  }

struct pp_trivtype *TRIVBasic(enum BasicType ty) {
  create(res, pp_trivtype);
  res->t = PP_TRIV_BASIC;
  res->d.BASIC.ty = ty;
  res->is_extern_or_static = 0;
  return res;
}
struct pp_trivtype *TRIVStruct(char *name) {
  create(res, pp_trivtype);
  res->t = PP_TRIV_STRUCT;
  res->d.STRUCT.name = name;
  res->is_extern_or_static = 0;
  return res;
}
struct pp_trivtype *TRIVUnion(char *name) {
  create(res, pp_trivtype);
  res->t = PP_TRIV_UNION;
  res->d.UNION.name = name;
  res->is_extern_or_static = 0;
  return res;
}
struct pp_trivtype *TRIVEnum(char *name) {
  create(res, pp_trivtype);
  res->t = PP_TRIV_ENUM;
  res->d.ENUM.name = name;
  res->is_extern_or_static = 0;
  return res;
}
struct pp_trivtype *TRIVAnonStruct(char *name, struct annot_list *fields) {
  create(res, pp_trivtype);
  res->t = PP_TRIV_ANON_STRUCT;
  res->d.ANON_STRUCT.name = name;
  res->d.ANON_STRUCT.fields = fields;
  res->is_extern_or_static = 0;
  return res;
}
struct pp_trivtype *TRIVAnonUnion(char *name, struct annot_list *fields) {
  create(res, pp_trivtype);
  res->t = PP_TRIV_ANON_UNION;
  res->d.ANON_UNION.name = name;
  res->d.ANON_UNION.fields = fields;
  res->is_extern_or_static = 0;
  return res;
}
struct pp_trivtype *TRIVAnonEnum(char *name, struct pp_enum_list *names) {
  create(res, pp_trivtype);
  res->t = PP_TRIV_ANON_ENUM;
  res->d.ANON_ENUM.name = name;
  res->d.ANON_ENUM.names = names;
  res->is_extern_or_static = 0;
  return res;
}
struct pp_trivtype *TRIVTypeAlias(char *name) {
  create(res, pp_trivtype);
  res->t = PP_TRIV_TYPE_ALIAS;
  res->d.TYPE_ALIAS.name = name;
  res->is_extern_or_static = 0;
  return res;
}
struct pp_trivtype *TRIVExternOrStatic(struct pp_trivtype *triv) {
  triv->is_extern_or_static = 1;
  return triv;
}

struct pp_derivtype *DERIVEnd(char *name) {
  create(res, pp_derivtype);
  res->t = PP_DERIV_END;
  res->d.END.name = name;
  return res;
}
struct pp_derivtype *DERIVPtr(struct pp_derivtype *ty) {
  create(res, pp_derivtype);
  res->t = PP_DERIV_PTR;
  res->d.PTR.deriv = ty;
  return res;
}
struct pp_derivtype *DERIVArray(struct pp_derivtype *ty, struct pp_expr *size) {
  create(res, pp_derivtype);
  res->t = PP_DERIV_ARRAY;
  res->d.ARRAY.deriv = ty;
  res->d.ARRAY.size = size;
  return res;
}
struct pp_derivtype *DERIVFunction(struct pp_derivtype *ret, struct annot_list *param) {
  create(res, pp_derivtype);
  res->t = PP_DERIV_FUNCTION;
  res->d.FUNCTION.deriv = ret;
  res->d.FUNCTION.param = param;
  return res;
}

struct pp_pretype *PreType(struct pp_trivtype *triv, struct pp_derivtype *deriv) {
  create(res, pp_pretype);
  res->triv = triv;
  res->deriv = deriv;
  return res;
}

struct annot *TAnnot(struct pp_pretype *ty) {
  create(res, annot);
  res->type = ty;
  return res;
}

struct annot_list *ALNil() { return NULL; }
struct annot_list *ALCons(struct annot *head, struct annot_list *tail) {
  create(res, annot_list);
  res->head = head;
  res->tail = tail;
  return res;
}

struct pp_enum_list *pp_enum_list_cons(char *name, int value_valid, int neg, unsigned long long value, struct pp_enum_list *next) {
  create(res, pp_enum_list);
  res->name = name;
  res->value_valid = value_valid;
  res->neg = neg;
  res->value = value;
  res->next = next;
  return res;
}

struct term_list *term_list_cons(char *name, struct atype_list *qv, struct atype *body, struct term_list *next) {
  create(res, term_list);
  res->name = name;
  res->qv = qv;
  if (body != NULL)
    ASSIGN_ATYPE(res->body, body)
  else
    res->body = NULL;
  res->next = next;
  return res;
}

struct lvar_list *lvar_list_cons(char *name, struct atype *type, struct lvar_list *next) {
  create(res, lvar_list);
  res->name = name;
  if (type != NULL)
    ASSIGN_ATYPE(res->type, type)
  else
    res->type = NULL;
  res->next = next;
  return res;
}

struct atype_list *atype_list_cons(char *name, struct kind *kind, struct atype_list *next) {
  create(res, atype_list);
  res->name = name;
  if (kind != NULL)
    ASSIGN_KIND(res->kind, kind)
  else
    res->kind = NULL;
  res->next = next;
  return res;
}

struct atype_list *clone_atype_list(struct atype_list *qv) {
  if (qv == NULL)
    return NULL;
  return atype_list_cons(clone_str(qv->name), qv->kind, clone_atype_list(qv->next));
}

void deep_free_atype_list(struct atype_list *qv) {
  if (qv == NULL)
    return;
  deep_free_atype_list(qv->next);
  if (qv->kind != NULL)
    free_kind(qv->kind);
  free(qv->name);
  free(qv);
}

struct term_list *term_list_cons_multi(struct name_list *names, struct atype_list *qv, struct atype *body, struct term_list *next) {
  if (names == NULL) {
    deep_free_atype_list(qv);
    return next;
  } else {
    char *name = names->head;
    struct name_list *names0 = names->tail;
    free(names);
    struct atype_list *cqv = clone_atype_list(qv);
    return term_list_cons(name, cqv, body, term_list_cons_multi(names0, qv, body, next));
  }
}

struct atype_list *atype_list_cons_multi(struct name_list *names, struct kind *kind, struct atype_list *next) {
  if (names == NULL) {
    return next;
  } else {
    char *name = names->head;
    struct name_list *names0 = names->tail;
    free(names);
    return atype_list_cons(name, kind, atype_list_cons_multi(names0, kind, next));
  }
}

struct lvar_list *lvar_list_cons_multi(struct name_list *names, struct atype *type, struct lvar_list *next) {
  if (names == NULL) {
    return next;
  } else {
    char *name = names->head;
    struct name_list *names0 = names->tail;
    free(names);
    return lvar_list_cons(name, type, lvar_list_cons_multi(names0, type, next));
  }
}

struct type_arg_list *ATypeArg(char *name, struct atype *type, struct type_arg_list *next) {
  create(res, type_arg_list);
  res->name = name;
  ASSIGN_ATYPE(res->type, type);
  res->next = next;
  return res;
}

struct pp_varg_list *PPVArg(char *name, struct RAssertion *val, struct pp_varg_list *next) {
  create(res, pp_varg_list);
  res->name = name;
  res->val = val;
  res->next = next;
  return res;
}

struct pp_type *PPBasic(enum BasicType ty) {
  create(res, pp_type);
  res->t = PP_BASIC;
  res->d.BASIC.ty = ty;
  return res;
}

struct pp_type *PPStruct(char *name) {
  create(res, pp_type);
  res->t = PP_STRUCT;
  res->d.STRUCT.name = name;
  return res;
}

struct pp_type *PPUnion(char *name) {
  create(res, pp_type);
  res->t = PP_UNION;
  res->d.UNION.name = name;
  return res;
}

struct pp_type *PPEnum(char *name) {
  create(res, pp_type);
  res->t = PP_ENUM;
  res->d.ENUM.name = name;
  return res;
}

struct pp_type *PPPtr(struct pp_type *ty) {
  create(res, pp_type);
  res->t = PP_PTR;
  res->d.PTR.ty = ty;
  return res;
}

struct pp_type *PPArray(struct pp_type *ty, struct pp_expr *size) {
  create(res, pp_type);
  res->t = PP_ARRAY;
  res->d.ARRAY.ty = ty;
  res->d.ARRAY.size = size;
  return res;
}

struct pp_type *PPAnonStruct(char *name, struct annot_list *fields) {
  create(res, pp_type);
  res->t = PP_ANON_STRUCT;
  res->d.ANON_STRUCT.name = name;
  res->d.ANON_STRUCT.fields = fields;
  return res;
}

struct pp_type *PPAnonUnion(char *name, struct annot_list *fields) {
  create(res, pp_type);
  res->t = PP_ANON_UNION;
  res->d.ANON_UNION.name = name;
  res->d.ANON_UNION.fields = fields;
  return res;
}

struct pp_type *PPAnonEnum(char *name, struct pp_enum_list *names) {
  create(res, pp_type);
  res->t = PP_ANON_ENUM;
  res->d.ANON_ENUM.name = name;
  res->d.ANON_ENUM.names = names;
  return res;
}

struct pp_type *PPFunction(struct pp_type *ret, struct annot_list *param) {
  create(res, pp_type);
  res->t = PP_FUNCTION;
  res->d.FUNCTION.ret = ret;
  res->d.FUNCTION.param = param;
  return res;
}

struct pp_type *PPTypeAlias(char *name) {
  create(res, pp_type);
  res->t = PP_TYPE_ALIAS;
  res->d.TYPE_ALIAS.name = name;
  return res;
}

struct pp_expr *PPConst(unsigned long long value, int hex, int l, int u) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_CONST;
  res->d.CONST.value = value;
  res->d.CONST.hex = hex;
  res->d.CONST.l = l;
  res->d.CONST.u = u;
  return res;
}

struct pp_expr *PPString(char *str) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_STRING;
  res->d.STRING.str = str;
  return res;
}

struct pp_expr *PPVar(char *name) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_VAR;
  res->d.VAR.name = name;
  return res;
}

struct pp_expr *PPBinop(enum BinOpType op, struct pp_expr *left, struct pp_expr *right) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_BINOP;
  res->d.BINOP.op = op;
  res->d.BINOP.left = left;
  res->d.BINOP.right = right;
  return res;
}

struct pp_expr *PPUnop(enum UnOpType op, struct pp_expr *arg) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_UNOP;
  res->d.UNOP.arg = arg;
  res->d.UNOP.op = op;
  return res;
}

struct pp_expr *PPDeref(struct pp_expr *arg) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_DEREF;
  res->d.DEREF.arg = arg;
  return res;
}

struct pp_expr *PPAddress(struct pp_expr *arg) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_ADDRESS;
  res->d.ADDRESS.arg = arg;
  return res;
}

struct pp_expr *PPCast(struct pp_pretype *ty, struct pp_expr *arg) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_CAST;
  res->d.CAST.arg = arg;
  res->d.CAST.ty = ty;
  return res;
}

struct pp_expr *PPCall(struct pp_expr *func, struct pp_expr_list *args,
                       char *spec_name, struct StringList *scopes, struct type_arg_list *type_arg, struct pp_varg_list *vargs) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_CALL;
  res->d.CALL.args = args;
  res->d.CALL.func = func;
  if (spec_name == NULL && vargs == NULL && type_arg == NULL && scopes == NULL)
    res->d.CALL.vargs = NULL;
  else {
    res->d.CALL.vargs = (struct pp_varg *)malloc(sizeof(struct pp_varg));
    res->d.CALL.vargs->spec_name = spec_name;
    res->d.CALL.vargs->scopes = scopes;
    res->d.CALL.vargs->type = type_arg;
    res->d.CALL.vargs->pre = vargs;
  }
  return res;
}

struct pp_expr *PPSizeofType(struct pp_pretype *ty) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_SIZEOFTYPE;
  res->d.SIZEOFTYPE.ty = ty;
  return res;
}

struct pp_expr *PPIndex(struct pp_expr *arg, struct pp_expr *pos) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_INDEX;
  res->d.INDEX.arg = arg;
  res->d.INDEX.pos = pos;
  return res;
}

struct pp_expr *PPFieldof(struct pp_expr *arg, char *name) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_FIELDOF;
  res->d.FIELDOF.arg = arg;
  res->d.FIELDOF.name = name;
  return res;
}

struct pp_expr *PPFieldofptr(struct pp_expr *arg, char *name) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_FIELDOFPTR;
  res->d.FIELDOFPTR.arg = arg;
  res->d.FIELDOFPTR.name = name;
  return res;
}

struct pp_expr *PPEnumLit(char *name) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_ENUMLIT;
  res->d.ENUMLIT.name = name;
  return res;
}

struct pp_expr *PPCondition(struct pp_expr *cond, struct pp_expr *btrue, struct pp_expr *bfalse) {
  create(res, pp_expr);
  res->type = NULL;
  res->t = PP_CONDITION;
  res->d.CONDITION.cond = cond;
  res->d.CONDITION.btrue = btrue;
  res->d.CONDITION.bfalse = bfalse;
  return res;
}

struct pp_expr_list *PELNil() { return NULL; }
struct pp_expr_list *PELCons(struct pp_expr *head, struct pp_expr_list *tail) {
  create(res, pp_expr_list);
  res->head = head;
  res->tail = tail;
  return res;
}

struct pp_simple *PPComputation(struct pp_expr *arg) {
  create(res, pp_simple);
  res->t = PP_COMPUTATION;
  res->d.COMPUTATION.arg = arg;
  return res;
}

struct pp_simple *PPAsgn(enum AssignType op, struct pp_expr *left,
                        struct pp_expr *right) {
  create(res, pp_simple);
  res->t = PP_ASGN;
  res->d.ASGN.left = left;
  res->d.ASGN.op = op;
  res->d.ASGN.right = right;
  return res;
}

struct pp_simple *PPIncDec(enum IncDecType op, struct pp_expr *arg) {
  create(res, pp_simple);
  res->t = PP_INCDEC;
  res->d.INCDEC.arg = arg;
  res->d.INCDEC.op = op;
  return res;
}

struct pp_initializer *PPSingleExpr(struct pp_expr *expr) {
  struct pp_initializer *res = (struct pp_initializer *)malloc(sizeof(struct pp_initializer));
  res->t = PP_SINGLE_EXPR;
  res->d.SINGLE_EXPR.expr = expr;
  return res;
}
struct pp_initializer *PPInitList(struct pp_initializer_list *list) {
  struct pp_initializer *res = (struct pp_initializer *)malloc(sizeof(struct pp_initializer));
  res->t = PP_INIT_LIST;
  res->d.INIT_LIST.list = list;
  return res;
}
struct pp_initializer_list *PPNext(struct pp_initializer *init, struct pp_initializer_list *next) {
  struct pp_initializer_list *res = (struct pp_initializer_list *)malloc(sizeof(struct pp_initializer_list));
  res->t = PP_NEXT;
  res->d.NEXT.init = init;
  res->next = next;
  return res;
}
struct pp_initializer_list *PPDesig(struct pp_designator *desig,
                                    struct pp_initializer *init,
                                    struct pp_initializer_list *next) {
  struct pp_initializer_list *res = (struct pp_initializer_list *)malloc(sizeof(struct pp_initializer_list));
  res->t = PP_DESIG;
  res->d.DESIG.desig = desig;
  res->d.DESIG.init = init;
  res->next = next;
  return res;
}
struct pp_designator *PPAtIndex(struct pp_expr *index, struct pp_designator *next) {
  struct pp_designator *res = (struct pp_designator *)malloc(sizeof(struct pp_designator));
  res->t = PP_AT_INDEX;
  res->d.AT_INDEX.index = index;
  res->next = next;
  return res;
}
struct pp_designator *PPAtMember(char *field, struct pp_designator *next) {
  struct pp_designator *res = (struct pp_designator *)malloc(sizeof(struct pp_designator));
  res->t = PP_AT_MEMBER;
  res->d.AT_MEMBER.field = field;
  res->next = next;
  return res;
}

struct partial_program *PPFirstDecl(int end, int is_typedef, struct pp_pretype *type, struct pp_initializer *init) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_FIRST_DECL;
  ps->d.FIRST_DECL.is_end = end;
  ps->d.FIRST_DECL.is_typedef = is_typedef;
  ps->d.FIRST_DECL.pre = type;
  ps->d.FIRST_DECL.init = init;
  return ps;
}

struct partial_program *PPMoreDecl(int end, struct pp_derivtype *deriv, struct pp_initializer *init) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_MORE_DECL;
  ps->d.MORE_DECL.is_end = end;
  ps->d.MORE_DECL.deriv = deriv;
  ps->d.MORE_DECL.init = init;
  return ps;
}

struct partial_program *PPSimple(struct pp_simple *simple) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_SIMPLE;
  ps->d.SIMPLE.simple = simple;
  return ps;
}
struct partial_program *PPBreak() {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_BREAK;
  return ps;
}
struct partial_program *PPContinue() {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_CONTINUE;
  return ps;
}
struct partial_program *PPReturn(struct pp_expr *ret) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_RETURN;
  ps->d.RETURN.ret = ret;
  return ps;
}
struct partial_program *PPIf(struct pp_expr *cond) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_IF;
  ps->d.IF.cond = cond;
  return ps;
}
struct partial_program *PPWhile(struct pp_expr *cond) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_WHILE;
  ps->d.WHILE.cond = cond;
  return ps;
}
struct partial_program *PPElse() {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_ELSE;
  return ps;
}
struct partial_program *PPDo() {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_DO;
  return ps;
}
struct partial_program *PPFor(struct pp_simple *init, struct pp_expr *cond, struct pp_simple *step) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_FOR;
  ps->d.FOR.init = init;
  ps->d.FOR.cond = cond;
  ps->d.FOR.step = step;
  return ps;
}
struct partial_program *PPSwitch(struct pp_expr *cond) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_SWITCH;
  ps->d.SWITCH.cond = cond;
  return ps;
}
struct partial_program *PPCase(struct pp_expr *cond) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_CASE;
  ps->d.CASE.cond = cond;
  return ps;
}
struct partial_program *PPDefault() {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_DEFAULT;
  return ps;
}
struct partial_program *PPBlock() {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_BLOCK;
  return ps;
}
struct partial_program *PPEnd() {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_END;
  return ps;
}
struct partial_program *PPAssert(struct RAssertion *assert, char *mark, int partial, struct StringList *scopes) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_ASSERT;
  ps->d.ASSERT.assert = assert;
  ps->d.ASSERT.mark = mark;
  ps->d.ASSERT.partial = partial;
  ps->d.ASSERT.scopes = scopes;
  return ps;
}
struct partial_program *PPInv(struct RAssertion *assert, int partial, struct StringList *scopes) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_INV;
  ps->d.INV.assert = assert;
  ps->d.INV.partial = partial;
  ps->d.INV.scopes = scopes;
  return ps;
}
struct partial_program *PPWI(struct RAssertion *pre, struct StringList *pre_scopes, struct RAssertion *post, struct StringList *post_scopes) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_WI;
  ps->d.WI.pre = pre;
  ps->d.WI.pre_scopes = pre_scopes;
  ps->d.WI.post = post;
  ps->d.WI.post_scopes = post_scopes;
  return ps;
}
struct partial_program *PPProof(char *name) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_PROOF;
  ps->d.PROOF.name = name;
  return ps;
}
struct partial_program *PPMissingInv() {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_MISSING_INV;
  return ps;
}
struct partial_program *PPDoStrategy(char *name) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_DO_STRATEGY;
  ps->d.DO_STRATEGY.name = name;
  return ps;
}
struct partial_program *PPSkip() {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_SKIP;
  return ps;
}

struct partial_program *PPStructDef(char *name, struct annot_list *field) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_STRUCT_DEF;
  ps->d.STRUCT_DEF.name = name;
  ps->d.STRUCT_DEF.field = field;
  return ps;
}
struct partial_program *PPUnionDef(char *name, struct annot_list *field) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_UNION_DEF;
  ps->d.UNION_DEF.name = name;
  ps->d.UNION_DEF.field = field;
  return ps;
}
struct partial_program *PPEnumDef(char *name, struct pp_enum_list *rator) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_ENUM_DEF;
  ps->d.ENUM_DEF.name = name;
  ps->d.ENUM_DEF.rator = rator;
  return ps;
}
struct partial_program *PPStructDec(char *name) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_STRUCT_DEC;
  ps->d.STRUCT_DEC.name = name;
  return ps;
}
struct partial_program *PPUnionDec(char *name) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_UNION_DEC;
  ps->d.UNION_DEC.name = name;
  return ps;
}
struct partial_program *PPEnumDec(char *name) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_ENUM_DEC;
  ps->d.ENUM_DEC.name = name;
  return ps;
}
struct partial_program *PPSepdef(char *name, struct atype_list *witht, struct lvar_list *with, struct RAssertion *cond) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_SEPDEF;
  ps->d.SEPDEF.witht = witht;
  ps->d.SEPDEF.with = with;
  ps->d.SEPDEF.name = name;
  ps->d.SEPDEF.condition = cond;
  return ps;
}
struct partial_program *PPCoqDec(struct term_list *names) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_COQ_DEC;
  ps->d.COQ_DEC.name = names;
  return ps;
}
struct partial_program *PPCoqTypeAlias(char *name, struct atype *type) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_COQ_TYPE_ALIAS;
  ps->d.COQ_TYPE_ALIAS.name = name;
  ASSIGN_ATYPE(ps->d.COQ_TYPE_ALIAS.type, type);
  return ps;
}
struct partial_program *PPATypeDec(struct atype_list *names) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_ATYPE_DEC;
  ps->d.ATYPE_DEC.name = names;
  return ps;
}
struct partial_program *PPProjDec(struct term_list *projs) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_PROJ_DEC;
  ps->d.PROJ_DEC.projs = projs;
  return ps;
}
struct partial_program *PPRecordDec(struct atype_list *params,
                                    char *record_name, char *constr_name,
                                    struct lvar_list *fields) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_RECORD_DEC;
  ps->d.RECORD_DEC.params = params;
  ps->d.RECORD_DEC.record_name = record_name;
  ps->d.RECORD_DEC.constr_name = constr_name;
  ps->d.RECORD_DEC.fields = fields;
  return ps;
}
struct partial_program *PPFuncDef(struct pp_pretype *func, struct pp_spec *spec) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_FUNC_DEF;
  ps->d.FUNC_DEF.func = func;
  ps->d.FUNC_DEF.spec = spec;
  return ps;
}
struct partial_program *PPFuncDec(struct pp_pretype *func, struct pp_spec *spec) {
  struct partial_program *ps;
  ps = (struct partial_program *)malloc(sizeof(struct partial_program));
  ps->t = PP_FUNC_DEC;
  ps->d.FUNC_DEC.func = func;
  ps->d.FUNC_DEC.spec = spec;
  return ps;
}

struct pp_spec *PPSpec(char *name,
                       char *derived_by,
                       struct atype_list *witht,
                       struct lvar_list *with,
                       struct RAssertion *pre,
                       struct RAssertion *post) {
  struct pp_spec *ps;
  ps = (struct pp_spec *)malloc(sizeof(struct pp_spec));
  ps->name = name;
  ps->derived_by = derived_by;
  ps->with = with;
  ps->witht = witht;
  ps->pre = pre;
  ps->post = post;
  return ps;
}

#undef create

void print_pp_expr_list_File(FILE *f, struct pp_expr_list *el, char *sep);

void print_pp_expr_list(struct pp_expr_list *el, char *sep) {
  print_pp_expr_list_File(stdout, el, sep);
}

void print_type_arg_File(FILE *f, struct type_arg_list *l) {
  if (l == NULL)
    return;
  fprintf(f, "%s = ", l->name);
  print_pp_atype_File(f, l->type);
  if (l->next != NULL) {
    fprintf(f, ", ");
    print_type_arg_File(f, l->next);
  }
}

void print_type_arg(struct type_arg_list *l) {
  print_type_arg_File(stdout, l);
}

void print_varg_File(FILE *f, struct pp_varg_list *l) {
  if (l == NULL)
    return;
  fprintf(f, "%s = ", l->name);
  print_RA_File(f, l->val);
  if (l->next != NULL) {
    fprintf(f,", ");
    print_varg_File(f, l->next);
  }
}

void print_varg(struct pp_varg_list *l) {
  print_varg_File(stdout, l);
}

void print_scopes_File(FILE *f, struct StringList *scopes) {
  if (scopes != NULL) {
    fprintf(f," by");
    struct StringListNode *i;
    for (i = scopes->head; i != NULL; i = i->next)
      fprintf(f, " %s", i->data);
  }
}

void print_scopes(struct StringList *scopes) {
  print_scopes_File(stdout, scopes);
}

void print_pp_expr_File(FILE *f, struct pp_expr *e) {
  switch (e->t) {
  case PP_CONST:
    if (e->d.CONST.hex)
      fprintf(f, "0x%llx", e->d.CONST.value);
    else
      fprintf(f, "%llu", e->d.CONST.value);
    if (e->d.CONST.l)
      printf("ll");
    if (e->d.CONST.u)
      printf("u");
    break;
  case PP_STRING:
    fprintf(f,"\"");
    print_escaped_str_File(f,e->d.STRING.str);
    fprintf(f,"\"");
    break;
  case PP_VAR:
    fprintf(f,"%s", e->d.VAR.name);
    /* printf(".%u", e->d.VAR.id); */
    break;
  case PP_BINOP:
    fprintf(f,"(");
    print_pp_expr_File(f,e->d.BINOP.left);
    fprintf(f," ");
    print_BinOp_File(f,e->d.BINOP.op);
    fprintf(f," ");
    print_pp_expr_File(f,e->d.BINOP.right);
    fprintf(f, ")");
    break;
  case PP_UNOP:
    fprintf(f,"(");
    print_UnOp_File(f,e->d.UNOP.op);
    print_pp_expr_File(f,e->d.UNOP.arg);
    fprintf(f,")");
    break;
  case PP_CAST:
    fprintf(f,"((");
    print_pretype_File(f,e->d.CAST.ty);
    fprintf(f,")");
    print_pp_expr_File(f,e->d.CAST.arg);
    fprintf(f,")");
    break;
  case PP_CALL:
    fprintf(f,"(");
    print_pp_expr_File(f,e->d.CALL.func);
    fprintf(f,"(");
    print_pp_expr_list_File(f, e->d.CALL.args, ", ");
    fprintf(f,")");
    if (e->d.CALL.vargs != NULL) {
      fprintf(f,"/*@ ");
      if (e->d.CALL.vargs->spec_name != NULL)
        fprintf(f,"%s ", e->d.CALL.vargs->spec_name);
      fprintf(f,"where ");
      print_varg_File(f,e->d.CALL.vargs->pre);
      if (e->d.CALL.vargs->type != NULL) {
        fprintf(f,"; ");
        print_type_arg_File(f, e->d.CALL.vargs->type);
      }
      print_scopes_File(f, e->d.CALL.vargs->scopes);
      fprintf(f, " */");
    }
    fprintf(f, ")");
    break;
  case PP_DEREF:
    fprintf(f,"(*");
    print_pp_expr_File(f, e->d.DEREF.arg);
    fprintf(f,")");
    break;
  case PP_ADDRESS:
    fprintf(f,"(&");
    print_pp_expr_File(f,e->d.ADDRESS.arg);
    fprintf(f,")");
    break;
  case PP_SIZEOFTYPE:
    fprintf(f,"(sizeof(");
    print_pretype_File(f,e->d.SIZEOFTYPE.ty);
    fprintf(f,"))");
    break;
  case PP_INDEX:
    fprintf(f,"(");
    print_pp_expr_File(f,e->d.INDEX.arg);
    fprintf(f,"[");
    print_pp_expr_File(f,e->d.INDEX.pos);
    fprintf(f,"])");
    break;
  case PP_FIELDOF:
    fprintf(f,"(");
    print_pp_expr_File(f,e->d.FIELDOF.arg);
    fprintf(f,".%s)", e->d.FIELDOF.name);
    break;
  case PP_FIELDOFPTR:
    fprintf(f,"(");
    print_pp_expr_File(f,e->d.FIELDOFPTR.arg);
    fprintf(f,"->%s)", e->d.FIELDOFPTR.name);
    break;
  case PP_ENUMLIT:
    fprintf(f,"%s", e->d.ENUMLIT.name);
    break;
  case PP_CONDITION:
    fprintf(f,"(");
    print_pp_expr_File(f,e->d.CONDITION.cond);
    fprintf(f," ? ");
    print_pp_expr_File(f,e->d.CONDITION.btrue);
    fprintf(f," : ");
    print_pp_expr_File(f,e->d.CONDITION.bfalse);
    fprintf(f,")");
    break;
  }
}

void print_pp_expr(struct pp_expr *e) {
  print_pp_expr_File(stdout, e);
}

void print_pp_expr_list_File(FILE *f, struct pp_expr_list *el, char *sep) {
  if (el == NULL)
    return;
  else if (el->tail == NULL)
    print_pp_expr_File(f, el->head);
  else {
    print_pp_expr_File(f, el->head);
    fprintf(f, "%s", sep);
    print_pp_expr_list_File(f, el->tail, sep);
  }
}

void print_annot_list_File(FILE *f, struct annot_list *al, char *sep);

void print_annot_list(struct annot_list *al, char *sep) {
  print_annot_list_File(stdout, al, sep);
}

void print_name_list_File(FILE *f, struct name_list *nl, char *sep) {
  if (nl == NULL)
    return;
  fprintf(f,"%s", nl->head);
  if (nl->tail != NULL) {
    fprintf(f,"%s", sep);
    print_name_list_File(f, nl->tail, sep);
  }
}

void print_name_list(struct name_list *nl, char *sep) {
  print_name_list_File(stdout, nl, sep);
}

void print_pp_enum_list_File(FILE *f, struct pp_enum_list *l) {
  if (l == NULL)
    return;
  fprintf(f,"%s", l->name);
  if (l->value_valid) {
    if (l->neg)
      fprintf(f," = -%lld", l->value);
    else
      fprintf(f," = %lld", l->value);
  }
  if (l->next != NULL) {
    fprintf(f,", ");
    print_pp_enum_list_File(f,l->next);
  }
}

void print_pp_enum_list(struct pp_enum_list *l) {
  print_pp_enum_list_File(stdout, l);
}

void print_derivtype_File(FILE *f, struct pp_derivtype *deriv) {
  switch (deriv->t) {
  case PP_DERIV_PTR:
    fprintf(f,"(*");
    print_derivtype_File(f, deriv->d.PTR.deriv);
    fprintf(f,")");
    break;
  case PP_DERIV_ARRAY:
    fprintf(f,"(");
    print_derivtype_File(f,deriv->d.ARRAY.deriv);
    fprintf(f,"[");
    print_pp_expr_File(f,deriv->d.ARRAY.size);
    fprintf(f,"])");
    break;
  case PP_DERIV_FUNCTION:
    fprintf(f,"(");
    print_derivtype_File(f,deriv->d.FUNCTION.deriv);
    fprintf(f,"(");
    print_annot_list_File(f,deriv->d.FUNCTION.param, ", ");
    fprintf(f,"))");
    break;
  case PP_DERIV_END:
    if (deriv->d.END.name != NULL)
      fprintf(f,"%s", deriv->d.END.name);
    break;
  }
}

void print_derivtype(struct pp_derivtype *deriv) {
  print_derivtype_File(stdout, deriv);
}

void print_pretype_File(FILE *f, struct pp_pretype *ty) {
  struct pp_trivtype *triv = ty->triv;
  struct pp_derivtype *deriv = ty->deriv;
  switch (triv->t) {
  case PP_TRIV_BASIC:
    switch (triv->d.BASIC.ty) {
    case T_VOID:   fprintf(f,"void"); break;
    case T_CHAR:   fprintf(f,"char"); break;
    case T_U8:     fprintf(f,"unsigned char"); break;
    case T_SHORT:  fprintf(f,"short"); break;
    case T_U16:    fprintf(f,"unsigned short"); break;
    case T_INT:    fprintf(f,"int"); break;
    case T_INT64:  fprintf(f,"long long"); break;
    case T_UINT:   fprintf(f,"unsigned int"); break;
    case T_UINT64: fprintf(f,"unsigned long long"); break;
    }
    break;
  case PP_TRIV_STRUCT:      fprintf(f,"struct %s", triv->d.STRUCT.name); break;
  case PP_TRIV_UNION:       fprintf(f,"union %s", triv->d.UNION.name); break;
  case PP_TRIV_ENUM:        fprintf(f,"enum %s", triv->d.ENUM.name); break;
  case PP_TRIV_ANON_STRUCT: fprintf(f,"struct ");
                            if (triv->d.ANON_STRUCT.name != NULL)
                              fprintf(f,"%s ", triv->d.ANON_STRUCT.name);
                            fprintf(f,"{");
                            print_annot_list_File(f,triv->d.ANON_STRUCT.fields, "; ");
                            if (triv->d.ANON_STRUCT.fields != NULL)
                              fprintf(f,"; ");
                            fprintf(f,"}");
                            break;
  case PP_TRIV_ANON_UNION: fprintf(f,"union ");
                           if (triv->d.ANON_UNION.name != NULL)
                             fprintf(f,"%s ", triv->d.ANON_UNION.name);
                           fprintf(f,"{");
                           print_annot_list_File(f,triv->d.ANON_UNION.fields, "; ");
                           if (triv->d.ANON_UNION.fields != NULL)
                             fprintf(f,"; ");
                           fprintf(f,"}");
                           break;
  case PP_TRIV_ANON_ENUM: fprintf(f,"enum ");
                          if (triv->d.ANON_ENUM.name != NULL)
                            fprintf(f,"%s ", triv->d.ANON_ENUM.name);
                          fprintf(f,"{");
                          print_pp_enum_list_File(f, triv->d.ANON_ENUM.names);
                          fprintf(f,"}");
                          break;
  case PP_TRIV_TYPE_ALIAS: fprintf(f,"%s", triv->d.TYPE_ALIAS.name);
                           break;
  }
  if (deriv->t == PP_DERIV_END && deriv->d.END.name == NULL)
    return;
  fprintf(f," ");
  print_derivtype_File(f,deriv);
}

void print_pretype(struct pp_pretype *ty) {
  print_pretype_File(stdout, ty);
}

void print_annot_File(FILE *f, struct annot *a) {
  print_pretype_File(f, a->type);
}

void print_annot(struct annot *a) {
  print_annot_File(stdout, a);
}

void print_annot_list_File(FILE *f, struct annot_list *al, char *sep) {
  if (al == NULL)
    return;
  else if (al->tail == NULL)
    print_annot_File(f, al->head);
  else {
    print_annot_File(f, al->head);
    fprintf(f, "%s", sep);
    print_annot_list_File(f, al->tail, sep);
  }
}

void print_pp_simple_File(FILE *f, struct pp_simple *scmd) {
  switch (scmd->t) {
  case PP_COMPUTATION:
    print_pp_expr_File(f, scmd->d.COMPUTATION.arg);
    break;
  case PP_ASGN:
    print_pp_expr_File(f, scmd->d.ASGN.left);
    print_AsgnOp_File(f,scmd->d.ASGN.op);
    print_pp_expr_File(f,scmd->d.ASGN.right);
    break;
  case PP_INCDEC:
    switch (scmd->d.INCDEC.op) {
    case T_INC_F: fprintf(f,"++"); print_pp_expr_File(f,scmd->d.INCDEC.arg); break;
    case T_DEC_F: fprintf(f,"--"); print_pp_expr_File(f,scmd->d.INCDEC.arg); break;
    case T_INC_B: print_pp_expr_File(f,scmd->d.INCDEC.arg); fprintf(f,"++"); break;
    case T_DEC_B: print_pp_expr_File(f,scmd->d.INCDEC.arg); fprintf(f,"--"); break;
    }
  }
}

void print_pp_simple(struct pp_simple *scmd) {
  print_pp_simple_File(stdout, scmd);
}

void print_pp_initializer_list_File(FILE *f, struct pp_initializer_list *init);

void print_pp_initializer_list(struct pp_initializer_list *init_list) {
  print_pp_initializer_list_File(stdout, init_list);
}

void print_pp_initializer_File(FILE *f, struct pp_initializer *init) {
  switch (init->t) {
  case PP_SINGLE_EXPR: print_pp_expr_File(f,init->d.SINGLE_EXPR.expr);
                       break;
  case PP_INIT_LIST: fprintf(f,"{");
                     print_pp_initializer_list_File(f,init->d.INIT_LIST.list);
                     fprintf(f,"}");
                     break;
  }
}

void print_pp_initializer(struct pp_initializer *init) {
  print_pp_initializer_File(stdout, init);
}

void print_pp_designator_File(FILE *f, struct pp_designator *desig) {
  if (desig == NULL)
    return;
  switch (desig->t) {
  case PP_AT_INDEX: fprintf(f,"[");
                    print_pp_expr_File(f,desig->d.AT_INDEX.index);
                    fprintf(f,"]");
                    break;
  case PP_AT_MEMBER: fprintf(f,".%s", desig->d.AT_MEMBER.field);
                     break;
  }
  print_pp_designator_File(f, desig->next);
}

void print_pp_designator(struct pp_designator *desig) {
  print_pp_designator_File(stdout, desig);
}

void print_pp_initializer_list_File(FILE *f, struct pp_initializer_list *init_list) {
  switch (init_list->t) {
  case PP_NEXT: print_pp_initializer_File(f, init_list->d.NEXT.init);
                break;
  case PP_DESIG: print_pp_designator_File(f, init_list->d.DESIG.desig);
                 fprintf(f," = ");
                 print_pp_initializer_File(f,init_list->d.DESIG.init);
                 break;
  }
  if (init_list->next != NULL) {
    fprintf(f,",");
    print_pp_initializer_list_File(f,init_list->next);
  }
}

void print_pp_kind_File(FILE *f, struct kind *k) {
  switch (k->t) {
  case K_STAR:
    fprintf(f,"*");
    break;
  case K_ARROW:
    fprintf(f,"(");
    print_pp_kind_File(f,k->d.ARROW.from);
    fprintf(f," => ");
    print_pp_kind_File(f,k->d.ARROW.to);
    fprintf(f,")");
    break;
  case K_KVAR:
    assert(0);
  }
}

void print_pp_kind(struct kind *k) {
  print_pp_kind_File(stdout, k);
}

void print_pp_atype_File(FILE *f, struct atype *ty) {
  switch (ty->t) {
  case AT_ARROW:
    fprintf(f,"(");
    print_pp_atype_File(f,ty->d.ARROW.from);
    fprintf(f," -> ");
    print_pp_atype_File(f,ty->d.ARROW.to);
    fprintf(f,")");
    break;
  case AT_APP:
    fprintf(f,"(");
    print_pp_atype_File(f,ty->d.APP.tfn);
    fprintf(f," ");
    print_pp_atype_File(f,ty->d.APP.rand);
    fprintf(f,")");
    break;
  case AT_TVAR:
    fprintf(f,"%s", ty->d.TVAR.name);
    break;
  case AT_ATOM:
  case AT_QVAR:
    assert(0);
  }
}

void print_pp_atype(struct atype *ty) {
  print_pp_atype_File(stdout, ty);
}

void print_atype_list_File(FILE *f, struct atype_list *l, char *left, char *right, char *sep) {
  if (l == NULL)
    return;
  fprintf(f,"%s%s", left, l->name);
  if (l->kind != NULL) {
    fprintf(f," :: ");
    print_pp_kind_File(f,l->kind);
  }
  fprintf(f,"%s", right);
  if (l->next != NULL) {
    fprintf(f,"%s", sep);
    print_atype_list_File(f,l->next, left, right, sep);
  }
}

void print_atype_list(struct atype_list *l, char *left, char *right, char *sep) {
  print_atype_list_File(stdout, l, left, right, sep);
}

void print_term_list_File(FILE *f, struct term_list *l) {
  if (l == NULL)
    return;
  fprintf(f,"(%s", l->name);
  if (l->body != NULL) {
    fprintf(f," : ");
    if (l->qv != NULL) {
      print_atype_list_File(f,l->qv, "{", "}", " ");
      fprintf(f," -> ");
    }
    print_pp_atype_File(f,l->body);
  }
  fprintf(f,")");
  if (l->next != NULL) {
    fprintf(f," ");
    print_term_list_File(f,l->next);
  }
}

void print_term_list(struct term_list *l) {
  print_term_list_File(stdout, l);
}

void print_lvar_list_File(FILE *f, struct lvar_list *l, char *left, char *right, char *sep) {
  if (l == NULL)
    return;
  if (l->type != NULL) {
    fprintf(f,"%s%s", left, l->name);
    fprintf(f," : ");
    print_pp_atype_File(f,l->type);
    fprintf(f,"%s", right);
  } else
    fprintf(f,"%s", l->name);
  if (l->next != NULL) {
    fprintf(f,"%s", sep);
    print_lvar_list_File(f,l->next, left, right, sep);
  }
}

void print_lvar_list(struct lvar_list *l, char *left, char *right, char *sep) {
  print_lvar_list_File(stdout, l, left, right, sep);
}

void print_pp_spec_File(FILE *f, struct pp_spec *spec) {
  print_space_File(f);
  fprintf(f,"/*@");
  if (spec->name != NULL) {
    print_space_File(f);
    fprintf(f," %s", spec->name);
    if (spec->derived_by != NULL)
      fprintf(f," : %s", spec->derived_by);
    fprintf(f,"\n   ");
  }
  if (spec->witht != NULL || spec->with != NULL) {
    fprintf(f," With");
    if (spec->witht != NULL) {
      fprintf(f," ");
      print_atype_list_File(f,spec->witht, "{", "}", " ");
    }
    if (spec->with != NULL) {
      fprintf(f," ");
      print_lvar_list_File(f,spec->with, "(", ")", " ");
    }
    fprintf(f,"\n");
  } else {
    fprintf(f,"\n");
  }
  print_space_File(f);
  fprintf(f,"    Require ");
  print_RA_File(f,spec->pre);
  fprintf(f,"\n");
  print_space_File(f);
  fprintf(f,"    Ensure ");
  print_RA_File(f,spec->post);
  fprintf(f," */\n");
}

void print_pp_spec(struct pp_spec *spec) {
  print_pp_spec_File(stdout, spec);
}

void print_partial_program_File(FILE *f, struct partial_program *pp) {
  switch (pp->t) {
  case PP_FIRST_DECL: print_space_File(f);
                      if (pp->d.FIRST_DECL.is_typedef)
                        printf("typedef ");
                      print_pretype_File(f,pp->d.FIRST_DECL.pre);
                      if (pp->d.FIRST_DECL.init != NULL) {
                        fprintf(f," = ");
                        print_pp_initializer_File(f,pp->d.FIRST_DECL.init);
                      }
                      if (pp->d.FIRST_DECL.is_end)
                        fprintf(f,";\n");
                      break;
  case PP_MORE_DECL: fprintf(f,", ");
                     print_derivtype_File(f,pp->d.MORE_DECL.deriv);
                     if (pp->d.MORE_DECL.init != NULL) {
                       fprintf(f," = ");
                       print_pp_initializer_File(f,pp->d.MORE_DECL.init);
                     }
                     if (pp->d.MORE_DECL.is_end)
                       fprintf(f,";\n");
                     break;
  case PP_SIMPLE: print_space_File(f);
                  print_pp_simple_File(f,pp->d.SIMPLE.simple);
                  fprintf(f,";\n");
                  break;
  case PP_BREAK: print_space_File(f);
                 fprintf(f,"break;\n");
                 break;
  case PP_CONTINUE: print_space_File(f);
                    fprintf(f,"continue;\n");
                    break;
  case PP_RETURN: print_space_File(f);
                  fprintf(f,"return");
                  if (pp->d.RETURN.ret != NULL) {
                    fprintf(f," ");
                    print_pp_expr_File(f,pp->d.RETURN.ret);
                  }
                  fprintf(f,";\n");
                  break;
  case PP_WHILE: print_space_File(f);
                 fprintf(f,"while (");
                 print_pp_expr_File(f,pp->d.WHILE.cond);
                 fprintf(f,")\n");
                 break;
  case PP_IF: print_space_File(f);
              fprintf(f,"if (");
              print_pp_expr_File(f,pp->d.IF.cond);
              fprintf(f,")\n");
              break;
  case PP_ELSE: print_space_File(f);
                fprintf(f,"else\n");
                break;
  case PP_DO: print_space_File(f);
              fprintf(f,"do\n");
              break;
  case PP_FOR: print_space_File(f);
               fprintf(f,"for (");
               if (pp->d.FOR.init != NULL) { print_pp_simple_File(f,pp->d.FOR.init); }
               fprintf(f,"; ");
               if (pp->d.FOR.cond != NULL) { print_pp_expr_File(f,pp->d.FOR.cond); }
               fprintf(f,"; ");
               if (pp->d.FOR.step != NULL) { print_pp_simple_File(f,pp->d.FOR.step); }
               fprintf(f,")\n");
               break;
  case PP_SWITCH: print_space_File(f);
                  fprintf(f,"switch (");
                  print_pp_expr_File(f,pp->d.SWITCH.cond);
                  fprintf(f,")\n");
                  break;
  case PP_CASE: print_space_File(f);
                fprintf(f,"case ");
                print_pp_expr_File(f,pp->d.CASE.cond);
                fprintf(f,":\n");
                break;
  case PP_DEFAULT: print_space_File(f);
                   fprintf(f,"default:\n");
                   break;
  case PP_BLOCK: print_space_File(f);
                 fprintf(f,"{\n");
                 break;
  case PP_END: print_space_File(f);
               fprintf(f,"}\n");
               break;
  case PP_ASSERT: print_space_File(f);
                  fprintf(f,"//@ ");
                  if (!pp->d.ASSERT.partial)
                    fprintf(f,"Assert ");
                  print_RA_File(f,pp->d.ASSERT.assert);
                  if (pp->d.ASSERT.mark != NULL)
                    fprintf(f," @%s", pp->d.ASSERT.mark);
                  print_scopes_File(f,pp->d.ASSERT.scopes);
                  fprintf(f,"\n");
                  break;
  case PP_INV: print_space_File(f);
               fprintf(f,"//@ ");
               if (!pp->d.INV.partial)
                 fprintf(f,"Assert ");
               fprintf(f,"Inv ");
               print_RA_File(f,pp->d.INV.assert);
               print_scopes_File(f,pp->d.INV.scopes);
               fprintf(f,"\n");
               break;
  case PP_WI: print_space_File(f);
              fprintf(f,"/*@ ");
              print_RA_File(f,pp->d.WI.pre);
              print_scopes_File(f,pp->d.WI.pre_scopes);
              fprintf(f,"\n");
              print_space_File(f);
              fprintf(f,"    which implies ");
              print_RA_File(f,pp->d.WI.post);
              print_scopes_File(f,pp->d.WI.post_scopes);
              fprintf(f," */\n");
              break;
  case PP_MISSING_INV: print_space_File(f);
                       fprintf(f,"/*@ FILL IN INVARIANT */\n");
                       break;
  case PP_PROOF: print_space_File(f);
                 fprintf(f,"// Proof %s\n", pp->d.PROOF.name);
                 break;
  case PP_DO_STRATEGY: print_space_File(f);
                       fprintf(f, "/*@ do %s */", pp->d.DO_STRATEGY.name);
                       break;
  case PP_SKIP: print_space_File(f);
                fprintf(f,";\n");
                break;

  case PP_STRUCT_DEF: { struct annot_list *it;
                        print_space_File(f);
                        fprintf(f,"struct %s\n", pp->d.STRUCT_DEF.name);
                        print_space_File(f);
                        fprintf(f,"{\n");
                        nspace += 2;
                        for (it = pp->d.STRUCT_DEF.field; it != NULL; it = it->tail) {
                          print_space_File(f);
                          print_annot_File(f,it->head);
                          fprintf(f,";\n");
                        }
                        nspace -= 2;
                        print_space_File(f);
                        fprintf(f,"};\n");
                        break; }
  case PP_UNION_DEF: { struct annot_list *it;
                       print_space_File(f);
                       fprintf(f,"union %s\n", pp->d.UNION_DEF.name);
                       print_space_File(f);
                       fprintf(f,"{\n");
                       nspace += 2;
                       for (it = pp->d.UNION_DEF.field; it != NULL; it = it->tail) {
                         print_space_File(f);
                         print_annot_File(f,it->head);
                         fprintf(f,";\n");
                       }
                       nspace -= 2;
                       print_space_File(f);
                       fprintf(f,"};\n");
                       break; }
  case PP_ENUM_DEF: { struct pp_enum_list *rator;
                      print_space_File(f);
                      fprintf(f,"enum %s\n", pp->d.ENUM_DEF.name);
                      print_space_File(f);
                      fprintf(f,"{\n");
                      nspace += 2;
                      for (rator = pp->d.ENUM_DEF.rator;
                           rator != NULL;
                           rator = rator->next) {
                        print_space_File(f);
                        fprintf(f,"%s", rator->name);
                        if (rator->value_valid)
                          if (rator->neg)
                            fprintf(f," = -%lld", rator->value);
                          else
                            fprintf(f," = %lld", rator->value);
                        if (rator->next != NULL)
                          fprintf(f,",");
                        fprintf(f,"\n");
                      }
                      nspace -= 2;
                      print_space_File(f);
                      fprintf(f,"};\n");
                      break; }
  case PP_STRUCT_DEC: print_space_File(f);
                      fprintf(f,"struct %s;\n", pp->d.STRUCT_DEC.name);
                      break;
  case PP_UNION_DEC: print_space_File(f);
                     fprintf(f,"union %s;\n", pp->d.UNION_DEC.name);
                     break;
  case PP_ENUM_DEC: print_space_File(f);
                    fprintf(f,"enum %s;\n", pp->d.ENUM_DEC.name);
                    break;
  case PP_SEPDEF: print_space_File(f);
                  fprintf(f,"/*@ Let ");
                  fprintf(f,"%s(", pp->d.SEPDEF.name);
                  if (pp->d.SEPDEF.witht != NULL) {
                    print_atype_list_File(f,pp->d.SEPDEF.witht, "{", "}", ",");
                    fprintf(f,"; ");
                  }
                  print_lvar_list_File(f,pp->d.SEPDEF.with, "", "", ", ");
                  fprintf(f,")");
                  fprintf(f," =\n");
                  nspace += 6;
                  print_space_File(f);
                  print_RA_File(f,pp->d.SEPDEF.condition);
                  fprintf(f," */\n");
                  nspace -= 6;
                  break;
  case PP_COQ_DEC: print_space_File(f);
                   fprintf(f,"/*@ Extern Coq ");
                   print_term_list_File(f,pp->d.COQ_DEC.name);
                   fprintf(f," */\n");
                   break;
  case PP_PROJ_DEC: print_space();
                    printf("/*@ Extern Coq Field ");
                    print_term_list(pp->d.PROJ_DEC.projs);
                    printf(" */\n");
                    break;
  case PP_RECORD_DEC: print_space_File(f);
                      fprintf(f, "/*@ Extern Coq Record ");
                      print_atype_list_File(f, pp->d.RECORD_DEC.params,
                                            "(", ")", " ");
                      fprintf(f, " %s", pp->d.RECORD_DEC.record_name);
                      if (pp->d.RECORD_DEC.constr_name != NULL)
                        fprintf(f, " %s", pp->d.RECORD_DEC.constr_name);
                      fprintf(f, " {\n      ");
                      print_lvar_list_File(f, pp->d.RECORD_DEC.fields, "", "", ";\n      ");
                      print_space_File(f);
                      fprintf(f, ";\n} */\n");
                      break;
  case PP_COQ_TYPE_ALIAS: print_space_File(f);
                          fprintf(f,"/*@ Extern Coq %s := ", pp->d.COQ_TYPE_ALIAS.name);
                          print_pp_atype_File(f,pp->d.COQ_TYPE_ALIAS.type);
                          fprintf(f," */\n");
                          break;
  case PP_ATYPE_DEC: print_space_File(f);
                     fprintf(f,"/*@ Extern Coq ");
                     print_atype_list_File(f,pp->d.ATYPE_DEC.name, "(", ")", " ");
                     fprintf(f," */\n");
                     break;
  case PP_FUNC_DEF: print_space_File(f);
                    print_pretype_File(f,pp->d.FUNC_DEF.func);
                    if (pp->d.FUNC_DEF.spec != NULL) {
                      fprintf(f,"\n");
                      print_pp_spec_File(f,pp->d.FUNC_DEF.spec);
                      print_space_File(f);
                      fprintf(f,"{\n");
                    } else
                      fprintf(f," {\n");
                    break;
  case PP_FUNC_DEC: print_space_File(f);
                    print_pretype_File(f,pp->d.FUNC_DEC.func);
                    if (pp->d.FUNC_DEC.spec != NULL) {
                      fprintf(f,"\n");
                      print_pp_spec_File(f,pp->d.FUNC_DEC.spec);
                      fprintf(f,";\n");
                    } else
                      fprintf(f,";\n");
                    break;
  }
}

void print_partial_program(struct partial_program *pp) {
  print_partial_program_File(stdout, pp);
}

void free_derivtype(struct pp_derivtype *deriv) {
  switch (deriv->t) {
  case PP_DERIV_END:
    break;
  case PP_DERIV_PTR:
    free_derivtype(deriv->d.PTR.deriv);
    break;
  case PP_DERIV_ARRAY:
    free_derivtype(deriv->d.ARRAY.deriv);
    break;
  case PP_DERIV_FUNCTION:
    free_derivtype(deriv->d.FUNCTION.deriv);
    break;
  }
  free(deriv);
}

void free_pp_pretype(struct pp_pretype *pre) {
  free(pre->triv);
  free_derivtype(pre->deriv);
  free_pp_type(pre->type);
  free(pre);
}

void free_pp_expr_list(struct pp_expr_list *el) {
  if (el == NULL)
    return;
  struct pp_expr_list *next = el->tail;
  free_pp_expr(el->head);
  free(el);
  free_pp_expr_list(next);
}

void free_annot_list_with_name(struct annot_list *al) {
  if (al == NULL)
    return;
  struct annot_list *tl = al->tail;
  if (al->head->type != NULL)
    free_pp_pretype(al->head->type);
  free(al->head->name);
  free(al->head);
  free(al);
  free_annot_list_with_name(tl);
}

void free_pp_type(struct pp_type *ty) {
  switch (ty->t) {
  case PP_BASIC:
    break;
  case PP_STRUCT:
    free(ty->d.STRUCT.name);
    break;
  case PP_UNION:
    free(ty->d.UNION.name);
    break;
  case PP_ENUM:
    free(ty->d.ENUM.name);
    break;
  case PP_PTR:
    free_pp_type(ty->d.PTR.ty);
    break;
  case PP_ARRAY:
    free_pp_type(ty->d.ARRAY.ty);
    free_pp_expr(ty->d.ARRAY.size);
    break;
  case PP_TYPE_ALIAS:
    free(ty->d.TYPE_ALIAS.name);
    break;
  case PP_FUNCTION:
    free_pp_type(ty->d.FUNCTION.ret);
    free_annot_list_with_name(ty->d.FUNCTION.param);
    break;
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
  free(ty);
}

void free_varg(struct pp_varg_list *l) {
  if (l == NULL)
    return;
  free_varg(l->next);
  free_ra(l->val);
  free_atype(l->type);
  free(l);
}

void free_pp_expr(struct pp_expr *e) {
  switch (e->t) {
  case PP_CONST:
    break;
  case PP_STRING:
    break;
  case PP_VAR:
    free(e->d.VAR.name);
    break;
  case PP_BINOP:
    free_pp_expr(e->d.BINOP.left);
    free_pp_expr(e->d.BINOP.right);
    break;
  case PP_UNOP:
    free_pp_expr(e->d.UNOP.arg);
    break;
  case PP_CAST:
    free_pp_pretype(e->d.CAST.ty);
    free_pp_expr(e->d.CAST.arg);
    break;
  case PP_CALL:
    free_pp_expr(e->d.CALL.func);
    free_pp_expr_list(e->d.CALL.args);
    if (e->d.CALL.vargs != NULL) {
      free_varg(e->d.CALL.vargs->pre);
      free(e->d.CALL.vargs);
    }
    break;
  case PP_DEREF:
    free_pp_expr(e->d.DEREF.arg);
    break;
  case PP_ADDRESS:
    free_pp_expr(e->d.ADDRESS.arg);
    break;
  case PP_SIZEOFTYPE:
    free_pp_pretype(e->d.SIZEOFTYPE.ty);
    break;
  case PP_INDEX:
    free_pp_expr(e->d.INDEX.arg);
    free_pp_expr(e->d.INDEX.pos);
    break;
  case PP_FIELDOF:
    free_pp_expr(e->d.FIELDOF.arg);
    free(e->d.FIELDOF.name);
    break;
  case PP_FIELDOFPTR:
    free_pp_expr(e->d.FIELDOFPTR.arg);
    free(e->d.FIELDOFPTR.name);
    break;
  case PP_ENUMLIT:
    free(e->d.ENUMLIT.name);
    break;
  case PP_CONDITION:
    free_pp_expr(e->d.CONDITION.cond);
    free_pp_expr(e->d.CONDITION.btrue);
    free_pp_expr(e->d.CONDITION.bfalse);
    break;
  }
  free_type(e->type);
  free(e);
}

void free_annot_list(struct annot_list *al) {
  if (al == NULL)
    return;
  struct annot_list *tl = al->tail;
  if (al->head->type != NULL)
    free_pp_pretype(al->head->type);
  free(al->head);
  free(al);
  free_annot_list(tl);
}

void free_pp_simple(struct pp_simple *s) {
  if (s == NULL)
    return;
  switch (s->t) {
  case PP_COMPUTATION:
    free_pp_expr(s->d.COMPUTATION.arg);
    break;
  case PP_ASGN:
    free_pp_expr(s->d.ASGN.left);
    free_pp_expr(s->d.ASGN.right);
    break;
  case PP_INCDEC:
    free_pp_expr(s->d.INCDEC.arg);
    break;
  }
  free(s);
}

void free_pp_decl_type(struct pp_type *ty) {
  switch (ty->t) {
  case PP_BASIC:
  case PP_STRUCT:
  case PP_UNION:
  case PP_ENUM:
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
  case PP_TYPE_ALIAS:
    return;
  case PP_PTR:
    free_pp_decl_type(ty->d.PTR.ty);
    break;
  case PP_ARRAY:
    free_pp_expr(ty->d.ARRAY.size);
    free_pp_decl_type(ty->d.ARRAY.ty);
    break;
  case PP_FUNCTION:
    free_annot_list_with_name(ty->d.FUNCTION.param);
    free_pp_decl_type(ty->d.FUNCTION.ret);
    break;
  }
  free(ty);
}

void free_pp_initializer_list(struct pp_initializer_list *init_list);

void free_pp_initializer(struct pp_initializer *init) {
  switch (init->t) {
  case PP_SINGLE_EXPR: free_pp_expr(init->d.SINGLE_EXPR.expr);
                       break;
  case PP_INIT_LIST: free_pp_initializer_list(init->d.INIT_LIST.list);
                     break;
  }
  free(init);
}

void free_pp_designator(struct pp_designator *desig) {
  if (desig == NULL)
    return;
  switch (desig->t) {
  case PP_AT_INDEX: free_pp_expr(desig->d.AT_INDEX.index);
                    break;
  case PP_AT_MEMBER: free(desig->d.AT_MEMBER.field);
                     break;
  }
  free_pp_designator(desig->next);
  free(desig);
}

void free_pp_initializer_list(struct pp_initializer_list *init_list) {
  switch (init_list->t) {
  case PP_NEXT: free_pp_initializer(init_list->d.NEXT.init);
                break;
  case PP_DESIG: free_pp_designator(init_list->d.DESIG.desig);
                 free_pp_initializer(init_list->d.DESIG.init);
                 break;
  }
  if (init_list->next != NULL)
    free_pp_initializer_list(init_list->next);
  free(init_list);
}

void free_pp_enum_list(struct pp_enum_list *l) {
  if (l == NULL)
    return;
  struct pp_enum_list *tl = l->next;
  free(l);
  free_pp_enum_list(tl);
}

void free_lvar_list(struct lvar_list *l) {
  if (l == NULL)
    return;
  struct lvar_list *tl = l->next;
  free_atype(l->type);
  free(l);
  free_lvar_list(tl);
}

void free_atype_list(struct atype_list *l) {
  if (l == NULL)
    return;
  struct atype_list *tl = l->next;
  free(l);
  free_atype_list(tl);
}

void free_term_list(struct term_list *l) {
  if (l == NULL)
    return;
  struct term_list *tl = l->next;
  free_atype_list(l->qv);
  free(l);
  free_term_list(tl);
}

void free_pp_spec(struct pp_spec *s) {
  free_lvar_list(s->with);
  free_atype_list(s->witht);
  free(s);
}

void free_partial_program(struct partial_program *pp) {
  switch (pp->t) {
  case PP_FIRST_DECL:
    free(pp->d.FIRST_DECL.pre->triv);
    free_derivtype(pp->d.FIRST_DECL.pre->deriv);
    free(pp->d.FIRST_DECL.pre);
    if (pp->d.FIRST_DECL.init != NULL)
      free_pp_initializer(pp->d.FIRST_DECL.init);
    break;
  case PP_MORE_DECL:
    free_derivtype(pp->d.MORE_DECL.deriv);
    if (pp->d.MORE_DECL.init != NULL)
      free_pp_initializer(pp->d.MORE_DECL.init);
    break;
  case PP_SIMPLE:
    free_pp_simple(pp->d.SIMPLE.simple);
    break;
  case PP_RETURN:
    if (pp->d.RETURN.ret != NULL)
      free_pp_expr(pp->d.RETURN.ret);
    break;
  case PP_WHILE:
    free_pp_expr(pp->d.WHILE.cond);
    break;
  case PP_IF:
    free_pp_expr(pp->d.IF.cond);
    break;
  case PP_BREAK:
  case PP_CONTINUE:
  case PP_ELSE:
  case PP_DO:
  case PP_END:
  case PP_BLOCK:
  case PP_DEFAULT:
    break;
  case PP_FOR:
    free_pp_simple(pp->d.FOR.init);
    if (pp->d.FOR.cond != NULL)
      free_pp_expr(pp->d.FOR.cond);
    free_pp_simple(pp->d.FOR.step);
    break;
  case PP_SWITCH:
    free_pp_expr(pp->d.SWITCH.cond);
    break;
  case PP_CASE:
    free_pp_expr(pp->d.CASE.cond);
    break;
  case PP_ASSERT:
  case PP_INV:
  case PP_WI:
    break;
  case PP_PROOF:
  case PP_DO_STRATEGY:
  case PP_MISSING_INV:
  case PP_SKIP:
    break;
  case PP_STRUCT_DEF:
    free_annot_list(pp->d.STRUCT_DEF.field);
    break;
  case PP_UNION_DEF:
    free_annot_list(pp->d.UNION_DEF.field);
    break;
  case PP_ENUM_DEF:
    free_pp_enum_list(pp->d.ENUM_DEF.rator);
    break;
  case PP_STRUCT_DEC:
  case PP_UNION_DEC:
  case PP_ENUM_DEC:
    break;
  case PP_SEPDEF:
    free_atype_list(pp->d.SEPDEF.witht);
    free_lvar_list(pp->d.SEPDEF.with);
    break;
  case PP_COQ_DEC:
    free_term_list(pp->d.COQ_DEC.name);
    break;
  case PP_COQ_TYPE_ALIAS:
    free_atype(pp->d.COQ_TYPE_ALIAS.type);
    break;
  case PP_ATYPE_DEC:
    free_atype_list(pp->d.ATYPE_DEC.name);
    break;
  case PP_PROJ_DEC:
    free_term_list(pp->d.PROJ_DEC.projs);
    break;
  case PP_RECORD_DEC:
    free_atype_list(pp->d.RECORD_DEC.params);
    free_lvar_list(pp->d.RECORD_DEC.fields);
    break;
  case PP_FUNC_DEF:
    free_pp_pretype(pp->d.FUNC_DEF.func);
    if (pp->d.FUNC_DEF.spec != NULL)
      free_pp_spec(pp->d.FUNC_DEF.spec);
    break;
  case PP_FUNC_DEC:
    free_pp_pretype(pp->d.FUNC_DEC.func);
    if (pp->d.FUNC_DEC.spec != NULL)
      free_pp_spec(pp->d.FUNC_DEC.spec);
    break;
  }
  free(pp);
}
