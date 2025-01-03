#include "utils.h"
#include "cp.h"

// destruct type
struct pp_type *cpap_param_type(struct pp_type *type) {
  switch (type->t) {
  case PP_ARRAY:
    free_pp_expr(type->d.ARRAY.size);
    type->t = PP_PTR;
    type->d.PTR.ty = type->d.ARRAY.ty;
    return type;
  case PP_STRUCT:
  case PP_UNION:
  case PP_BASIC:
  case PP_ENUM:
  case PP_PTR:
    return type;
  case PP_FUNCTION:
    return PPPtr(type);
  case PP_TYPE_ALIAS: {
    struct type *onto = type->d.TYPE_ALIAS.info->type;
    free(type->d.TYPE_ALIAS.name);
    free(type);
    struct pp_type *pp = pp_type_of_type(type_unalias(onto));
    return cpap_param_type(pp); }
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
}

void cpap_type(struct pp_type *ty) {
  switch (ty->t) {
  case PP_BASIC:
  case PP_STRUCT:
  case PP_UNION:
  case PP_ENUM:
  case PP_TYPE_ALIAS:
    break;
  case PP_PTR:
    cpap_type(ty->d.PTR.ty);
    break;
  case PP_ARRAY:
    cpap_type(ty->d.ARRAY.ty);
    break;
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM: {
    assert(0);
    break;
  }
  case PP_FUNCTION: {
    struct annot_list *i;
    for (i = ty->d.FUNCTION.param; i != NULL; i = i->tail)
      i->head->type->type = cpap_param_type(i->head->type->type);
    break; }
  }
}

void cpap_expr(struct pp_expr *e) {
  switch (e->t) {
  case PP_CONST:
  case PP_STRING:
  case PP_VAR:
  case PP_ENUMLIT:
    break;
  case PP_BINOP:
    cpap_expr(e->d.BINOP.left);
    cpap_expr(e->d.BINOP.right);
    break;
  case PP_UNOP:
    cpap_expr(e->d.UNOP.arg);
    break;
  case PP_CAST:
    cpap_type(e->d.CAST.ty->type);
    cpap_expr(e->d.CAST.arg);
    break;
  case PP_CALL: {
    cpap_expr(e->d.CALL.func);
    struct pp_expr_list *i;
    for (i = e->d.CALL.args; i != NULL; i = i->tail)
      cpap_expr(i->head);
    break; }
  case PP_DEREF:
    cpap_expr(e->d.DEREF.arg);
    break;
  case PP_ADDRESS:
    cpap_expr(e->d.ADDRESS.arg);
    break;
  case PP_SIZEOFTYPE:
    cpap_type(e->d.SIZEOFTYPE.ty->type);
    break;
  case PP_INDEX:
    cpap_expr(e->d.INDEX.arg);
    cpap_expr(e->d.INDEX.pos);
    break;
  case PP_FIELDOF:
    cpap_expr(e->d.FIELDOF.arg);
    break;
  case PP_FIELDOFPTR:
    cpap_expr(e->d.FIELDOFPTR.arg);
    break;
  case PP_CONDITION:
    cpap_expr(e->d.CONDITION.cond);
    cpap_expr(e->d.CONDITION.btrue);
    cpap_expr(e->d.CONDITION.bfalse);
    break;
  }
}

void cpap_param(struct annot_list *param) {
  for (; param != NULL; param = param->tail)
    param->head->type->type = cpap_param_type(param->head->type->type);
}
