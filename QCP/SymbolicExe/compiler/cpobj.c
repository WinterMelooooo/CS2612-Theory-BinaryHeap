#include "utils.h"
#include "cp.h"

int cpo_is_function(struct pp_type *ty) {
  return (ty->t == PP_FUNCTION) ||
         (ty->t == PP_TYPE_ALIAS && type_unalias(ty->d.TYPE_ALIAS.info->type)->t == T_FUNCTION);
}

void cpo_type(struct pp_type *ty) {
  switch (ty->t) {
  case PP_BASIC:
  case PP_STRUCT:
  case PP_UNION:
  case PP_ENUM:
  case PP_TYPE_ALIAS:
    break;
  case PP_PTR:
    cpo_type(ty->d.PTR.ty);
    break;
  case PP_ARRAY:
    if (cpo_is_function(ty->d.ARRAY.ty))
      failwith("Array of functions");
    cpo_type(ty->d.ARRAY.ty);
    break;
  case PP_FUNCTION: {
    struct annot_list *i;
    for (i = ty->d.FUNCTION.param; i != NULL; i = i->tail)
      cpo_type(i->head->type->type);
    break; }
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
}

void cpo_expr(struct pp_expr *e) {
  switch (e->t) {
  case PP_CONST:
  case PP_STRING:
  case PP_VAR:
  case PP_ENUMLIT:
    break;
  case PP_BINOP:
    cpo_expr(e->d.BINOP.left);
    cpo_expr(e->d.BINOP.right);
    break;
  case PP_UNOP:
    cpo_expr(e->d.UNOP.arg);
    break;
  case PP_CAST:
    cpo_type(e->d.CAST.ty->type);
    if (cpo_is_function(e->d.CAST.ty->type))
      failwith("Invalid type where arithmetic or pointer type is required");
    cpo_expr(e->d.CAST.arg);
    break;
  case PP_CALL: {
    cpo_expr(e->d.CALL.func);
    struct pp_expr_list *i;
    for (i = e->d.CALL.args; i != NULL; i = i->tail)
      cpo_expr(i->head);
    break; }
  case PP_DEREF:
    cpo_expr(e->d.DEREF.arg);
    break;
  case PP_ADDRESS:
    cpo_expr(e->d.ADDRESS.arg);
    break;
  case PP_SIZEOFTYPE:
    cpo_type(e->d.SIZEOFTYPE.ty->type);
    if (cpo_is_function(e->d.SIZEOFTYPE.ty->type))
      failwith("`sizeof' cannot be used with function types");
    break;
  case PP_INDEX:
    cpo_expr(e->d.INDEX.arg);
    cpo_expr(e->d.INDEX.pos);
    break;
  case PP_FIELDOF:
    cpo_expr(e->d.FIELDOF.arg);
    break;
  case PP_FIELDOFPTR:
    cpo_expr(e->d.FIELDOFPTR.arg);
    break;
  case PP_CONDITION:
    cpo_expr(e->d.CONDITION.cond);
    cpo_expr(e->d.CONDITION.btrue);
    cpo_expr(e->d.CONDITION.bfalse);
    break;
  }
}

