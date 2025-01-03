#include "utils.h"
#include "cp.h"

int cppa_is_incomplete(struct type *ty) {
  ty = type_unalias(ty);
  switch (ty->t) {
  case T_STRUCT:
    return ty->d.STRUCT.info->defined == 0;
  case T_UNION:
    return ty->d.UNION.info->defined == 0;
  case T_ENUM:
    return ty->d.ENUM.info->defined == 0;
  case T_FUNCTION:
  case T_BASIC:
  case T_PTR:
  case T_ARRAY:
    return 0; // it might not be complete, but it is, at this stage of compilation
  case T_TYPE_ALIAS:
    assert(0);
  }
}

int cppa_invalid_ptr_arith(struct type *ty) {
  ty = type_unalias(ty);
  if (ty->t == T_PTR)
    return cppa_is_incomplete(ty->d.PTR.ty);
  else if (ty->t == T_ARRAY) // is this case possible?
    return cppa_is_incomplete(ty->d.ARRAY.ty);
  return 0;
}

void cppa_expr(struct pp_expr *e) {
  struct pp_expr_list *el;

  switch (e->t) {
  case PP_SIZEOFTYPE:
    break;
  case PP_CAST:
    cppa_expr(e->d.CAST.arg);
    break;
  case PP_CONST:
  case PP_STRING:
  case PP_VAR:
  case PP_ENUMLIT:
    break;
  case PP_BINOP:
    cppa_expr(e->d.BINOP.left);
    cppa_expr(e->d.BINOP.right);
    if (e->d.BINOP.op == T_PLUS ||
        e->d.BINOP.op == T_MINUS) {
      if (cppa_invalid_ptr_arith(e->d.BINOP.left->type) ||
          cppa_invalid_ptr_arith(e->d.BINOP.right->type))
        failwith("Arithmetic on a pointer to an incomplete type");
    }
    break;
  case PP_UNOP:
    cppa_expr(e->d.UNOP.arg);
    break;
  case PP_INDEX:
    cppa_expr(e->d.INDEX.arg);
    cppa_expr(e->d.INDEX.pos);
    break;
  case PP_FIELDOFPTR:
    cppa_expr(e->d.FIELDOFPTR.arg);
    break;
  case PP_CALL:
    for (el = e->d.CALL.args; el != NULL; el = el->tail)
      cppa_expr(el->head);
    break;
  case PP_DEREF:
    cppa_expr(e->d.DEREF.arg);
    if (cppa_invalid_ptr_arith(e->d.DEREF.arg->type))
      failwith("Incomplete type where a complete type is required");
    break;
  case PP_ADDRESS:
    cppa_expr(e->d.ADDRESS.arg);
    break;
  case PP_FIELDOF:
    cppa_expr(e->d.FIELDOF.arg);
    break;
  case PP_CONDITION:
    cppa_expr(e->d.CONDITION.cond);
    cppa_expr(e->d.CONDITION.btrue);
    cppa_expr(e->d.CONDITION.bfalse);
    break;
  }
}

void cppa_simple_cmd(struct pp_simple *simple) {
  switch (simple->t) {
  case PP_COMPUTATION:
    break;
  case PP_ASGN:
    if (simple->d.ASGN.op == T_ADD_ASSIGN ||
        simple->d.ASGN.op == T_SUB_ASSIGN)
      if (cppa_invalid_ptr_arith(simple->d.ASGN.left->type))
        failwith("Arithmetic on a pointer to an incomplete type");
    break;
  case PP_INCDEC:
    if (cppa_invalid_ptr_arith(simple->d.INCDEC.arg->type))
      failwith("Arithmetic on a pointer to an incomplete type");
    break;
  }
}

