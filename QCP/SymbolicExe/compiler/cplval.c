#include "utils.h"
#include "cp.h"

int cplv_is_lval(struct pp_expr *e) {
  switch (e->t) {
  case PP_FIELDOFPTR:
  case PP_INDEX:
  case PP_VAR:
  case PP_DEREF:
  case PP_FIELDOF:
    return 1;
  case PP_SIZEOFTYPE:
  case PP_CONST:
  case PP_STRING:
  case PP_BINOP:
  case PP_UNOP:
  case PP_CAST:
  case PP_CALL:
  case PP_ADDRESS:
  case PP_ENUMLIT:
  case PP_CONDITION:
    return 0;
  }
}

void cplv_expr(struct pp_expr *e) {
  struct pp_expr_list *el;

  switch (e->t) {

  case PP_ADDRESS:
    if (!cplv_is_lval(e->d.ADDRESS.arg))
      failwith("Cannot take the address of an rvalue");
    cplv_expr(e->d.ADDRESS.arg);
    break;

  case PP_CONST:
  case PP_STRING:
  case PP_VAR:
    break;
  case PP_BINOP:
    cplv_expr(e->d.BINOP.left);
    cplv_expr(e->d.BINOP.right);
    break;
  case PP_UNOP:
    cplv_expr(e->d.UNOP.arg);
    break;
  case PP_INDEX:
    cplv_expr(e->d.INDEX.arg);
    cplv_expr(e->d.INDEX.pos);
    break;
  case PP_FIELDOFPTR:
    cplv_expr(e->d.FIELDOFPTR.arg);
    break;
  case PP_SIZEOFTYPE:
    break;
  case PP_CAST:
    cplv_expr(e->d.CAST.arg);
    break;
  case PP_CALL:
    for (el = e->d.CALL.args; el != NULL; el = el->tail)
      cplv_expr(el->head);
    break;
  case PP_DEREF:
    cplv_expr(e->d.DEREF.arg);
    break;
  case PP_FIELDOF:
    cplv_expr(e->d.FIELDOF.arg);
    break;
  case PP_ENUMLIT:
    break;
  case PP_CONDITION:
    cplv_expr(e->d.CONDITION.cond);
    cplv_expr(e->d.CONDITION.btrue);
    cplv_expr(e->d.CONDITION.bfalse);
    break;
  }
}

void cplv_simple_cmd(struct pp_simple *scmd) {
  if (scmd == NULL)
    return;

  switch (scmd->t) {
  case PP_COMPUTATION:
    break;
  case PP_ASGN:
    if (!cplv_is_lval(scmd->d.ASGN.left))
      failwith("Expression is not assignable");
    break;
  case PP_INCDEC:
    if (!cplv_is_lval(scmd->d.INCDEC.arg))
      failwith("Expression is not assignable");
    break;
  }
}
