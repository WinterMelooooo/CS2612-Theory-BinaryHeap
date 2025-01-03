#include "utils.h"
#include "cp.h"

int cpi_is_incomplete(struct pp_type *ty);

int cpi_is_incomplete_pointed(struct pp_type *ty) {
  switch (ty->t) {
  case PP_ARRAY:
    return cpi_is_incomplete(ty->d.ARRAY.ty);
  case PP_BASIC:
  case PP_STRUCT:
  case PP_UNION:
  case PP_ENUM:
  case PP_FUNCTION:
    return 0;
  case PP_PTR:
    return cpi_is_incomplete_pointed(ty->d.PTR.ty);
  case PP_TYPE_ALIAS: {
    int ret;
    CALL_WITH_TYPE(ty->d.TYPE_ALIAS.info->type, cpi_is_incomplete_pointed, ret);
    return ret; }
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
}

int cpi_is_incomplete(struct pp_type *ty) {
  switch (ty->t) {
  case PP_BASIC:
    return ty->d.BASIC.ty == T_VOID;
  case PP_ARRAY:
    return cpi_is_incomplete(ty->d.ARRAY.ty);
  case PP_STRUCT:
    return ty->d.STRUCT.info->defined == 0;
  case PP_UNION:
    return ty->d.UNION.info->defined == 0;
  case PP_ENUM:
    return 0;
  case PP_PTR:
    return cpi_is_incomplete_pointed(ty->d.PTR.ty);
  case PP_TYPE_ALIAS: {
    int ret;
    CALL_WITH_TYPE(ty->d.TYPE_ALIAS.info->type, cpi_is_incomplete, ret);
    return ret; }
  case PP_FUNCTION:
    return 0;
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
}

int cpi_is_void(struct pp_type *ty) {
  if (ty->t == PP_TYPE_ALIAS) {
    int ret;
    CALL_WITH_TYPE(ty->d.TYPE_ALIAS.info->type, cpi_is_void, ret);
    return ret;
  } else
    return ty->t == PP_BASIC && ty->d.BASIC.ty == T_VOID;
}

void cpi_expr(struct pp_expr *e) {
  struct pp_expr_list *el;

  switch (e->t) {
  case PP_SIZEOFTYPE:
    if (cpi_is_incomplete(e->d.SIZEOFTYPE.ty->type) && !cpi_is_void(e->d.SIZEOFTYPE.ty->type))
      failwith("Invalid application of `sizeof' to an incomplete type");
    break;
  case PP_CAST:
    if (cpi_is_incomplete(e->d.CAST.ty->type) && !cpi_is_void(e->d.CAST.ty->type))
      failwith("Cast target is an incomplete type");
    cpi_expr(e->d.CAST.arg);
    break;
  case PP_CONST:
  case PP_STRING:
  case PP_VAR:
  case PP_ENUMLIT:
    break;
  case PP_BINOP:
    cpi_expr(e->d.BINOP.left);
    cpi_expr(e->d.BINOP.right);
    break;
  case PP_UNOP:
    cpi_expr(e->d.UNOP.arg);
    break;
  case PP_INDEX:
    cpi_expr(e->d.INDEX.arg);
    cpi_expr(e->d.INDEX.pos);
    break;
  case PP_FIELDOFPTR:
    cpi_expr(e->d.FIELDOFPTR.arg);
    break;
  case PP_CALL:
    for (el = e->d.CALL.args; el != NULL; el = el->tail)
      cpi_expr(el->head);
    break;
  case PP_DEREF:
    cpi_expr(e->d.DEREF.arg);
    break;
  case PP_ADDRESS:
    cpi_expr(e->d.ADDRESS.arg);
    break;
  case PP_FIELDOF:
    cpi_expr(e->d.FIELDOF.arg);
    break;
  case PP_CONDITION:
    cpi_expr(e->d.CONDITION.cond);
    cpi_expr(e->d.CONDITION.btrue);
    cpi_expr(e->d.CONDITION.bfalse);
    break;
  }
}

/* void cpi_assert(struct RAssertion *ra) { */
/*   struct RA_list *ral; */

/*   switch (ra->t) { */
/*   case RA_CAST: */
/*     if (cpi_is_incomplete(ra->d.RACAST.ty, env) && !cpi_is_void(ra->d.RACAST.ty, env)) */
/*       failwith("Cast target is an incomplete type"); */
/*     cpi_assert(ra->d.RACAST.arg, env); */
/*     break; */
/*   case RA_SIZEOF: */
/*     if (cpi_is_incomplete(ra->d.RASIZEOF.ty, env) && !cpi_is_void(ra->d.RASIZEOF.ty, env)) */
/*       failwith("Invalid application of `sizeof' to an incomplete type"); */
/*     break; */
/*   case RA_BINOP: */
/*     cpi_assert(ra->d.RABINOP.left, env); */
/*     cpi_assert(ra->d.RABINOP.right, env); */
/*     break; */
/*   case RA_CONN: */
/*     cpi_assert(ra->d.RACONN.left, env); */
/*     cpi_assert(ra->d.RACONN.right, env); */
/*     break; */
/*   case RA_UNOP: */
/*     cpi_assert(ra->d.RAUNOP.arg, env); */
/*     break; */
/*   case RA_CALL: */
/*     for (ral = ra->d.RACALL.args; ral != NULL; ral = ral->tail) */
/*       cpi_assert(ral->head, env); */
/*     break; */
/*   case RA_DEREF: */
/*     if (ra->d.RADEREF.ty != NULL && cpi_is_incomplete(ra->d.RADEREF.ty, env)) */
/*       failwith("Incomplete type where a complete type is required"); */
/*     cpi_assert(ra->d.RADEREF.arg, env); */
/*     break; */
/*   case RA_ADDRES: */
/*     cpi_assert(ra->d.RAADDRES.arg, env); */
/*     break; */
/*   case RA_FIELDOF: */
/*     cpi_assert(ra->d.RAFIELDOF.arg, env); */
/*     break; */
/*   case RA_QFOP: */
/*     cpi_assert(ra->d.RAQFOP.arg, env); */
/*     break; */
/*   case RA_INDEX: */
/*     cpi_assert(ra->d.RAINDEX.arg, env); */
/*     cpi_assert(ra->d.RAINDEX.pos, env); */
/*     break; */
/*   case RA_FIELDOFPTR: */
/*     cpi_assert(ra->d.RAFIELDOFPTR.arg, env); */
/*     break; */
/*   case RA_SHADOW: */
/*     cpi_assert(ra->d.RASHADOW.arg, env); */
/*     break; */
/*   case RA_OLD: */
/*     cpi_assert(ra->d.RAOLD.arg, env); */
/*     break; */
/*   case RA_DATA_AT: */
/*     if (ra->d.RADATA_TA.type != NULL && cpi_is_incomplete(ra->d.RADATA_TA.type, env)) */
/*       failwith("Incomplete type where a complete type is required"); */
/*     cpi_assert(ra->d.RADATA_TA.addr, env); */
/*     cpi_assert(ra->d.RADATA_TA.val, env); */
/*     break; */
/*   case RA_FIELD_ADDRESS: */
/*     cpi_assert(ra->d.RAFIELD_ADDRESS.addr, env); */
/*     break; */
/*   case RA_ARR: */
/*     if (ra->d.RAARR.elt != NULL && cpi_is_incomplete(ra->d.RAARR.elt, env)) */
/*       failwith("Incomplete type where a complete type is required"); */
/*     cpi_assert(ra->d.RAARR.addr, env); */
/*     cpi_assert(ra->d.RAARR.len, env); */
/*     cpi_assert(ra->d.RAARR.list, env); */
/*     break; */
/*   case RA_TIME_COST: */
/*   case RA_VAR: */
/*   case RA_CONST: */
/*   case RA_ENUMLIT: */
/*   case RA_EMP: */
/*   case RA___RETURN: */
/*   case RA_TRUE: */
/*   case RA_FALSE: */
/*     break; */
/*   } */
/* } */
