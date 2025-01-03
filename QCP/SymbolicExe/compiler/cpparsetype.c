#include "utils.h"
#include "cp.h"

struct annot_list *cppt_annot_list(struct annot_list *l) {
  if (l == NULL)
    return l;
  l->head->name = cppt_type(l->head->type);
  cppt_annot_list(l->tail);
  return l;
}

char *cppt_derive_type(struct pp_type **base, struct pp_derivtype *deriv) {
  struct pp_derivtype *i = deriv;
  struct pp_type *res = *base;
  do {
    switch (i->t) {
    case PP_DERIV_END:
      *base = res;
      return i->d.END.name;
    case PP_DERIV_PTR:
      res = PPPtr(res);
      i = i->d.PTR.deriv;
      break;
    case PP_DERIV_ARRAY:
      res = PPArray(res, i->d.ARRAY.size);
      i = i->d.ARRAY.deriv;
      break;
    case PP_DERIV_FUNCTION:
      res = PPFunction(res, cppt_annot_list(i->d.FUNCTION.param));
      i = i->d.FUNCTION.deriv;
      break;
    }
  } while (1);
}

char *cppt_type(struct pp_pretype *pre) {
  switch (pre->triv->t) {
  case PP_TRIV_BASIC:
    pre->type = PPBasic(pre->triv->d.BASIC.ty);
    break;
  case PP_TRIV_STRUCT:
    pre->type = PPStruct(pre->triv->d.STRUCT.name);
    break;
  case PP_TRIV_UNION:
    pre->type = PPUnion(pre->triv->d.UNION.name);
    break;
  case PP_TRIV_ENUM:
    pre->type = PPEnum(pre->triv->d.ENUM.name);
    break;
  case PP_TRIV_ANON_STRUCT:
    pre->type = PPAnonStruct(pre->triv->d.ANON_STRUCT.name,
                             cppt_annot_list(pre->triv->d.ANON_STRUCT.fields));
    break;
  case PP_TRIV_ANON_UNION:
    pre->type = PPAnonUnion(pre->triv->d.ANON_UNION.name,
                            cppt_annot_list(pre->triv->d.ANON_UNION.fields));
    break;
  case PP_TRIV_ANON_ENUM:
    pre->type = PPAnonEnum(pre->triv->d.ANON_ENUM.name,
                           pre->triv->d.ANON_ENUM.names);
    break;
  case PP_TRIV_TYPE_ALIAS:
    pre->type = PPTypeAlias(pre->triv->d.TYPE_ALIAS.name);
    break;
  }
  return cppt_derive_type(&pre->type, pre->deriv);
}

void cppt_expr_list(struct pp_expr_list *l) {
  if (l == NULL)
    return;
  cppt_expr(l->head);
  cppt_expr_list(l->tail);
}

void cppt_varg(struct pp_varg_list *l) {
  if (l == NULL)
    return;
  cppt_assert(l->val);
  cppt_varg(l->next);
}

void cppt_expr(struct pp_expr *e) {
  switch (e->t) {
  case PP_CONST:
  case PP_STRING:
  case PP_VAR:
  case PP_ENUMLIT:
    break;
  case PP_BINOP:
    cppt_expr(e->d.BINOP.left);
    cppt_expr(e->d.BINOP.right);
    break;
  case PP_UNOP:
    cppt_expr(e->d.UNOP.arg);
    break;
  case PP_CAST:
    cppt_type(e->d.CAST.ty);
    cppt_expr(e->d.CAST.arg);
    break;
  case PP_CALL:
    cppt_expr(e->d.CALL.func);
    cppt_expr_list(e->d.CALL.args);
    if (e->d.CALL.vargs != NULL)
      cppt_varg(e->d.CALL.vargs->pre);
    break;
  case PP_DEREF:
    cppt_expr(e->d.DEREF.arg);
    break;
  case PP_ADDRESS:
    cppt_expr(e->d.ADDRESS.arg);
    break;
  case PP_SIZEOFTYPE:
    cppt_type(e->d.SIZEOFTYPE.ty);
    break;
  case PP_INDEX:
    cppt_expr(e->d.INDEX.arg);
    cppt_expr(e->d.INDEX.pos);
    break;
  case PP_FIELDOF:
    cppt_expr(e->d.FIELDOF.arg);
    break;
  case PP_FIELDOFPTR:
    cppt_expr(e->d.FIELDOFPTR.arg);
    break;
  case PP_CONDITION:
    cppt_expr(e->d.CONDITION.cond);
    cppt_expr(e->d.CONDITION.btrue);
    cppt_expr(e->d.CONDITION.bfalse);
    break;
 }
}

void cppt_assert(struct RAssertion *a) {
  switch (a->t) {
  case RA_CONST:
  case RA_PROGVAR:
  case RA_LOGICVAR:
  case RA_ENUMLIT:
  case RA_EMP:
  case RA___RETURN:
  case RA_TRUE:
  case RA_FALSE:
  case RA_TIME_COST:
    break;
  case RA_BINOP:
    cppt_assert(a->d.RABINOP.left);
    cppt_assert(a->d.RABINOP.right);
    break;
  case RA_CONN:
    cppt_assert(a->d.RACONN.left);
    cppt_assert(a->d.RACONN.right);
    break;
  case RA_UNOP:
    cppt_assert(a->d.RAUNOP.arg);
    break;
  case RA_CAST:
    cppt_type(a->d.RACAST.ty);
    cppt_assert(a->d.RACAST.arg);
    break;
  case RA_APP:
    cppt_assert(a->d.RAAPP.f);
    cppt_assert(a->d.RAAPP.rand);
    break;
  case RA_DEREF:
    cppt_assert(a->d.RADEREF.arg);
    if (a->d.RADEREF.ty != NULL)
      cppt_type(a->d.RADEREF.ty);
    break;
  case RA_ADDRESS:
    cppt_assert(a->d.RAADDRESS.arg);
    break;
  case RA_INDEX:
    cppt_assert(a->d.RAINDEX.arg);
    cppt_assert(a->d.RAINDEX.pos);
    break;
  case RA_FIELDOF:
    cppt_assert(a->d.RAFIELDOF.arg);
    if (a->d.RAFIELDOF.ty != NULL)
      cppt_type(a->d.RAFIELDOF.ty);
    break;
  case RA_FIELDOFPTR:
    cppt_assert(a->d.RAFIELDOFPTR.arg);
    if (a->d.RAFIELDOFPTR.ty != NULL)
      cppt_type(a->d.RAFIELDOFPTR.ty);
    break;
  case RA_QFOP:
    cppt_assert(a->d.RAQFOP.arg);
    break;
  case RA_SIZEOF:
    cppt_type(a->d.RASIZEOF.ty);
    ASSIGN_TYPE(a->d.RASIZEOF.type, type_of_pp_type(a->d.RASIZEOF.ty->type));
    break;
  case RA_OLD:
    cppt_assert(a->d.RAOLD.arg);
    break;
  case RA_SHADOW:
    cppt_assert(a->d.RASHADOW.arg);
    break;
  case RA_DATA_AT:
    cppt_assert(a->d.RADATA_AT.addr);
    cppt_assert(a->d.RADATA_AT.val);
    if (a->d.RADATA_AT.type != NULL)
      cppt_type(a->d.RADATA_AT.type);
    break;
  case RA_UNDEF_DATA_AT:
    cppt_assert(a->d.RAUNDEF_DATA_AT.addr);
    if (a->d.RAUNDEF_DATA_AT.type != NULL)
      cppt_type(a->d.RAUNDEF_DATA_AT.type);
    break;
  case RA_FIELD_ADDRESS:
    cppt_assert(a->d.RAFIELD_ADDRESS.addr);
    if (a->d.RAFIELD_ADDRESS.ty != NULL)
      cppt_type(a->d.RAFIELD_ADDRESS.ty);
    break;
  case RA_ARR:
    cppt_assert(a->d.RAARR.addr);
    cppt_assert(a->d.RAARR.len);
    cppt_assert(a->d.RAARR.list);
    if (a->d.RAARR.elt != NULL)
      cppt_type(a->d.RAARR.elt);
    break;
  case RA_SPEC:
    cppt_assert(a->d.RASPEC.f);
    break;
  case RA_ANN:
    cppt_assert(a->d.RAANN.expr);
    break;
  }
}
