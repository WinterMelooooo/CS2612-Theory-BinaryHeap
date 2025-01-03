#include "utils.h"
#include "cp.h"

unsigned long long cpc_eval(struct pp_expr *e);
int cpc_sizeof(struct pp_type *ty);

// int -> unsigned int
void cpc_eval_to_const(struct pp_expr *e) {
  unsigned long long n = cpc_eval(e);
  switch (e->t) {
  case PP_BINOP:
    free_pp_expr(e->d.BINOP.left);
    free_pp_expr(e->d.BINOP.right);
    break;
  case PP_UNOP:
    free_pp_expr(e->d.UNOP.arg);
    break;
  case PP_SIZEOFTYPE:
    free_pp_pretype(e->d.SIZEOFTYPE.ty);
    break;
  default: /* impossible */
    break;
  }
  e->t = PP_CONST;
  e->d.CONST.value = n;
}

/* check and convert array size to constant. */
void cpc_type(struct pp_type *type) {
  switch (type->t) {
  case PP_BASIC:
  case PP_STRUCT:
  case PP_UNION:
  case PP_ENUM:
  case PP_TYPE_ALIAS:
    break;
  case PP_PTR:
    cpc_type(type->d.PTR.ty);
    break;
  case PP_ARRAY:
    cpc_eval_to_const(type->d.ARRAY.size);
    if ((int)type->d.ARRAY.size->d.CONST.value < 0)
      failwith("Array with a negative size");
    break;
  case PP_FUNCTION: {
    struct annot_list *i;
    for (i = type->d.FUNCTION.param; i != NULL; i = i->tail)
      cpc_type(i->head->type->type);
    cpc_type(type->d.FUNCTION.ret);
    break; }
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
}

/* do not check */
int cpc_align_of(struct pp_type *type) {
  switch (type->t) {
  case PP_BASIC:
    switch (type->d.BASIC.ty) {
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
    return 0; //no case
  case PP_STRUCT:
    return type->d.STRUCT.info->alignment;
  case PP_UNION:
    return type->d.UNION.info->alignment;
  case PP_ENUM: return 4;
  case PP_PTR:  return 8;
  case PP_ARRAY:
    return cpc_align_of(type->d.ARRAY.ty);
  case PP_TYPE_ALIAS:
    return type_align(type->d.TYPE_ALIAS.info->type);
  case PP_FUNCTION:
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
}

/* do not check */
int cpc_sizeof(struct pp_type *type) {
  switch (type->t) {
  case PP_BASIC:
    switch (type->d.BASIC.ty) {
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
    return 0; //no case
  case PP_STRUCT:
    return type->d.STRUCT.info->size;
  case PP_UNION:
    return type->d.UNION.info->size;
  case PP_ENUM: return 4;
  case PP_PTR:  return 8;
  case PP_ARRAY:
    if (type->d.ARRAY.size->d.CONST.value == 0)
      return 0;
    return type->d.ARRAY.size->d.CONST.value * cpc_sizeof(type->d.ARRAY.ty);
  case PP_TYPE_ALIAS:
    return type_size(type->d.TYPE_ALIAS.info->type);
  case PP_FUNCTION:
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
}

/* do check T when meet `sizeof(T)' */
unsigned long long cpc_eval(struct pp_expr *e) {
  switch (e->t) {
  case PP_CONST:
    return e->d.CONST.value;
  case PP_BINOP:
    switch (e->d.BINOP.op) {
    case T_PLUS:  return cpc_eval(e->d.BINOP.left) +  cpc_eval(e->d.BINOP.right);
    case T_MINUS: return cpc_eval(e->d.BINOP.left) -  cpc_eval(e->d.BINOP.right);
    case T_MUL:   return cpc_eval(e->d.BINOP.left) *  cpc_eval(e->d.BINOP.right);
    case T_DIV:   return cpc_eval(e->d.BINOP.left) /  cpc_eval(e->d.BINOP.right);
    case T_MOD:   return cpc_eval(e->d.BINOP.left) %  cpc_eval(e->d.BINOP.right);
    case T_LT:    return cpc_eval(e->d.BINOP.left) <  cpc_eval(e->d.BINOP.right);
    case T_GT:    return cpc_eval(e->d.BINOP.left) >  cpc_eval(e->d.BINOP.right);
    case T_LE:    return cpc_eval(e->d.BINOP.left) <= cpc_eval(e->d.BINOP.right);
    case T_GE:    return cpc_eval(e->d.BINOP.left) >= cpc_eval(e->d.BINOP.right);
    case T_EQ:    return cpc_eval(e->d.BINOP.left) == cpc_eval(e->d.BINOP.right);
    case T_NE:    return cpc_eval(e->d.BINOP.left) != cpc_eval(e->d.BINOP.right);
    case T_AND:   return cpc_eval(e->d.BINOP.left) && cpc_eval(e->d.BINOP.right);
    case T_OR:    return cpc_eval(e->d.BINOP.left) || cpc_eval(e->d.BINOP.right);
    case T_BAND:  return cpc_eval(e->d.BINOP.left) &  cpc_eval(e->d.BINOP.right);
    case T_BOR:   return cpc_eval(e->d.BINOP.left) |  cpc_eval(e->d.BINOP.right);
    case T_XOR:   return cpc_eval(e->d.BINOP.left) ^  cpc_eval(e->d.BINOP.right);
    case T_SHL:   return cpc_eval(e->d.BINOP.left) << cpc_eval(e->d.BINOP.right);
    case T_SHR:   return cpc_eval(e->d.BINOP.left) >> cpc_eval(e->d.BINOP.right);
    }
    failwith("Expression is not an integer constant expression");
    return 0; //no case
  case PP_UNOP:
    switch (e->d.UNOP.op) {
    case T_UMINUS:  return -cpc_eval(e->d.UNOP.arg);
    case T_UPLUS:   return +cpc_eval(e->d.UNOP.arg);
    case T_NOTBOOL: return !cpc_eval(e->d.UNOP.arg);
    case T_NOTINT:  return ~cpc_eval(e->d.UNOP.arg);
    }
    failwith("Expression is not an integer constant expression");
    return 0; //no case
  case PP_SIZEOFTYPE:
    cpc_type(e->d.SIZEOFTYPE.ty->type);
    return cpc_sizeof(e->d.SIZEOFTYPE.ty->type);
  case PP_ENUMLIT:
    return e->d.ENUMLIT.info->repr;
  case PP_CONDITION:
    if (cpc_eval(e->d.CONDITION.cond))
      return cpc_eval(e->d.CONDITION.btrue);
    else
      return cpc_eval(e->d.CONDITION.bfalse);
  case PP_CAST: {
    struct pp_type *ty = e->d.CAST.ty->type;
    if (ty->t == PP_BASIC && ty->d.BASIC.ty == T_INT)
      return cpc_eval(e->d.CAST.arg);
    else if (ty->t == PP_TYPE_ALIAS) {
      struct type *ty = type_unalias(e->d.CAST.ty->type->d.TYPE_ALIAS.info->type);
      if (ty->t == T_BASIC && ty->d.BASIC.ty == T_INT)
        return cpc_eval(e->d.CAST.arg);
    }
    failwith("Expression is not an integer constant expression");
    return 0; //no case
  }
  case PP_CALL:
  case PP_DEREF:
  case PP_ADDRESS:
  case PP_FIELDOF:
  case PP_VAR:
  case PP_INDEX:
  case PP_FIELDOFPTR:
  case PP_STRING:
    failwith("Expression is not an integer constant expression");
  }
}

void cpc_varg(struct pp_varg_list *l) {
  if (l == NULL)
    return;
  cpc_assert(l->val);
  cpc_varg(l->next);
}

void cpc_expr(struct pp_expr *e) {
  struct pp_expr_list *el;
  unsigned long long n;

  switch (e->t) {
  case PP_SIZEOFTYPE:
    cpc_type(e->d.SIZEOFTYPE.ty->type);
    break;
  case PP_VAR:
  case PP_CONST:
  case PP_STRING:
  case PP_ENUMLIT:
    break;
  case PP_BINOP:
    cpc_expr(e->d.BINOP.left);
    cpc_expr(e->d.BINOP.right);
    break;
  case PP_UNOP:
    cpc_expr(e->d.UNOP.arg);
    break;
  case PP_INDEX:
    cpc_expr(e->d.INDEX.arg);
    cpc_expr(e->d.INDEX.pos);
    break;
  case PP_FIELDOFPTR:
    cpc_expr(e->d.FIELDOFPTR.arg);
    break;
  case PP_CAST:
    cpc_type(e->d.CAST.ty->type);
    cpc_expr(e->d.CAST.arg);
    break;
  case PP_CALL:
    for (el = e->d.CALL.args; el != NULL; el = el->tail)
      cpc_expr(el->head);
    if (e->d.CALL.vargs != NULL)
      cpc_varg(e->d.CALL.vargs->pre);
    break;
  case PP_DEREF:
    cpc_expr(e->d.DEREF.arg);
    break;
  case PP_ADDRESS:
    cpc_expr(e->d.ADDRESS.arg);
    break;
  case PP_FIELDOF:
    cpc_expr(e->d.FIELDOF.arg);
    break;
  case PP_CONDITION:
    cpc_expr(e->d.CONDITION.cond);
    cpc_expr(e->d.CONDITION.btrue);
    cpc_expr(e->d.CONDITION.bfalse);
    break;
  }
}

void cpc_assert(struct RAssertion *ra) {
  switch (ra->t) {
  case RA_PROGVAR:
  case RA_LOGICVAR:
  case RA_CONST:
  case RA_TRUE:
  case RA_FALSE:
  case RA_EMP:
  case RA___RETURN:
  case RA_ENUMLIT:
  case RA_TIME_COST:
    break;
  case RA_BINOP:
    cpc_assert(ra->d.RABINOP.left);
    cpc_assert(ra->d.RABINOP.right);
    break;
  case RA_CONN:
    cpc_assert(ra->d.RACONN.left);
    cpc_assert(ra->d.RACONN.right);
    break;
  case RA_UNOP:
    cpc_assert(ra->d.RAUNOP.arg);
    break;
  case RA_CAST:
    cpc_type(ra->d.RACAST.ty->type);
    cpc_assert(ra->d.RACAST.arg);
    break;
  case RA_ANN:
    cpc_assert(ra->d.RAANN.expr);
    break;
  case RA_APP:
    cpc_assert(ra->d.RAAPP.f);
    cpc_assert(ra->d.RAAPP.rand);
    break;
  case RA_DEREF:
    if (ra->d.RADEREF.ty != NULL)
      cpc_type(ra->d.RADEREF.ty->type);
    cpc_assert(ra->d.RADEREF.arg);
    break;
  case RA_ADDRESS:
    cpc_assert(ra->d.RAADDRESS.arg);
    break;
  case RA_FIELDOF:
    cpc_assert(ra->d.RAFIELDOF.arg);
    if (ra->d.RAFIELDOF.ty != NULL)
      cpc_type(ra->d.RAFIELDOF.ty->type);
    break;
  case RA_QFOP:
    cpc_assert(ra->d.RAQFOP.arg);
    break;
  case RA_SIZEOF:
    cpc_type(ra->d.RASIZEOF.ty->type);
    break;
  case RA_OLD:
    cpc_assert(ra->d.RAOLD.arg);
    break;
  case RA_INDEX:
    cpc_assert(ra->d.RAINDEX.pos);
    cpc_assert(ra->d.RAINDEX.arg);
    break;
  case RA_FIELDOFPTR:
    cpc_assert(ra->d.RAFIELDOFPTR.arg);
    if (ra->d.RAFIELDOFPTR.ty != NULL)
      cpc_type(ra->d.RAFIELDOFPTR.ty->type);
    break;
  case RA_SHADOW:
    cpc_assert(ra->d.RASHADOW.arg);
    break;
  case RA_DATA_AT:
    if (ra->d.RADATA_AT.type != NULL)
      cpc_type(ra->d.RADATA_AT.type->type);
    cpc_assert(ra->d.RADATA_AT.addr);
    cpc_assert(ra->d.RADATA_AT.val);
    break;
  case RA_UNDEF_DATA_AT:
    if (ra->d.RAUNDEF_DATA_AT.type != NULL)
      cpc_type(ra->d.RAUNDEF_DATA_AT.type->type);
    cpc_assert(ra->d.RAUNDEF_DATA_AT.addr);
    break;
  case RA_FIELD_ADDRESS:
    cpc_assert(ra->d.RAFIELD_ADDRESS.addr);
    if (ra->d.RAFIELD_ADDRESS.ty != NULL)
      cpc_type(ra->d.RAFIELD_ADDRESS.ty->type);
    break;
  case RA_ARR:
    if (ra->d.RAARR.elt != NULL)
      cpc_type(ra->d.RAARR.elt->type);
    cpc_assert(ra->d.RAARR.addr);
    cpc_assert(ra->d.RAARR.len);
    cpc_assert(ra->d.RAARR.list);
    break;
  case RA_SPEC:
    cpc_assert(ra->d.RASPEC.f);
    break;
  }
}

int cpc_max(int a, int b) {
  if (a > b)
    return a;
  return b;
}

void cpc_struct_aux(struct field_info *fl, unsigned int cur_size, unsigned int cur_align,
                    unsigned int *final_size, unsigned int *final_align) {
  if (fl == NULL) {
    *final_size = roundup(cur_size, cur_align);
    *final_align = cur_align;
    return;
  }

  unsigned int align = type_align(fl->type), size = type_size(fl->type);

  cur_size = roundup(cur_size, align);
  fl->offset = cur_size;
  return cpc_struct_aux(fl->next,
                        cur_size + size,
                        cpc_max(cur_align, align),
                        final_size, final_align);
}

void cpc_union_aux(struct field_info *fl, unsigned int cur_size, unsigned int cur_align,
                   unsigned int *final_size, unsigned int *final_align) {
  if (fl == NULL) {
    *final_size = roundup(cur_size, cur_align);
    *final_align = cur_align;
    return;
  }

  unsigned int align = type_align(fl->type), size = type_size(fl->type);

  fl->offset = 0;
  return cpc_union_aux(fl->next,
                       cpc_max(cur_size, align),
                       cpc_max(cur_align, size),
                       final_size, final_align);
}

void cpc_struct(struct struct_union_info *info) {
  cpc_struct_aux(info->first_field, 0, 1, &info->size, &info->alignment);
}

void cpc_union(struct struct_union_info *info) {
  cpc_union_aux(info->first_field, 0, 1, &info->size, &info->alignment);
}
