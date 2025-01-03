#include "utils.h"
#include "cp.h"

void cpt_err_bin(enum BinOpType op) {
  stdout = stderr;
  fprintf(stderr, "\e[1;31merror:\e[0m Invalid operand type in binary operation `");
  print_BinOp(op);
  fprintf(stderr, "' ");
  if (__current_file != NULL)
    fprintf(stderr, " in %s:", __current_file);
  if (__current_scanner != NULL)
    fprintf(stderr, "%d:%d",
            yyget_lineno(__current_scanner),
            yyget_column(__current_scanner));
  exit(1);
}

struct type *cpt_ptr_like_base(struct type *ty) {
  if (ty->t == T_PTR)
    return ty->d.PTR.ty;
  else if (ty->t == T_ARRAY)
    return ty->d.ARRAY.ty;
  else if (ty->t == T_FUNCTION)
    return ty;
  else
    return NULL;
}

/* now symmetric */
int cpt_conv(struct type *src, struct type *dst) {
  // stop early
  if (src->t == T_TYPE_ALIAS && dst->t == T_TYPE_ALIAS &&
      src->d.TYPE_ALIAS.info == dst->d.TYPE_ALIAS.info)
    return 1;

  dst = type_unalias(dst);
  src = type_unalias(src);

  struct type *b1, *b2;
  b1 = cpt_ptr_like_base(src);
  b2 = cpt_ptr_like_base(dst);
  if (b1 != NULL && b2 != NULL) {
    if (type_is_void(b1) || type_is_void(b2))
      return 1;
    else
      return type_equal(b1, b2);
  }

  switch (dst->t) {
  case T_BASIC:
    return src->t == T_BASIC && src->d.BASIC.ty == dst->d.BASIC.ty;
  case T_STRUCT:
    return src->t == T_STRUCT && src->d.STRUCT.info == dst->d.STRUCT.info;
  case T_UNION:
    return src->t == T_UNION && src->d.UNION.info == dst->d.UNION.info;
  case T_ENUM:
    return src->t == T_ENUM && src->d.ENUM.info == dst->d.ENUM.info;
  case T_FUNCTION:
    return src->t == T_FUNCTION && type_equal(src, dst);
  case T_PTR:
  case T_ARRAY:
    return 0;
  case T_TYPE_ALIAS:
    assert(0);
  }
}

// t1 = INT or t1 = INT_64
int cpt_wider_const(enum BasicType t1, enum BasicType t2) {
  if (t1 == T_INT || t1 == T_UINT) {
    return
      t2 == T_UINT || t2 == T_INT64 || t2 == T_UINT64;
  } else {
    return t2 == T_UINT64;
  }
}

int cpt_recov_conv(struct type *src, struct type *dst,
                   struct pp_expr *esrc, struct pp_expr *edst) {
  if (cpt_conv(src, dst))
    return 1;
  else if (esrc != NULL && esrc->t == PP_CONST) {
    if (cpt_is_integral(dst) &&
        cpt_wider_const(src->d.BASIC.ty, dst->d.BASIC.ty)) {
      src->d.BASIC.ty = dst->d.BASIC.ty;
      return 1;
    } else if (esrc->d.CONST.value == 0 &&
               cpt_ptr_like_base(dst) != NULL) {
      REPLACE_TYPE(esrc->type, dst);
      return 1;
    } else {
      return 0;
    }
  } else if (edst != NULL && edst->t == PP_CONST) {
    if (cpt_is_integral(src) &&
        cpt_wider_const(dst->d.BASIC.ty, src->d.BASIC.ty)) {
      dst->d.BASIC.ty = src->d.BASIC.ty;
      return 1;
    } else if (edst->d.CONST.value == 0 &&
               cpt_ptr_like_base(src) != NULL) {
      REPLACE_TYPE(edst->type, src);
      return 1;
    } else {
      return 0;
    }
  } else
    return 0;
}

int cpt_is_assignable(struct type *ty) {
  switch (ty->t) {
  case T_BASIC:
    if (ty->d.BASIC.ty == T_VOID)
      return 0;
    else
      return 1;
  case T_STRUCT:
    return ty->d.STRUCT.info->defined;
  case T_UNION:
    return ty->d.UNION.info->defined;
  case T_PTR:
  case T_ENUM:
    return 1;
  case T_ARRAY:
  case T_FUNCTION:
    return 0;
  case T_TYPE_ALIAS:
    return cpt_is_assignable(ty->d.TYPE_ALIAS.info->type);
  }
}
int cpt_is_integral(struct type *ty) {
  ty = type_unalias(ty);
  return ty->t == T_BASIC && ty->d.BASIC.ty != T_VOID;
}
int cpt_is_ptr_like(struct type *ty) {
  ty = type_unalias(ty);
  return ty->t == T_PTR || ty->t == T_ARRAY;
}
int cpt_is_scalar(struct type *ty) {
  ty = type_unalias(ty);
  return cpt_is_integral(ty) || ty->t == T_PTR;
}
int cpt_is_effective_scalar(struct type *ty) {
  ty = type_unalias(ty);
  return cpt_is_integral(ty) || cpt_is_ptr_like(ty) || ty->t == T_FUNCTION;
}

struct field_info *cpt_find_slot(struct struct_union_info *info, char *name) {
  struct field_info *it;
  if (!info->defined)
    switch (info->t) {
    case IS_STRUCT:
      failwith("Use of incomplete type `struct %s'", info->name);
      break;
    case IS_UNION:
      failwith("Use of incomplete type `union %s'", info->name);
      break;
    }
  for (it = info->first_field; it != NULL; it = it->next)
    if (strcmp(name, it->name) == 0)
      return it;
  switch (info->t) {
  case IS_STRUCT:
    failwith("No member named `%s' in `struct %s'", name, info->name);
    break;
  case IS_UNION:
    failwith("No member named `%s' in `union %s'", name, info->name);
    break;
  }
}

/********************************/

struct type *cpt_binop_aux(enum BinOpType op, struct pp_expr *el, struct pp_expr *er) {
  struct type *tl = el->type, *tr = er->type;
  switch (op) {
  case T_EQ:
  case T_NE:
    if (tl->t == T_ENUM && tr->t == T_ENUM &&
        cpt_recov_conv(tl, tr, el, er))
      return TBasic(T_INT);
  case T_LT:
  case T_GT:
  case T_LE:
  case T_GE:
    if (!cpt_is_effective_scalar(tl) || !cpt_is_effective_scalar(tr))
      cpt_err_bin(op);
    if (!cpt_recov_conv(tl, tr, el, er))
      cpt_err_bin(op);
    return TBasic(T_INT);
  case T_AND:
  case T_OR:
    if (!cpt_is_effective_scalar(tl) || !cpt_is_effective_scalar(tr))
      cpt_err_bin(op);
    return TBasic(T_INT);
  case T_PLUS:
  case T_MINUS:
    if (cpt_is_integral(tl) && cpt_is_integral(tr)) {
      if (!cpt_recov_conv(tl, tr, el, er))
        cpt_err_bin(op);
      return tl;
    } else if (cpt_is_ptr_like(tl)) { /* pointer arithmetic */
      if (cpt_is_integral(tr)) {
        if (type_unalias(tl)->t == T_PTR)
          return tl;
        else
          return TPtr(tl->d.ARRAY.ty);
      } else if (cpt_is_ptr_like(tr) &&
                 op == T_MINUS &&
                 cpt_recov_conv(tl, tr, el, er)) {
        return TBasic(T_INT);
      } else
        cpt_err_bin(op);
    } else if (op == T_PLUS && cpt_is_ptr_like(tr)) { /* pointer arithmetic */
      if (!cpt_is_integral(tl))
        cpt_err_bin(op);
      if (type_unalias(tr)->t == T_PTR)
        return tr;
      return TPtr(tr->d.ARRAY.ty);
    } else
      cpt_err_bin(op);
    break; // not reachable
  case T_DIV:
  case T_MOD:
  case T_MUL:
  case T_BAND:
  case T_BOR:
  case T_XOR:
  case T_SHL:
  case T_SHR:
    if (!cpt_is_integral(tl) || !cpt_is_integral(tr))
      cpt_err_bin(op);
    if (!cpt_recov_conv(tl, tr, el, er))
      cpt_err_bin(op);
    return tl;
  }
}

int cpt_func_arg(struct pp_expr_list *args, struct type_list *paras) {
  while (args != NULL && paras != NULL) {
    if (!cpt_recov_conv(args->head->type, paras->hd,
                        args->head, NULL))
      return 0;
    args = args->tail;
    paras = paras->tl;
  }
  if (args != NULL || paras != NULL)
    return 0;
  return 1;
}

struct type *cpt_const(unsigned long long n,
                       int hex, int l, int u) {
#define check_int32() if (n <= 0x0fffffff) return TBasic(T_INT)
#define check_uint32() if (n <= 0xffffffff) return TBasic(T_UINT)
#define check_int64() if (n <= 0x0fffffffffffffff) return TBasic(T_INT64)
#define check_uint64() if (n <= 0xffffffffffffffff) return TBasic(T_UINT64)
  if (hex) {
    if (u) {
      if (l) {
        check_uint64();
      } else {
        check_uint32();
        check_uint64();
      }
    } else {
      if (l) {
        check_int64();
        check_uint64();
      } else {
        check_int32();
        check_uint32();
        check_int64();
        check_uint64();
      }
    }
  } else {
    if (u) {
      if (l) {
        check_uint64();
      } else {
        check_uint32();
        check_uint64();
      }
    } else {
      if (l) {
        check_int64();
      } else {
        check_int32();
        check_int64();
      }
    }
  }
  failwith("Integer literal is too large");
}

void cpt_expr(struct pp_expr *e) {
  switch (e->t) {
  case PP_CALL: {
    cpt_expr(e->d.CALL.func);
    struct pp_expr_list *i;
    for (i = e->d.CALL.args; i != NULL; i = i->tail)
      cpt_expr(i->head);
    struct type *fn_type = e->d.CALL.func->type,
                *b_type = cpt_ptr_like_base(fn_type);
    if (b_type != NULL)
      fn_type = b_type;
    if (fn_type->t != T_FUNCTION)
      failwith("Called object type is not a function or function pointer");
    if (!cpt_func_arg(e->d.CALL.args, fn_type->d.FUNCTION.param))
      failwith("Incompatible argument passing in function call");
    ASSIGN_TYPE(e->type, fn_type->d.FUNCTION.ret);
    if (e->d.CALL.vargs != NULL) {
      struct pp_varg_list *i;
      for (i = e->d.CALL.vargs->pre; i != NULL; i = i->next)
        cpt_assert(i->val, NULL);
    }
    break; }

  case PP_CONST:
    ASSIGN_TYPE(e->type, cpt_const(e->d.CONST.value,
                                   e->d.CONST.hex, e->d.CONST.l, e->d.CONST.u));
    break;

  case PP_STRING:
    ASSIGN_TYPE(e->type, TArray(TBasic(T_CHAR), strlen(e->d.STRING.str)));
    break;

  case PP_VAR:
    ASSIGN_TYPE(e->type, e->d.VAR.info->type);
    break;

  case PP_BINOP:
    cpt_expr(e->d.BINOP.left);
    cpt_expr(e->d.BINOP.right);
    ASSIGN_TYPE(e->type,
                cpt_binop_aux(e->d.BINOP.op,
                              e->d.BINOP.left, e->d.BINOP.right));
    break;

  case PP_UNOP:
    cpt_expr(e->d.UNOP.arg);
    switch (e->d.UNOP.op) {
    case T_UMINUS:
    case T_UPLUS:
    case T_NOTINT:
      if (cpt_is_integral(e->d.UNOP.arg->type))
        ASSIGN_TYPE(e->type, e->d.UNOP.arg->type)
      else
        failwith("Invalid argument to unary expression `~'");
      break;
    case T_NOTBOOL:
      if (cpt_is_effective_scalar(e->d.UNOP.arg->type))
        ASSIGN_TYPE(e->type, e->d.UNOP.arg->type)
      else
        failwith("Invalid argument to unary expression `!'");
    }
    break;

  case PP_CAST: {
    cpt_expr(e->d.CAST.arg);
    if (!cpt_is_effective_scalar(e->d.CAST.arg->type) &&
        type_unalias(e->d.CAST.arg->type)->t != T_ENUM)
      failwith("Invalid operand in cast expression where arithmetic or pointer type is required");
    struct type *ty = type_unalias(type_of_pp_type(e->d.CAST.ty->type));
    if (!cpt_is_scalar(ty) && !type_is_void(ty))
      failwith("Invalid type in cast expression where arithmetic or pointer type is required");
    ASSIGN_TYPE(e->type, ty);
    break; }

  case PP_DEREF: {
    cpt_expr(e->d.DEREF.arg);
    struct type *ty = cpt_ptr_like_base(type_unalias(e->d.DEREF.arg->type));
    if (ty != NULL)
      ASSIGN_TYPE(e->type, ty)
    else
      failwith("indirection requires pointer operand");
    break; }

  case PP_ADDRESS:
    cpt_expr(e->d.ADDRESS.arg);
    ASSIGN_TYPE(e->type, TPtr(e->d.ADDRESS.arg->type));
    break;

  case PP_INDEX: { // todo: 5[a] is illegal now
    cpt_expr(e->d.INDEX.arg);
    cpt_expr(e->d.INDEX.pos);
    struct type *ty = cpt_ptr_like_base(type_unalias(e->d.INDEX.arg->type));
    if (ty != NULL)
      ASSIGN_TYPE(e->type, ty)
    else
      failwith("Subscripted value is not an array or pointer");
    if (!cpt_is_integral(e->d.INDEX.pos->type) ||
        e->d.INDEX.pos->type->t == T_ENUM)
      failwith("Subscript is not an integer");
    break; }

  case PP_FIELDOFPTR: {
    cpt_expr(e->d.FIELDOFPTR.arg);
    struct type *ty = cpt_ptr_like_base(type_unalias(e->d.FIELDOFPTR.arg->type));
    if (ty != NULL)
      ty = type_unalias(ty);
    else
      failwith("Member reference type is not a pointer");
    if (ty->t == T_STRUCT) {
      e->d.FIELDOFPTR.field = cpt_find_slot(ty->d.STRUCT.info, e->d.FIELDOFPTR.name);
      ASSIGN_TYPE(e->type, e->d.FIELDOFPTR.field->type);
    } else if (ty->t == T_UNION) {
      e->d.FIELDOFPTR.field = cpt_find_slot(ty->d.UNION.info, e->d.FIELDOFPTR.name);
      ASSIGN_TYPE(e->type, e->d.FIELDOFPTR.field->type);
    } else
      failwith("Member reference base type is not a structure or union");
    break; }

  case PP_SIZEOFTYPE:
    ASSIGN_TYPE(e->type, TBasic(T_UINT));
    break;

  case PP_FIELDOF: {
    cpt_expr(e->d.FIELDOF.arg);
    struct type *ty = type_unalias(e->d.FIELDOF.arg->type);
    if (ty->t == T_STRUCT) {
      e->d.FIELDOF.field = cpt_find_slot(ty->d.STRUCT.info, e->d.FIELDOF.name);
      ASSIGN_TYPE(e->type, e->d.FIELDOF.field->type);
    } else if (ty->t == T_UNION) {
      e->d.FIELDOF.field = cpt_find_slot(ty->d.UNION.info, e->d.FIELDOF.name);
      ASSIGN_TYPE(e->type, e->d.FIELDOF.field->type);
    } else
      failwith("Member reference base type is not a structure or union");
    break; }

  case PP_ENUMLIT:
    ASSIGN_TYPE(e->type, TEnum(e->d.ENUMLIT.info->parent));
    break;

  case PP_CONDITION:
    cpt_expr(e->d.CONDITION.cond);
    if (!cpt_is_effective_scalar(e->d.CONDITION.cond->type))
      failwith("Invalid operand in conditional expression "
               "where arithmetic or pointer type is required");
    cpt_expr(e->d.CONDITION.btrue);
    cpt_expr(e->d.CONDITION.bfalse);
    if (!cpt_recov_conv(e->d.CONDITION.bfalse->type, e->d.CONDITION.btrue->type,
                        e->d.CONDITION.bfalse, e->d.CONDITION.btrue))
      failwith("Type mismatch in conditional expression");
    e->type = e->d.CONDITION.btrue->type;
  }
}

void cpt_simple_cmd(struct pp_simple *scmd) {
  if (scmd == NULL)
    return;

  switch (scmd->t) {
  case PP_COMPUTATION:
    break;

  case PP_ASGN:
    if (!cpt_is_assignable(scmd->d.ASGN.left->type))
      failwith("Type is not assignable");
    switch (scmd->d.ASGN.op) {
    case T_ASSIGN:
      if (!cpt_recov_conv(scmd->d.ASGN.right->type, scmd->d.ASGN.left->type,
                          scmd->d.ASGN.right, NULL))
        failwith("Assigning to incompatible type");
      break;
    case T_ADD_ASSIGN:
    case T_SUB_ASSIGN:
      if (!cpt_is_scalar(scmd->d.ASGN.left->type))
        failwith("Assigning to incompatible type");
      if (cpt_is_integral(scmd->d.ASGN.left->type)) {
        if (!cpt_recov_conv(scmd->d.ASGN.right->type, scmd->d.ASGN.left->type,
                            scmd->d.ASGN.right, NULL))
          failwith("Assigning to incompatible type");
      } else { /* pointer arithmetic */
        if (!cpt_is_integral(scmd->d.ASGN.right->type))
          failwith("Assigning to incompatible type");
      }
      break;
    case T_DIV_ASSIGN:
    case T_MOD_ASSIGN:
    case T_MUL_ASSIGN:
    case T_BAND_ASSIGN:
    case T_BOR_ASSIGN:
    case T_XOR_ASSIGN:
    case T_SHL_ASSIGN:
    case T_SHR_ASSIGN:
      if (!cpt_is_integral(scmd->d.ASGN.left->type) ||
          !cpt_is_integral(scmd->d.ASGN.right->type))
        failwith("Assigning to incompatible type");
      if (!cpt_recov_conv(scmd->d.ASGN.right->type, scmd->d.ASGN.left->type,
                          scmd->d.ASGN.right, NULL))
        failwith("Assigning to incompatible type");
      break;
    }
    break;

  case PP_INCDEC:
    if (!cpt_is_scalar(scmd->d.INCDEC.arg->type))
      failwith("Cannot increment or decrement value of this type");
    break;
  }
}

void cpt_assert(struct RAssertion *ra, struct type *ret) {
  switch (ra->t) {
  case RA_CONST:
  case RA_LOGICVAR:
  case RA_TRUE:
  case RA_FALSE:
  case RA_ENUMLIT:
  case RA_EMP:
  case RA_TIME_COST:
    ra->type = NULL;
    break;
  case RA_PROGVAR:
    ASSIGN_TYPE(ra->type, ra->d.RAPROGVAR.info->type)
    break;
  case RA_BINOP:
    cpt_assert(ra->d.RABINOP.left, ret);
    cpt_assert(ra->d.RABINOP.right, ret);
    ra->type = NULL;
    break;
  case RA_CONN:
    cpt_assert(ra->d.RACONN.left, ret);
    cpt_assert(ra->d.RACONN.right, ret);
    ra->type = NULL;
    break;
  case RA_UNOP:
    cpt_assert(ra->d.RAUNOP.arg, ret);
    ra->type = NULL;
    break;
  case RA_CAST:
    cpt_assert(ra->d.RACAST.arg, ret);
    ASSIGN_TYPE(ra->type, type_of_pp_type(ra->d.RACAST.ty->type));
    break;
  case RA_SIZEOF:
    // should I put it here? we produce a type here, but not fot type checking.
    ASSIGN_TYPE(ra->d.RASIZEOF.type, type_of_pp_type(ra->d.RASIZEOF.ty->type));
    ASSIGN_TYPE(ra->type, TBasic(T_UINT));
    break;
  case RA_APP:
    ra->type = NULL;
    cpt_assert(ra->d.RAAPP.f, ret);
    cpt_assert(ra->d.RAAPP.rand, ret);
    break;
  case RA_ANN:
    cpt_assert(ra->d.RAANN.expr, ret);
    if (ra->d.RAANN.expr->type != NULL)
      ASSIGN_TYPE(ra->type, ra->d.RAANN.expr->type);
    break;
  case RA_ADDRESS: {
    cpt_assert(ra->d.RAADDRESS.arg, ret);
    if (ra->d.RAADDRESS.arg->type != NULL)
      ASSIGN_TYPE(ra->type, TPtr(ra->d.RAADDRESS.arg->type))
    else
      ra->type = NULL;
    break; }
  case RA_INDEX: {
    cpt_assert(ra->d.RAINDEX.arg, ret);
    struct type *ty = type_unalias(ra->d.RAINDEX.arg->type);
    if (ty != NULL) {
      ty = cpt_ptr_like_base(ty);
      if (ty != NULL)
        ASSIGN_TYPE(ra->type, ty)
      else
        ra->type = NULL;
    } else
      ra->type = NULL;
    break; }
  case RA___RETURN:
    ASSIGN_TYPE(ra->type, ret);
    break;
  case RA_QFOP:
    cpt_assert(ra->d.RAQFOP.arg, ret);
    ra->type = NULL;
    break;
  case RA_OLD:
    cpt_assert(ra->d.RAOLD.arg, ret);
    if (ra->d.RAOLD.arg->type != NULL)
      ASSIGN_TYPE(ra->type, ra->d.RAOLD.arg->type)
    else
      ra->type = NULL;
    break;
  case RA_DEREF:
    cpt_assert(ra->d.RADEREF.arg, ret);
    if (ra->d.RADEREF.ty == NULL) {
      struct type *ty = type_unalias(ra->d.RADEREF.arg->type);
      if (ty != NULL)
        ty = cpt_ptr_like_base(ty);
      if (ty != NULL)
        ASSIGN_TYPE(ra->type, ty)
      else 
        failwith("Cannot decide the type of dereference");
    } else
      ASSIGN_TYPE(ra->type, type_of_pp_type(ra->d.RADEREF.ty->type));
    break;
  case RA_DATA_AT:
    ra->type = NULL;
    cpt_assert(ra->d.RADATA_AT.addr, ret);
    cpt_assert(ra->d.RADATA_AT.val, ret);
    if (ra->d.RADATA_AT.type == NULL) {
      struct type *ty = type_unalias(ra->d.RADATA_AT.addr->type);
      if (ty != NULL)
        ty = cpt_ptr_like_base(ty);
      if (ty != NULL)
        ASSIGN_TYPE(ra->d.RADATA_AT.ty, ty)
      else
        failwith("Cannot decide the type of `data_at'");
    } else {
        ASSIGN_TYPE(ra->d.RADATA_AT.ty, type_of_pp_type(ra->d.RADATA_AT.type->type))
    }
    break;
  case RA_UNDEF_DATA_AT:
    ra->type = NULL;
    cpt_assert(ra->d.RAUNDEF_DATA_AT.addr, ret);
    if (ra->d.RAUNDEF_DATA_AT.type == NULL) {
      struct type *ty = type_unalias(ra->d.RAUNDEF_DATA_AT.addr->type);
      if (ty != NULL)
        ty = cpt_ptr_like_base(ty);
      if (ty != NULL)
        ASSIGN_TYPE(ra->d.RAUNDEF_DATA_AT.ty, ty)
      else
        failwith("Cannot decide the type of `undef_data_at'");
    } else {
        ASSIGN_TYPE(ra->d.RAUNDEF_DATA_AT.ty, type_of_pp_type(ra->d.RAUNDEF_DATA_AT.type->type))
    }
    break;
  case RA_ARR:
    ra->type = NULL;
    cpt_assert(ra->d.RAARR.addr, ret);
    cpt_assert(ra->d.RAARR.len, ret);
    cpt_assert(ra->d.RAARR.list, ret);
    if (ra->d.RAARR.elt == NULL) {
      if (ra->d.RAARR.addr->type != NULL) {
        struct type *ty = cpt_ptr_like_base(type_unalias(ra->d.RAARR.addr->type));
        if (ty != NULL)
          ASSIGN_TYPE(ra->d.RAARR.ty, ty)
        else
          failwith("Cannot decide the type of `Arr'");
      } else
        failwith("Cannot decide the type of `Arr'");
    } else
      ASSIGN_TYPE(ra->d.RAARR.ty, type_of_pp_type(ra->d.RAARR.elt->type));
    break;
  case RA_SPEC:
    ra->type = NULL;
    cpt_assert(ra->d.RASPEC.f, ret);
    break;
  case RA_FIELDOF:
    cpt_assert(ra->d.RAFIELDOF.arg, ret);
    if (ra->d.RAFIELDOF.ty == NULL) {
      struct type *ty = type_unalias(ra->d.RAFIELDOF.arg->type);
      if (ty != NULL && ty->t == T_STRUCT)
        ra->d.RAFIELDOF.field = cpt_find_slot(ty->d.STRUCT.info, ra->d.RAFIELDOF.name);
      else if (ty != NULL && ty->t == T_UNION)
        ra->d.RAFIELDOF.field = cpt_find_slot(ty->d.UNION.info, ra->d.RAFIELDOF.name);
      else if (ra->d.RAFIELDOF.field == NULL || ra->d.RAFIELDOF.field->another != NULL)
        failwith("Cannot decide the type of member reference");
    } else
      ra->d.RAFIELDOF.field = cpt_find_slot(ra->d.RAFIELDOF.type, ra->d.RAFIELDOF.name);
    ASSIGN_TYPE(ra->type, ra->d.RAFIELDOF.field->type)
    break;
  case RA_FIELDOFPTR:
    cpt_assert(ra->d.RAFIELDOFPTR.arg, ret);
    if (ra->d.RAFIELDOFPTR.ty == NULL) {
      struct type *ty = type_unalias(ra->d.RAFIELDOFPTR.arg->type);
      do {
        if (ty != NULL)
          ty = type_unalias(cpt_ptr_like_base(ty));
        if (ty != NULL) {
          if (ty->t == T_STRUCT) {
            ra->d.RAFIELDOFPTR.field = cpt_find_slot(ty->d.STRUCT.info, ra->d.RAFIELDOFPTR.name);
            break;
          } else if (ty->t == T_UNION) {
            ra->d.RAFIELDOFPTR.field = cpt_find_slot(ty->d.UNION.info, ra->d.RAFIELDOFPTR.name);
            break;
          }
        }
        if (ra->d.RAFIELDOFPTR.field->another != NULL)
          failwith("Cannot decide the type of member reference");
      } while (0);
    } else
      ra->d.RAFIELDOFPTR.field = cpt_find_slot(ra->d.RAFIELDOFPTR.type, ra->d.RAFIELDOFPTR.name);
    ASSIGN_TYPE(ra->type, ra->d.RAFIELDOFPTR.field->type)
    break;
  case RA_FIELD_ADDRESS:
    cpt_assert(ra->d.RAFIELD_ADDRESS.addr, ret);
    if (ra->d.RAFIELD_ADDRESS.ty == NULL) {
      struct type *ty = type_unalias(ra->d.RAFIELD_ADDRESS.addr->type);
      do {
        if (ty != NULL)
          ty = type_unalias(cpt_ptr_like_base(ty));
        if (ty != NULL) {
          if (ty->t == T_STRUCT) {
            ra->d.RAFIELD_ADDRESS.field = cpt_find_slot(ty->d.STRUCT.info, ra->d.RAFIELD_ADDRESS.field_name);
            break;
          } else if (ty->t == T_UNION) {
            ra->d.RAFIELD_ADDRESS.field = cpt_find_slot(ty->d.UNION.info, ra->d.RAFIELD_ADDRESS.field_name);
            break;
          }
        }
        if (ra->d.RAFIELDOFPTR.field->another != NULL)
          failwith("Cannot decide the type of member reference");
      } while (0);
    } else
      ra->d.RAFIELD_ADDRESS.field = cpt_find_slot(ra->d.RAFIELD_ADDRESS.type,
                                                  ra->d.RAFIELD_ADDRESS.field_name);
    ASSIGN_TYPE(ra->type, TPtr(ra->d.RAFIELD_ADDRESS.field->type))
    break;
  case RA_SHADOW:
    assert(0);
  }
}
