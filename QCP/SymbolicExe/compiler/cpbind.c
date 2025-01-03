#include "utils.h"
#include "cp.h"
#include "pparser.h"

void cpb_expr(struct pp_expr *expr, struct environment *env);

void cpb_decl_type(struct pp_type *type, struct environment *env) {
  switch (type->t) {
  case PP_BASIC:
  case PP_STRUCT:
  case PP_UNION:
  case PP_ENUM:
  case PP_TYPE_ALIAS:
    break;
  case PP_PTR:
    cpb_decl_type(type->d.PTR.ty, env);
    break;
  case PP_ARRAY:
    cpb_expr(type->d.ARRAY.size, env);
    cpb_decl_type(type->d.ARRAY.ty, env);
    break;
  case PP_FUNCTION: {
    struct annot_list *i;
    for (i = type->d.FUNCTION.param; i != NULL; i = i->tail)
      cpb_type(i->head->type->type, env);
    cpb_decl_type(type->d.FUNCTION.ret, env);
    break; }
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
}

void cpb_type(struct pp_type *type, struct environment *env) {
  struct struct_union_info *suinfo;
  struct enum_info *einfo;
  struct ephemeral_env *eph = &env->ephemer;
  switch (type->t) {
  case PP_BASIC:
    break;
  case PP_STRUCT:
    suinfo = find_struct_or_union_by_name(type->d.STRUCT.name, eph);
    if (suinfo == NULL || suinfo->t != IS_STRUCT)
      failwith("Use of undeclared type `struct %s'", type->d.STRUCT.name);
    type->d.STRUCT.info = suinfo;
    break;
  case PP_UNION:
    suinfo = find_struct_or_union_by_name(type->d.UNION.name, eph);
    if (suinfo == NULL || suinfo->t != IS_UNION)
      failwith("Use of undeclared type `union %s'", type->d.UNION.name);
    type->d.UNION.info = suinfo;
    break;
  case PP_ENUM:
    einfo = find_enum_by_name(type->d.ENUM.name, eph);
    if (einfo == NULL)
      failwith("Use of undeclared type `enum %s'", type->d.ENUM.name);
    type->d.ENUM.info = einfo;
    break;
  case PP_PTR:
    cpb_type(type->d.PTR.ty, env);
    break;
  case PP_ARRAY:
    cpb_type(type->d.ARRAY.ty, env);
    cpb_expr(type->d.ARRAY.size, env);
    break;
  case PP_FUNCTION: {
    struct annot_list *i;
    for (i = type->d.FUNCTION.param; i != NULL; i = i->tail)
      cpb_type(i->head->type->type, env);
    cpb_type(type->d.FUNCTION.ret, env);
    break; }
  case PP_TYPE_ALIAS: {
    struct var_scope_union *u = find_type_by_name(type->d.TYPE_ALIAS.name, eph);
    if (u == NULL) // impossible because lexer has addressed that
      failwith("Undeclared identifier `%s'", type->d.TYPE_ALIAS.name);
    type->d.TYPE_ALIAS.info = u->d.type;
    break; }
  case PP_ANON_STRUCT: {
    struct struct_union_info *info;
    if (type->d.ANON_STRUCT.name != NULL)
      info = parse_struct_def(type->d.ANON_STRUCT.name, type->d.ANON_STRUCT.fields, env);
    else
      info = parse_anon_struct_def(type->d.ANON_STRUCT.fields, env);
    free_annot_list(type->d.ANON_STRUCT.fields);
    type->t = PP_STRUCT;
    type->d.STRUCT.info = info;
    type->d.STRUCT.name = NULL;
    break; }
  case PP_ANON_UNION: {
    struct struct_union_info *info;
    if (type->d.ANON_UNION.name != NULL)
      info = parse_union_def(type->d.ANON_UNION.name, type->d.ANON_UNION.fields, env);
    else
      info = parse_anon_union_def(type->d.ANON_UNION.fields, env);
    free_annot_list(type->d.ANON_UNION.fields);
    type->t = PP_UNION;
    type->d.UNION.info = info;
    type->d.STRUCT.name = NULL;
    break; }
  case PP_ANON_ENUM:{
    struct enum_info *info;
    if (type->d.ANON_ENUM.name != NULL)
      info = parse_enum_def(type->d.ANON_ENUM.name, type->d.ANON_ENUM.names, env);
    else
      info = parse_anon_enum_def(type->d.ANON_ENUM.names, env);
    free_pp_enum_list(type->d.ANON_ENUM.names);
    type->t = PP_ENUM;
    type->d.ENUM.info = info;
    type->d.STRUCT.name = NULL;
    break; }
  }
}

void cpb_type_arg(struct type_arg_list *l, struct environment *env) {
  if (l == NULL)
    return;
  REPLACE_ATYPE(l->type, cpb_atype(NULL, l->type, NULL, env));
  cpb_type_arg(l->next, env);
}

void cpb_varg(struct pp_varg_list *l, struct environment *env) {
  if (l == NULL)
    return;
  cpb_assert(l->val, env);
  struct pp_varg_list *i;
  for (i = l->next; i != NULL; i = i->next)
    if (strcmp(i->name, l->name) == 0)
      failwith("Multiple assignment to same variable %s", l->name);
  cpb_varg(l->next, env);
}

void cpb_expr(struct pp_expr *expr, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  switch (expr->t) {
  case PP_CONST:
  case PP_STRING:
    break;
  case PP_VAR: {
    struct var_scope_union *u = find_prog_var_like_by_name(expr->d.VAR.name, eph);
    if (u == NULL)
      failwith("Use of undeclared identifier `%s'", expr->d.VAR.name);
    if (u->t == IS_PROG_VAR)
      expr->d.VAR.info = u->d.prog_var;
    else {
      expr->t = PP_ENUMLIT;
      expr->d.ENUMLIT.name = expr->d.VAR.name;
      expr->d.ENUMLIT.info = u->d.enumerator;
    }
    break; }
  case PP_BINOP:
    cpb_expr(expr->d.BINOP.left, env);
    cpb_expr(expr->d.BINOP.right, env);
    break;
  case PP_UNOP:
    cpb_expr(expr->d.UNOP.arg, env);
    break;
  case PP_CAST:
    cpb_expr(expr->d.CAST.arg, env);
    cpb_type(expr->d.CAST.ty->type, env);
    break;
  case PP_CALL: {
    struct pp_expr_list *el;
    for (el = expr->d.CALL.args; el != NULL; el = el->tail)
      cpb_expr(el->head, env);
    cpb_expr(expr->d.CALL.func, env);
    if (expr->d.CALL.vargs != NULL) {
      cpb_type_arg(expr->d.CALL.vargs->type, env);
      cpb_varg(expr->d.CALL.vargs->pre, env);
    }
    break; }
  case PP_DEREF:
    cpb_expr(expr->d.DEREF.arg, env);
    break;
  case PP_ADDRESS:
    cpb_expr(expr->d.ADDRESS.arg, env);
    break;
  case PP_SIZEOFTYPE:
    cpb_type(expr->d.SIZEOFTYPE.ty->type, env);
    break;
  case PP_INDEX:
    cpb_expr(expr->d.INDEX.arg, env);
    cpb_expr(expr->d.INDEX.pos, env);
    break;
  case PP_FIELDOF:
    cpb_expr(expr->d.FIELDOF.arg, env);
    break;
  case PP_FIELDOFPTR:
    cpb_expr(expr->d.FIELDOFPTR.arg, env);
    break;
  case PP_ENUMLIT: {
    assert(0);
    break;
  }
  case PP_CONDITION:
    cpb_expr(expr->d.CONDITION.cond, env);
    cpb_expr(expr->d.CONDITION.btrue, env);
    cpb_expr(expr->d.CONDITION.bfalse, env);
    break;
  }
}

void cpb_free_shadow_chain(struct RAssertion *ra) {
  if (ra->t == RA_SHADOW)
    cpb_free_shadow_chain(ra->d.RASHADOW.arg);
  free(ra);
}

void cpb_assert_rec(struct RAssertion *ra, struct environment *env);

void cpb_assert_struct_union_type(struct struct_union_info **info,
                                  struct pp_type *ty,
                                  struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  if (ty->t == PP_TYPE_ALIAS) {
    if (find_type_by_name(ty->d.TYPE_ALIAS.name, eph) == NULL) {
      *info = find_struct_or_union_by_name(ty->d.TYPE_ALIAS.name, eph);
      if (*info == NULL)
        failwith("No such struct `%s' or union `%s'",
                 ty->d.TYPE_ALIAS.name, ty->d.TYPE_ALIAS.name)
      else
        return;
    }
  }
  cpb_type(ty, env);
  if (ty->t == PP_TYPE_ALIAS) {
    struct type *t = type_unalias(ty->d.TYPE_ALIAS.info->type);
    if (t->t == T_STRUCT)
      *info = t->d.STRUCT.info;
    else if (t->t == T_UNION)
      *info = t->d.UNION.info;
    else
      failwith("Member reference base type is not a structure or union");
  }
  else if (ty->t == PP_STRUCT)
    *info = ty->d.STRUCT.info;
  else if (ty->t == PP_UNION)
    *info = ty->d.UNION.info;
  else
    failwith("Member reference base type is not a structure or union");
}

void cpb_assert_rec(struct RAssertion *ra, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  switch (ra->t) {
  case RA_CONST:
  case RA_TRUE:
  case RA_FALSE:
  case RA_EMP:
  case RA___RETURN:
  case RA_ENUMLIT:
  case RA_TIME_COST:
    break;
  case RA_PROGVAR: {
    struct var_scope_union *u = find_var_like_by_name(ra->d.RAPROGVAR.name, eph);
    if (u == NULL)
      failwith("Use of undeclared identifier `%s'", ra->d.RAPROGVAR.name);
    if (u->t == IS_PROG_VAR)
      ra->d.RAPROGVAR.info = u->d.prog_var;
    else if (u->t == IS_ENUMERATOR) {
      ra->t = RA_ENUMLIT;
      ra->d.RAENUMLIT.name = ra->d.RAPROGVAR.name;
      ra->d.RAENUMLIT.info = u->d.enumerator;
    } else {
      ra->t = RA_LOGICVAR;
      free(ra->d.RAPROGVAR.name);
      ra->d.RALOGICVAR.info = u->d.logic_var;
    }
    break; }
  case RA_APP:
    cpb_assert_rec(ra->d.RAAPP.f, env);
    cpb_assert_rec(ra->d.RAAPP.rand, env);
    break;
  case RA_BINOP:
    cpb_assert_rec(ra->d.RABINOP.left, env);
    cpb_assert_rec(ra->d.RABINOP.right, env);
    break;
  case RA_CONN:
    cpb_assert_rec(ra->d.RACONN.left, env);
    cpb_assert_rec(ra->d.RACONN.right, env);
    break;
  case RA_UNOP:
    cpb_assert_rec(ra->d.RAUNOP.arg, env);
    break;
  case RA_CAST:
    cpb_type(ra->d.RACAST.ty->type, env);
    cpb_assert_rec(ra->d.RACAST.arg, env);
    break;
  case RA_SIZEOF:
    cpb_type(ra->d.RASIZEOF.ty->type, env);
    break;
  case RA_ANN:
    REPLACE_ATYPE(ra->d.RAANN.type, cpb_atype(NULL, ra->d.RAANN.type, NULL, env));
    cpb_assert_rec(ra->d.RAANN.expr, env);
    break;
  case RA_DEREF:
    if (ra->d.RADEREF.ty != NULL)
      cpb_type(ra->d.RADEREF.ty->type, env);
    cpb_assert_rec(ra->d.RADEREF.arg, env);
    break;
  case RA_ADDRESS:
    cpb_assert_rec(ra->d.RAADDRESS.arg, env);
    break;
  case RA_INDEX:
    cpb_assert_rec(ra->d.RAINDEX.arg, env);
    cpb_assert_rec(ra->d.RAINDEX.pos, env);
    break;
  case RA_FIELDOF: {
    cpb_assert_rec(ra->d.RAFIELDOF.arg, env);
    ra->d.RAFIELDOF.field = find_field_by_name(ra->d.RAFIELDOF.name, eph);
    ra->d.RAFIELDOF.proj = find_projection_by_name(ra->d.RAFIELDOF.name, eph);
    if (ra->d.RAFIELDOF.ty != NULL) {
      cpb_assert_struct_union_type(&ra->d.RAFIELDOF.type, ra->d.RAFIELDOF.ty->type,
                                   env);
      if (ra->d.RAFIELDOF.field == NULL)
        failwith("No such member `%s'", ra->d.RAFIELDOF.name);
    }
    break; }
  case RA_FIELDOFPTR:
    cpb_assert_rec(ra->d.RAFIELDOFPTR.arg, env);
    ra->d.RAFIELDOFPTR.field = find_field_by_name(ra->d.RAFIELDOFPTR.name, eph);
    if (ra->d.RAFIELDOFPTR.field == NULL)
      failwith("No such member `%s'", ra->d.RAFIELDOFPTR.name);
    if (ra->d.RAFIELDOFPTR.ty != NULL)
      cpb_assert_struct_union_type(&ra->d.RAFIELDOFPTR.type, ra->d.RAFIELDOFPTR.ty->type,
                                   env);
    break;
  case RA_QFOP: {
    struct logic_var_info *info;
    struct qvar_list *qv;
    if (ra->d.RAQFOP.abs.body == NULL) {
      if (ra->d.RAQFOP.op == A_FORALL)
        ra->d.RAQFOP.abs.body = ATTVar(ra->d.RAQFOP.abs.name, KStar());
      else
        ra->d.RAQFOP.abs.body = ATTVar(ra->d.RAQFOP.abs.name, KStar());
      qv = NULL;
    } else
      REPLACE_ATYPE(ra->d.RAQFOP.abs.body,
                    cpb_atype(ra->d.RAQFOP.abs.qv, ra->d.RAQFOP.abs.body, &qv, env));
    if (ra->d.RAQFOP.op == A_FORALL)
      info = add_forall_var(ra->d.RAQFOP.abs.name, qv, ra->d.RAQFOP.abs.body, env);
    else
      info = add_exists_var(ra->d.RAQFOP.abs.name, qv, ra->d.RAQFOP.abs.body, env);
    ra->d.RAQFOP.abs.info = info;
    cpb_assert_rec(ra->d.RAQFOP.arg, env);
    remove_var_by_name(ra->d.RAQFOP.abs.name, eph);
    break; }
  case RA_OLD:
    cpb_assert_rec(ra->d.RAOLD.arg, env);
    break;
  case RA_DATA_AT:
    if (ra->d.RADATA_AT.type != NULL)
      cpb_type(ra->d.RADATA_AT.type->type, env);
    cpb_assert_rec(ra->d.RADATA_AT.addr, env);
    cpb_assert_rec(ra->d.RADATA_AT.val, env);
    break;
  case RA_UNDEF_DATA_AT:
    if (ra->d.RAUNDEF_DATA_AT.type != NULL)
      cpb_type(ra->d.RAUNDEF_DATA_AT.type->type, env);
    cpb_assert_rec(ra->d.RAUNDEF_DATA_AT.addr, env);
    break;
  case RA_FIELD_ADDRESS:
    cpb_assert_rec(ra->d.RAFIELD_ADDRESS.addr, env);
    ra->d.RAFIELD_ADDRESS.field = find_field_by_name(ra->d.RAFIELD_ADDRESS.field_name, eph);
    if (ra->d.RAFIELD_ADDRESS.field == NULL)
      failwith("No such member `%s'", ra->d.RAFIELD_ADDRESS.field_name);
    if (ra->d.RAFIELD_ADDRESS.ty != NULL)
      cpb_assert_struct_union_type(&ra->d.RAFIELD_ADDRESS.type, ra->d.RAFIELD_ADDRESS.ty->type,
                                   env);
    break;
  case RA_ARR:
    if (ra->d.RAARR.elt != NULL)
      cpb_type(ra->d.RAARR.elt->type, env);
    cpb_assert_rec(ra->d.RAARR.addr, env);
    cpb_assert_rec(ra->d.RAARR.len, env);
    cpb_assert_rec(ra->d.RAARR.list, env);
    break;
  case RA_SPEC:
    cpb_assert_rec(ra->d.RASPEC.f, env);
    ra->d.RASPEC.info = parse_anon_func_dec(ra->d.RASPEC.sig, ra->d.RASPEC.spec, env);
    break;
  case RA_SHADOW: {
    int depth = 0;
    struct RAssertion *it;
    for (it = ra; it->t == RA_SHADOW; it = it->d.RASHADOW.arg)
      depth += 1;
    if (it->t != RA_PROGVAR)
      failwith("Not shadowing a variable");
    char *name = it->d.RAPROGVAR.name;
    struct var_scope_union *u = find_prog_var_by_name(name, eph);
    if (u == NULL)
      failwith("Shadow level exceeds");
    struct prog_var_info *info;
    for (info = u->d.prog_var; info != NULL; info = info->shadowing)
      if (depth == 0)
        break;
      else
        depth -= 1;
    if (info == NULL)
      failwith("Shadow level exceeds");
    cpb_free_shadow_chain(ra->d.RASHADOW.arg);
    ra->t = RA_PROGVAR;
    ra->d.RAPROGVAR.name = name;
    ra->d.RAPROGVAR.info = info;
    break; }
  case RA_LOGICVAR:
    assert(0);
  }
}

void cpb_assert(struct RAssertion *ra, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  scope_env_deep(eph);
  cpb_assert_rec(ra, env);
  scope_env_up(eph);
}

struct atype *cpb_atype_rec(struct atype *ty, struct hashtbl *h, struct ephemeral_env *env) {
  switch (ty->t) {
  case AT_ARROW:
    REPLACE_ATYPE(ty->d.ARROW.from, cpb_atype_rec(ty->d.ARROW.from, h, env));
    REPLACE_ATYPE(ty->d.ARROW.to, cpb_atype_rec(ty->d.ARROW.to, h, env));
    return ty;
  case AT_APP:
    REPLACE_ATYPE(ty->d.APP.tfn, cpb_atype_rec(ty->d.APP.tfn, h, env));
    REPLACE_ATYPE(ty->d.APP.rand, cpb_atype_rec(ty->d.APP.rand, h, env));
    return ty;
  case AT_TVAR: {
    int v;
    struct atype *tv = hashtbl_find(h, ty->d.TVAR.name, &v);
    if (tv != NULL) {
      if (ty->d.TVAR.name != NULL) {
        free(ty->d.TVAR.name);
        ty->d.TVAR.name = NULL;
      }
      return tv;
    } else {
      struct atype_info *a = find_atype_by_name(ty->d.TVAR.name, env);
      if (a == NULL) {
        struct atype *t = find_atype_alias_by_name(ty->d.TVAR.name, env);
        if (t == NULL)
          failwith("Undefined identifier `%s'", ty->d.TVAR.name);
        if (ty->refcnt <= 1) {
          free(ty->d.TVAR.name);
          ty->d.TVAR.name = NULL;
        }
        return t;
      }
      free(ty->d.TVAR.name);
      ty->t = AT_ATOM;
      ty->d.ATOM.info = a;
      return ty;
    } }
  case AT_ATOM:
    return ty; // already processed
  case AT_QVAR:
    assert(0);
  }
}

struct qvar_list *cpb_build_map(struct atype_list *qv, struct hashtbl *h) {
  if (qv == NULL)
    return NULL;
  struct qvar_list *next = cpb_build_map(qv->next, h);
  int v;
  if (hashtbl_find(h, qv->name, &v) != NULL)
    failwith("Redefinition of quantified type %s", qv->name);
  if (qv->kind == NULL)
    qv->kind = KVar(qv->name);
  struct atype *q = ATQVar(qv->name, qv->kind);
  hashtbl_add(h, qv->name, q);
  return qvar_list_cons(q, next);
}

struct atype *cpb_atype(struct atype_list *qv, struct atype *body,
                        struct qvar_list **ql,
                        struct environment *env) {
  struct hashtbl h;
  init_hashtbl(&h, hash_string, string_equal);
  if (ql != NULL)
    *ql = cpb_build_map(qv, &h);
  struct atype *res = cpb_atype_rec(body, &h, &env->ephemer);
  hashtbl_clear(&h);
  return res;
}

