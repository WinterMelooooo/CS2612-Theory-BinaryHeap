#include "utils.h"
#include "env.h"
#include "plang.h"
#include "cp.h"

void cpat_error_incompatible_type(struct atype *t1, struct atype *t2) {
  stdout = stderr;
  fprintf(stderr, "\e[1;31merror:\e[0m Cannot unify types ");
  print_atype(t1);
  fprintf(stderr, " and ");
  print_atype(t2);
  fprintf(stderr, " ");
  if (__current_file != NULL)
    fprintf(stderr, "in %s:", __current_file);
  if (__current_scanner != NULL)
    fprintf(stderr, "%d:%d",
            yyget_lineno(__current_scanner),
            yyget_column(__current_scanner));
  exit(1);
}

int cpat_kind_occurs(struct kind *kv, struct kind *k) {
  switch (k->t) {
  case K_STAR:
    return 0;
  case K_ARROW:
    return cpat_kind_occurs(kv, k->d.ARROW.from) || cpat_kind_occurs(kv, k->d.ARROW.to);
  case K_KVAR:
    if (k->d.KVAR.link == NULL)
      return kv == k;
    else
      return cpat_kind_occurs(kv, k->d.KVAR.link);
  }
}

struct kind *cpat_kind_repr(struct kind *k) {
  if (kind_is_kvar(k)) {
    if (k->d.KVAR.link == NULL)
      return k;
    struct kind *ret = cpat_kind_repr(k->d.KVAR.link);
    REPLACE_KIND(k->d.KVAR.link, ret);
    return ret;
  } else
    return k;
}

void cpat_unify_kind(struct kind *k1, struct kind *k2) {
  k1 = cpat_kind_repr(k1);
  k2 = cpat_kind_repr(k2);
  if (k1 == k2)
    return;
  if (kind_is_kvar(k1)) {
    if (cpat_kind_occurs(k1, k2))
      failwith("Circular kind");
    REPLACE_KIND(k1->d.KVAR.link, k2);
  } else if (kind_is_kvar(k2)) {
    if (cpat_kind_occurs(k2, k1))
      failwith("Circular kind");
    REPLACE_KIND(k2->d.KVAR.link, k1);
  } else if (k1->t != k2->t)
    failwith("Incompatible kind")
  else
    switch (k1->t) {
    case K_STAR:
      break;
    case K_ARROW:
      cpat_unify_kind(k1->d.ARROW.from, k2->d.ARROW.from);
      cpat_unify_kind(k1->d.ARROW.to, k2->d.ARROW.to);
      break;
    case K_KVAR:
      assert(0);
    }
}

struct kind *cpat_kindof(struct atype *ty) {
  switch (ty->t) {
  case AT_ARROW: {
    struct kind *k1 = cpat_kindof(ty->d.ARROW.from);
    struct kind *k2 = cpat_kindof(ty->d.ARROW.to);
    struct kind *S = KStar();
    cpat_unify_kind(k1, S);
    cpat_unify_kind(k2, S);
    free_kind_if_unused(k1);
    free_kind_if_unused(S);
    return k2; }
  case AT_APP: {
    struct kind *k_f = cpat_kindof(ty->d.APP.tfn);
    struct kind *k_d = cpat_kindof(ty->d.APP.rand);
    struct kind *k_r = KVar("r");
    struct kind *k_f_e = KArrow(k_d, k_r);
    cpat_unify_kind(k_f_e, k_f);
    k_r->refcnt += 1;
    free_kind_if_unused(k_f);
    free_kind_if_unused(k_f_e);
    k_r->refcnt -= 1;
    return k_r; }
  case AT_QVAR:
    return ty->d.QVAR.kind;
  case AT_ATOM:
    return ty->d.ATOM.info->kind;
  case AT_TVAR:
    return ty->d.TVAR.kind;
  }
}

void cpat_inhabited(struct atype *ty) {
  struct kind *k = cpat_kindof(ty);
  struct kind *S = KStar();
  cpat_unify_kind(k, S);
  free_kind_if_unused(S);
  free_kind_if_unused(k);
}

struct atype *cpat_repr(struct atype *ty) {
  if (atype_is_tvar(ty)) {
    if (ty->d.TVAR.link == NULL)
      return ty;
    struct atype *ret = cpat_repr(ty->d.TVAR.link);
    REPLACE_ATYPE(ty->d.TVAR.link, ret);
    return ret;
  } else
    return ty;
}

int cpat_occurs(struct atype *tv, struct atype *ty) {
  switch (ty->t) {
  case AT_ATOM:
    return 0;
  case AT_ARROW:
    return cpat_occurs(tv, ty->d.ARROW.from) || cpat_occurs(tv, ty->d.ARROW.to);
  case AT_APP:
    return cpat_occurs(tv, ty->d.APP.tfn) || cpat_occurs(tv, ty->d.APP.rand);
  case AT_TVAR:
    if (ty->d.TVAR.link == NULL)
      return tv == ty;
    else
      return cpat_occurs(tv, ty->d.TVAR.link);
  case AT_QVAR:
    assert(0);
  }
}

void cpat_unify(struct atype *t1, struct atype *t2) {
  t1 = cpat_repr(t1);
  t2 = cpat_repr(t2);
  if (t1 == t2)
    return;
  if (atype_is_tvar(t1)) {
    if (cpat_occurs(t1, t2))
      failwith("Circular type");
    REPLACE_ATYPE(t1->d.TVAR.link, t2);
  } else if (atype_is_tvar(t2)) {
    if (cpat_occurs(t2, t1))
      failwith("Circular type");
    REPLACE_ATYPE(t2->d.TVAR.link, t1);
  } else if (t1->t != t2->t) {
    cpat_error_incompatible_type(t1, t2);
  }
  else
    switch (t1->t) {
    case AT_ARROW:
      cpat_unify(t1->d.ARROW.from, t2->d.ARROW.from);
      cpat_unify(t1->d.ARROW.to, t2->d.ARROW.to);
      break;
    case AT_APP:
      cpat_unify(t1->d.APP.tfn, t2->d.APP.tfn);
      cpat_unify(t1->d.APP.rand, t2->d.APP.rand);
      break;
    case AT_ATOM:
      if (t1->d.ATOM.info != t2->d.ATOM.info)
        cpat_error_incompatible_type(t1, t2);
      break;
    case AT_TVAR:
    case AT_QVAR:
      assert(0);
    }
}

struct qvar_list *cpat_inst_qv(struct qvar_list *qv) {
  if (qv == NULL)
    return NULL;
  struct qvar_list *next = cpat_inst_qv(qv->next);
  if (qv->qv->d.QVAR.inst != NULL)
    free_atype(qv->qv->d.QVAR.inst);
  struct atype *tv = ATTVar(qv->qv->d.QVAR.name, qv->qv->d.QVAR.kind);
  ASSIGN_ATYPE(qv->qv->d.QVAR.inst, tv);
  return qvar_list_cons(tv, next);
}

struct atype *cpat_inst_qv_build(struct atype *ty) {
  switch (ty->t) {
  case AT_ATOM:
    return ty;
  case AT_TVAR:
    if (ty->d.TVAR.link != NULL)
      return cpat_inst_qv_build(ty->d.TVAR.link);
    else
      return ty;
  case AT_ARROW: {
    struct atype *from = cpat_inst_qv_build(ty->d.ARROW.from);
    struct atype *to = cpat_inst_qv_build(ty->d.ARROW.to);
    if (from == ty->d.ARROW.from && to == ty->d.ARROW.to)
      return ty;
    else
      return ATArrow(from, to); }
  case AT_APP: {
    struct atype *tfn = cpat_inst_qv_build(ty->d.APP.tfn);
    struct atype *rand = cpat_inst_qv_build(ty->d.APP.rand);
    if (tfn == ty->d.APP.tfn && rand == ty->d.APP.rand)
      return ty;
    else
      return ATApp(tfn, rand); }
  case AT_QVAR:
    return ty->d.QVAR.inst;
  }
}

struct atype *cpat_instantiate(struct qvar_list *qv, struct atype *ty, struct qvar_list **impl) {
  *impl = cpat_inst_qv(qv);
  return cpat_inst_qv_build(ty);
}

struct atype *cpat_atypeof(struct RAssertion *e, int ctx_assert, struct persistent_env *env);

struct atype *cpat_check_with_fixed(struct RAssertion *e, struct atype *T, int ctx_assert,
                                    struct persistent_env *env) {
  struct atype *t = cpat_atypeof(e, ctx_assert, env);
  cpat_unify(t, T);
  free_atype_if_unused(T);
  return t;
}

int cpat_is_Z(struct atype *ty) {
  return ty->t == AT_ATOM && ty->d.ATOM.info->id == BUILTINTYPE_Z ||
    ty->t == AT_TVAR && ty->d.TVAR.link != NULL && cpat_is_Z(ty->d.TVAR.link);
}

int cpat_is_Prop(struct atype *ty) {
  return ty->t == AT_ATOM && ty->d.ATOM.info->id == BUILTINTYPE_PROP ||
    ty->t == AT_TVAR && ty->d.TVAR.link != NULL && cpat_is_Prop(ty->d.TVAR.link);
}

struct atype *cpat_convert_proj(struct RAssertion *e, struct atype *record,
                                struct logic_var_info *proj, struct RAssertion *rcd) {
  free(e->d.RAFIELDOF.name);
  e->t = RA_APP;
  e->d.RAAPP.f = RALogicVar(proj);
  e->d.RAAPP.rand = rcd;
  struct atype *y = cpat_instantiate(proj->qv, proj->atype,
                                     &e->d.RAAPP.f->d.RALOGICVAR.impl);
  cpat_unify(record, y->d.ARROW.from);
  struct atype *ret = y->d.ARROW.to;
  ret->refcnt += 1;
  free_atype_if_unused(y);
  ret->refcnt -= 1;
  return ret;
}

int cpat_more_specific(struct atype *t1, struct atype *t2) {
  if (atype_is_qvar(t2))
    return 1;
  if (t1->t != t2->t)
    return 0;
  switch (t1->t) {
  case AT_ATOM:
    return t1->d.ATOM.info->id == t2->d.ATOM.info->id;
  case AT_ARROW:
    return
      cpat_more_specific(t1->d.ARROW.from, t2->d.ARROW.from) &&
      cpat_more_specific(t1->d.ARROW.to, t2->d.ARROW.to);
  case AT_APP:
    return
      cpat_more_specific(t1->d.APP.tfn, t2->d.APP.tfn) &&
      cpat_more_specific(t1->d.APP.rand, t2->d.APP.rand);
  case AT_QVAR:
  case AT_TVAR:
    return 0;
  }
}

struct atype *cpat_atypeof(struct RAssertion *e, int ctx_assert,
                           struct persistent_env *env) {
  switch (e->t) {
  case RA_CONST:
  case RA_ENUMLIT:
  case RA___RETURN:
  case RA_TIME_COST:
  case RA_SIZEOF:
  case RA_PROGVAR:
    return ATZ(env);
  case RA_LOGICVAR:
    return cpat_instantiate(e->d.RALOGICVAR.info->qv, e->d.RALOGICVAR.info->atype,
                            &e->d.RALOGICVAR.impl);
  case RA_BINOP:
    if (ctx_assert) {
      if (e->d.RABINOP.op == T_AND ||
          e->d.RABINOP.op == T_OR ||
          e->d.RABINOP.op == T_MUL) {
        struct atype *A = ATAssertion(env);
        struct atype *t1 = cpat_atypeof(e->d.RABINOP.left, 1, env);
        struct atype *t2 = cpat_atypeof(e->d.RABINOP.right, 1, env);
        if (!cpat_is_Prop(t1))
          cpat_unify(t1, A);
        if (!cpat_is_Prop(t2))
          cpat_unify(t2, A);
        free_atype_if_unused(t1);
        free_atype_if_unused(t2);
        return A;
      } else if (e->d.RABINOP.op == T_EQ || e->d.RABINOP.op == T_NE) {
        struct atype *t1 = cpat_atypeof(e->d.RABINOP.left, 0, env);
        struct atype *t2 = cpat_atypeof(e->d.RABINOP.right, 0, env);
        cpat_unify(t1, t2);
        free_atype_if_unused(t1);
        free_atype_if_unused(t2);
        return ATAssertion(env);
      } else {
        struct atype *Z = ATZ(env);
        struct atype *t1 = cpat_atypeof(e->d.RABINOP.left, 0, env);
        struct atype *t2 = cpat_atypeof(e->d.RABINOP.right, 0, env);
        cpat_unify(t1, Z);
        cpat_unify(t2, Z);
        free_atype_if_unused(t1);
        free_atype_if_unused(Z);
        free_atype_if_unused(t2);
        return ATAssertion(env);
      }
    } else {
        struct atype *Z = ATZ(env);
        struct atype *t1 = cpat_atypeof(e->d.RABINOP.left, 0, env);
        struct atype *t2 = cpat_atypeof(e->d.RABINOP.right, 0, env);
        cpat_unify(t1, Z);
        cpat_unify(t2, Z);
        free_atype_if_unused(t1);
        free_atype_if_unused(Z);
        return t2;
    }
  case RA_UNOP:
    if (ctx_assert)
      return cpat_check_with_fixed(e->d.RAUNOP.arg, ATAssertion(env), ctx_assert, env);
    else
      return cpat_check_with_fixed(e->d.RAUNOP.arg, ATZ(env), ctx_assert, env);
  case RA_CAST:
    return cpat_check_with_fixed(e->d.RACAST.arg, ATZ(env), 0, env);
  case RA_APP: {
    struct atype *t_f = cpat_atypeof(e->d.RAAPP.f, 0, env);
    struct atype *t_d = cpat_atypeof(e->d.RAAPP.rand, 0, env);
    struct atype *t_r = ATTVar("r", KStar());
    struct atype *t_f_e = ATArrow(t_d, t_r);
    cpat_unify(t_f_e, t_f);
    t_r->refcnt += 1;
    free_atype_if_unused(t_f);
    free_atype_if_unused(t_f_e);
    t_r->refcnt -= 1;
    return t_r; }
  case RA_ANN: {
    cpat_inhabited(e->d.RAANN.type);
    struct atype *t = cpat_atypeof(e->d.RAANN.expr, ctx_assert, env);
    cpat_unify(t, e->d.RAANN.type);
    free_atype_if_unused(t);
    return e->d.RAANN.type; }
  case RA_DEREF:
    return cpat_check_with_fixed(e->d.RADEREF.arg, ATZ(env), 0, env);
  case RA_ADDRESS:
    return cpat_check_with_fixed(e->d.RAADDRESS.arg, ATZ(env), 0, env);
  case RA_INDEX: {
    // todo: array is a special case 
    free_atype_if_unused(cpat_check_with_fixed(e->d.RAINDEX.pos, ATZ(env), 0, env));
    struct atype *t_l = cpat_atypeof(e->d.RAINDEX.arg, 0, env);
    if (cpat_is_Z(t_l))
      return t_l;
    struct atype *t_e = ATTVar("e", KStar());
    struct atype *t_l_e = ATApp(ATList(env), t_e);
    cpat_unify(t_l_e, t_l);
    t_e->refcnt += 1;
    free_atype_if_unused(t_l);
    free_atype_if_unused(t_l_e);
    t_e->refcnt -= 1;
    return t_e; }
  case RA_FIELDOF: {
    struct atype *t = cpat_atypeof(e->d.RAFIELDOF.arg, 0, env);
    if (!cpat_is_Z(t)) { /* structures should not be Z. do not bother it now */
      if (e->d.RAFIELDOF.proj == NULL) {
        failwith("No such projection %s", e->d.RAFIELDOF.name);
      } else if (e->d.RAFIELDOF.proj->next == NULL) {
        /* only one possible projection */
        struct projection_info *info = e->d.RAFIELDOF.proj;
        struct atype *p = cpat_convert_proj(e, t, info->var, e->d.RAFIELDOF.arg);
        free_atype_if_unused(t);
        return p;
      } else {
        struct projection_info *i;
        for (i = e->d.RAFIELDOF.proj; i != NULL; i = i->next)
          // do not unify because it may abort
          if (cpat_more_specific(t, i->var->atype->d.ARROW.from)) {
            struct atype *p = cpat_convert_proj(e, t, i->var, e->d.RAFIELDOF.arg);
            free_atype_if_unused(t);
            return p;
          }
        failwith("No projection %s has a compatible type", e->d.RAFIELDOF.name);
      }
    } else {
      return t;
    } }
  case RA_FIELDOFPTR:
    return cpat_check_with_fixed(e->d.RAFIELDOFPTR.arg, ATZ(env), 0, env);
  case RA_OLD:
    return cpat_atypeof(e->d.RAOLD.arg, 0, env);
  case RA_SHADOW:
    return cpat_atypeof(e->d.RASHADOW.arg, 0, env);
  case RA_FIELD_ADDRESS:
    return cpat_check_with_fixed(e->d.RAFIELD_ADDRESS.addr, ATZ(env), 0, env);

  case RA_CONN: {
    struct atype *t1 = cpat_atypeof(e->d.RACONN.left, 1, env);
    struct atype *t2 = cpat_atypeof(e->d.RACONN.right, 1, env);
    struct atype *A = ATAssertion(env);
    cpat_unify(t1, A);
    cpat_unify(t2, A);
    free_atype_if_unused(t1);
    free_atype_if_unused(A);
    return t2; }
  case RA_QFOP:
    return cpat_check_with_fixed(e->d.RAQFOP.arg, ATAssertion(env), 1, env);
  case RA_EMP:
  case RA_TRUE:
  case RA_FALSE:
    return ATAssertion(env);
  case RA_DATA_AT:
    free_atype_if_unused(cpat_check_with_fixed(e->d.RADATA_AT.addr, ATZ(env), 0, env));
    free_atype_if_unused(cpat_check_with_fixed(e->d.RADATA_AT.val, ATZ(env), 0, env));
    return ATAssertion(env);
  case RA_UNDEF_DATA_AT:
    free_atype_if_unused(cpat_check_with_fixed(e->d.RAUNDEF_DATA_AT.addr, ATZ(env), 0, env));
    return ATAssertion(env);
  case RA_ARR:
    free_atype_if_unused(cpat_check_with_fixed(e->d.RAARR.addr, ATZ(env), 0, env));
    free_atype_if_unused(cpat_check_with_fixed(e->d.RAARR.len, ATZ(env), 0, env));
    free_atype_if_unused(cpat_check_with_fixed(e->d.RAARR.list, ATApp(ATList(env), ATZ(env)), 0, env));
    return ATAssertion(env);
  case RA_SPEC:
    free_atype_if_unused(cpat_check_with_fixed(e->d.RASPEC.f, ATZ(env), 0, env));
    return ATAssertion(env);
  }
}

void cpat_check_kind_resolve(struct kind *k) {
  switch (k->t) {
  case K_STAR:
    break;
  case K_ARROW:
    cpat_check_kind_resolve(k->d.ARROW.from);
    cpat_check_kind_resolve(k->d.ARROW.to);
    break;
  case K_KVAR:
    if (k->d.KVAR.link == NULL)
      failwith("Kind '%s' cannot be inferred", k->d.KVAR.name);
    cpat_check_kind_resolve(k->d.KVAR.link);
    break;
  }
}

void cpat_check_resolve(struct atype *ty) {
  if (atype_is_tvar(ty) && ty->d.TVAR.link == NULL)
    failwith("Type variable '_%s cannot be inferred", ty->d.TVAR.name);
}

void cpat_all_resolved(struct RAssertion *ra) {
  switch (ra->t) {
  case RA_LOGICVAR: {
    struct qvar_list *i;
    for (i = ra->d.RALOGICVAR.impl; i != NULL; i = i->next)
      cpat_check_resolve(i->qv);
    break; }
  case RA_BINOP:
    cpat_all_resolved(ra->d.RABINOP.left);
    cpat_all_resolved(ra->d.RABINOP.right);
    break;
  case RA_CONN:
    cpat_all_resolved(ra->d.RACONN.left);
    cpat_all_resolved(ra->d.RACONN.right);
    break;
  case RA_UNOP:
    cpat_all_resolved(ra->d.RAUNOP.arg);
    break;
  case RA_QFOP:
    cpat_check_resolve(ra->d.RAQFOP.abs.body);
    cpat_all_resolved(ra->d.RAQFOP.arg);
    break;
  case RA_ANN:
     cpat_all_resolved(ra->d.RAANN.expr);
     break;
  case RA_APP:
     cpat_all_resolved(ra->d.RAAPP.f);
     cpat_all_resolved(ra->d.RAAPP.rand);
     break;
  case RA_EMP:
  case RA_TRUE:
  case RA_FALSE:
  case RA_DATA_AT:
  case RA_UNDEF_DATA_AT:
  case RA_ARR:
  case RA_SPEC:

  case RA_CONST:
  case RA_PROGVAR:
  case RA_CAST:
  case RA_DEREF:
  case RA_ADDRESS:
  case RA_INDEX:
  case RA_FIELDOF:
  case RA_FIELDOFPTR:
  case RA_ENUMLIT:
  case RA___RETURN:
  case RA_SIZEOF:
  case RA_OLD:
  case RA_SHADOW:
  case RA_FIELD_ADDRESS:
  case RA_TIME_COST:
    break;
  }
}

void cpat_assert(struct RAssertion *p, struct persistent_env *env) {
  struct atype *t = cpat_atypeof(p, 1, env);
  if (cpat_is_Prop(t)) {
    free_atype_if_unused(t);
  } else {
    struct atype *a = ATAssertion(env);
    cpat_unify(a, t);
    free_atype_if_unused(a);
    free_atype_if_unused(t);
  }
  cpat_all_resolved(p);
}

void cpat_expr(struct pp_expr *e, struct persistent_env *env) {
  switch (e->t) {
  case PP_CONST:
  case PP_STRING:
  case PP_VAR:
  case PP_SIZEOFTYPE:
  case PP_ENUMLIT:
    break;
  case PP_BINOP:
    cpat_expr(e->d.BINOP.left, env);
    cpat_expr(e->d.BINOP.right, env);
    break;
  case PP_UNOP:
    cpat_expr(e->d.UNOP.arg, env);
    break;
  case PP_CAST:
    cpat_expr(e->d.CAST.arg, env);
    break;
  case PP_CALL: {
    cpat_expr(e->d.CALL.func, env);
    struct pp_expr_list *l;
    for (l = e->d.CALL.args; l != NULL; l = l->tail)
      cpat_expr(l->head, env);
    if (e->d.CALL.vargs != NULL) {
      struct pp_varg_list *i;
      for (i = e->d.CALL.vargs->pre; i != NULL; i = i->next) {
        ASSIGN_ATYPE(i->type, cpat_atypeof(i->val, 0, env));
        cpat_inhabited(i->type);
      }
      struct type_arg_list *j;
      for (j = e->d.CALL.vargs->type; j != NULL; j = j->next) {
        struct kind *k = cpat_kindof(j->type);
        free_kind_if_unused(k);
      }
    }
    break;}
  case PP_DEREF:
    cpat_expr(e->d.DEREF.arg, env);
    break;
  case PP_ADDRESS:
    cpat_expr(e->d.ADDRESS.arg, env);
    break;
  case PP_INDEX:
    cpat_expr(e->d.INDEX.arg, env);
    cpat_expr(e->d.INDEX.pos, env);
    break;
  case PP_FIELDOF:
    cpat_expr(e->d.FIELDOF.arg, env);
    break;
  case PP_FIELDOFPTR:
    cpat_expr(e->d.FIELDOFPTR.arg, env);
    break;
  case PP_CONDITION:
    cpat_expr(e->d.CONDITION.cond, env);
    cpat_expr(e->d.CONDITION.btrue, env);
    cpat_expr(e->d.CONDITION.bfalse, env);
    break;
  }
}

struct atype *cpat_generalize_rec(struct atype *ty, struct hashtbl *h) {
  switch (ty->t) {
  case AT_ATOM: {
    int v;
    struct atype *q = hashtbl_find(h, ty->d.ATOM.info, &v);
    if (q != NULL)
      return q;
    else
      return ty; }
  case AT_ARROW:
    REPLACE_ATYPE(ty->d.ARROW.from, cpat_generalize_rec(ty->d.ARROW.from, h));
    REPLACE_ATYPE(ty->d.ARROW.to, cpat_generalize_rec(ty->d.ARROW.to, h));
    return ty;
  case AT_APP:
    REPLACE_ATYPE(ty->d.APP.tfn, cpat_generalize_rec(ty->d.APP.tfn, h));
    REPLACE_ATYPE(ty->d.APP.rand, cpat_generalize_rec(ty->d.APP.rand, h));
    return ty;
  case AT_QVAR:
    return ty;
  case AT_TVAR:
    if (ty->d.TVAR.link != NULL)
      return cpat_generalize_rec(ty->d.TVAR.link, h);
    else
      failwith("Type variable '_%s cannot be inferred", ty->d.TVAR.name);
  }
}

void cpat_generalize_prop(struct Proposition *p, struct hashtbl *h, struct persistent_env *env) {
  switch (p->t) {
  case T_PROP_TRUE:
  case T_PROP_FALSE:
  case T_PROP_PTR:
  case T_PROP_COMPARE:
  case T_PROP_OTHER:
    break;
  case T_PROP_UNARY:
    cpat_generalize_prop(p->d.UNARY.prop, h, env);
    break;
  case T_PROP_BINARY:
    cpat_generalize_prop(p->d.BINARY.prop1, h, env);
    cpat_generalize_prop(p->d.BINARY.prop2, h, env);
    break;
  case T_PROP_QUANTIFIER: {
    struct logic_var_info *info = find_logic_var_by_id(p->d.QUANTIFIER.ident, env);
    REPLACE_ATYPE(info->atype, cpat_generalize_rec(info->atype, h));
    cpat_generalize_prop(p->d.QUANTIFIER.prop, h, env);
    break; }
  }
}

void cpat_generalize_var(struct ExistList *with, struct hashtbl *h, struct persistent_env *env) {
  for (; with != NULL; with = with->next) {
    struct logic_var_info *info = find_logic_var_by_id(with->id, env);
    REPLACE_ATYPE(info->atype, cpat_generalize_rec(info->atype, h));
  }
}

void cpat_generalize_asrtlist(struct AsrtList *a, struct hashtbl *h, struct persistent_env *env) {
  struct PropList *i;
  struct ExistList *j;
  struct FPSpecListNode *k;
  for (; a != NULL; a = a->next) {
    for (i = a->head->prop_list; i != NULL; i = i->next)
      cpat_generalize_prop(i->head, h, env);
    for (j = a->head->exist_list; j != NULL; j = j->next) {
      struct logic_var_info *info = find_logic_var_by_id(j->id, env);
      REPLACE_ATYPE(info->atype, cpat_generalize_rec(info->atype, h));
    }
    for (k = a->head->fp_spec_list->head; k != NULL; k = k->next) {
      cpat_generalize_var(k->data->func_info->spec->with, h, env);
      cpat_generalize_asrtlist(k->data->func_info->spec->pre, h, env);
      cpat_generalize_asrtlist(k->data->func_info->spec->post, h, env);
    }
  }
}

struct qvar_list *cpat_build_map(struct ExistList *qv, struct hashtbl *h, struct persistent_env *env) {
  if (qv == NULL)
    return NULL;
  struct qvar_list *next = cpat_build_map(qv->next, h, env);
  struct atype_info *info = find_atype_by_id(qv->id, env);
  struct atype *q = ATQVar(info->name, info->kind);
  hashtbl_add(h, info, q);
  free_kind(info->kind);
  free(info);
  return qvar_list_cons(q, next);
}

struct qvar_list *cpat_generalize(struct ExistList *qv, struct ExistList *with,
                                   struct AsrtList *as[], int nas,
                                   struct persistent_env *env) {
  struct hashtbl h;
  init_hashtbl(&h, hash_ptr, ptr_equal);
  struct qvar_list *ql = cpat_build_map(qv, &h, env);
  cpat_generalize_var(with, &h, env);
  int j;
  for (j = 0; j < nas; j++)
    cpat_generalize_asrtlist(as[j], &h, env);
  hashtbl_clear(&h);
  ExistListFree(qv);
  return ql;
}

/* tweak begin */

struct atype *cpat_inst_qv_build_alt(struct atype *t, struct hashtbl *map) {
  switch (t->t) {
  case AT_ATOM: {
    int v;
    struct atype *new = hashtbl_find(map, t->d.ATOM.info, &v);
    if (v)
      return new;
    else
      return t; }
  case AT_ARROW:
    return ATArrow(cpat_inst_qv_build_alt(t->d.ARROW.from, map),
                   cpat_inst_qv_build_alt(t->d.ARROW.to, map));
  case AT_APP:
    return ATApp(cpat_inst_qv_build_alt(t->d.APP.tfn, map),
                 cpat_inst_qv_build_alt(t->d.APP.rand, map));
  case AT_QVAR: {
    assert(0);
    return NULL;
  }
  case AT_TVAR:
    return cpat_inst_qv_build_alt(t->d.TVAR.link, map);
  }
}

struct qvar_list *cpat_inst_qv_alt(struct ExistList *witht, struct hashtbl *map,
                                   struct persistent_env *env) {
  if (witht == NULL)
    return NULL;
  struct atype_info *info = find_atype_by_id(witht->id, env);
  struct atype *tv = ATTVar(info->name, info->kind);
  hashtbl_add(map, info, tv);
  return qvar_list_cons(tv, cpat_inst_qv_alt(witht->next, map, env));
}

// making a self-recursive call
struct qvar_list *cpat_check_varg_alt(struct virt_arg *varg, struct func_spec *spec, struct persistent_env *env) {
  struct hashtbl map;
  init_hashtbl(&map, hash_ptr, ptr_equal);
  struct qvar_list *qv = cpat_inst_qv_alt(spec->witht, &map, env);

  struct type_arg_list *it;
  for (it = varg->type_arg; it != NULL; it = it->next) {
    struct qvar_list *iq;
    struct qvar_list *ii = qv;
    for (iq = spec->qv; iq != NULL; iq = iq->next) {
      if (strcmp(iq->qv->d.QVAR.name, it->name) == 0) {
        cpat_unify(ii->qv, it->type);
        break;
      }
      ii = ii->next;
    }
    if (iq == NULL)
      failwith("No such type `%s'", it->name);
  }
  struct ExistList *i;
  struct virt_arg_list *iv;
  struct qvar_list *iq;
  for (iv = varg->arg; iv != NULL; iv = iv->next) {
    for (i = spec->with; i != NULL; i = i->next) {
      struct logic_var_info *info = find_logic_var_by_id(i->id, env);
      if (strcmp(iv->name, info->name) == 0) {
        struct atype *t = iv->type;
        struct atype *t_e = cpat_inst_qv_build_alt(info->atype, &map);
        cpat_unify(t, t_e);
        free_atype_if_unused(t);
        free_atype_if_unused(t_e);
        break;
      }
    }
    if (i == NULL)
      failwith("No such logic parameter `%s'", iv->name);
  }
  for (iq = qv; iq != NULL; iq = iq->next)
    cpat_check_resolve(iq->qv);
  for (iv = varg->arg; iv != NULL; iv = iv->next)
    cpat_check_resolve(iv->type);

  hashtbl_clear(&map);
  return qv;
}

/* tweak end */

struct qvar_list *cpat_check_varg(struct virt_arg *varg, struct func_spec *spec, struct persistent_env *env) {
  struct ExistList *i;
  struct qvar_list *qv = cpat_inst_qv(spec->qv), *iq;

  struct type_arg_list *it;
  for (it = varg->type_arg; it != NULL; it = it->next) {
    struct qvar_list *iq;
    struct qvar_list *ii = qv;
    for (iq = spec->qv; iq != NULL; iq = iq->next) {
      if (strcmp(iq->qv->d.QVAR.name, it->name) == 0) {
        cpat_unify(ii->qv, it->type);
        break;
      }
      ii = ii->next;
    }
    if (iq == NULL)
      failwith("No such type `%s'", it->name);
  }
  struct virt_arg_list *iv;
  for (iv = varg->arg; iv != NULL; iv = iv->next) {
    for (i = spec->with; i != NULL; i = i->next) {
      struct logic_var_info *info = find_logic_var_by_id(i->id, env);
      if (strcmp(iv->name, info->name) == 0) {
        struct atype *t = iv->type;
        struct atype *t_e = cpat_inst_qv_build(info->atype);
        cpat_unify(t, t_e);
        free_atype_if_unused(t);
        free_atype_if_unused(t_e);
        break;
      }
    }
    if (i == NULL)
      failwith("No such logic parameter `%s'", iv->name);
  }
  for (iq = qv; iq != NULL; iq = iq->next)
    cpat_check_resolve(iq->qv);
  for (iv = varg->arg; iv != NULL; iv = iv->next)
    cpat_check_resolve(iv->type);
  return qv;
}

