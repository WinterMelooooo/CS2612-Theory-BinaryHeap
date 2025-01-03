#include "utils.h"
#include "cp.h"
#include "pparser.h"

void parse_expr(struct pp_expr *e, struct environment *env) {
  cppt_expr(e);
  cpb_expr(e, env);
  cpat_expr(e, &env->persist);
  cpap_expr(e);
  cpi_expr(e);
  cpo_expr(e);
  cpc_expr(e);
  cpt_expr(e);
  cpa_expr(e, env);
  cppa_expr(e);
  cplv_expr(e);
}

struct expr *parse_cond(struct pp_expr *e, struct environment *env) {
  parse_expr(e, env);
  if (!cpt_is_effective_scalar(e->type))
    failwith("Statement requires controlling expression of scalar type");
  return expr_of_pp_expr(e);
}

struct expr *parse_switch_cond(struct pp_expr *e, struct environment *env) {
  parse_expr(e, env);
  if (e->type->t == T_ENUM ||
      e->type->t == T_BASIC && e->type->d.BASIC.ty == T_INT)
  return expr_of_pp_expr(e);
  failwith("Switch statement requires controlling expression of integer type or enumeration type");
}

struct expr *parse_case_cond(struct pp_expr *e, struct environment *env) {
  parse_expr(e, env);
  struct context_stack *s;
  for (s = env->context.c; s->t != CTX_SWITCH; s = s->outer)
    ;
  if (!type_equal(e->type, s->d.SWITCH.c->d.SWITCH.cond->type))
    failwith("Incompatible type between switch controlling expression and case label expression");
  if (e->type->t == T_ENUM) {
    if (e->t != PP_ENUMLIT)
      failwith("Case label expression is not an enumerator constant");
  } else if (e->type->t == T_BASIC && e->type->d.BASIC.ty == T_INT)
    cpc_eval_to_const(e);
  else
    failwith("Case label expression is not an integer constant expression");
  return expr_of_pp_expr(e);
}

struct expr *parse_ret(struct pp_expr *e, struct environment *env) {
  parse_expr(e, env);
  struct context_stack *s;
  for (s = env->context.c; s->t != CTX_FUNC; s = s->outer)
    ;
  if (!cpt_recov_conv(e->type, s->d.FUNC.info->ret_type, e, NULL))
    failwith("Returning from a function with incompatible result type");
  return expr_of_pp_expr(e);
}

char *parse_type(struct pp_pretype *t, struct environment *env) {
  char *name = cppt_type(t);
  cpb_type(t->type, env);
  cpap_type(t->type);
  cpo_type(t->type);
  cpc_type(t->type);
  return name;
}

struct pp_type *parse_decl_head(struct pp_trivtype *triv, struct environment *env) {
  if (triv->is_extern_or_static &&
      env->context.c->t != CTX_TOP)
    failwith("Declaring variable with global storage in function is not supported yet");
  struct pp_pretype *tr = PreType(triv, DERIVEnd(NULL));
  parse_type(tr, env);
  struct pp_type *res = tr->type;
  free(tr->deriv);
  free(tr);
  return res;
}

void parse_assert_common(struct RAssertion *ra, struct environment *env) {
  cppt_assert(ra);
  cpb_assert(ra, env);
  /* cpi_assert(ra); */
  cpat_assert(ra, &env->persist);
  cpc_assert(ra);
}

void bind_or_guess_lvar(struct lvar_list *with, struct environment *env) {
  struct lvar_list *it;
  for (it = with; it != NULL; it = it->next) {
    if (it->type == NULL)
      ASSIGN_ATYPE(it->type, ATTVar(it->name, KStar()))
    else
      REPLACE_ATYPE(it->type, cpb_atype(NULL, it->type, NULL, env));
    cpat_inhabited(it->type);
  }
}

struct func_spec *parse_spec(struct atype_list *witht,
                             struct lvar_list *with,
                             struct RAssertion *pre,
                             struct RAssertion *post,
                             struct prog_var_info_list *param,
                             struct type *ret_ty,
                             struct environment *env) {
  struct atype_list *i;
  struct lvar_list *it;
  struct ExistList *t_l = cpd_declare_atypes(witht, env);
  bind_or_guess_lvar(with, env);
  struct ExistList *v_l = cpd_define_free(with, env);

  parse_assert_common(pre, env);
  parse_assert_common(post, env);

  for (i = witht; i != NULL; i = i->next)
    cpat_check_kind_resolve(i->kind);
  for (it = with; it != NULL; it = it->next)
    cpat_check_resolve(it->type);

  cpt_assert(pre, ret_ty);
  cpt_assert(post, ret_ty);
  struct func_spec *res = cpa_spec(t_l, v_l, pre, post, param, env);
  return res;
}

struct func_spec *name_only_spec(char *name) {
  struct func_spec *spec = (struct func_spec *)malloc(sizeof(struct func_spec));
  spec->name = name;
  spec->derived_by = NULL;
  spec->next = NULL;
  spec->pre = spec->post = NULL;
  spec->with = spec->witht = NULL;
  spec->qv = NULL;
  spec->__return = NULL;
  return spec;
}

struct func_info *parse_func_common(struct pp_type *ty,
                                    char *name,
                                    struct pp_spec *spec,
                                    struct environment *env,
                                    int define,
                                    int named) {
  struct ephemeral_env *eph = &env->ephemer;
  if (ty->t != PP_FUNCTION)
    failwith("Function declaration does not have function type");
  struct pp_type *ret = ty->d.FUNCTION.ret;
  struct annot_list *param = ty->d.FUNCTION.param;
  cpap_param(param);
  if (cpo_is_function(ret))
    failwith("Function cannot return function type");
  if (define) {
    if (cpi_is_incomplete(ret) &&
        !(ret->t == PP_BASIC && ret->d.BASIC.ty == T_VOID) &&
        !(ret->t == PP_TYPE_ALIAS && type_is_void(ret->d.TYPE_ALIAS.info->type)))
      failwith("Incomplete result type in function definition");
    struct annot_list *it;
    for (it = param; it != NULL; it = it->tail) {
      if (cpi_is_incomplete(it->head->type->type))
        failwith("Function parameter has incomplete type");
    }
  }
  struct type *ret_ty = type_of_pp_type(ret);
  ret_ty->refcnt += 1;
  scope_env_deep(eph);
  struct prog_var_info_list *param_info = cpd_define_param(named ? name : NULL, param, env);
  struct func_spec *fspec = NULL;
  if (spec != NULL) {
    printf("Start to parse function spec %s of function %s\n", (spec->name != NULL) ? spec->name : "<anonymous>", name);
    if (spec->pre == NULL) {
      if (!define)
        failwith("It is meaning less to specify a specified specification");
      fspec = name_only_spec(spec->name);
    } else {
      fspec = parse_spec(spec->witht, spec->with,
                         spec->pre, spec->post,
                         param_info, ret_ty, env);
      fspec->name = spec->name;
      fspec->derived_by = spec->derived_by;
    }
  }
  ret_ty->refcnt -= 1;
  if (!define)
    scope_env_up(eph);
  if (named)
    if (define)
      return cpd_define_func(ret_ty, name, param_info, fspec, env);
    else
      return cpd_declare_func(ret_ty, name, param_info, fspec, env);
  else
    return define_anonymous_func(name, ret_ty, param_info, fspec, &env->persist);
}

void free_decl_pp_type(struct pp_type *ty) {
  struct pp_type **i = &ty;
  while (1) {
    switch ((*i)->t) {
    case PP_BASIC:
    case PP_STRUCT:
    case PP_UNION:
    case PP_ENUM:
    case PP_TYPE_ALIAS:
      break;
    case PP_PTR:
      i = &(*i)->d.PTR.ty;
      continue;
    case PP_ARRAY:
      i = &(*i)->d.ARRAY.ty;
      continue;
    case PP_FUNCTION:
      i = &(*i)->d.FUNCTION.ret;
      continue;
    case PP_ANON_STRUCT:
    case PP_ANON_UNION:
    case PP_ANON_ENUM:
      assert(0);
    }
    break;
  }
  *i = PPBasic(T_INT);
  free_pp_type(ty);
}

struct prog_var_info *parse_decl(struct pp_type *base, struct pp_derivtype *deriv, struct environment *env) {
  int is_top = env->context.c->t == CTX_TOP ||
               env->context.c->t == CTX_DECL && env->context.c->outer->t == CTX_TOP;
  char *name = cppt_derive_type(&base, deriv);
  cpb_decl_type(base, env);
  if (cpo_is_function(base)) {
    if (!is_top)
      failwith("Variable declared as a function is not supported yet");
    if (base->t == PP_FUNCTION) {
      parse_func_common(base, name, NULL, env, 0, 1);
      free_decl_pp_type(base);
    } else {
      struct pp_type *tmp_f = pp_type_of_type(type_unalias(base->d.TYPE_ALIAS.info->type));
      parse_func_common(tmp_f, name, NULL, env, 0, 1);
      free_pp_type(tmp_f);
    }
    return find_prog_var_by_name(name, &env->ephemer)->d.prog_var;
  }
  cpap_type(base);
  cpo_type(base);
  cpc_type(base);
  if (cpi_is_incomplete(base))
    failwith("Variable has incomplete type");
  struct type *type = type_of_pp_type(base);
  free_decl_pp_type(base);
  if (is_top)
    return cpd_define_global_var(type, name, env);
  else
    return cpd_define_local(name, type, env);
}

struct type_info *parse_type_def(struct pp_type *base, struct pp_derivtype *deriv,
                                 struct environment *env) {
  char *name = cppt_derive_type(&base, deriv);
  cpb_decl_type(base, env);
  cpap_type(base);
  cpo_type(base);
  cpc_type(base);
  struct type *type = type_of_pp_type(base);
  free_decl_pp_type(base);
  return cpd_define_type(name, type, env);
}

struct RAssertion *extract_forall_from_exists(struct RAssertion *pre,
                                              struct lvar_list **with) {
  if (pre->t == RA_QFOP && pre->d.RAQFOP.op == A_EXISTS) {
    if (!pre->d.RAQFOP.bracket) {
      *with = lvar_list_cons(pre->d.RAQFOP.abs.name, pre->d.RAQFOP.abs.body, NULL);
      with = &((*with)->next);
      if (pre->d.RAQFOP.abs.body != NULL)
        pre->d.RAQFOP.abs.body->refcnt -= 1;
      struct RAssertion *res = extract_forall_from_exists(pre->d.RAQFOP.arg, with);
      free(pre);
      return res;
    } else {
      pre->d.RAQFOP.arg = extract_forall_from_exists(pre->d.RAQFOP.arg, with);
      return pre;
    }
  } else {
    return pre;
  }
}

struct func_spec *parse_local_spec_single(struct RAssertion *pre, struct RAssertion *post,
                                          struct environment *env) {
  scope_env_deep(&env->ephemer);
  struct lvar_list *with = NULL;
  struct RAssertion *pre_body = extract_forall_from_exists(pre, &with);

  bind_or_guess_lvar(with, env);
  struct ExistList *with_ret = cpd_define_free(with, env);

  parse_assert_common(pre_body, env);
  parse_assert_common(post, env);
  cpt_assert(pre_body, NULL);
  cpt_assert(post, NULL);
  struct lvar_list *i;
  for (i = with; i != NULL; i = i->next)
    cpat_check_resolve(i->type);

  struct func_spec *res = cpa_local_spec(with_ret, pre_body, post, env);

  scope_env_up(&env->ephemer);
  return res;
}

struct func_spec *parse_local_spec(struct RAssertion *pre, struct RAssertion *post,
                                   struct environment *env) {
  if (pre->t != RA_BINOP || pre->d.RABINOP.op != T_OR) {
    return parse_local_spec_single(pre, post, env);
  } else {
    struct func_spec *res = NULL;
    for (; pre->t == RA_BINOP && pre->d.RABINOP.op == T_OR &&
           post->t == RA_BINOP && post->d.RABINOP.op == T_OR ;
         pre = pre->d.RABINOP.left, post = post->d.RABINOP.left) {
      struct func_spec *spec =
        parse_local_spec_single(pre->d.RABINOP.right, post->d.RABINOP.right, env);
      spec->next = res;
      res = spec;
    }
    if ((pre->t == RA_BINOP && pre->d.RABINOP.op == T_OR) ||
        (post->t == RA_BINOP && post->d.RABINOP.op == T_OR)) {
      failwith("Unmatched numbers of pre- and post-condition cases");
    } else {
      struct func_spec *spec = parse_local_spec_single(pre, post, env);
      spec->next = res;
      res = spec;
    }
    return res;
  }
}

struct AsrtList *parse_comment(struct RAssertion *ra, char *name, struct environment *env) {
  parse_assert_common(ra, env);
  cpt_assert(ra, NULL);
  struct AsrtList *a = cpa_comment(ra, env);
  return a;
}

struct simple_cmd *parse_simple_cmd(struct pp_simple *simple, struct environment *env) {
  if (simple == NULL)
    return NULL;
  switch (simple->t) {
  case T_COMPUTATION:
    parse_expr(simple->d.COMPUTATION.arg, env);
    break;
  case T_ASGN:
    parse_expr(simple->d.ASGN.left, env);
    parse_expr(simple->d.ASGN.right, env);
    break;
  case T_INCDEC:
    parse_expr(simple->d.INCDEC.arg, env);
    break;
  }
  cpt_simple_cmd(simple);
  cppa_simple_cmd(simple);
  cplv_simple_cmd(simple);
  return simple_of_pp_simple(simple);
}

struct sepdef_info *parse_sepdef(char *name,
                                 struct atype_list *witht,
                                 struct lvar_list *with,
                                 struct RAssertion *cond,
                                 struct environment *env) {
  scope_env_deep(&env->ephemer);
  struct ExistList *qv = cpd_declare_atypes(witht, env);
  bind_or_guess_lvar(with, env);
  struct ExistList *withv = cpd_declare_sep_param(with, env);
  struct sepdef_info *info = cpd_define_sep(name, withv, env);
  struct AsrtList *a = parse_comment(cond, NULL, env);
  struct lvar_list *it;
  for (it = with; it != NULL; it = it->next)
    cpat_check_resolve(it->type);
  struct AsrtList *arr[1];
  arr[0] = a;
  struct qvar_list *ql = cpat_generalize(qv, withv, arr, 1, &env->persist);
  scope_env_up(&env->ephemer);
  return cpd_finalize_sep(info, ql, a);
}

struct atype_info *parse_atype_def(char *name, struct kind *k, struct environment *env) {
  if (k == NULL)
    failwith("Expected kind");
  return cpd_declare_extern_type(name, k, env);
}

struct logic_var_info *parse_extern_def(char *name, struct atype_list *qv, struct atype *body, struct environment *env) {
  struct qvar_list *ql;
  if (body == NULL)
    failwith("Expected type");
  body = cpb_atype(qv, body, &ql, env);
  cpat_inhabited(body);
  struct atype_list *i;
  for (i = qv; i != NULL; i = i->next)
    cpat_check_kind_resolve(i->kind);
  return cpd_declare_extern(name, ql, body, env);
}

struct kind *parameterize_kind(struct atype_list *qv, struct kind *k) {
  if (qv == NULL)
    return k;
  else
    return KArrow(qv->kind, parameterize_kind(qv->next, k));
}

struct atype *parameterize_atype(struct atype *t, struct atype_list *qv) {
  if (qv == NULL)
    return t;
  else
    return parameterize_atype(ATApp(t, ATTVar(clone_str(qv->name), NULL)), qv->next);
}

void parse_record_def(struct atype_list *params,
                      char *record_name, char *constr_name,
                      struct lvar_list *fields, struct environment *env) {
  for (struct atype_list *i = params; i != NULL; i = i->next)
    if (i->kind == NULL)
      ASSIGN_KIND(i->kind, KVar(i->name));
  struct atype_info *r =
    cpd_declare_extern_type(record_name, parameterize_kind(params, KStar()), env);
  struct lvar_list *i;
  if (constr_name != NULL) {
    struct atype *constr_type = parameterize_atype(ATAtom(r), params);
    struct atype **cur = &constr_type;
    for (i = fields; i != NULL; i = i->next) {
      *cur = ATArrow(clone_atype(i->type), *cur);
      cur = &(*cur)->d.APP.rand;
    }
    if (constr_type != *cur)
      (*cur)->refcnt = 1;

    struct qvar_list *ql;
    constr_type = cpb_atype(params, constr_type, &ql, env);
    cpd_declare_extern(constr_name, ql, constr_type, env);
  }
  for (i = fields; i != NULL; i = i->next) {
    struct qvar_list *ql;
    struct atype *ptype = cpb_atype(params, ATArrow(parameterize_atype(ATAtom(r), params), i->type), &ql, env);
    cpat_inhabited(ptype);
    cpd_declare_projection(i->name, ql, ptype, env);
  }
  for (struct atype_list *i = params; i != NULL; i = i->next)
    cpat_check_kind_resolve(i->kind);
}

struct projection_info *parse_proj_def(char *name, struct atype_list *qv,
                                       struct atype *type,
                                       struct environment *env) {
  struct qvar_list *q;
  type = cpb_atype(qv, type, &q, env);
  cpat_inhabited(type);
  while (type->t == AT_TVAR && type->d.TVAR.link != NULL)
    type = type->d.TVAR.link;
  if (type->t != AT_ARROW)
    failwith("Declared projection `%s' does not have an arrow type", name);
  struct atype_list *i;
  for (i = qv; i != NULL; i = i->next)
    cpat_check_kind_resolve(i->kind);
  struct projection_info *ret = cpd_declare_projection(name, q, type, env);
  return ret;
}

void parse_atype_alias(char *name, struct atype *type, struct environment *env) {
  type = cpb_atype(NULL, type, NULL, env);
  cpd_declare_extern_type_alias(name, type, env);
}

struct func_info *finalize_func_def(struct func_info *f, struct environment *env) {
  // if (f->spec != NULL) {
  //   struct AsrtList *arr[2];
  //   arr[0] = f->spec->pre;
  //   arr[1] = f->spec->post;
  //   f->spec->qv = cpat_generalize(f->spec->witht, f->spec->with, arr, 2, &env->persist);
  // }
  (void)env;
  return f;
}

struct func_info *parse_func_def(struct pp_pretype *ty,
                                 struct pp_spec *spec,
                                 struct environment *env) {
  char *name = parse_type(ty, env);
  return parse_func_common(ty->type, name, spec, env, 1, 1);
}

struct func_info *parse_func_dec(struct pp_pretype *ty,
                                 struct pp_spec *spec,
                                 struct environment *env) {
  char *name = parse_type(ty, env);
  return finalize_func_def(parse_func_common(ty->type, name, spec, env, 0, 1), env);
}


struct func_info *parse_anon_func_dec(struct pp_pretype *ty,
                                      struct pp_spec *spec,
                                      struct environment *env) {
  parse_type(ty, env);
  return finalize_func_def(parse_func_common(ty->type, "<anonymous function>", spec, env, 0, 0), env);
}

void parse_field_list(struct annot_list *fields, struct environment *env) {
  struct annot_list *it;
  for (it = fields; it != NULL; it = it->tail) {
    it->head->name = parse_type(it->head->type, env);
    if (cpi_is_incomplete(it->head->type->type))
      failwith("Field has incomplete type");
    if (cpo_is_function(it->head->type->type))
      failwith("Field declared as a function");
  }
}

struct struct_union_info *parse_struct_def(char *name, struct annot_list *fields, struct environment *env) {
  struct struct_union_info *info = cpd_declare_struct(name, env);
  parse_field_list(fields, env);
  cpd_define_field_list(fields, info, env);
  cpc_struct(info);
  return cpd_finalize_struct(info);
}

struct struct_union_info *parse_union_def(char *name, struct annot_list *fields, struct environment *env) {
  struct struct_union_info *info = cpd_declare_union(name, env);
  parse_field_list(fields, env);
  cpd_define_field_list(fields, info, env);
  cpc_union(info);
  return cpd_finalize_union(info);
}

struct enum_info *parse_enum_def(char *name, struct pp_enum_list *rator, struct environment *env) {
  struct enum_info *info = cpd_define_enum(name, env);
  cpd_define_enum_list(rator, 0, info, env);
  return info;
}

struct struct_union_info *parse_anon_struct_def(struct annot_list *fields, struct environment *env) {
  parse_field_list(fields, env);
  struct struct_union_info *info = define_anonymous_struct(clone_str("<anonymous struct>"), &env->persist);
  cpd_define_field_list(fields, info, env);
  cpc_struct(info);
  return info;
}

struct struct_union_info *parse_anon_union_def(struct annot_list *fields, struct environment *env) {
  parse_field_list(fields, env);
  struct struct_union_info *info = define_anonymous_union(clone_str("<anonymous union>"), &env->persist);
  cpd_define_field_list(fields, info, env);
  cpc_union(info);
  return info;
}

struct enum_info *parse_anon_enum_def(struct pp_enum_list *rator, struct environment *env) {
  struct enum_info *info = define_anonoymous_enum(clone_str("<anonymous enum>"), &env->persist);
  cpd_define_enum_list(rator, 0, info, env);
  return info;
}

struct struct_union_info *parse_struct_dec(char *name, struct environment *env) {
  return cpd_declare_struct(name, env);
}

struct struct_union_info *parse_union_dec(char *name, struct environment *env) {
  return cpd_declare_union(name, env);
}

struct enum_info *parse_enum_dec(char *name, struct environment *env) {
  return cpd_declare_enum(name, env);
}

struct type_list *type_list_of_annot_list(struct annot_list *tl) {
  if (tl == NULL)
    return NULL;
  return TLCons(type_of_pp_type(tl->head->type->type),
                type_list_of_annot_list(tl->tail));
}

struct type *type_of_pp_type(struct pp_type *ty) {
  switch (ty->t) {
  case PP_BASIC:
    return TBasic(ty->d.BASIC.ty);
  case PP_STRUCT:
    return TStruct(ty->d.STRUCT.info);
  case PP_UNION:
    return TUnion(ty->d.UNION.info);
  case PP_ENUM:
    return TEnum(ty->d.ENUM.info);
  case PP_PTR:
    return TPtr(type_of_pp_type(ty->d.PTR.ty));
  case PP_ARRAY:
    return TArray(type_of_pp_type(ty->d.ARRAY.ty), ty->d.ARRAY.size->d.CONST.value);
  case PP_FUNCTION:
    return TFunction(type_of_pp_type(ty->d.FUNCTION.ret),
                     type_list_of_annot_list(ty->d.FUNCTION.param));
  case PP_TYPE_ALIAS:
    return TTypeAlias(ty->d.TYPE_ALIAS.info);
  case PP_ANON_STRUCT:
  case PP_ANON_UNION:
  case PP_ANON_ENUM:
    assert(0);
  }
}

struct expr *expr_of_pp_expr(struct pp_expr *e);

struct expr_list *expr_list_of_pp_expr_list(struct pp_expr_list *el) {
  if (el == NULL)
    return NULL;
  return ELCons(expr_of_pp_expr(el->head), expr_list_of_pp_expr_list(el->tail));
}

struct expr *expr_of_pp_expr(struct pp_expr *e) {
  struct expr *res;
  switch(e->t) {
  case PP_CONST:
    res = TConst(e->d.CONST.value);
    break;
  case PP_STRING:
    res = TString(e->d.STRING.str);
    break;
  case PP_VAR:
    res = TVar(e->d.VAR.info);
    break;
  case PP_BINOP:
    res = TBinop(e->d.BINOP.op,
                  expr_of_pp_expr(e->d.BINOP.left), expr_of_pp_expr(e->d.BINOP.right));
    break;
  case PP_UNOP:
    res = TUnop(e->d.UNOP.op, expr_of_pp_expr(e->d.UNOP.arg));
    break;
  case PP_CAST:
    res = TCast(type_of_pp_type(e->d.CAST.ty->type), expr_of_pp_expr(e->d.CAST.arg));
    break;
  case PP_CALL:
    if (e->d.CALL.vargs != NULL)
      res = TCall(expr_of_pp_expr(e->d.CALL.func),
                  expr_list_of_pp_expr_list(e->d.CALL.args),
                  e->d.CALL.vargs->after);
    else
      res = TCall(expr_of_pp_expr(e->d.CALL.func),
                  expr_list_of_pp_expr_list(e->d.CALL.args), NULL);
    break;
  case PP_DEREF:
    res = TDeref(expr_of_pp_expr(e->d.DEREF.arg));
    break;
  case PP_ADDRESS:
    res = TAddress(expr_of_pp_expr(e->d.ADDRESS.arg));
    break;
  case PP_SIZEOFTYPE:
    res = TSizeofType(type_of_pp_type(e->d.SIZEOFTYPE.ty->type));
    break;
  case PP_INDEX:
    res = TIndex(expr_of_pp_expr(e->d.INDEX.arg), expr_of_pp_expr(e->d.INDEX.pos));
    break;
  case PP_FIELDOF:
    res = TFieldof(expr_of_pp_expr(e->d.FIELDOF.arg), e->d.FIELDOF.field);
    break;
  case PP_FIELDOFPTR:
    res = TFieldofptr(expr_of_pp_expr(e->d.FIELDOFPTR.arg), e->d.FIELDOFPTR.field);
    break;
  case PP_ENUMLIT:
    res = TEnumLit(e->d.ENUMLIT.info);
    break;
  case PP_CONDITION:
    res = TCondition(expr_of_pp_expr(e->d.CONDITION.cond),
                     expr_of_pp_expr(e->d.CONDITION.btrue),
                     expr_of_pp_expr(e->d.CONDITION.bfalse));
    break;
  }
  ASSIGN_TYPE(res->type, e->type);
  return res;
}

struct annot_list *annot_list_of_type_list(struct type_list *tl) {
  if (tl == NULL)
    return NULL;
  struct annot *ann = TAnnot(PreType(NULL, DERIVEnd(NULL))); // either (1) consider nullptr in free, or (2) like here
  ann->name = NULL;
  ann->type->type = pp_type_of_type(tl->hd);
  return ALCons(ann, annot_list_of_type_list(tl->tl));
}

struct pp_type *pp_type_of_type(struct type *ty) {
  struct pp_type *res;
  switch (ty->t) {
  case T_BASIC:
    res = PPBasic(ty->d.BASIC.ty);
    break;
  case T_STRUCT:
    res = PPStruct(NULL);
    res->d.STRUCT.info = ty->d.STRUCT.info;
    break;
  case T_UNION:
    res = PPUnion(NULL);
    res->d.UNION.info = ty->d.UNION.info;
    break;
  case T_ENUM:
    res = PPEnum(NULL);
    res->d.ENUM.info = ty->d.ENUM.info;
    break;
  case T_PTR:
    res = PPPtr(pp_type_of_type(ty->d.PTR.ty));
    break;
  case T_ARRAY:
    res = PPArray(pp_type_of_type(ty->d.ARRAY.ty), PPConst(ty->d.ARRAY.size, 0, 0, 0));
    break;
  case T_FUNCTION:
    res = PPFunction(pp_type_of_type(ty->d.FUNCTION.ret),
                     annot_list_of_type_list(ty->d.FUNCTION.param));
    break;
  case T_TYPE_ALIAS:
    res = PPTypeAlias(NULL);
    res->d.TYPE_ALIAS.info = ty->d.TYPE_ALIAS.info;
    break;
  }
  return res;
}

struct simple_cmd *simple_of_pp_simple(struct pp_simple *s) {
  switch (s->t) {
  case PP_COMPUTATION:
    return TComputation(expr_of_pp_expr(s->d.COMPUTATION.arg));
  case PP_ASGN:
    return TAsgn(s->d.ASGN.op,
                 expr_of_pp_expr(s->d.ASGN.left), expr_of_pp_expr(s->d.ASGN.right));
  case PP_INCDEC:
    return TIncDec(s->d.INCDEC.op, expr_of_pp_expr(s->d.INCDEC.arg));
  }
}

