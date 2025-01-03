/* prerequisites:
     types of members should be processed already
     types of parameters should be processed already
*/

#include "utils.h"
#include "cp.h"

struct field_info *cpd_define_field_list(struct annot_list *field,
                                         struct struct_union_info *parent,
                                         struct environment *env) {
  if (field == NULL) {
    parent->first_field = NULL;
    return NULL;
  }
  struct field_info *next = cpd_define_field_list(field->tail, parent, env);
  struct annot *f = field->head;
  struct ephemeral_env *eph = &env->ephemer;
  struct field_info *old;
  WITH_CURRENT_SCOPE_ONLY(old, find_field_by_name(f->name, eph), eph);
  if (old != NULL && old->parent == parent)
    failwith("Duplicate member `%s'", f->name);
  struct field_info *info = define_field(f->name, type_of_pp_type(f->type->type), parent, next, env);
  parent->first_field = info;
  return info;
}

struct struct_union_info *cpd_define_struct(char *name, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct struct_union_info *info;
  WITH_CURRENT_SCOPE_ONLY(info, find_struct_or_union_by_name(name, eph), eph);
  if (info != NULL) {
    if (info->t == IS_UNION)
      failwith("Use of `%s' with tag type that does not match previous declaration", name);
    if (info->defined)
      failwith("Redefinition of type `struct %s'", name);
    info->defined = 1;
    free(name);
  } else
    info = define_struct(name, env);
  return info;
}

struct struct_union_info *cpd_define_union(char *name, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct struct_union_info *info;
  WITH_CURRENT_SCOPE_ONLY(info, find_struct_or_union_by_name(name, eph), eph);
  if (info != NULL) {
    if (info->t == IS_STRUCT)
      failwith("Use of `%s' with tag type that does not match previous declaration", name);
    if (info->defined)
      failwith("Redefinition of type `union %s'", name);
    info->defined = 1;
    free(name);
  } else
    info = define_union(name, env);
  return info;
}

void cpd_check_redef(enum var_scope_union_type t, char *name, struct ephemeral_env *eph) {
  struct var_scope_union *u;
  WITH_CURRENT_SCOPE_ONLY(u, find_name_in_var_scope(name, eph), eph);
  if (u != NULL) {
    if (u->t == t)
      failwith("Redefinition of `%s'", name)
    else
      failwith("Redefinition of `%s' as different kind of symbol", name);
  }
}

struct enumerator_info *cpd_define_enum_list(struct pp_enum_list *rator,
                                             int val,
                                             struct enum_info *parent,
                                             struct environment *env) {
  if (rator == NULL) {
    parent->first_rator = NULL;
    return NULL;
  }
  if (rator->value_valid) {
    if (rator->neg) {
      if (rator->value > 2147483648)
        failwith("Integer literal is too large to be represented as int type");
      val = (int)(-(long long)rator->value);
    } else {
      if (rator->value > 2147483647)
        failwith("Integer literal is too large to be represented as int type");
      val = (int)(rator->value);
    }
  }
  struct enumerator_info *next = cpd_define_enum_list(rator->next, val + 1, parent, env);
  cpd_check_redef(IS_ENUMERATOR, rator->name, &env->ephemer);
  struct enumerator_info *info = define_enumerator(rator->name, val, parent, next, env);
  parent->first_rator = info;
  return info;
}

struct enum_info *cpd_define_enum(char *name, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct enum_info* info;
  WITH_CURRENT_SCOPE_ONLY(info, find_enum_by_name(name, eph), eph);
  if (info != NULL) {
    if (info->defined)
      failwith("Redefinition of type `enum %s'", name);
    info->defined = 1;
    free(name);
  } else
    info = define_enum(name, env);
  return info;
}

struct struct_union_info *cpd_declare_struct(char *name, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct struct_union_info *info;
  WITH_CURRENT_SCOPE_ONLY(info, find_struct_or_union_by_name(name, eph), eph);
  if (info != NULL) {
    if (info->t == IS_UNION)
      failwith("Use of `%s' with tag type that does not match previous declaration", name);
    free(name);
  } else
    info = declare_struct(name, env);
  return info;
}

struct struct_union_info *cpd_declare_union(char *name, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct struct_union_info *info;
  WITH_CURRENT_SCOPE_ONLY(info, find_struct_or_union_by_name(name, eph), eph);
  if (info != NULL) {
    if (info->t == IS_STRUCT)
      failwith("Use of `%s' with tag type that does not match previous declaration", name);
    free(name);
  } else
    info = declare_union(name, env);
  return info;
}

struct enum_info *cpd_declare_enum(char *name, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct enum_info* info;
  WITH_CURRENT_SCOPE_ONLY(info, find_enum_by_name(name, eph), eph);
  if (info == NULL)
    info = declare_enum(name, env);
  else
    free(name);
  return info;
}

struct struct_union_info *cpd_finalize_struct(struct struct_union_info *info) {
  if (info->defined)
    failwith("Redefinition of type `struct %s'", info->name);
  info->defined = 1;
  return info;
}

struct struct_union_info *cpd_finalize_union(struct struct_union_info *info) {
  if (info->defined)
    failwith("Redefinition of type `union %s'", info->name);
  info->defined = 1;
  return info;
}

struct logic_var_info *cpd_declare_extern(char *name,
                                          struct qvar_list *qv, struct atype *ty,
                                          struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct var_scope_union *u;
  WITH_CURRENT_SCOPE_ONLY(u, find_name_in_var_scope(name, eph), eph);
  if (u != NULL) {
    if (u->t == IS_LOGIC_VAR)
      if (atype_equal(ty, u->d.logic_var->atype)) {
        free_qvar_list(qv);
        free_atype_if_unused(ty);
        return u->d.logic_var;
      } else
        failwith("Redefinition of `%s' with a different type", name)
    else
      failwith("Redefinition of `%s' as different kind of symbol", name);
  }
  return add_extern_var(name, qv, ty, env);
}

struct atype_info *cpd_declare_extern_type(char *name, struct kind *k, struct environment *env) {
  if (find_atype_alias_by_name(name, &env->ephemer) != NULL)
    failwith("Redefinition of %s", name);
  struct atype_info *info = find_atype_by_name(name, &env->ephemer);
  if (info != NULL) {
    if (kind_equal(info->kind, k)) {
      free_kind_if_unused(k);
      return info;
    } else
      failwith("Redefinition of `%s' with a different kind", name);
  } else
    return define_atype(name, k, env);
}

struct projection_info *cpd_declare_projection(char *name,
                                               struct qvar_list *qv,
                                               struct atype *type,
                                               struct environment *env) {
  return define_projection(name, qv, type, env);
}

void cpd_declare_extern_type_alias(char *name, struct atype *type, struct environment *env) {
  if (find_atype_by_name(name, &env->ephemer) != NULL)
    failwith("Redefinition of %s", name);
  struct atype *t = find_atype_alias_by_name(name, &env->ephemer);
  if (t != NULL) {
    if (atype_equal(type, t)) {
      free_atype_if_unused(type);
      return;
    } else
      failwith("Redefinition of `%s' as a different type", name);
  } else
    define_atype_alias(name, type, &env->ephemer);
}

struct prog_var_info *cpd_define_global_var(struct type *ty, char *name, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct var_scope_union *u;
  struct prog_var_info *info;

  WITH_CURRENT_SCOPE_ONLY(u, find_name_in_var_scope(name, eph), eph);
  if (u != NULL) {
    if (u->t == IS_PROG_VAR) {
      if (!type_equal(ty, u->d.prog_var->type))
        failwith("Redefinition of `%s' with a different type", name);
      free(name);
      free_type(ty);
      info = u->d.prog_var;
    } else
      failwith("Redefinition of `%s' as different kind of symbol", name);
  } else
    info = add_global_var(name, ty, env);

  return info;
}

struct prog_var_info_list *cpd_define_param_rec(struct annot_list *param, struct environment *env) {
  if (param == NULL)
    return NULL;
  struct annot *p = param->head;
  struct prog_var_info_list *next = cpd_define_param_rec(param->tail, env);
  struct prog_var_info *info;
  if (p->name == NULL) {
    info = add_anonymous_prog_var(PROG_LOCAL, "<anonymous parameter>",
                                  type_of_pp_type(p->type->type), &env->persist);
  } else {
    cpd_check_redef(IS_PROG_VAR, p->name, &env->ephemer);
    info = add_local_var(p->name, type_of_pp_type(p->type->type), env);
    p->name = NULL;
  }
  return VILCons(info, next);
}

struct prog_var_info_list *cpd_define_param(char *func, struct annot_list *param,
                                            struct environment *env) {
  struct var_scope_union *u = NULL;
  if (func != NULL)
    u = find_prog_var_by_name(func, &env->ephemer);
  if (u != NULL) {
    struct prog_var_info_list *i;
    for (i = u->d.prog_var->func->param; i != NULL; i = i->tail) {
      struct var_scope_union *u = (struct var_scope_union *)malloc(sizeof(struct var_scope_union));
      u->t = IS_PROG_VAR;
      u->d.prog_var = i->head;
      hashtbl_add(&env->ephemer.scope->var_scope, i->head->name, u);
    }
    return u->d.prog_var->func->param;
  } else {
    return cpd_define_param_rec(param, env);
  }
}

struct ExistList *cpd_declare_atypes(struct atype_list *type, struct environment *env) {
  if (type == NULL)
    return NULL;
  struct ExistList *next = cpd_declare_atypes(type->next, env);
  struct ephemeral_env *eph = &env->ephemer;
  struct atype_info *info;
  WITH_CURRENT_SCOPE_ONLY(info, find_atype_by_name(type->name, eph), eph);
  if (info != NULL)
    failwith("Redefinition of `%s'", type->name);
  if (type->kind == NULL)
    ASSIGN_KIND(type->kind, KVar(type->name));
  info = declare_atype(type->name, type->kind, env);
  return ExistListCons(info->id, next);
}

struct ExistList *cpd_define_free(struct lvar_list *free, struct environment *env) {
  if (free == NULL)
    return NULL;
  struct ExistList *next = cpd_define_free(free->next, env);
  cpd_check_redef(IS_LOGIC_VAR, free->name, &env->ephemer);
  struct logic_var_info *info = add_free_var(free->name, free->type, env);
  return ExistListCons(info->id, next);
}

struct ExistList *cpd_declare_sep_param(struct lvar_list *p, struct environment *env) {
  if (p == NULL)
    return NULL;
  struct ExistList *next = cpd_declare_sep_param(p->next, env);
  cpd_check_redef(IS_LOGIC_VAR, p->name, &env->ephemer);
  struct logic_var_info *info = add_free_var(p->name, p->type, env);
  return ExistListCons(info->id, next);
}

int cpd_check_param(struct prog_var_info_list *t1, struct prog_var_info_list *t2) {
  if (t1 == NULL && t2 == NULL)
    return 1;
  if (t1 == NULL || t2 == NULL)
    return 0;
  return type_equal(t1->head->type, t2->head->type) && cpd_check_param(t1->tail, t2->tail);
}

int cpd_is_nameonly_spec(struct func_spec *s) {
  return s->pre == NULL;
}

#include "../SymExec/Trans/AddressabilityTrans.h"

struct func_info *cpd_define_func(struct type *ty,
                                  char *name,
                                  struct prog_var_info_list *param,
                                  struct func_spec *spec,
                                  struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct func_info *info;
  struct var_scope_union *u;
  WITH_TOP_SCOPE(eph, {u = find_name_in_var_scope(name, eph);});
  if (u != NULL) {
    if (u->t == IS_PROG_VAR && u->d.prog_var->category == PROG_FUNC) {
      info = u->d.prog_var->func;
      if (info->defined)
        failwith("Redefinition of `%s'", name);
      if (!cpd_check_param(param, info->param) ||
          !type_equal(ty, info->ret_type))
        failwith("Conflicting types for `%s'", name);
      info->defined = 1;
      free(name);
      free_type(ty);
      if (spec != NULL && !cpd_is_nameonly_spec(spec)) {
        if (spec->name) {
          struct func_spec *i;
          for (i = info->spec; i != NULL; i = i->next)
            if (i->name && strcmp(spec->name, i->name) == 0)
              failwith("Redefinition of function specs");
        }
        spec->next = info->spec;
        info->spec = spec;
      } else do {
        if (cpd_is_nameonly_spec(spec)) {
          struct func_spec **i;
          struct func_spec *focus = NULL;
          for (i = &info->spec; *i != NULL; i = &(*i)->next)
            if (string_equal((*i)->name, spec->name)) {
              focus = *i;
              *i = focus->next;
              focus->next = info->spec;
              info->spec = focus;
              break;
            }
          if (focus == NULL)
            failwith("No such function specification %s", spec->name);
        }
        if (info->spec == NULL)
          break;
        /* should I place it here? if there were a unique spec, use it. */
        struct ExistList *it, *iv;
        for (it = info->spec->witht; it != NULL; it = it->next) {
          struct atype_info *info = find_atype_by_id(it->id, &env->persist);
          hashtbl_add(&env->ephemer.scope->atype, info->name, info);
        }
        for (iv = info->spec->with; iv != NULL; iv = iv->next) {
          /* some of them are generated (not in text)
             intricate relationship with the name used */
          struct logic_var_info *info = find_logic_var_by_id(iv->id, &env->persist);
          struct var_scope_union *u;
          WITH_CURRENT_SCOPE_ONLY(u, find_name_in_var_scope(info->name, eph), eph);
          if (u == NULL) {
            u = (struct var_scope_union *)malloc(sizeof(struct var_scope_union));
            u->t = IS_LOGIC_VAR;
            u->d.logic_var = info;
            hashtbl_add(&env->ephemer.scope->var_scope, info->name, u);
          }
        }
        add_assertion("pre", ToAddressable(info->spec->pre, env), &env->ephemer);
      } while(0);
    } else
      failwith("Redefinition of `%s' as different kind of symbol", name);
  } else {
    info = define_func(name, ty, param, spec, env);
    struct type_list *ptype = NULL, **tail = &ptype;
    for (; param != NULL; param = param->tail) {
      *tail = TLCons(param->head->type, NULL);
      tail = &((*tail)->tl);
    }
    WITH_TOP_SCOPE(eph, {add_func_var(name, TFunction(ty, ptype), info, env);});
  }
  return info;
}

struct func_info *cpd_declare_func(struct type *ty,
                                   char *name,
                                   struct prog_var_info_list *param,
                                   struct func_spec *spec,
                                   struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct func_info *info;
  struct var_scope_union *u;
  WITH_CURRENT_SCOPE_ONLY(u, find_name_in_var_scope(name, eph), eph);
  if (u != NULL) {
    if (u->t == IS_PROG_VAR && u->d.prog_var->category == PROG_FUNC) {
      info = u->d.prog_var->func;
      if (!cpd_check_param(param, info->param) ||
          !type_equal(ty, info->ret_type))
        failwith("Conflicting types for `%s'", name);
      free(name);
      free_type(ty);
      if (spec != NULL) {
        spec->next = info->spec;
        info->spec = spec;
      }
    } else
      failwith("Redefinition of `%s' as different kind of symbol", name);
  } else {
    info = declare_func(name, ty, param, spec, env);
    struct type_list *ptype = NULL, **tail = &ptype;
    for (; param != NULL; param = param->tail) {
      *tail = TLCons(param->head->type, NULL);
      tail = &((*tail)->tl);
    }
    add_func_var(name, TFunction(ty, ptype), info, env);
  }
  return info;
}

struct atype *cpd_build_sep_type(struct ExistList *param, struct persistent_env *env) {
  if (param == NULL)
    return ATAssertion(env);
  struct logic_var_info *info = find_logic_var_by_id(param->id, env);
  return ATArrow(info->atype, cpd_build_sep_type(param->next, env));
}

struct sepdef_info *cpd_define_sep(char *name, struct ExistList *param, struct environment *env) {
  struct sepdef_info *info;
  WITH_TOP_SCOPE(&env->ephemer,{
      cpd_check_redef(IS_LOGIC_VAR, name, &env->ephemer);
      info = declare_sep(name, param, env);
      add_sepdef_var(info->name, cpd_build_sep_type(param, &env->persist), info, env);
    });
  return info;
}

struct sepdef_info *cpd_finalize_sep(struct sepdef_info *info,
                                     struct qvar_list *qv, struct AsrtList *cond) {
  info->var->qv = qv;
  info->defined = 1;
  info->condition = cond;
  return info;
}

struct prog_var_info *cpd_define_local(char *name, struct type *type, struct environment *env) {
  cpd_check_redef(IS_PROG_VAR, name, &env->ephemer);
  return add_local_var(name, type, env);
}

struct type_info *cpd_define_type(char *name, struct type *type, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct type_info *info;
  struct var_scope_union *u;
  WITH_CURRENT_SCOPE_ONLY(u, find_name_in_var_scope(name, eph), eph);
  if (u != NULL) {
    if (u->t == IS_TYPE) {
      info = u->d.type;
      if (!type_equal(type, info->type))
        failwith("Typedef redefinition with different types");
      free(name);
      free_type(type);
    } else
      failwith("Redefinition of `%s' as different kind of symbol", name);
  } else
    info = define_type(name, type, env);
  return info;
}
