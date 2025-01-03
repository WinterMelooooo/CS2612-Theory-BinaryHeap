#include "utils.h"
#include "env.h"

unsigned int fresh(struct persistent_env *env) {
  env->next_fresh += 1;
  return env->next_fresh - 1;
}

struct atype *ATZ(struct persistent_env *env) {
  return ATAtom(find_atype_by_id(BUILTINTYPE_Z, env));
}

struct atype *ATList(struct persistent_env *env) {
  return ATAtom(find_atype_by_id(BUILTINTYPE_LIST, env));
}

struct atype *ATProd(struct persistent_env *env) {
  return ATAtom(find_atype_by_id(BUILTINTYPE_PROD, env));
}

struct atype *ATAssertion(struct persistent_env *env) {
  return ATAtom(find_atype_by_id(BUILTINTYPE_ASSERTION, env));
}

struct atype *ATProp(struct persistent_env *env) {
  return ATAtom(find_atype_by_id(BUILTINTYPE_PROP, env));
}

void init_env(struct environment *env) {
  init_hashtbl(&env->persist.prog_var, hash_uint, uint_equal);
  init_hashtbl(&env->persist.logic_var, hash_uint, uint_equal);
  init_hashtbl(&env->persist.type, hash_uint, uint_equal);
  init_hashtbl(&env->persist.func, hash_uint, uint_equal);
  init_hashtbl(&env->persist.structs, hash_uint, uint_equal);
  init_hashtbl(&env->persist.unions, hash_uint, uint_equal);
  init_hashtbl(&env->persist.enums, hash_uint, uint_equal);
  init_hashtbl(&env->persist.enumerator, hash_uint, uint_equal);
  init_hashtbl(&env->persist.field, hash_uint, uint_equal);
  init_hashtbl(&env->persist.sepdef, hash_uint, uint_equal);
  init_hashtbl(&env->persist.atype, hash_uint, uint_equal);
  init_hashtbl(&env->persist.twin, hash_ptr, ptr_equal);
  init_hashtbl(&env->persist.projection, hash_ptr, ptr_equal);
  env->persist.modules = NULL;
  env->persist.next_fresh = 1; // 0 is reserved

  env->ephemer.scope = NULL;
  env->ephemer.flow = NULL;
  scope_env_deep(&env->ephemer);

  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_TOP;
  s->outer = NULL;
  env->context.c = s;

  // remember to update the enums!!
  define_atype("Z", KStar(), env);
  define_atype("nat", KStar(), env);
  define_atype("bool", KStar(), env);
  define_atype("list", KArrow(KStar(), KStar()), env);
  define_atype("prod", KArrow(KStar(), KArrow(KStar(), KStar())), env);
  define_atype("Prop", KStar(), env);
  define_atype("Assertion", KStar(), env);

  add_extern_var("INT_MAX", NULL, ATZ(&env->persist), env);
  add_extern_var("INT_MIN", NULL, ATZ(&env->persist), env);
  add_extern_var("Z.pow", NULL, ATArrow(ATZ(&env->persist), ATArrow(ATZ(&env->persist), ATZ(&env->persist))), env);
  add_extern_var("unsigned_last_nbits", NULL, ATArrow(ATZ(&env->persist), ATArrow(ATZ(&env->persist), ATZ(&env->persist))), env);
  add_extern_var("signed_last_nbits", NULL, ATArrow(ATZ(&env->persist), ATArrow(ATZ(&env->persist), ATZ(&env->persist))), env);
}

void context_deep_func(struct func_info *info, struct context *ctx) {
  info->body = NULL;
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_FUNC;
  s->d.FUNC.info = info;
  s->d.FUNC.tail = &info->body;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_hole(struct cmd *c, struct cmd **hole, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_HOLE;
  s->d.HOLE.c = c;
  s->d.HOLE.hole = hole;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_then(struct cmd *c, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_THEN;
  s->d.THEN.c = c;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_dowhile(struct cmd *c, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_DOWHILE;
  s->d.DOWHILE.c = c;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_switch(struct cmd *c, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_SWITCH;
  s->d.SWITCH.c = c;
  s->d.SWITCH.tail = &c->d.SWITCH.body;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_case(struct Case *c, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_CASE;
  s->d.CASE.c = c;
  if (c->t == T_CASE)
    s->d.CASE.tail = &c->d.CASE.body;
  else
    s->d.CASE.tail = &c->d.DEFAULT.body;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_inv(struct AsrtList *assert, int partial, struct StringList * scopes, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_INV;
  s->d.INV.inv = assert;
  s->d.INV.partial = partial;
  s->d.INV.scopes = scopes;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_block(struct cmd *c, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_BLOCK;
  s->d.BLOCK.c = c;
  s->d.BLOCK.tail = &c->d.BLOCK.cmd;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_after_then(struct cmd *c, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_AFTER_THEN;
  s->d.AFTER_THEN.c = c;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_before_while(struct cmd *c, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_BEFORE_WHILE;
  s->d.BEFORE_WHILE.c = c;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_after_while(struct cmd *c, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_AFTER_WHILE;
  s->d.AFTER_WHILE.c = c;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_deep_decl(struct pp_type *base, int is_typedef, struct context *ctx) {
  struct context_stack *s = (struct context_stack *)malloc(sizeof(struct context_stack));
  s->t = CTX_DECL;
  s->d.DECL.base = base;
  s->d.DECL.is_typedef = is_typedef;
  s->outer = ctx->c;
  ctx->c = s;
}

void context_up(struct context *ctx) {
  struct context_stack *s = ctx->c;
  ctx->c = s->outer;
  free(s);
}

void scope_env_deep(struct ephemeral_env *env) {
  struct scope_env *se = (struct scope_env *)malloc(sizeof(struct scope_env));
  init_hashtbl(&se->var_scope, hash_string, string_equal);
  init_hashtbl(&se->struct_union, hash_string, string_equal);
  init_hashtbl(&se->field, hash_string, string_equal);
  init_hashtbl(&se->enums, hash_string, string_equal);
  init_hashtbl(&se->atype, hash_string, string_equal);
  init_hashtbl(&se->atype_alias, hash_string, string_equal);
  init_hashtbl(&se->projection, hash_string, string_equal);
  se->outer = env->scope;
  env->scope = se;
}

void clean_wrapper(void *name, void *wr) {
  (void) name;
  free(wr);
}

void clean_type_ref(void *name, void *type) {
  free(name);
  struct atype *t = type;
  free_atype(t);
}

void scope_env_up(struct ephemeral_env *env) {
  struct scope_env *se = env->scope;
  env->scope = se->outer;
  hashtbl_iter(&se->var_scope, clean_wrapper);
  hashtbl_iter(&se->atype_alias, clean_type_ref);
  hashtbl_clear(&se->var_scope);
  hashtbl_clear(&se->struct_union);
  hashtbl_clear(&se->field);
  hashtbl_clear(&se->enums);
  hashtbl_clear(&se->atype);
  hashtbl_clear(&se->atype_alias);
  hashtbl_clear(&se->projection);
  free(se);
}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wint-to-pointer-cast"

#define ITER_ON_SCOPE(type, map)                        \
  {                                                     \
    struct scope_env *se;                               \
    struct type *res;                                   \
    int v;                                              \
    for (se = env->scope; se != NULL; se = se->outer) { \
      res = hashtbl_find(&se->map, name, &v);           \
      if (v)                                            \
        return res;                                     \
    }                                                   \
    return NULL;                                        \
  }

struct var_scope_union *find_name_in_var_scope(char *name, struct ephemeral_env *env) {
  ITER_ON_SCOPE(var_scope_union, var_scope);
}

#define FIND_IN_VAR_SCOPE(cond, s)                                      \
  {                                                                     \
    int v;                                                              \
    struct scope_env *i;                                                \
    for (i = s; i != NULL; i = i->outer) {                              \
      struct var_scope_union *u = hashtbl_find(&i->var_scope, name, &v); \
      if (u != NULL) {                                                  \
        enum var_scope_union_type t = u->t;                             \
        if (cond)                                                       \
          return u;                                                     \
      }                                                                 \
    }                                                                   \
    return NULL;                                                        \
 }

struct var_scope_union *find_prog_var_by_name(char *name, struct ephemeral_env *env) {
  FIND_IN_VAR_SCOPE(t == IS_PROG_VAR, env->scope);
}

struct var_scope_union *find_logic_var_by_name(char *name, struct ephemeral_env *env) {
  FIND_IN_VAR_SCOPE(t == IS_LOGIC_VAR, env->scope);
}

struct var_scope_union *find_var_like_by_name(char *name, struct ephemeral_env *env) {
  FIND_IN_VAR_SCOPE(t == IS_PROG_VAR || t == IS_LOGIC_VAR || t == IS_ENUMERATOR, env->scope);
}

struct var_scope_union *find_prog_var_like_by_name(char *name, struct ephemeral_env *env) {
  FIND_IN_VAR_SCOPE(t == IS_PROG_VAR || t == IS_ENUMERATOR, env->scope);
}

struct var_scope_union *find_type_by_name(char *name, struct ephemeral_env *env) {
  FIND_IN_VAR_SCOPE(t == IS_TYPE, env->scope);
}

struct prog_var_info *find_prog_var_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->prog_var, (void *)id, &v);
}

struct logic_var_info *find_logic_var_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->logic_var, (void *)id, &v);
}

struct prog_var_info *add_prog_var_common(enum prog_var_category cat,
                                          char *name, struct type *type,
                                          struct environment *env) {
  struct prog_var_info *info = (struct prog_var_info *)malloc(sizeof(struct prog_var_info));
  struct ephemeral_env *eph = &env->ephemer;
  struct persistent_env *per = &env->persist;

  info->category = cat;
  info->id = fresh(per);
  info->name = name;
  ASSIGN_TYPE(info->type, type);
  info->value = add_anonymous_logic_var(LOGIC_FREE, embed_str("%s", name), per);
  info->value->renaming = renaming_info_var_pre_value(name);
  info->value->value_or_address = info;
  info->address = add_anonymous_logic_var(LOGIC_FREE, embed_str("%s_p", name), per);
  info->address->renaming = renaming_info_var_addr(name);
  info->address->value_or_address = info;
  ASSIGN_ATYPE(info->value->atype, ATZ(per));
  ASSIGN_ATYPE(info->address->atype, ATZ(per));
  info->value->qv = NULL;
  info->address->qv = NULL;
  struct var_scope_union *u = find_prog_var_by_name(name, eph);
  if (u != NULL)
    info->shadowing = u->d.prog_var;
  else
    info->shadowing = NULL;

  u = (struct var_scope_union *)malloc(sizeof(struct var_scope_union));
  u->t = IS_PROG_VAR;
  u->d.prog_var = info;

  hashtbl_add(&eph->scope->var_scope, name, u);
  hashtbl_add(&per->prog_var, (void *)info->id, info);

  return info;
}

struct logic_var_info *add_logic_var_common(enum logic_var_category cat,
                                            char *name,
                                            struct qvar_list *qv, struct atype *type,
                                            struct renaming_info *r,
                                            struct environment *env) {
  struct logic_var_info *info = (struct logic_var_info *)malloc(sizeof(struct logic_var_info));
  struct ephemeral_env *eph = &env->ephemer;
  struct persistent_env *per = &env->persist;

  info->category = cat;
  info->id = fresh(per);
  info->name = name;
  info->renaming = r;
  info->qv = qv;
  info->value_or_address = NULL;
  ASSIGN_ATYPE(info->atype, type);

  struct var_scope_union *u = (struct var_scope_union *)malloc(sizeof(struct var_scope_union));
  u->t = IS_LOGIC_VAR;
  u->d.logic_var = info;

  hashtbl_add(&eph->scope->var_scope, name, u);
  hashtbl_add(&per->logic_var, (void *)info->id, info);

  return info;
}

struct prog_var_info *add_local_var(char *name, struct type *ty, struct environment *env) {
  return add_prog_var_common(PROG_LOCAL, name, ty, env);
}

struct prog_var_info *add_global_var(char *name, struct type *ty, struct environment *env) {
  return add_prog_var_common(PROG_GLOBAL, name, ty, env);
}

struct prog_var_info *add_func_var(char *name, struct type *ty, struct func_info *def,
                                   struct environment *env) {
  struct prog_var_info *info = add_prog_var_common(PROG_FUNC, name, ty, env);
  info->func = def;
  def->var = info;
  return info;
}

struct logic_var_info *add_free_var(char *name, struct atype *ty, struct environment *env) {
  return add_logic_var_common(LOGIC_FREE, name, NULL, ty, renaming_info_free_var(name), env);
}

struct logic_var_info *add_exists_var(char *name,
                                      struct qvar_list *qv, struct atype *ty,
                                      struct environment *env) {
  return add_logic_var_common(LOGIC_USER_EXISTS, name, qv, ty, renaming_info_exists_var(name, 0, 0), env);
}

struct logic_var_info *add_forall_var(char *name,
                                      struct qvar_list *qv, struct atype *ty,
                                      struct environment *env) {
  return add_logic_var_common(LOGIC_FORALL, name, qv, ty, renaming_info_forall_var(name, 0, 0), env);
}

struct logic_var_info *add_extern_var(char *name,
                                      struct qvar_list *qv, struct atype *ty,
                                      struct environment *env) {
  return add_logic_var_common(LOGIC_EXTERN, name, qv, ty, renaming_info_free_var(name), env);
}

struct logic_var_info *add_sepdef_var(char *name, struct atype *ty, struct sepdef_info *def, struct environment *env) {
  struct logic_var_info *info = add_logic_var_common(LOGIC_SEPDEF, name, NULL, ty,
                                                     renaming_info_free_var(name), env);
  info->sep = def;
  def->var = info;
  return info;
}

struct prog_var_info *add_anonymous_prog_var(enum prog_var_category cat, char *pp_name, struct type *type,
                                             struct persistent_env *env) {
  struct prog_var_info *info = (struct prog_var_info *)malloc(sizeof(struct prog_var_info));
  info->category = cat;
  info->id = fresh(env);
  info->name = pp_name;
  ASSIGN_TYPE(info->type, type);
  info->value = add_anonymous_logic_var(LOGIC_FREE, embed_str("%s", pp_name), env);
  info->value->renaming = renaming_info_var_pre_value(pp_name);
  info->value->value_or_address = info;
  info->address = add_anonymous_logic_var(LOGIC_FREE, embed_str("%s_p", pp_name), env);
  info->address->renaming = renaming_info_var_addr(pp_name);
  info->address->value_or_address = info;
  ASSIGN_ATYPE(info->value->atype, ATZ(env));
  ASSIGN_ATYPE(info->address->atype, ATZ(env));
  info->value->qv = NULL;
  info->address->qv = NULL;
  hashtbl_add(&env->prog_var, (void *)info->id, info);
  return info;
}

struct logic_var_info *add_anonymous_logic_var(enum logic_var_category cat, char *pp_name,
                                               struct persistent_env *env) {
  struct logic_var_info *info = (struct logic_var_info *)malloc(sizeof(struct logic_var_info));
  info->category = cat;
  info->id = fresh(env);
  info->name = pp_name;
  info->renaming = NULL;
  info->qv = NULL;
  info->value_or_address = NULL;
  hashtbl_add(&env->logic_var, (void *)info->id, info);
  return info;
}

struct logic_var_info * add_anonymous_var_with_id(enum logic_var_category cat,
                                                  char *pp_name, unsigned int id,
                                                  struct persistent_env *env) {
  struct logic_var_info *info = (struct logic_var_info *)malloc(sizeof(struct logic_var_info));
  info->category = cat;
  info->id = id;
  info->name = pp_name;
  info->renaming = NULL;
  info->qv = NULL;
  info->value_or_address = NULL;
  hashtbl_add(&env->logic_var, (void *)info->id, info);
  return info;
}

void remove_var_by_name(char *name, struct ephemeral_env *env) {
  struct scope_env *se;
  int r;
  for (se = env->scope; se != NULL; se = se->outer) {
    void *wr = hashtbl_remove(&se->var_scope, name, &r);
    if (r) {
      free(wr);
      return;
    }
  }
}

void remove_logic_var_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  struct logic_var_info *info = hashtbl_find(&env->logic_var, cast_int(id), &v);
  if (v) {
    free(info->name);
    free_qvar_list(info->qv);
    if (info->atype != NULL)
      free_atype(info->atype);
    free(info);
    hashtbl_remove(&env->logic_var, cast_int(id), &v);
  }
}

struct type_info *define_type(char *name, struct type *type, struct environment *env) {
  struct persistent_env *per = &env->persist;
  struct type_info *info = (struct type_info *)malloc(sizeof(struct type_info));
  info->name = name;
  info->id = fresh(per);
  ASSIGN_TYPE(info->type, type);

  struct var_scope_union *u = (struct var_scope_union *)malloc(sizeof(struct var_scope_union));
  u->t = IS_TYPE;
  u->d.type = info;

  hashtbl_add(&env->ephemer.scope->var_scope, name, u);
  hashtbl_add(&per->type, (void *)info->id, info);
  return info;
}

struct type_info *find_type_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->type, (void *)id, &v);
}

void flow_env_deep(struct ephemeral_env *env) {
  struct flow_env *fe = (struct flow_env *)malloc(sizeof(struct flow_env));
  init_hashtbl(&fe->assertion, hash_string, string_equal);
  fe->outer = env->flow;
  env->flow = fe;
}

void flow_env_up(struct ephemeral_env *env) {
  struct flow_env *fe;
  fe = env->flow;
  env->flow = fe->outer;
  hashtbl_clear(&fe->assertion);
  free(fe);
}

struct AsrtList *find_assertion(char *name, struct ephemeral_env *env) {
  struct flow_env *fe;
  struct AsrtList *res;
  int v;
  for (fe = env->flow; fe != NULL; fe = fe->outer) {
    res = hashtbl_find(&fe->assertion, name, &v);
    if (v)
      return res;
  }
  return NULL;
}

void add_assertion(char *name, struct AsrtList *a, struct ephemeral_env *env) {
  hashtbl_add(&env->flow->assertion, name, a);
}

struct struct_union_info *de_struct_union_common(char *name, struct persistent_env *env) {
  struct struct_union_info *info = (struct struct_union_info *)malloc(sizeof(struct struct_union_info));
  info->id = fresh(env);
  info->name = name;
  return info;
}

struct struct_union_info *define_struct(char *name, struct environment *env) {
  struct struct_union_info *info = de_struct_union_common(name, &env->persist);
  info->t = IS_STRUCT;
  info->defined = 1;
  hashtbl_add(&env->ephemer.scope->struct_union, name, info);
  hashtbl_add(&env->persist.structs, (void *)info->id, info);
  return info;
}

struct struct_union_info *declare_struct(char *name, struct environment *env) {
  struct struct_union_info *info = de_struct_union_common(name, &env->persist);
  info->t = IS_STRUCT;
  info->defined = 0;
  hashtbl_add(&env->ephemer.scope->struct_union, name, info);
  hashtbl_add(&env->persist.structs, (void *)info->id, info);
  return info;
}

struct struct_union_info *define_anonymous_struct(char *pp_name, struct persistent_env *env) {
  struct struct_union_info *info = de_struct_union_common(pp_name, env);
  info->t = IS_STRUCT;
  info->defined = 1;
  hashtbl_add(&env->structs, (void *)info->id, info);
  return info;
}

struct struct_union_info *define_union(char *name, struct environment *env) {
  struct struct_union_info *info = de_struct_union_common(name, &env->persist);
  info->t = IS_UNION;
  info->defined = 1;
  hashtbl_add(&env->ephemer.scope->struct_union, name, info);
  hashtbl_add(&env->persist.unions, (void *)info->id, info);
  return info;
}

struct struct_union_info *declare_union(char *name, struct environment *env) {
  struct struct_union_info *info = de_struct_union_common(name, &env->persist);
  info->t = IS_UNION;
  info->defined = 0;
  hashtbl_add(&env->ephemer.scope->struct_union, name, info);
  hashtbl_add(&env->persist.unions, (void *)info->id, info);
  return info;
}

struct struct_union_info *define_anonymous_union(char *pp_name, struct persistent_env *env) {
  struct struct_union_info *info = de_struct_union_common(pp_name, env);
  info->t = IS_UNION;
  info->defined = 1;
  hashtbl_add(&env->unions, (void *)info->id, info);
  return info;
}

struct struct_union_info *find_struct_or_union_by_name(char *name, struct ephemeral_env *env) {
  ITER_ON_SCOPE(struct_union_info, struct_union);
}

struct struct_union_info *find_struct_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->structs, (void *)id, &v);
}

struct struct_union_info *find_union_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->unions, (void *)id, &v);
}


struct field_info *define_field(char *name, struct type *type, struct struct_union_info *parent, struct field_info *next, struct environment *env) {
  struct ephemeral_env *eph = &env->ephemer;
  struct persistent_env *per = &env->persist;
  struct field_info *info = (struct field_info *)malloc(sizeof(struct field_info));
  info->id = fresh(per);
  info->another = find_field_by_name(name, eph);
  info->name = name;
  ASSIGN_TYPE(info->type, type);
  info->parent = parent;
  info->next = next;
  hashtbl_add(&eph->scope->field, name, info);
  hashtbl_add(&per->field, (void *)info->id, info);
  return info;
}

struct field_info *find_field_by_name(char *name, struct ephemeral_env *env) {
  ITER_ON_SCOPE(field_info, field);
}

struct field_info *find_field_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->field, (void *)id, &v);
}

struct enum_info *de_enum_common(char *name, struct persistent_env *env) {
  struct enum_info *info = (struct enum_info *)malloc(sizeof(struct enum_info));
  info->id = fresh(env);
  info->name = name;
  hashtbl_add(&env->enums, (void *)info->id, info);
  return info;
}

struct enum_info *define_enum(char *name, struct environment *env) {
  struct enum_info *info = de_enum_common(name, &env->persist);
  info->defined = 1;
  hashtbl_add(&env->ephemer.scope->enums, name, info);
  return info;
}

struct enum_info *define_anonoymous_enum(char *pp_name, struct persistent_env *env) {
  struct enum_info *info = de_enum_common(pp_name, env);
  info->defined = 1;
  return info;
}

struct enum_info *declare_enum(char *name, struct environment *env) {
  struct enum_info *info = de_enum_common(name, &env->persist);
  info->defined = 0;
  hashtbl_add(&env->ephemer.scope->enums, name, info);
  return info;
}

struct enum_info *find_enum_by_name(char *name, struct ephemeral_env *env) {
  ITER_ON_SCOPE(enum_info, enums);
}

struct enum_info *find_enum_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->enums, (void *)id, &v);
}

struct atype_info *de_atype_common(char *name, struct kind *k, struct environment *env) {
  struct atype_info *info = (struct atype_info *)malloc(sizeof(struct atype_info));
  info->id = fresh(&env->persist);
  info->name = name;
  ASSIGN_KIND(info->kind, k);
  hashtbl_add(&env->ephemer.scope->atype, name, info);
  hashtbl_add(&env->persist.atype, (void *)info->id, info);
  return info;
}

struct atype_info *define_atype(char *name, struct kind *k, struct environment *env) {
  struct atype_info *info = de_atype_common(name, k, env);
  info->defined = 1;
  return info;
}

struct atype_info *declare_atype(char *name, struct kind *k, struct environment *env) {
  struct atype_info *info = de_atype_common(name, k, env);
  info->defined = 0;
  return info;
}

struct atype_info *find_atype_by_name(char *name, struct ephemeral_env *env) {
  ITER_ON_SCOPE(atype_info, atype);
}

struct atype_info *find_atype_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->atype, (void *)id, &v);
}

void define_atype_alias(char *name, struct atype *type, struct ephemeral_env *env) {
  type->refcnt += 1;
  hashtbl_add(&env->scope->atype_alias, name, type);
}

struct atype *find_atype_alias_by_name(char *name, struct ephemeral_env *env) {
  ITER_ON_SCOPE(atype, atype_alias);
}

struct sepdef_info *declare_sep(char *name, struct ExistList *param, struct environment *env) {
  struct persistent_env *per = &env->persist;
  struct sepdef_info *info = (struct sepdef_info *)malloc(sizeof(struct sepdef_info));
  info->defined = 0;
  info->id = fresh(per);
  info->param = param;
  info->name = name;

  hashtbl_add(&per->sepdef, (void *)info->id, info);
  return info;
}

struct sepdef_info *define_sep(char *name, struct ExistList *param, struct AsrtList *assert, struct environment *env) {
  struct sepdef_info *info = declare_sep(name, param, env);
  info->defined = 1;
  info->condition = assert;
  return info;
}

struct sepdef_info *find_sep_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->sepdef, (void *)id, &v);
}

struct enumerator_info *define_enumerator(char *name, int val, struct enum_info *parent, struct enumerator_info *next, struct environment *env) {
  struct persistent_env *per = &env->persist;
  struct enumerator_info *info = (struct enumerator_info *)malloc(sizeof(struct enumerator_info));
  info->id = fresh(per);
  info->name = name;
  info->repr = val;
  info->parent = parent;
  info->next = next;

  struct var_scope_union *u = (struct var_scope_union *)malloc(sizeof(struct var_scope_union));
  u->t = IS_ENUMERATOR;
  u->d.enumerator = info;

  hashtbl_add(&env->ephemer.scope->var_scope, name, u);
  hashtbl_add(&per->enumerator, (void *)info->id, info);
  return info;
}

struct enumerator_info *find_enumerator_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->enumerator, (void *)id, &v);
}

struct projection_info *define_projection(char *name,
                                          struct qvar_list *qv,
                                          struct atype *type,
                                          struct environment *env) {
  struct projection_info *info =
    (struct projection_info *)malloc(sizeof(struct projection_info));
  info->id = fresh(&env->persist);
  info->name = name;
  info->qv = qv;
  info->next = find_projection_by_name(name, &env->ephemer);
  hashtbl_add(&env->ephemer.scope->projection, name, info);
  hashtbl_add(&env->persist.projection, (void *)info->id, info);
  info->var = add_anonymous_logic_var(LOGIC_PROJ, clone_str(name), &env->persist);
  info->var->qv = clone_qvar_list(qv);
  ASSIGN_ATYPE(info->var->atype, type);
  return info;
}

struct projection_info *find_projection_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->projection, (void *)id, &v);
}

struct projection_info *find_projection_by_name(char *name, struct ephemeral_env *env) {
  ITER_ON_SCOPE(projection_info, projection);
}

struct func_info *de_func_common(char *name,
                                 int defined,
                                 struct type *ty,
                                 struct prog_var_info_list *param,
                                 struct func_spec *spec,
                                 struct persistent_env *env) {
  struct func_info *info = (struct func_info *)malloc(sizeof(struct func_info));
  info->defined = defined;
  info->id = fresh(env);
  ASSIGN_TYPE(info->ret_type, ty);
  info->name = name;
  info->param = param;
  info->spec = spec;
  if (spec != NULL)
    spec->next = NULL;
  hashtbl_add(&env->func, (void *)info->id, info);
  return info;
}

struct func_info *define_func(char *name,
                              struct type *ty,
                              struct prog_var_info_list *param,
                              struct func_spec *spec,
                              struct environment *env) {
  return de_func_common(name, 1, ty, param, spec, &env->persist);
}

struct func_info *declare_func(char *name,
                               struct type *ty,
                               struct prog_var_info_list *param,
                               struct func_spec *spec,
                               struct environment *env) {
  struct func_info *info = de_func_common(name, 0, ty, param, spec, &env->persist);
  info->body = NULL;
  return info;
}

struct func_info *define_anonymous_func(char *pp_name,
                                       struct type *ty,
                                       struct prog_var_info_list *param,
                                       struct func_spec *spec,
                                       struct persistent_env *env) {
  struct func_info *info = de_func_common(pp_name, 0, ty, param, spec, env);
  info->body = NULL;
  return info;
}

void add_coq_module(char *command, struct persistent_env *env) {
  struct coq_module_list *list = (struct coq_module_list *)malloc(sizeof(struct coq_module_list));
  list->command = command;
  list->next = env->modules;
  env->modules = list;
}

struct coq_module_list *reverse_coq_module(struct coq_module_list *list) {
  struct coq_module_list *res = NULL;
  struct coq_module_list *i = list;
  while (i != NULL) {
    struct coq_module_list *next = i->next;
    i->next = res;
    res = i;
    i = next;
  }
  return res;
}

void dump_coq_module(struct persistent_env *env, FILE *fp) {
  struct coq_module_list *i;
  for (i = env->modules; i != NULL; i = i->next) {
    if (fp != NULL) {
      fprintf(fp, "%s.\n", i->command);
    }
  }
}

struct prog_var_info_list *VILNil() {
  return NULL;
}
struct prog_var_info_list *VILCons(struct prog_var_info *head, struct prog_var_info_list *tail) {
  struct prog_var_info_list *res = (struct prog_var_info_list *)malloc(sizeof(struct prog_var_info_list));
  res->head = head;
  res->tail = tail;
  return res;
}

struct func_info *find_func_by_id(unsigned int id, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->func, (void *)id, &v);
}

struct func_spec *find_func_spec(struct func_info *f, char *name) {
  if (f == NULL)
    return NULL;
  struct func_spec *i;
  for (i = f->spec; i != NULL; i = i->next)
    if (strcmp(i->name, name) == 0)
      return i;
  return NULL;
}

void add_twin_assertion(struct AsrtList *post, struct AsrtList *pre,
                        struct persistent_env *env) {
  hashtbl_add(&env->twin, post, pre);
  hashtbl_add(&env->twin, pre, post);
}

void delete_twin_assertion(struct AsrtList * asrt, struct persistent_env *env) {
  struct AsrtList *twin = find_twin_assertion(asrt, env);
  if (twin != NULL) {
    int removed;
    hashtbl_remove(&env->twin, asrt, &removed);
    hashtbl_remove(&env->twin, twin, &removed);
  }
}

struct AsrtList *find_twin_assertion(struct AsrtList *a, struct persistent_env *env) {
  int v;
  return hashtbl_find(&env->twin, a, &v);
}

#undef ITER_ON_SCOPE

void free_prog_var_info(struct prog_var_info *info) {
  free(info->name);
  free_type(info->type);
  free(info);
}

void free_prog_var_info_list(struct prog_var_info_list *il) {
  if (il == NULL)
    return;
  free_prog_var_info(il->head);
  struct prog_var_info_list *tl = il->tail;
  free(il);
  free_prog_var_info_list(tl);
}

#pragma GCC diagnostic pop
