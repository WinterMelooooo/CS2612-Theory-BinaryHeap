#ifndef ENV_H
#define ENV_H

#include "lang.h"
#include "alang.h"
#include "hashtbl.h"
#include "renaming.h"

enum context_type {
  CTX_TOP,
  CTX_FUNC,
  CTX_THEN,
  CTX_AFTER_THEN,
  CTX_HOLE,
  CTX_DOWHILE,
  CTX_BEFORE_WHILE,
  CTX_AFTER_WHILE,
  CTX_SWITCH,
  CTX_CASE,
  CTX_BLOCK,
  CTX_INV,
  CTX_DECL
};

struct context_stack {
  enum context_type t;
  struct context_stack *outer;
  union {
    struct { } TOP;
    struct { struct func_info *info; struct cmd **tail; } FUNC;
    struct { struct cmd *c; } THEN;
    struct { struct cmd *c; } AFTER_THEN;
    struct { struct cmd *c; } DOWHILE;
    struct { struct cmd *c; } BEFORE_WHILE; /* do ... | while () ; */
    struct { struct cmd *c; } AFTER_WHILE;  /* do ... while () | ; */
    struct { struct cmd *c; struct cmd **hole; } HOLE; /* while, else, for waiting for body */
    struct { struct cmd *c; struct Case_list **tail; } SWITCH;
    struct { struct Case *c; struct cmd **tail; } CASE;
    struct { struct cmd *c; struct cmd **tail; } BLOCK;
    struct { struct AsrtList *inv; int partial; struct StringList * scopes; } INV;
    struct { struct pp_type *base; int is_typedef; } DECL;
  } d;
};

struct context { struct context_stack *c; };

struct prog_var_info_list {
  struct prog_var_info *head;
  struct prog_var_info_list *tail;
};

enum var_scope_union_type { IS_PROG_VAR, IS_LOGIC_VAR, IS_TYPE, IS_ENUMERATOR };

struct var_scope_union {
  enum var_scope_union_type t;
  union {
    struct prog_var_info *prog_var;
    struct logic_var_info *logic_var;
    struct type_info *type;
    struct enumerator_info *enumerator;
  } d;
};

struct scope_env {
  struct hashtbl var_scope;
  struct hashtbl struct_union;
  struct hashtbl enums;
  struct hashtbl field;
  struct hashtbl atype;
  struct hashtbl atype_alias;
  struct hashtbl projection;
  struct scope_env *outer;
};

struct flow_env {
  struct hashtbl assertion;
  struct flow_env *outer;
};

struct ephemeral_env {
  struct scope_env *scope;
  struct flow_env *flow;
};

struct coq_module_list {
  char *command;
  struct coq_module_list *next;
};

struct persistent_env {
  struct hashtbl prog_var;
  struct hashtbl logic_var;
  struct hashtbl type;
  struct hashtbl func;
  struct hashtbl structs;
  struct hashtbl unions;
  struct hashtbl enums;
  struct hashtbl enumerator;
  struct hashtbl field;
  struct hashtbl sepdef;
  struct hashtbl atype;
  struct hashtbl twin;
  struct hashtbl projection;
  unsigned int next_fresh;
  struct coq_module_list *modules;
};

struct environment {
  struct context context;
  struct ephemeral_env ephemer;
  struct persistent_env persist;
};

void init_env(struct environment *env);

void context_deep_func(struct func_info *info, struct context *ctx);
void context_deep_hole(struct cmd *c, struct cmd **hole, struct context *ctx);
void context_deep_then(struct cmd *c, struct context *ctx);
void context_deep_dowhile(struct cmd *c, struct context *ctx);
void context_deep_switch(struct cmd *c, struct context *ctx);
void context_deep_case(struct Case *c, struct context *ctx);
void context_deep_inv(struct AsrtList *ra, int partial, struct StringList * scopes, struct context *ctx);
void context_deep_block(struct cmd *c, struct context *ctx);
void context_deep_after_then(struct cmd *c, struct context *ctx);
void context_deep_before_while(struct cmd *c, struct context *ctx);
void context_deep_after_while(struct cmd *c, struct context *ctx);
void context_deep_decl(struct pp_type *base, int is_typedef, struct context *ctx);
void context_up(struct context *ctx);

void scope_env_deep(struct ephemeral_env *env);
void scope_env_up(struct ephemeral_env *env);

/* the following do not check anything (improper shadowing, improper context, etc.) */

struct var_scope_union *find_name_in_var_scope(char *name, struct ephemeral_env *env);

struct var_scope_union *find_prog_var_by_name(char *name, struct ephemeral_env *env);
struct var_scope_union *find_logic_var_by_name(char *name, struct ephemeral_env *env);
struct var_scope_union *find_var_like_by_name(char *name, struct ephemeral_env *env);
struct var_scope_union *find_prog_var_like_by_name(char *name, struct ephemeral_env *env);
struct var_scope_union *find_type_by_name(char *name, struct ephemeral_env *env);

struct prog_var_info *find_prog_var_by_id(unsigned int id, struct persistent_env *env);
struct logic_var_info *find_logic_var_by_id(unsigned int id, struct persistent_env *env);

struct prog_var_info *add_local_var(char *name, struct type *ty, struct environment *env);
struct prog_var_info *add_global_var(char *name, struct type *ty, struct environment *env);
struct prog_var_info *add_func_var(char *name, struct type *ty, struct func_info *def, struct environment *env);
struct logic_var_info *add_free_var(char *name, struct atype *ty, struct environment *env);
struct logic_var_info *add_exists_var(char *name, struct qvar_list *qv, struct atype *ty, struct environment *env);
struct logic_var_info *add_forall_var(char *name, struct qvar_list *qv, struct atype *ty, struct environment *env);
struct logic_var_info *add_extern_var(char *name, struct qvar_list *qv, struct atype *ty, struct environment *env);
struct logic_var_info *add_sepdef_var(char *name, struct atype *ty, struct sepdef_info *info, struct environment *env);
struct prog_var_info *add_anonymous_prog_var(enum prog_var_category cat, char *pp_name, struct type *type, struct persistent_env *env);
struct logic_var_info *add_anonymous_logic_var(enum logic_var_category cat, char *pp_name, struct persistent_env *env);
struct logic_var_info *add_anonymous_var_with_id(enum logic_var_category cat, char *pp_name, unsigned int id, struct persistent_env *env);
void remove_var_by_name(char *name, struct ephemeral_env *env);
void remove_logic_var_by_id(unsigned int id, struct persistent_env *env);

struct type_info *define_type(char *name, struct type *type, struct environment *env);
struct type_info *find_type_by_id(unsigned int id, struct persistent_env *env);

void flow_env_deep(struct ephemeral_env *env);
void flow_env_up(struct ephemeral_env *env);
struct AsrtList *find_assertion(char *name, struct ephemeral_env *env);
void add_assertion(char *name, struct AsrtList *a, struct ephemeral_env *env);

// remember to update first_field
struct struct_union_info *define_struct(char *name, struct environment *env);
struct struct_union_info *declare_struct(char *name, struct environment *env);
struct struct_union_info *define_anonymous_struct(char *pp_name, struct persistent_env *env);
struct struct_union_info *define_union(char *name, struct environment *env);
struct struct_union_info *declare_union(char *name, struct environment *env);
struct struct_union_info *define_anonymous_union(char *pp_name, struct persistent_env *env);

struct struct_union_info *find_struct_or_union_by_name(char *name, struct ephemeral_env *env);
struct struct_union_info *find_struct_by_id(unsigned int id, struct persistent_env *env);
struct struct_union_info *find_union_by_id(unsigned int id, struct persistent_env *env);

struct field_info *define_field(char *name, struct type *type, struct struct_union_info *parent, struct field_info *next, struct environment *env);
struct field_info *find_field_by_name(char *name, struct ephemeral_env *env);
struct field_info *find_field_by_id(unsigned int id, struct persistent_env *env);

// remember to update first_rator
struct enum_info *define_enum(char *name, struct environment *env);
struct enum_info *declare_enum(char *name, struct environment *env);
struct enum_info *define_anonoymous_enum(char *pp_name, struct persistent_env *env);
struct enum_info *find_enum_by_name(char *name, struct ephemeral_env *env);
struct enum_info *find_enum_by_id(unsigned int id, struct persistent_env *env);

struct atype_info *define_atype(char *name, struct kind *k, struct environment *env);
struct atype_info *declare_atype(char *name, struct kind *k, struct environment *env);
struct atype_info *find_atype_by_name(char *name, struct ephemeral_env *env);
struct atype_info *find_atype_by_id(unsigned int id, struct persistent_env *env);

void define_atype_alias(char *name, struct atype *type, struct ephemeral_env *env);
struct atype *find_atype_alias_by_name(char *name, struct ephemeral_env *env);

struct sepdef_info *declare_sep(char *name, struct ExistList *param, struct environment *env);
struct sepdef_info *define_sep(char *name, struct ExistList *param, struct AsrtList *assert, struct environment *env);
struct sepdef_info *find_sep_by_id(unsigned int id, struct persistent_env *env);

struct enumerator_info *define_enumerator(char *name, int val, struct enum_info *parent, struct enumerator_info *next, struct environment *env);
struct enumerator_info *find_enumerator_by_id(unsigned int id, struct persistent_env *env);

struct projection_info *define_projection(char *name,
                                          struct qvar_list *qv,
                                          struct atype *type,
                                          struct environment *env);
struct projection_info *find_projection_by_id(unsigned int id, struct persistent_env *env);
struct projection_info *find_projection_by_name(char *name, struct ephemeral_env *env);

struct func_info *define_func(char *name,
                              struct type *ty,
                              struct prog_var_info_list *param,
                              struct func_spec *spec,
                              struct environment *env);
struct func_info *declare_func(char *name,
                               struct type *ty,
                               struct prog_var_info_list *param,
                               struct func_spec *spec,
                               struct environment *env);
struct func_info *define_anonymous_func(char *pp_name,
                                        struct type *ty,
                                        struct prog_var_info_list *param,
                                        struct func_spec *spec,
                                        struct persistent_env *env);
struct func_info *find_func_by_id(unsigned int id, struct persistent_env *env);
struct func_spec *find_func_spec(struct func_info *f, char *name);
void add_twin_assertion(struct AsrtList *post, struct AsrtList *pre,
                        struct persistent_env *env);
void delete_twin_assertion(struct AsrtList * asrt, struct persistent_env *env);
struct AsrtList *find_twin_assertion(struct AsrtList *a, struct persistent_env *env);

void add_coq_module(char *command, struct persistent_env *env);
struct coq_module_list *reverse_coq_module(struct coq_module_list *l);
void dump_coq_module(struct persistent_env *env, FILE *fp);

struct prog_var_info_list *VILNil();
struct prog_var_info_list *VILCons(struct prog_var_info *head, struct prog_var_info_list *tail);

unsigned int fresh(struct persistent_env *env);

struct atype *ATZ(struct persistent_env *env);
struct atype *ATList(struct persistent_env *env);
struct atype *ATProd(struct persistent_env *env);
struct atype *ATAssertion(struct persistent_env *env);
struct atype *ATProp(struct persistent_env *env);

void free_prog_var_info(struct prog_var_info *info);
void free_prog_var_info_list(struct prog_var_info_list *il);
void free_spec(struct func_spec *spec);

#define WITH_CURRENT_SCOPE_ONLY(x, f, eph)              \
  {                                                     \
    struct scope_env *__tmp = eph->scope->outer;        \
    eph->scope->outer = NULL;                           \
    x = f;                                              \
    eph->scope->outer = __tmp;                          \
  }

#define WITH_TOP_SCOPE(eph, stmt)                                       \
  {                                                                     \
    struct ephemeral_env *__e = eph;                                    \
    struct scope_env *__s, *__old;                                      \
    for (__s = __e->scope; __s->outer != NULL; __s = __s->outer)        \
      ;                                                                 \
    __old = __e->scope;                                                 \
    __e->scope = __s;                                                   \
    { stmt }                                                            \
    __e->scope = __old;                                                 \
  }

#endif
