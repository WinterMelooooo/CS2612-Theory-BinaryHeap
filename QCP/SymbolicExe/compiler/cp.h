#ifndef CP_H
#define CP_H

#include "env.h"
#include "plang.h"

/* cp parse type */
char *cppt_derive_type(struct pp_type **base, struct pp_derivtype *deriv);
char *cppt_type(struct pp_pretype *pre);
void cppt_expr(struct pp_expr *expr);
void cppt_assert(struct RAssertion *expr);

/* cp def */
struct field_info *cpd_define_field_list(struct annot_list *field,
                                         struct struct_union_info *parent,
                                         struct environment *env);
struct struct_union_info *cpd_define_struct(char *name, struct environment *env);
struct struct_union_info *cpd_define_union(char *name, struct environment *env);
struct enumerator_info *cpd_define_enum_list(struct pp_enum_list *rator,
                                             int val,
                                             struct enum_info *parent,
                                             struct environment *env);
struct enum_info *cpd_define_enum(char *name,
                                  struct environment *env);
struct struct_union_info *cpd_declare_struct(char *name, struct environment *env);
struct struct_union_info *cpd_declare_union(char *name, struct environment *env);
struct logic_var_info *cpd_declare_extern(char *name,
                                          struct qvar_list *qv, struct atype *ty,
                                          struct environment *env);
struct atype_info *cpd_declare_extern_type(char *name, struct kind *k, struct environment *env);
struct projection_info *cpd_declare_projection(char *name,
                                               struct qvar_list *qv,
                                               struct atype *type,
                                               struct environment *env);
void cpd_declare_extern_type_alias(char *name, struct atype *type, struct environment *env);
struct enum_info *cpd_declare_enum(char *name, struct environment *env);
struct struct_union_info *cpd_finalize_struct(struct struct_union_info *info);
struct struct_union_info *cpd_finalize_union(struct struct_union_info *info);
struct prog_var_info *cpd_define_global_var(struct type *ty, char *name, struct environment *env);
struct sepdef_info *cpd_define_sep(char *name, struct ExistList *param, struct environment *env);
struct sepdef_info *cpd_finalize_sep(struct sepdef_info *info,
                                     struct qvar_list *qv, struct AsrtList *cond);
struct prog_var_info_list *cpd_define_param(char *func, struct annot_list *param,
                                            struct environment *env);
struct ExistList *cpd_declare_atypes(struct atype_list *type, struct environment *env);
struct ExistList *cpd_define_free(struct lvar_list *free, struct environment *env);
struct ExistList *cpd_declare_sep_param(struct lvar_list *p, struct environment *env);
struct func_info *cpd_define_func(struct type *ty,
                                  char *name,
                                  struct prog_var_info_list *param,
                                  struct func_spec *spec,
                                  struct environment *env);
struct func_info *cpd_declare_func(struct type *ty,
                                   char *name,
                                   struct prog_var_info_list *param,
                                   struct func_spec *spec,
                                   struct environment *env);
struct prog_var_info *cpd_define_local(char *name, struct type *type, struct environment *env);
struct type_info *cpd_define_type(char *name, struct type *type, struct environment *env);

/* cp incomplete */
int cpi_is_incomplete(struct pp_type *ty);
void cpi_expr(struct pp_expr *e);
/* void cpi_assert(struct RAssertion *ra); */

/* cp pointer arith */
void cppa_expr(struct pp_expr *e);
void cppa_simple_cmd(struct pp_simple *simple);

/* cp array parameter */
void cpap_param(struct annot_list *param);
void cpap_type(struct pp_type *type);
void cpap_expr(struct pp_expr *expr);

/* cp object type */
void cpo_type(struct pp_type *type);
void cpo_expr(struct pp_expr *type);
int cpo_is_function(struct pp_type *ty);

/* cp bind */
void cpb_type(struct pp_type *type, struct environment *env);
void cpb_decl_type(struct pp_type *type, struct environment *env);
void cpb_expr(struct pp_expr *expr, struct environment *env);
void cpb_assert(struct RAssertion *ra, struct environment *env);
struct atype *cpb_atype(struct atype_list *qv, struct atype *body,
                        struct qvar_list **ql,
                        struct environment *env);

/* cp const */
void cpc_eval_to_const(struct pp_expr *e);
void cpc_type(struct pp_type *type);
void cpc_expr(struct pp_expr *expr);
void cpc_assert(struct RAssertion *ra);
void cpc_struct(struct struct_union_info *info);
void cpc_union(struct struct_union_info *info);

/* cp type */
int cpt_conv(struct type *src, struct type *dst);
int cpt_recov_conv(struct type *src, struct type *dst,
                   struct pp_expr *esrc, struct pp_expr *edst);
void cpt_expr(struct pp_expr *e);
void cpt_assert(struct RAssertion *ra, struct type *ret);
void cpt_simple_cmd(struct pp_simple *scmd);
int cpt_is_integral(struct type *ty);
int cpt_is_scalar(struct type *ty);
int cpt_is_effective_scalar(struct type *ty);
struct field_info *cpt_find_slot(struct struct_union_info *info, char *name);

/* cp left value */
void cplv_expr(struct pp_expr *e);
void cplv_simple_cmd(struct pp_simple *scmd);

/* cp assertion type */
void cpat_inhabited(struct atype *ty);
void cpat_assert(struct RAssertion *p, struct persistent_env *env);
void cpat_expr(struct pp_expr *e, struct persistent_env *env);
void cpat_check_kind_resolve(struct kind *k);
void cpat_check_resolve(struct atype *ty);
struct qvar_list *cpat_generalize(struct ExistList *qv, struct ExistList *with,
                                  struct AsrtList *as[], int nas,
                                  struct persistent_env *env);
int cpat_is_Prop(struct atype *ty);
struct qvar_list *cpat_check_varg_alt(struct virt_arg *varg, struct func_spec *spec, struct persistent_env *env);
struct qvar_list *cpat_check_varg(struct virt_arg *varg, struct func_spec *spec, struct persistent_env *env);
struct atype *cpat_instantiate(struct qvar_list *qv, struct atype *ty, struct qvar_list **impl);
void cpat_unify(struct atype *t1, struct atype *t2);

/* cp assertion */
struct AsrtList *cpa_comment(struct RAssertion *ra, struct environment *env);
struct func_spec *cpa_local_spec(struct ExistList *with,
                                 struct RAssertion *pre, struct RAssertion *post,
                                 struct environment *env);
struct func_spec *cpa_spec(struct ExistList *witht,
                           struct ExistList *with,
                           struct RAssertion *pre,
                           struct RAssertion *post,
                           struct prog_var_info_list *param,
                           struct environment *env);
void cpa_expr(struct pp_expr *e, struct environment *env);
void cpa_rename_func_spec(struct func_spec *spec, struct hashtbl *mapping,
                          struct persistent_env *env);

/* cp user */
struct RAssertion *cpu_comment(struct AsrtList *a, struct environment *env);
struct pp_spec *cpu_spec(struct func_spec *spec, struct environment *env);
void cpu_free_pp_spec(struct pp_spec *spec);
void cpu_free_ra(struct RAssertion *ra);

/* others */
struct type *type_of_pp_type(struct pp_type *ty);
struct expr *expr_of_pp_expr(struct pp_expr *e);
struct simple_cmd *simple_of_pp_simple(struct pp_simple *s);
struct pp_type *pp_type_of_type(struct type *ty);
#define CALL_WITH_TYPE(type, f, ret)                            \
  {                                                             \
    struct pp_type *__t = pp_type_of_type(type_unalias(type));  \
    ret = f(__t);                                               \
    free_pp_type(__t);                                          \
  }

#endif
