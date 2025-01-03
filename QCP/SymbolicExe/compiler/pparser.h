#ifndef PPARSER_H
#define PPARSER_H

#include "plang.h"
#include "lang.h"
#include "env.h"

/* elaboration and possibly update the environment (but not the context, though behaviour
   could be context dependent) */

struct expr *parse_cond(struct pp_expr *e, struct environment *env);
struct expr *parse_switch_cond(struct pp_expr *e, struct environment *env);
struct expr *parse_case_cond(struct pp_expr *e, struct environment *env);
struct expr *parse_ret(struct pp_expr *e, struct environment *env);
struct pp_type *parse_decl_head(struct pp_trivtype *triv, struct environment *env);
struct prog_var_info *parse_decl(struct pp_type *base, struct pp_derivtype *deriv, struct environment *env);
struct type_info *parse_type_def(struct pp_type *base, struct pp_derivtype *deriv,
                                 struct environment *env);
struct func_spec *parse_local_spec(struct RAssertion *pre, struct RAssertion *post,
                                   struct environment *env);
struct AsrtList *parse_comment(struct RAssertion *ra, char *mark, struct environment *env);
struct simple_cmd *parse_simple_cmd(struct pp_simple *simple, struct environment *env);

struct sepdef_info *parse_sepdef(char *name,
                                 struct atype_list *witht,
                                 struct lvar_list *with,
                                 struct RAssertion *cond,
                                 struct environment *env);
struct atype_info *parse_atype_def(char *name, struct kind *k, struct environment *env);
struct logic_var_info *parse_extern_def(char *name, struct atype_list *qv, struct atype *body, struct environment *env);
void parse_atype_alias(char *name, struct atype *type, struct environment *env);
struct projection_info *parse_proj_def(char *name, struct atype_list *qv,
                                       struct atype *type,
                                       struct environment *env);
void parse_record_def(struct atype_list *params,
                      char *record_name, char *constr_name,
                      struct lvar_list *fields, struct environment *env);
struct coqdef_info *parse_coqdef(char *name, struct environment *env);
struct func_info *parse_func_def(struct pp_pretype *ty, struct pp_spec *spec, struct environment *env);
struct func_info *parse_func_dec(struct pp_pretype *ty, struct pp_spec *spec, struct environment *env);
struct func_info *finalize_func_def(struct func_info *f, struct environment *env);
struct func_info *parse_anon_func_dec(struct pp_pretype *ty,
                                      struct pp_spec *spec,
                                      struct environment *env);
struct struct_union_info *parse_struct_def(char *name, struct annot_list *fields, struct environment *env);
struct struct_union_info * parse_union_def(char *name, struct annot_list *fields, struct environment *env);
struct enum_info *parse_enum_def(char *name, struct pp_enum_list *rator, struct environment *env);
struct struct_union_info *parse_anon_struct_def(struct annot_list *fields, struct environment *env);
struct struct_union_info *parse_anon_union_def(struct annot_list *fields, struct environment *env);
struct enum_info *parse_anon_enum_def(struct pp_enum_list *rator, struct environment *env);
struct struct_union_info * parse_struct_dec(char *name, struct environment *env);
struct struct_union_info * parse_union_dec(char *name, struct environment *env);
struct enum_info *parse_enum_dec(char *name, struct environment *env);

#endif
