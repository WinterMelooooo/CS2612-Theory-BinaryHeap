#ifndef RENAMING_H
#define RENAMING_H

enum renaming_info_type {
   RENAME_VAR_PRE_VALUE,
   RENAME_VAR_VALUE,
   RENAME_VAR_ADDR,
   RENAME_DEREF,
   RENAME_FIELD,
   RENAME_FALLBACK,
   RENAME_POST_INTROED,      // existential variable in postcondition will be introduced by func-call
   RENAME_RETURN_VALUE,
   RENAME_FORALL_VAR,
   RENAME_EXISTS_VAR,
   RENAME_FREE_VAR,          // contains free variable, such as the variables in with_list
};

struct renaming_info {
   enum renaming_info_type t;
   union {
      struct { char * var_name; } var_pre_value;
      struct { char * var_name; int asrt_id; int branch_id; } var_value;
      struct { char * var_name; } var_addr;
      struct { struct renaming_info *info; } deref;
      struct { struct renaming_info *info; char *name; } field;
      struct { char *name; } fallback;
      struct { char * var_name; int call_id; } post_introed;
      struct { } return_value;
      struct { char * var_name; int asrt_id; int branch_id;} forall_var;
      struct { char * var_name; int asrt_id; int branch_id;} exists_var;
      struct { char * var_name; } free_var;
   }d;
   
   // only used in sac printer
   int is_old;
};

struct renaming_info * renaming_info_var_pre_value(char * var_name);
struct renaming_info * renaming_info_var_value(char * var_name, int asrt_id, int branch_id);
struct renaming_info * renaming_info_var_addr(char * var_name);
struct renaming_info * renaming_info_deref(struct renaming_info * info);
struct renaming_info * renaming_info_field(struct renaming_info * info, char *name);
struct renaming_info * renaming_info_fallback(char *name);
struct renaming_info * renaming_info_post_introed(char * var_name, int call_id);
struct renaming_info * renaming_info_return_value();
struct renaming_info * renaming_info_forall_var(char * var_name, int asrt_id, int branch_id);
struct renaming_info * renaming_info_exists_var(char * var_name, int asrt_id, int branch_id);
struct renaming_info * renaming_info_free_var(char * var_name);

struct renaming_info * renaming_info_deep_copy(struct renaming_info * renaming_info);

void print_renaming(struct renaming_info * renaming);
#endif // RENAMING_H