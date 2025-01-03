#include "utils.h"
#include "renaming.h"

struct renaming_info * renaming_info_var_pre_value(char * var_name) {
   struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_VAR_PRE_VALUE;
   renaming_info->d.var_value.var_name = malloc(sizeof(char) * (strlen(var_name) + 1));
   strcpy(renaming_info->d.var_pre_value.var_name, var_name);
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_var_value(char * var_name, int asrt_id, int branch_id) {
   struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_VAR_VALUE;
   renaming_info->d.var_value.var_name = malloc(sizeof(char) * (strlen(var_name) + 1));
   strcpy(renaming_info->d.var_value.var_name, var_name);
   renaming_info->d.var_value.asrt_id = asrt_id;
   renaming_info->d.var_value.branch_id = branch_id;
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_var_addr(char * var_name) {
   struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_VAR_ADDR;
   renaming_info->d.var_addr.var_name = malloc(sizeof(char) * (strlen(var_name) + 1));
   strcpy(renaming_info->d.var_addr.var_name, var_name);
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_deref(struct renaming_info * info) {
   struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_DEREF;
   renaming_info->d.deref.info = info;
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_field(struct renaming_info * info, char *name) {
  struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_FIELD;
   renaming_info->d.field.info = info;
   renaming_info->d.field.name = malloc(sizeof(char) * (strlen(name) + 1));
   strcpy(renaming_info->d.field.name, name);
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_fallback(char *name) {
  struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_FALLBACK;
   renaming_info->d.fallback.name = malloc(sizeof(char) * (strlen(name) + 1));
   strcpy(renaming_info->d.fallback.name, name);
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_post_introed(char * var_name, int call_id) {
   struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_POST_INTROED;
   renaming_info->d.post_introed.var_name = malloc(sizeof(char) * (strlen(var_name) + 1));
   strcpy(renaming_info->d.post_introed.var_name, var_name);
   renaming_info->d.post_introed.call_id = call_id;
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_return_value() {
   struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_RETURN_VALUE;
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_forall_var(char * var_name, int asrt_id, int branch_id) {
   struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_FORALL_VAR;
   renaming_info->d.forall_var.var_name = malloc(sizeof(char) * (strlen(var_name) + 1));
   strcpy(renaming_info->d.forall_var.var_name, var_name);
   renaming_info->d.forall_var.asrt_id = asrt_id;
   renaming_info->d.forall_var.branch_id = branch_id;
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_exists_var(char * var_name, int asrt_id, int branch_id) {
   struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_EXISTS_VAR;
   renaming_info->d.exists_var.var_name = malloc(sizeof(char) * (strlen(var_name) + 1));
   strcpy(renaming_info->d.exists_var.var_name, var_name);
   renaming_info->d.exists_var.asrt_id = asrt_id;
   renaming_info->d.exists_var.branch_id = branch_id;
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_free_var(char * var_name) {
   struct renaming_info * renaming_info;
   renaming_info = malloc(sizeof(struct renaming_info));
   renaming_info->t = RENAME_FREE_VAR;
   renaming_info->d.free_var.var_name = malloc(sizeof(char) * (strlen(var_name) + 1));
   strcpy(renaming_info->d.free_var.var_name, var_name);
   renaming_info->is_old = 0;
   return renaming_info;
}

struct renaming_info * renaming_info_deep_copy(struct renaming_info * info) {
   if (info == NULL) return NULL;
   switch (info->t) {
      case RENAME_VAR_PRE_VALUE:
         return renaming_info_var_pre_value(info->d.var_pre_value.var_name);
      case RENAME_VAR_VALUE:
         return renaming_info_var_value(info->d.var_value.var_name, info->d.var_value.asrt_id, info->d.var_value.branch_id);
      case RENAME_VAR_ADDR:
         return renaming_info_var_addr(info->d.var_addr.var_name);
      case RENAME_DEREF:
         return renaming_info_deref(info->d.deref.info);
      case RENAME_FIELD:
         return renaming_info_field(info->d.field.info, info->d.field.name);
      case RENAME_FALLBACK:
         return renaming_info_fallback(info->d.fallback.name);
      case RENAME_POST_INTROED:
         return renaming_info_post_introed(info->d.post_introed.var_name, info->d.post_introed.call_id);
      case RENAME_RETURN_VALUE:
         return renaming_info_return_value();
      case RENAME_FORALL_VAR:
         return renaming_info_forall_var(info->d.forall_var.var_name, info->d.forall_var.asrt_id, info->d.forall_var.branch_id);
      case RENAME_EXISTS_VAR:
         return renaming_info_exists_var(info->d.exists_var.var_name, info->d.exists_var.asrt_id, info->d.exists_var.branch_id);
      case RENAME_FREE_VAR:
         return renaming_info_free_var(info->d.free_var.var_name);
   }
   return NULL;
}

void print_renaming(struct renaming_info * renaming) {
   if (renaming == NULL) return;
   switch (renaming->t) {
      case RENAME_VAR_PRE_VALUE:
         printf("var_pre_value(%s)", renaming->d.var_pre_value.var_name);
         break;
      case RENAME_VAR_VALUE:
         printf("var_value(%s)", renaming->d.var_value.var_name, renaming->d.var_value.asrt_id, renaming->d.var_value.branch_id);
         break;
      case RENAME_VAR_ADDR:
         printf("var_addr(%s)", renaming->d.var_addr.var_name);
         break;
      case RENAME_DEREF:
         printf("deref(");
         print_renaming(renaming->d.deref.info);
         printf(")");
         break;
      case RENAME_FIELD:
         printf("field(");
         print_renaming(renaming->d.field.info);
         printf(", %s)", renaming->d.field.name);
         break;
      case RENAME_FALLBACK:
         printf("fallback(%s)", renaming->d.fallback.name);
         break;
      case RENAME_POST_INTROED:
         printf("post_introed(%s, %d)", renaming->d.post_introed.var_name, renaming->d.post_introed.call_id);
         break;
      case RENAME_RETURN_VALUE:
         printf("return_value()");
         break;
      case RENAME_FORALL_VAR:
         printf("forall_var(%s)", renaming->d.forall_var.var_name, renaming->d.forall_var.asrt_id, renaming->d.forall_var.branch_id);
         break;
      case RENAME_EXISTS_VAR:
         printf("exists_var(%s)", renaming->d.exists_var.var_name, renaming->d.exists_var.asrt_id, renaming->d.exists_var.branch_id);
         break;
      case RENAME_FREE_VAR:
         printf("free_var(%s)", renaming->d.free_var.var_name);
         break;
   }
}
