#include <string.h>
#include <assert.h>
#include "LogicNameManager.h"
#include "../../compiler/env.h"
#include "InnerAsrtPrinter.h"

struct environment * saved_env;
int asrt_id = 0;

void LogicNameManagerInit(struct environment * env) {
   saved_env = env;
}

int GetNewLogicVar() {
   int id = fresh(&saved_env->persist);
   return id;
}

int ToStringLength(int id) {
   if (id == 0) return 1;
   int length = 0;
   while (id > 0) {
      id /= 10;
      ++length;
   }
   return length;
}

void AsrtNormalizeName(struct Assertion * asrt, int asrt_id, int branch_id, int is_old, struct environment * env) {
   struct LocalLinkedHashMap * local_map = asrt->local_list;
   struct LocalLinkedHashMapNode * node;
   for (node = local_map->head; node != NULL; node = node->next) {
      if (node->state == 1) {
         int id = node->id;
         struct prog_var_info * var_info = find_prog_var_by_id(id, &env->persist);
         int addr_id = var_info->address->id;
         if (var_info->address->renaming == NULL) {
            var_info->address->renaming = renaming_info_var_addr(var_info->name);
         }
         struct ExprVal * addr_val = ExprVal_V_VARI(addr_id);
         struct ExprVal * val = GetDataAtValue(asrt, addr_val);
         ExprValFree(addr_val);
         if (val != NULL) {
            if (val->t == FUNCAPP && ExprValListIsEmpty(val->d.FUNCAPP.args) && PolyTypeListIsEmpty(val->d.FUNCAPP.types)) {
               struct logic_var_info * val_var_info = find_logic_var_by_id(val->d.FUNCAPP.id, &env->persist);
               if (val_var_info->name != NULL && val_var_info->renaming == NULL) {
                  val_var_info->renaming = renaming_info_var_value(val_var_info->name, asrt_id, branch_id);
                  val_var_info->renaming->is_old = is_old;
               }
            }
         }
      }
   }
   for (struct ExistList * i = asrt->exist_list; i != NULL; i = i->next) {
      int id = i->id;
      struct logic_var_info * var_info = find_logic_var_by_id(id, &env->persist);
      if (var_info->renaming == NULL) {
         if (var_info->category == LOGIC_GEN_EXISTS || var_info->category == LOGIC_USER_EXISTS) {
            var_info->renaming = renaming_info_exists_var(var_info->name, asrt_id, branch_id);
         } else if (var_info->category == LOGIC_FORALL) {
            var_info->renaming = renaming_info_forall_var(var_info->name, asrt_id, branch_id);
         } else {
            var_info->renaming = renaming_info_free_var(var_info->name);
         }
      }
   }
}

void AsrtListNormalizeName(struct AsrtList * asrt_list, struct environment * env) {
   ++asrt_id;
   struct AsrtList * tmp = find_twin_assertion(asrt_list, &env->persist);
   int branch_id = 1;
   for (struct AsrtList * i = asrt_list; i != NULL; i = i->next) {
      AsrtNormalizeName(i->head, asrt_id, branch_id, 0, env);
      ++branch_id;
   }
   branch_id = 1;
   for (struct AsrtList * i = find_twin_assertion(asrt_list, &env->persist); i != NULL; i = i->next) {
      AsrtNormalizeName(i->head, asrt_id, branch_id, 1, env);
      ++branch_id;
   }
}

void PrePostAsrtNormalizeName(struct Assertion * asrt, int asrt_id, int branch_id, int is_pre, struct environment * env) {
   struct LocalLinkedHashMap * local_map = asrt->local_list;
   struct LocalLinkedHashMapNode * node;
   for (node = local_map->head; node != NULL; node = node->next) {
      if (node->state == 1) {
         assert(node->value->t == FUNCAPP);
         int id = node->value->d.FUNCAPP.id;
         struct logic_var_info * var_info = find_logic_var_by_id(id, &env->persist);
         if (var_info->name != NULL && var_info->renaming == NULL) {
            if (is_pre) {
               var_info->renaming = renaming_info_var_pre_value(var_info->name);
            } else {
               var_info->renaming = renaming_info_var_value(var_info->name, asrt_id, branch_id);
            }
         } else if (is_pre && var_info->renaming != NULL && var_info->renaming->t == RENAME_VAR_VALUE) {
            char * tmp = var_info->renaming->d.var_value.var_name;
            var_info->renaming->t = RENAME_VAR_PRE_VALUE;
            var_info->renaming->d.var_pre_value.var_name = tmp;
         }
      }
   }
   for (struct ExistList * i = asrt->exist_list; i != NULL; i = i->next) {
      int id = i->id;
      struct logic_var_info * var_info = find_logic_var_by_id(id, &env->persist);
      if (var_info->renaming == NULL) {
         if (var_info->category == LOGIC_GEN_EXISTS || var_info->category == LOGIC_USER_EXISTS) {
            var_info->renaming = renaming_info_exists_var(var_info->name, asrt_id, branch_id);
         } else if (var_info->category == LOGIC_FORALL) {
            var_info->renaming = renaming_info_forall_var(var_info->name, asrt_id, branch_id);
         }
      }
   }
}

void PrePostAsrtListNormalizeName(struct AsrtList * asrt_list, int is_pre, struct environment * env) {
   ++asrt_id;
   int branch_id = 1;
   while (asrt_list != NULL) {
      PrePostAsrtNormalizeName(asrt_list->head, asrt_id, branch_id, is_pre, env);
      asrt_list = asrt_list->next;
      ++branch_id;
   }
}

void WithVarNormalizeName(struct ExistList * with_list, struct environment * env) {
   while (with_list != NULL) {
      int id = with_list->id;
      struct logic_var_info * var_info = find_logic_var_by_id(id, &env->persist);
      if (var_info->renaming == NULL) {
         var_info->renaming = renaming_info_free_var(var_info->name);
      }
      with_list = with_list->next;
   }
}