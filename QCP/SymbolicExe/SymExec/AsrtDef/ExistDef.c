#include <string.h>
#include <assert.h>
#include "ExistDef.h"
#include "../../compiler/lang.h"
#include "../../compiler/env.h"


struct PolyType *cpa_type_of(struct atype *ty);
struct atype * cpu_type_of(struct PolyType *ty, struct persistent_env *env);

struct ExistList * ExistListNil() { 
   return NULL; 
}

struct ExistList * ExistListCons(int id, struct ExistList *list) {
   struct ExistList * ret = (struct ExistList *) malloc(sizeof(struct ExistList));
   ret->id = id;
   ret->next = list;
   return ret;
}

struct ExistList * ExistListReverse(struct ExistList * list) {
   struct ExistList * ret = NULL;
   struct ExistList * iter = list;
   while (iter != NULL) {
      struct ExistList * tmp = iter->next;
      iter->next = ret;
      ret = iter;
      iter = tmp;
   }
   return ret;
}

struct ExistList * ExistListLink(struct ExistList *left, struct ExistList *right) {
   if (left == NULL) return right;
   if (right == NULL) return left;
   struct ExistList * tmp = left;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = right;
   return left;
}

struct ExistList * ExistListRemove(int ident, struct ExistList * list) {
   if (list == NULL)
      return NULL;
   if (ident == list->id) {
      struct ExistList * t;
      t = list->next;
      free(list);
      return t;
   }
   list->next = ExistListRemove(ident, list->next);
   return list;
}

struct ExistList *ExistListSort(struct ExistList * list) {
   if (list == NULL) return NULL;
   struct ExistList *i, *j;
   for (i = list; i != NULL; i = i->next) {
      for (j = list; j->next != NULL; j = j->next) {
         if (j->id > j->next->id) {
            int tmp = j->id;
            j->id = j->next->id;
            j->next->id = tmp;
         }
      }
   }
   return list;
}

struct ExistList * ExistListUnique(struct ExistList * list) {
   if (list == NULL) return NULL;
   list = ExistListSort(list);
   struct ExistList *i;
   i = list;
   while (i -> next != NULL) {
      if (i->id == i->next->id) {
         struct ExistList * tmp = i->next;
         i->next = i->next->next;
         free(tmp);
      } else {
         i = i->next;
      }
   }
   return list;
}

struct ExistList * ExistListDeepCopy(struct ExistList * exist_list) {
   if (exist_list == NULL) return NULL;
   return ExistListCons(exist_list->id, ExistListDeepCopy(exist_list->next));
}

struct ExistList * ExistListSubst(struct ExistList * exist_list, struct ExprVal * pre, struct ExprVal * post) {
   if (exist_list == NULL) return NULL;
   if (pre == NULL || post == NULL || pre->t != FUNCAPP || post->t != FUNCAPP) return exist_list;
   struct ExistList * iter;
   iter = exist_list;
   while (iter != NULL) {
      if (iter->id == pre->d.FUNCAPP.id) {
         iter->id = post->d.FUNCAPP.id;
      }
      iter = iter->next;
   }
   return exist_list;
}

struct ExistList *ExistListSubstPolyType(struct ExistList * exist_list, struct PolyType * pre, struct PolyType * post, struct persistent_env * env) {
   if (exist_list == NULL) return NULL;
   if (pre == NULL || post == NULL) return exist_list;
   struct ExistList * iter;
   iter = exist_list;
   while (iter != NULL) {
      struct logic_var_info * info = find_logic_var_by_id(iter->id, env);
      info->atype = cpu_type_of(PolyTypeSubst(cpa_type_of(info->atype), pre, post), env);
      iter = iter->next;
   }
   return exist_list;
}

int ExistListContains(int id, struct ExistList * exist_list) {
   if (exist_list == NULL) return 0;
   if (exist_list->id == id) return 1;
   return ExistListContains(id, exist_list->next);
}

void ExistListFree(struct ExistList * exist_list) {
   if (exist_list == NULL) return;
   ExistListFree(exist_list->next);
   free(exist_list);
}