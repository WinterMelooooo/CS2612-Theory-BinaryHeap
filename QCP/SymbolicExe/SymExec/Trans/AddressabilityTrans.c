#include "../Utility/InnerAsrtPrinter.h"
#include "AddressabilityTrans.h"
#include "TypeTrans.h"

struct Assertion * ToAddressableSingle(struct Assertion * asrt, struct environment * env) {
   struct LocalLinkedHashMap * new_local = CreateLocalLinkedHashMap();
   struct LocalLinkedHashMap * old_local = asrt->local_list;
   struct LocalLinkedHashMapNode * tmp = old_local->head;
   while (tmp != NULL) {
      struct prog_var_info *info = find_prog_var_by_id(tmp->id, &(env->persist));
      LocalInsert(tmp->id, ExprVal_V_VARI(info->address->id), new_local);
      struct Separation * sep = SepDataAt(ExprVal_V_VARI(info->address->id), 
                                          TransType(info->type), 
                                          ExprValDeepCopy(tmp->value));
      asrt->sep_list = SepListCons(sep, asrt->sep_list);
      tmp = tmp->next;
   }
   asrt->local_list = new_local;
   LocalLinkedHashMapFree(old_local);
   return asrt;
}

struct Assertion * ToNonaddressableSingle(struct Assertion * asrt) {
   struct LocalLinkedHashMap * local = asrt->local_list;
   struct LocalLinkedHashMapNode * tmp = local->head;
   while (tmp != NULL) {
      struct ExprVal * val = tmp->value;
      if (asrt->sep_list == NULL) {
         tmp->value = NULL;
      } else {
         struct SepList * it = asrt->sep_list;
         while (it != NULL && (it->head->t != T_DATA_AT || !ExprValCheckEqual(it->head->d.DATA_AT.left, val))) {
            it = it->next;
         }
         if (it == NULL) {
            tmp->value = NULL;
         } else {
            tmp->value = ExprValDeepCopy(it->head->d.DATA_AT.right);
            asrt->sep_list = SepListRemove(it, asrt->sep_list);
         }
      }
      ExprValFree(val);
      tmp = tmp->next;
   }
   return asrt;
}

struct AsrtList * ToAddressable(struct AsrtList * asrt, struct environment * env) {
   struct AsrtList * ret;
   ret = AsrtListDeepCopy(asrt);
   struct AsrtList * tmp = ret;
   while (tmp != NULL) {
      tmp->head = ToAddressableSingle(tmp->head, env);
      tmp = tmp->next;
   }
   return ret;
}

struct AsrtList * ToNonaddressable(struct AsrtList * asrt) {
   struct AsrtList * ret;
   ret = AsrtListDeepCopy(asrt);
   struct AsrtList * tmp = ret;
   while (tmp != NULL) {
      tmp->head = ToNonaddressableSingle(tmp->head);
      tmp = tmp->next;
   }
   return ret;
}
