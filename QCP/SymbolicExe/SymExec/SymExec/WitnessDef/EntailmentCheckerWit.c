#include "../../../compiler/env.h"
#include "EntailmentCheckerWit.h"
#include "../../Utility/InnerAsrtPrinter.h"

struct EntailmentCheckerWit * entailment_checker_wit;

struct EntailmentCheckerWit * EntailmentCheckerWitNil() {
   return NULL;
}

struct EntailmentCheckerWit * EntailmentCheckerWitCons(struct AsrtList * pre, 
                                                       struct AsrtList * post, 
                                                       struct StringList * strategy_scopes,
                                                       struct EntailmentCheckerWit * next) {
   struct EntailmentCheckerWit * ret;
   ret = (struct EntailmentCheckerWit *) malloc(sizeof(struct EntailmentCheckerWit));
   ret->pre = pre;
   ret->post = post;
   ret->next = next;
   ret->auto_solved = 0;
   ret->strategy_scopes = strategy_scopes;
   return ret;
}

struct EntailmentCheckerWit * EntailmentCheckerWitLink(struct EntailmentCheckerWit * list1, struct EntailmentCheckerWit * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct EntailmentCheckerWit * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}

void EntailmentCheckerWitFree(struct EntailmentCheckerWit * entailment_checker_wit) {
   if (entailment_checker_wit == NULL) return;
   AsrtListFree(entailment_checker_wit->pre);
   AsrtListFree(entailment_checker_wit->post);
   EntailmentCheckerWitFree(entailment_checker_wit->next);
   free(entailment_checker_wit);
}

// pre post are deep copied
struct EntailmentCheckerWit * CheckEntailment(struct AsrtList * pre, struct AsrtList * post,
                                              struct StringList * strategy_scopes,
                                              struct environment * env,
                                              struct EntailmentCheckerWit * entailment_checker_wit) {
   if (pre == NULL) return entailment_checker_wit;
   // puts("---------------Entailment----------------------------");
   // puts("Pre:");
   // PrintAsrtList(pre, 1);
   // puts("Post:");
   // PrintAsrtList(post, 1);
   // puts("-----------------------------------------------------");
   struct AsrtList * post_copy = AsrtListDeepCopy(post);
   for (struct AsrtList * iter = post_copy; iter != NULL; iter = iter->next) {
      struct Assertion * asrt = iter->head;
      for (struct ExistList * i = asrt->exist_list; i != NULL; i = i->next) {
         struct logic_var_info * var_info = find_logic_var_by_id(i->id, &env->persist);
         struct logic_var_info * new_var = add_anonymous_logic_var(LOGIC_GEN_EXISTS, var_info->name, &env->persist);
         int id = new_var->id;
         new_var->atype = atype_deep_copy(var_info->atype);
         new_var->renaming = renaming_info_deep_copy(var_info->renaming);
         asrt = AsrtSubst(asrt, ExprVal_V_VARI(i->id), ExprVal_V_VARI(id));
      }
      iter->head = asrt;
   }
   entailment_checker_wit = EntailmentCheckerWitCons(AsrtListDeepCopy(pre), post_copy, strategy_scopes, entailment_checker_wit);
   return entailment_checker_wit;
}