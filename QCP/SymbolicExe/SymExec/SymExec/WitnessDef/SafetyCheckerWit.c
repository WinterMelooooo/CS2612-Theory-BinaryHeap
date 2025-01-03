#include "SafetyCheckerWit.h"

struct SafetyCheckerWit * SafetyCheckerWitNil() {
   return NULL;
}

struct SafetyCheckerWit * SafetyCheckerWitCons(struct Assertion * asrt, 
                                               struct PropList * constraits, 
                                               struct SafetyCheckerWit * next) {
   struct SafetyCheckerWit * ret = (struct SafetyCheckerWit *) malloc(sizeof(struct SafetyCheckerWit));
   ret->asrt = asrt;
   ret->constraits = constraits;
   ret->next = next;
   ret->auto_solved = 0;
   return ret;
}

struct SafetyCheckerWit * SafetyCheckerWitLink(struct SafetyCheckerWit * list1, struct SafetyCheckerWit * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct SafetyCheckerWit * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}

void SafetyCheckerWitFree(struct SafetyCheckerWit * safety_checker_wit) {
   if (safety_checker_wit == NULL) return;
   AsrtFree(safety_checker_wit->asrt);
   PropListFree(safety_checker_wit->constraits);
   SafetyCheckerWitFree(safety_checker_wit->next);
   free(safety_checker_wit);
}
