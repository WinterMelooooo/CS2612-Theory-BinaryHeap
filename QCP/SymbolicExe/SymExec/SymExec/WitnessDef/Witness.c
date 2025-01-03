#include "Witness.h"

struct Witness* NewWitness() {
   struct Witness * ret = (struct Witness *) malloc(sizeof(struct Witness));
   ret->entailment_checker_wit = EntailmentCheckerWitNil();
   ret->safety_checker_wit = SafetyCheckerWitNil();
   ret->return_checker_wit = ReturnCheckWitNil();
   ret->which_implies_wit = WhichImpliesWitNil();
   ret->partial_solve_wit = PartialSolveWitNil();
   ret->func_call_wit = FuncCallWitNil();
   return ret;
}

void WitnessFree(struct Witness * wit) {
   SafetyCheckerWitFree(wit->safety_checker_wit);
   EntailmentCheckerWitFree(wit->entailment_checker_wit);
   ReturnCheckWitFree(wit->return_checker_wit);
   WhichImpliesWitFree(wit->which_implies_wit);
   PartialSolveWitFree(wit->partial_solve_wit);
   FuncCallWitFree(wit->func_call_wit);
   free(wit);
}

struct Witness * WitnessMerge(struct Witness * w1, struct Witness * w2) {
   w1->entailment_checker_wit = EntailmentCheckerWitLink(w1->entailment_checker_wit, w2->entailment_checker_wit);
   w1->safety_checker_wit = SafetyCheckerWitLink(w1->safety_checker_wit, w2->safety_checker_wit);
   w1->return_checker_wit = ReturnCheckWitLink(w1->return_checker_wit, w2->return_checker_wit);
   w1->which_implies_wit = WhichImpliesWitLink(w1->which_implies_wit, w2->which_implies_wit);
   w1->partial_solve_wit = PartialSolveWitLink(w1->partial_solve_wit, w2->partial_solve_wit);
   w1->func_call_wit = FuncCallWitLink(w1->func_call_wit, w2->func_call_wit);
   free(w2);
   return w1;
}

struct WitnessList * WitnessListNil() {
   return NULL;
}

struct WitnessList * WitnessListCons(char * name, struct Witness * witness, struct WitnessList * next) {
   struct WitnessList * ret = (struct WitnessList *) malloc(sizeof(struct WitnessList));
   ret->func_name = name;
   ret->witness = witness;
   ret->next = next;
   return ret;
}

struct WitnessList * WitnessListLink(struct WitnessList * list1, struct WitnessList * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct WitnessList * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}