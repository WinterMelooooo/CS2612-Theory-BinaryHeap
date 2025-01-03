#ifndef WITNESS_H
#define WITNESS_H

#include "SafetyCheckerWit.h"
#include "EntailmentCheckerWit.h"
#include "ReturnCheckerWit.h"
#include "WhichImpliesWit.h"
#include "PartialSolveWit.h"
#include "FuncCallWit.h"

enum WitnessType {
   WITNESS_TYPE_SAFETY_CHECKER,
   WITNESS_TYPE_ENTAILMENT_CHECKER,
   WITNESS_TYPE_RETURN_CHECKER,
   WITNESS_TYPE_WHICH_IMPLIES,
   WITNESS_TYPE_PARTIAL_SOLVE,
   WITNESS_TYPE_FUNC_CALL
};

struct Witness {
   struct SafetyCheckerWit * safety_checker_wit;
   struct EntailmentCheckerWit * entailment_checker_wit;
   struct ReturnCheckWit * return_checker_wit;
   struct WhichImpliesWit * which_implies_wit;
   struct PartialSolveWit * partial_solve_wit;
   struct FuncCallWit * func_call_wit;
};

struct Witness* NewWitness();
void WitnessFree(struct Witness * wit);

struct Witness * WitnessMerge(struct Witness * w1, struct Witness * w2);

struct WitnessList {
   char * func_name;
   struct Witness * witness;
   struct WitnessList * next;
};

struct WitnessList * WitnessListNil();
struct WitnessList * WitnessListCons(char * func_name, struct Witness * witness, struct WitnessList * next);
struct WitnessList * WitnessListLink(struct WitnessList * list1, struct WitnessList * list2);

#endif // WITNESS_H