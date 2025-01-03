#ifndef WITNESS_TRY_SOLVE
#define WITNESS_TRY_SOLVE

#include "Witness.h"
#include "../../../compiler/env.h"

void EliminateLocal(struct Assertion * pre, struct AsrtList * post, struct environment * env);
void EntailmentCheckerWitTrySolve(struct EntailmentCheckerWit * entailment_checker_wit, struct environment * env);
void ReturnCheckWitTrySolve(struct ReturnCheckWit * return_checker_wit, struct environment * env);
void WhichImpliesWitTrySolve(struct WhichImpliesWit * which_implies_wit, struct environment * env);
void SafetyCheckerWitTrySolve(struct SafetyCheckerWit * safety_checker_wit, struct environment * env);
void PartialSolveWitTrySolve(struct PartialSolveWit * partial_solve_wit, struct environment * env);
void WitnessTrySolve(struct Witness * wit, struct environment * env);

#endif