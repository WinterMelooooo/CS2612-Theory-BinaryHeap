#ifndef WITNESS_PRINTER_INCLUDED
#define WITNESS_PRINTER_INCLUDED

#include "../../compiler/env.h"
#include "../SymExec/WitnessDef/Witness.h"

void PrintSafetyCheckerWit(struct SafetyCheckerWit * safety_checker_wit, struct environment * env);
void PrintEntailmentCheckerWit(struct EntailmentCheckerWit * entailment_checker_wit, struct environment * env);
void PrintReturnCheckerWit(struct ReturnCheckWit * return_checker_wit, struct environment * env);
void PrintWitness(struct Witness * witness, struct environment * env);

#endif // WITNESS_PRINTER_INCLUDED