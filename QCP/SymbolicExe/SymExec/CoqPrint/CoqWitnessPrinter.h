#ifndef COQ_WITNESS_PRINTER_H
#define COQ_WITNESS_PRINTER_H

#include "../SymExec/WitnessDef/Witness.h"
#include "../Automation/AutomationSolver/solver.h"

void CoqEntailmentCheckerWitPrinter(struct EntailmentCheckerWit * entail, struct environment * env, FILE * fp);

int CoqEntailmentCheckerProofPrinter(int id, struct EntailmentCheckerWit * entail, struct environment * env, FILE * fp);

void CoqSafetyCheckerWitPrinter(struct SafetyCheckerWit * wit, struct environment * env, FILE * fp);

int CoqSafetyCheckerProofPrinter(int id, struct SafetyCheckerWit * wit, struct environment * env, FILE * fp);

void CoqWitnessPrinter(int id, struct Witness * witness, struct environment * env, FILE * fp);

void CoqWitnessProofPrinter(int id, struct Witness *witness, struct environment * env, FILE *fp);

#endif // COQ_WITNESS_PRINTER_H