#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H 1
#include "smt_lang.h"
#include "smt_preprocess_proof.h"
#include "nelson_oppen.h"
#include "nelson_oppen_proof.h"

sat_data *sat_data_copy(sat_data *s);
int *clause_copy(int *cl, int n);

// 0:unsat, 1:sat, -1: 永真
int smt_solver(SmtProp *p);



#endif