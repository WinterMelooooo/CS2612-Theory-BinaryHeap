#ifndef SMT_SOLVER_PROOF_H
#define SMT_SOLVER_PROOF_H 1
#include "smt_lang.h"
#include "proof_lang.h"
#include "smt_preprocess_proof.h"
#include "nelson_oppen.h"
#include "nelson_oppen_proof.h"
#include "CDCL_proof.h"
// 0:unsat, 1:sat, -1: 永真
SMT_PROOF* smt_solver_proof(SmtProp *p);

int theroy_infer_proof(ProofData *pdata, int *value, int n);

//最后一步，关闭原命题
int SCOPE_FINAL(ProofData* pdata);

int updata_proofdata(ProofData *pdata, ProofNode *node);
// 0表示check结果为false或者proof不存在， 1表示true
int smt_proof_check_high(SmtProp* goal, SMT_PROOF* proof);
#endif