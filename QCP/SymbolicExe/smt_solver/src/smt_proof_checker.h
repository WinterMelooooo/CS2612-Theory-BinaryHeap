#ifndef SMT_PROOF_CHECKER_H
#define SMT_PROOF_CHECKER_H
#include "proof_lang.h"
#include"hashtable.h"
#include "lia_theory.h"
#include"lia_proof.h"
typedef struct CheckData{
    MaxVar* max_table;
    int prop_cnt;
    int max_plen;
    Hash_Table* v_table;
    ProofTerm** p_list;
} CheckData;

//相等返回1，不等返回0
int ProofTerm_eqb(ProofTerm* t1, ProofTerm* t2);

//正确返回1，否则返回第一个错误的证明步骤编号
int proof_check(ProofNode** dlist, int dn, ProofNode** list, int n);

// 0表示check结果为false或者proof不存在， 1表示true
int smt_proof_check(SMT_PROOF* proof);
int smt_proof_check_low(ProofTerm* goal, SMT_PROOF* proof);
#endif