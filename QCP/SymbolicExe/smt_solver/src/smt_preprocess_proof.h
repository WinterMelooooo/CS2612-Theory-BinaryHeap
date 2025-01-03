#ifndef PREPROCESS_PROOF_H
#define PREPROCESS_PROOF_H
#include"proof_lang.h"
#include"preprocess.h"

//保留了vtable传递给proof
void freePredata_proof(PreData* data);

ProofTerm* SmtProp2ProofTerm(SmtProp* prop, Hash_Table* vtable);
ProofTerm* SmtTerm2ProofTerm(SmtTerm* t, Hash_Table* vtable);

SmtTerm* term_purify_proof(SmtTerm* t, PreData* data, ProofData* pdata);
SmtProp* prop_purify_proof(SmtProp* p, PreData* data, ProofData* pdata);
//生成purify时set a = b的证明
//生成purify前后的证明 p |- purify(p)
SmtProp* preprocess_data_proof(SmtProp* p, PreData* data, ProofData* pdata);
sat_data* preprocess_proof(SmtProp* p, PreData* data, ProofData* pdata);

//给原子命题编号
//SET_PROP atomic_p = Pvar
int add_prop2HashTable_proof(SmtProp* p, PreData* data, ProofData* pdata);
//由 atomic_p , atomic_p = Pvar |- Pvar
void add_proplist2HashTable_proof(SmtProplist* p, PreData* data, ProofData* pdata);
//生成SUB_PROP P |-- 将P中原子命题用编号替代后的结果
//其他purify list中的命题，对应的步骤由add_proplist2HashTable_proof生成
//返回SUB_PROP步骤的编号
int init_proplist_proof(SmtProp* p, PreData* data, ProofData* pdata);

//生成p3<->(p1 op p2)对应的cnf中的clause
//p3<->not p2 (op为 not时， 此时p1缺省为0)
//生成证明：SET_PROP: p3<->(p1 op p2) / p3<->not p2
//生成证明：p3<->(p1 op p2) |— cnf格式
void clause_gen_proof(int p1, int p2, int p3, int op, PreData* data, ProofData* pdata);
int prop2cnf_proof(SmtProp* p, PreData* data, ProofData* pdata);
clause_data* cnf_trans_proof(SmtProp* p, PreData* data, ProofData* pdata);

//SET t1 = var_id
int SET_VAR_gen(ProofTerm* t1, int id, ProofData* pdata);
//p3 <-> p1 op p2
//p3 <-> not p2
int SET_PROP_gen(int p1, int p2, int p3, int op, ProofData* pdata);
//由 p<-> p1 op p2 |-- cnf格式
int cnf_trans_proofgen(int pnode, ProofTerm* concl, ProofData* pdata);
// p0 /\ p1 /\  ... /\ Pn |-- Pi
//node为推出cnfp的证明步骤的编号
void AND_ELIM_proof(int node, ProofTerm* cnfp, ProofData* pdata);
int updata_proofdata_preprocess(ProofData* pdata, ProofNode* node);
// n = atomic_prop_cnt
void assign_assum_proof(int* value, int n, PreData* data, ProofData* pdata);
int preprocess_assume(ProofTerm* t, ProofData* pdata);
int updata_proofdata_theory(ProofData* pdata, ProofNode* node);
int search_prop(SmtProp* p, PreData* data, Hash_Table* table);
int search_prop2(ProofTerm* t, Hash_Table* table);
int search_prop_unsure(ProofTerm* t, Hash_Table* table);
#endif