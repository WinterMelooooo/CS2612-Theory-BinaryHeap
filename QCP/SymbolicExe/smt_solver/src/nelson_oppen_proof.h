#ifndef NELSON_OPPEN_PROOF
#define NELSON_OPPEN_PROOF 1
#include"uf_proof.h"
#include"nelson_oppen.h"

err proplist_trans_coef_proof(SmtProplist *prop_list, PreData *data, int *value, lia_list *list, ProofData* pdata);
// 初始化CombineData
CombineData *initCombineData_proof(PreData *data, int *value, ProofData* pdata);
void init_theory_assume(CombineData* cdata, PreData* data, ProofData* pdata);
int theroy_deduction_lia_proof(TheoryData* tdata, PreData* data, ProofData* pdata);
//返回1表示能推出vi=vj，返回0表示不能推出vi=vj
int lia_infer_proof(int vi, int vj, TheoryData* tdata, PreData* data, ProofData* pdata);

int theroy_deduction_uf_proof(TheoryData* tdata, PreData* data, ProofData* pdata);
int uf_infer_proof(int vi, int vj, TheoryData* tdata, PreData* data, ProofData* pdata);
int nelson_oppen_convex_proof(CombineData* cdata, PreData* data, ProofData* pdata);

#endif