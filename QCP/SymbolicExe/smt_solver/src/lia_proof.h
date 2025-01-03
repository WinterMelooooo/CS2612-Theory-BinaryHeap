#ifndef LIA_PROOF_H
#define LIA_PROOF_H 1
#include "lia_theory.h"

/*lia模块的证明生成: 一系列等式和不等式推出fasle*/
/*-------------------------------------------*/

// 用结论和证明步骤更新proofdata
//  -1表示添加成功，其他值表示已经存在该结论，并返回对应结论的编号
int updata_proofdata_lia(ProofData *pdata, ProofNode *node, int level);

//从系数数组变成proofterm
ProofTerm* inequ_trans_proofterm(int* coef, int n, TermType type);

//完成assume的生成：
void lia_proof_assume(InequList* r, ProofData* pdata, TermType type, int n, int level);
int lia_infer_assume(int* coef, ProofData *pdata, int n);

//检查当前等式或不等式是否成立
bool equation_true(int* coef, int n, TermType op, MaxVar* table);

//用等式left在right中消去val，得到res，right的关系符是op(=或者<=)
// 两个不等式left和right傅里叶消去val产生res, 此时op恒为<=
ProofNode* lia_proof_FME(int* left, int* right, int* res, int n, ProofData* pdata, int val, TermType op, ProofRule rule, int level, MaxVar* table);
//只包含常数项的等式或不等式可以直接推出false的情况
ProofNode* lia_FALSE(int* coef, int n, ProofData* pdata, TermType op, int level);

//下面四个函数，当已经推出false时返回空指针
int* equ_eliminate_simplify_proof(int* r1, int* r2, int* value, ProofData*pdata, MaxVar* table, int size, TermType op, int level);
InequList* eliminate_equa_constraint_proof(InequList* r1, InequList* r2, int* value, ProofData* pdata, MaxVar* table, int num, int level);
int* generate_new_constraint_proof(int* r1, int* r2, ProofData* pdata, MaxVar* table, int num, int cur_num, int level);
InequList* generate_new_constraint_list_proof(InequList* r1, InequList* r2, ProofData* pdata, MaxVar* table, int num, int cur_num, int level);

//带证明生成的real_shadow函数
InequList* real_shadow_proof(InequList* r, int* value, ProofData* pdata, MaxVar* table, int n, int level);
int lia_theory_deduction_proof(InequList* r1, InequList* r2, int* value, ProofData* pdata, int n, int int8_max, int int16_max, int int32_max, int int64_max, int level);

//lia_infer_proof中使用
int SCOPE_END_LIA(int fnode, int anode, ProofData* data);
int LIA_ARITH_NOT_ELIM(int* coef, int n, int node, ProofData* data);
#endif