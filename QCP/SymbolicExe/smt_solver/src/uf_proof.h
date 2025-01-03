#ifndef UF_PROOF_H
#define UF_PROOF_H
#include"preprocess.h"
#include"congruence.h"
#include"proof_lang.h"

//trans时出现的uf变量，则该变量对应的原函数必是一个全函数
//cong时出现的uf变量，其对应的原函数必为一个偏函数
//所有的uf函数其第二个参数一定对应原本的变量或者原本的函数，第一个参数对应原本函数名或者偏函数
//返回a = b对应的未curryfy的等式的证明步骤的编号
int explain_proof(database* S, ProofData* data, PreData* pdata, int a, int b);

//由b->b1->b2->...->a的等价链，利用传递性规则生成b = a的证明
int explain_trans_chain(database* S, ProofData* data, PreData* pdata, int a, int b);

//将f还原成全函数
ProofTerm* uf_recover(int f, PreData* pdata);
//将f1=f2分别还原后生成等式对应的proofterm
ProofTerm* uf_eq_recover(int f1, int f2, PreData* pdata);

int update_proofdata_uf(ProofData* pdata, ProofNode* node);

//用于在混合理论求解前，且在curryfy前将uf的命题加入假设，存在theory_global_table中
ProofTerm* uf_trans_ProofTerm(SmtTerm* t, PreData* pdata);
ProofTerm* ufeq_trans_ProofTerm(SmtProp* p, PreData* pdata);
int uf_proof_assume(SmtProp* prop, ProofData* data, PreData* pdata);

//用于在混合理论求解前，initCombineData之后将assign的命题加入假设，使用theory_global_table记录
//只处理a=b的等式，将其还原后加入assum
//若还原后等式两边都是变量：x1 = x2，则进行一步推导：x1-x2 = 0
void uf_proof_assume_pos(EquationNode* list, ProofData* data, PreData* pdata);
//处理a！=b，将其加入假设
void uf_proof_assume_neg(EquationNode* list, ProofData* data, PreData* pdata);

//由x=y推出x-y = 0
int uf_infer_add(ProofData* data, int n, int x, int y, int pnode);
int uf_false_gen(database* S, ProofData* data, PreData* pdata, int x, int y);
#endif
