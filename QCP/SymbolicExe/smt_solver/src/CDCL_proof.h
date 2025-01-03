#ifndef CDCL_PROOF_H
#define CDCL_PROOF_H
#include "CDCL.h"
#include "proof_lang.h"
#include "smt_preprocess_proof.h"
#include "smt_solver_proof.h"

typedef struct Node_list Node_list;
typedef struct local_ProofData local_ProofData;

struct local_ProofData
{
    int cur_num;
    int max_num;
    Hash_Table *local_table;
    ProofNode **node_table;
};

struct Node_list
{
    ProofNode *node;
    Node_list *next;
};
int *clause_resolution_proof(int *wi, int *wj, sat_data *s, ProofData *data);
int *clause_learning_proof(int wi, sat_data *s, ProofData *data);

// 目前的实现为多步的resolution， 也可以考虑生成一步的chain resolution，由于3cnf，所以其实最多两步
int bcp_resol_proof(int bcpvar, int *value, int n, local_ProofData *pdata, ProofData *data);
int cdcl_solver_proof(sat_data *s, ProofData *data);
int bcp_proof(sat_data *s, local_ProofData *pdata, ProofData *data); // 返回值>=0为冲突子句的编号，-1为正常运行

ProofTerm *clause2ProofTerm(int *value, int n);
int updata_proofdata_cdcl_local(local_ProofData *pdata, ProofNode *node);
local_ProofData *init_local_ProofData(int n);
void mergelocal_ProofData(local_ProofData *pdata, ProofData *data);
void freelocal_ProofData(local_ProofData *pdata);
#endif