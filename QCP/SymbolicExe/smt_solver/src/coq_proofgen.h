#ifndef COQ_PROOFGEN_H
#define COQ_PROOFGEN_H

#include "proof_lang.h"
#include "hashtable.h"
enum VAR_COQ_TYPE{
    COQ_Z = 1,
    COQ_NAT,
    COQ_LIST,
    COQ_Z_Z,
    COQ_LIST_Z,
    COQ_LIST_LIST
};

enum SMT_PROOF_ENV{
    GLOBAL_ENV = 1,
    THEORY_ENV,
    THEORY_LIA_ENV
};

typedef struct {
    int int8_max;
    int int16_max;
    int int32_max;
    int int64_max;
} MaxTable;

typedef struct {
    Hash_Table* purify_table; // purify产生的变量xi对应的命题编号，初始为-1，set完对应命题后为对应命题编号
    Hash_Table* local_table; // theory求解时推导得出的命题对应的编号，从1到local_num,在theory求解返回时清空
    Hash_Table* clause_table; //存储resol使用的所有clause的coq证明中的编号
    MaxTable* mt;
    int* assign;   //sat每次求解给出的赋值
    enum SMT_PROOF_ENV env;
    int atom_num; //原子命题数量（包括purify产生的）
    int new_cl_num; //theory学习产生的子句数量
    int local_num; //theroy求解过程中推导得出的局部命题数量 
    int resol_num; // resolution产生的命题数量
    int purify_num; //purify新增的命题数量
} PropTable;

PropTable* initPropTable();
enum VAR_COQ_TYPE var_type_search(char* v, int type);

//用于打印输出的coq证明
void printCoqProof(SMT_PROOF* proof, FILE* fp);

//返回下一步应该打印的step
int printCoqProofStep(SMT_PROOF* proof, PropTable* ptable, FILE* fp, int step_id);

void updata_local_table(ProofTerm* t, Hash_Table* table, int value);
void updata_clause_table(Hash_Table* table, char* hval, int step_id);
char* search_clause_table(Hash_Table* table, int step_id);
#endif