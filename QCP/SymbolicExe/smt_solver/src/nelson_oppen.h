#ifndef NELSON_OPPEN
#define NELSON_OPPEN 1
#include "proof_lang.h"
#include "lia_theory.h"
#include "congruence.h"
#include "preprocess.h"
typedef enum var_pair_state var_pair_state;
typedef enum theory_type theory_type;
typedef struct TheoryData TheoryData;
typedef struct CombineData CombineData;
typedef struct lia_list lia_list;
typedef struct uf_list uf_list;

enum var_pair_state
{
    NOT_SHARE_PAIR = 0, // 不是共享变量对
    SHARE_PAIR,         // 共享变量对，但是尚未推出相等关系
    EQ_PAIR             // 已经推出了a=b
};

enum theory_type
{
    LIA_THEORY,
    UF_THEORY
};


struct lia_list
{
    InequList *equ_list;
    InequList *inequ_list;
};

struct uf_list
{
    EquationNode *equ_list;
    EquationNode *inequ_list;
};

struct TheoryData
{
    theory_type type;
    int var_cnt;
    int *value; // value[i] = 0 表示没有变量i， =1表示有变量i
    int prop_cnt;
    SmtProplist *prop_list;
    union
    {
        lia_list *lialist;
        uf_list *uflist;
    } data;
};

struct CombineData
{
    TheoryData *lia_data;
    TheoryData *uf_data;
    int var_cnt;
    int common_cnt; // lia和uf共享的变量数量
    int **var_pair; // 变量对的情况，对应的等式是否已经共享
};

// 初始化theroy_data中的value数组
void var_in_term(TheoryData *tdata, PreData *data, SmtTerm *t);
void var_in_prop(TheoryData *tdata, PreData *data, SmtProp *p);
void var_in_proplist(TheoryData *tdata, PreData *data);

// 将表达式转换成系数数组
int *term_coef_trans(SmtTerm *t, PreData *data);
int *prop_trans_coef(SmtProp *p, PreData *data);
err proplist_trans_coef(SmtProplist *prop_list, PreData *data, int *value, lia_list *list);

// 初始化CombineData
CombineData *initCombineData(PreData *data, int *value);
void freeTheoryData(TheoryData *tdata);
void freeCombineData(CombineData *cdata);
// 将SmtProp转为EquationNode
EquationNode *prop_trans_EquationNode(SmtProp *p, PreData *data);
void proplist_trans_EquationNode(SmtProplist *prop_list, PreData *data, int *value, uf_list *list);

// 在lia的theroy_data中加入新的等式
void add_equation_lia(int vi, int vj, TheoryData *tdata, PreData *data);
// 在uf的theroy_data中加入新的等式
void add_equation_uf(int vi, int vj, TheoryData *tdata);

// lia的可满足性求解，0表示unsat，1表示sat
// value[i] = 1表示命题变元Pi在sat的结果中赋值为true
int theroy_deduction_lia(TheoryData *tdata, PreData *data);

int theroy_deduction_uf(TheoryData *tdata, PreData *data);

// 返回1表示能推出vi=vj，返回0表示不能推出vi=vj
int lia_infer(int vi, int vj, TheoryData *tdata, PreData *data);

// 根据SAT Solver结果判断混合理论是否sat
int nelson_oppen_convex(CombineData *cdata, PreData *data);

void printEquationNode(EquationNode *list, PreData *data);
#endif