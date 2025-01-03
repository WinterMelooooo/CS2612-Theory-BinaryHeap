#ifndef PROOF_LANG_H
#define PROOF_LANG_H 1
#include "hashtable.h"
#include "smt_lang.h"

typedef enum ProofRule ProofRule;
typedef enum TermType TermType;
typedef enum ValType ValType;
typedef enum ArgType ArgType;
typedef struct ProofTerm ProofTerm;
typedef struct ProofNode ProofNode;
typedef struct ArgTerm ArgTerm;
typedef struct UfMap UfMap;
typedef struct ProoffVal ProofVal;
typedef struct ProofData ProofData;
typedef struct val_linklist val_linklist;

enum ArgType
{
    NUM,    //既可以表示变量xi也可以表示node_number
    PTERM,
    B_FUNC, // 内置函数名
    N_FUNC  // 普通n元函数名
};

enum ProofRule
{   
    DECLARE,
    ASSUME,
    SCOPE,
    TF_SIMPLIFY,  //concl 为true，false或者不带true和false的命题
    SET_VAR,
    SET_PROP,
    SET_PROP_IFF,
    SUB_VAR,
    SUB_PROP,
    SUB_PROP_IFF,
    CNF_TRANS, // p<-> p1 op p2 |-- cnf 
    EQUALITY_RESOLUTION, // P P=P1 |- P1
    RESOLUTION,       // Boolean – Resolution
    //CHAIN_RESOLUTION, // Boolean – N-ary Resolution
    IMPLIES_ELIM,
    AND_ELIM,
    NOT_AND, // Boolean – De Morgan – Not And
    NOT_ELIM, //消去双重否定
    REFL,    // Equality – Reflexivity
    SYMM,    // Equality – Symmetry
    TRANS,   // Equality – Transitivity
    // HO_APP_ENCODE, //curryfy
    CONG,
    FUNC_REWRITE, // f(a) b=a |-- f(b), f可以是not，and这类函数
    ARITH_FME,          /* P1 P2 | t
                            ——————————
                                P
                        P1中t的符号为正，P2中t的符号为负，P1，P2，P均具有a1x1+a2x2+..+anxn <= c , 此规则消去了变量t得到了新的不等式
                        若P中不含有变量，则比较<=号两边数字是否是<=关系，若不是，则P为fasle
                        */
    ARITH_EQ_ELIM,      /* P1 P2 | t
                         ——————————
                             P
                     P1具有a0+a1x1+a2x2+..+anxn = 0, P2是等式或者不等式, 此规则消去了P2中的变量t得到了新的不等式
                     若P或P2中不含有变量，则P = P2
                     */
    ARITH_FALSE,        // 只包含常数项的等式或不等式可以直接推出false的情况
    ARITH_NOT_ELIM,     // not(a-b + 1 <= 0) |—— -a+b <= 0
    ARITH_EQ_INTRO,     // a-b <= 0 -a+b<=0 |— a=b  (arg : a, b)
    //ARITH_INT_DISCRETE, // a1x1+a2x2+..+anxn < c |— a1x1+a2x2+..+anxn  <= c-1
    ARITH_TRANS,        // 算术等式不等式恒等变换（移项）
    LIA_TRANS,       //树结构的lia命题转为n元函数FUNC_LE0
    UF_CONTRA_FALSE
};

enum TermType
{
    // :bool
    FUNC_AND,   // n-ary
    FUNC_OR,    // n-ary
    FUNC_IMPLY, // Binary
    FUNC_IFF,   // Binary
    FUNC_NOT,   // Unary
    FUNC_EQ,    // Binary
    FUNC_LE,    // Binary
    FUNC_LT,    // Binary
    FUNC_GE,    // Binary
    FUNC_GT,    // Binary
    FUNC_EQ0,   // n-ary
    FUNC_LE0,   // n-ary
    PROP_VAR,   // 0-ary
     // :int
    FUNC_ADD,   // Binary
    FUNC_MINUS, // Binary
    FUNC_MULT,  // Binary
    FUNC_DIV,   // Binary
    FUNC_NEG,   // Unary
    VAR,       // 0-ary
    INT_CONST, // 0-ary
    // : arbitrary
    FUNC_N,  // n-ary
            // other
    PROOFNODE_CONCL,
    PROP_FALSE,
    PROP_TRUE
};

struct ProofTerm
{
    TermType type;
    union
    {
        char *name;
        int const_val;   // 单纯的数字
        int node_number; // proof_concl 的编号 ,命题变元的编号，变量的编号
    } func_name;
    int arg_num;
    ProofTerm **args;
};

struct ArgTerm
{
    ArgType type;
    union
    {
        ProofTerm *pterm;
        int number;
        TermType func_type; // 指前五种内置func和FUNC_UF
        char *func_name;    // FUNC_N
    } args;
};

struct ProofNode
{
    int node_number;
    ProofRule rule;
    int premise_num;
    int arg_num;
    // ProofTerm **premise;
    int *premise_list;
    ArgTerm **args;
    ProofTerm *concl;
};

struct ProofData
{
    int cur_num; // 当前证明结论的数量
    int max_num; // 最多可以存储的证明结论数量，可以动态增长
    int declare_num;
    int declare_max_num;
    // char **var_data;
    Hash_Table *global_table;
    Hash_Table *theory_global_table;
    Hash_Table *local_table; // 存储当前局部证明下已经证明的结论
    ProofNode **node_table;  // 存储结论编号对应的证明步骤，第i个元素表示结论pi的证明步骤
    ProofNode **declare_table; //存储证明开始之前的变量声明
    // Hash_Table *concl_table; // 存储结论对应的node编号，其中key是结论的打印字符串
    //  变量编号对应的uf，而且要区分uf的类型：完整函数，部分函数，单纯的变量
};

struct val_linklist
{
    int val;
    val_linklist *next;
};

typedef struct{
    //0：unsat, 1:sat -1:永真
    //作为singlePropCheck的返回值时，成立返回0,不成立返回-1,无法判断返回1, 当ans=1时没有proof
    int ans;
    Hash_Table* vtable; //存储变量对应的编号
    //sat时不生成证明，下面两个数组均为空
    ProofNode** declare_table; //证明中的变量声明步骤
    ProofNode** proof_table;   //正式证明步骤
    int declare_num;          //变量声明的步骤数
    int proof_num;            //正式证明步骤数
} SMT_PROOF;

void freeSmtProof(SMT_PROOF* proof);
void freeProofData(ProofData* pdata);
// ProofTerm* newProofTerm(TermType type, char* name, int node_number, ProofTerm* arg1, ProofTerm* arg2); //n元函数专门处理
ProofTerm *newFalseTerm();
ProofTerm* newVarTerm(int v);
ProofTerm* newPropVarTerm(int v);
//res = t1 op t2 / res = not t1
ProofTerm* newPropTerm(ProofTerm* t1, ProofTerm* t2, TermType op);
//p > 0 返回 p , p < 0 返回 Not p
ProofTerm* newNotProp(int p);
//res = p1 \/ p2 \/ p3 , 负数表示NOT p， num表示clause中literal的个数，取值为2或3,小于3时p3设置为0
ProofTerm* newOrProp(int p1, int p2, int p3, int num);
// res = t1 /\ t2 /\ t3 /\ t4  num至少为2，只多为4
ProofTerm* newAndProp(ProofTerm* t1, ProofTerm* t2, ProofTerm* t3, ProofTerm* t4, int num);
ProofTerm* newEqProofTerm(int a, int b);
ProofTerm* newEqProofTerm2(ProofTerm* t1, ProofTerm* t2);
ProofNode *newProofNode(int *plist, int node_number, ProofRule rule, ProofTerm *concl, ArgTerm *arg, int premise_num);
ProofNode* newDeclareNode(int num, char* s);
void updata_DeclareData(ProofNode* node, ProofData* pdata);

char *ProofTerm2str(ProofTerm *t);

ProofTerm *copy_ProofTerm(const ProofTerm *t);
void freeProofTerm(ProofTerm *t);
void freeProofNode(ProofNode *node);
// just for test
ProofData *initProofData();
void printProofTerm(ProofTerm *t);
void printProofNode(ProofData *data, ProofNode *node);

int ProofTerm2Num(ProofTerm *t, Hash_Table *table1, Hash_Table *table2);

//用于输出证明的打印函数
void printProofTerm_prefix(ProofTerm* t, FILE* fp);
void printArgTerm(ArgTerm* t, ProofRule rule, FILE* fp);
void printProofNode_formal(ProofNode* node, FILE* fp);
void printSmtProof(SMT_PROOF* proof, FILE* fp);
#endif
