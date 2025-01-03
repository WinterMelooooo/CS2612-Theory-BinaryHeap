#ifndef SMT_LANG_H
#define SMT_LANG_H 1
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

typedef struct UFunction UFunction;
typedef struct SmtTerm SmtTerm;
typedef struct SmtProp SmtProp;
typedef struct SmtProplist SmtProplist;
typedef enum SmtTermBop SmtTermBop;
typedef enum SmtTermUop SmtTermUop;
typedef enum SmtTermType SmtTermType;
typedef enum SmtPropBop SmtPropBop;
typedef enum SmtPropUop SmtPropUop;
typedef enum SmtBinPred SmtBinPred;
typedef enum SmtPropType SmtPropType;
typedef enum err err;

enum err {
    OKAY = 0,
    MULT_nia = 1
};

enum SmtTermBop {
    LIA_ADD = 1, LIA_MINUS, LIA_MULT, LIA_DIV
};

enum SmtTermUop {
    LIA_NEG = LIA_DIV + 1
};

enum SmtTermType {
    SMT_LiaBTerm = LIA_NEG+1, //6
    SMT_LiaUTerm,
    SMT_NiaBTerm,
    SMT_UFTerm,
    SMT_ConstNum, 
    SMT_VarNum,
    SMT_VarName  
};

enum SmtPropBop{
    SMTPROP_AND = SMT_VarName+1, //11
    SMTPROP_OR, SMTPROP_IMPLY, SMTPROP_IFF
};

enum SmtPropUop{
    SMTPROP_NOT = SMTPROP_IFF+1  //15
};

enum SmtBinPred{
    SMT_LE = SMTPROP_NOT+1, //16
    SMT_LT, SMT_GE, SMT_GT, SMT_EQ
};

enum SmtPropType {
    SMTB_PROP = SMT_EQ+1, 
    SMTU_PROP, 
    SMTAT_PROP_EQ,
    SMTAT_PROP_LIA,
    SMTAT_PROP_UF_EQ,  
    SMTAT_PROP_LIA_EQ,
    SMTAT_PROP_NIA_EQ,
    SMT_PROPVAR, 
    SMTTF_PROP
};

struct UFunction{
    char* name; // 函数名
    int numArgs; // 参数数量
    SmtTerm** args; // 参数数组
};



struct LIAexpr {
    int varnum;
    int* coef;
};

struct SmtTerm{
    SmtTermType type;
    union {
        struct {
            SmtTermBop op;
            SmtTerm *t1, *t2;
        } BTerm;
        struct {
            SmtTermUop op;
            SmtTerm *t;
        } UTerm;
        int ConstNum;      //同时可以表示变量的编号
        char* Variable; 
        UFunction* UFTerm;
    } term;
};

struct SmtProp {
    SmtPropType type;
    union {
        struct {
            SmtPropBop op;
            SmtProp *prop1, *prop2;
        } Binary_prop;
        struct {
            SmtPropUop op;
            SmtProp *prop1;
        } Unary_prop;
        struct{
            SmtBinPred op;
            SmtTerm* term1, *term2;
        } Atomic_prop;
        int Propvar; //表示将原子命题抽象成的命题变元对应的编号
        bool TF;       //true表示永真，false表示永假
    } prop;
};

struct SmtProplist {
    SmtProp* prop;
    SmtProplist* next;
};

UFunction* newUFunction(char* name, int numArgs, SmtTerm* t1, SmtTerm* t2, SmtTerm* t3);
SmtTerm* newSmtTerm(int nodetype, int op, int number, char* var, UFunction* term, SmtTerm* t1, SmtTerm* t2);
SmtProp* newSmtProp(int nodetype, int op, SmtProp* prop1, SmtProp* prop2, SmtTerm* term1, SmtTerm* term2, bool TF);
UFunction* copy_UFunction(UFunction* uf);
SmtTerm* copy_SmtTerm(SmtTerm* t);
SmtProp* copy_SmtProp(SmtProp* p);
void printUFunction(UFunction* uf);
void printSmtTerm(SmtTerm* t);
void printSmtProp(SmtProp* p);
void printSmtProplist(SmtProplist* p);
void printUFunctionToFile(UFunction* uf, FILE * fp);
void printSmtTermToFile(SmtTerm* t, FILE * fp);
void printSmtPropToFile(SmtProp* p, FILE * fp);
void printSmtProplistToFile(SmtProplist* p, FILE * fp);
//化简prop中的TT和FF
SmtProp* prop_simplify(SmtProp* p);

void freeSmtTerm(SmtTerm* t);
void freeSmtProp(SmtProp* p);
void freeSmtProplist(SmtProplist* p);

//proof生成相关：

//相等返回1，否则返回0
bool SmtTerm_eqb(SmtTerm* t1, SmtTerm* t2);
bool SmtProp_eqb(SmtProp* p1, SmtProp* p2);

void yyerror (char *msg);
int yyparse (void);
#endif