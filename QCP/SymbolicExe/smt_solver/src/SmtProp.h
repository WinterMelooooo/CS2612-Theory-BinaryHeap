#ifndef SMTPROP_H
#define SMTPROP_H 1
#include <stdio.h>
#include<stdlib.h>
#include <stdbool.h>
#include <string.h>

typedef struct UFunction UFunction;
typedef enum SmtPropBop SmtPropBop;
typedef enum SmtPropUop SmtPropUop;
typedef enum SmtPropType SmtPropType;
typedef struct SmtProp SmtProp;

struct UFunction{
    char* name; // 函数名
    int numArgs; // 参数数量
    UFunction** args; // 参数数组
};


typedef struct {
    UFunction* luf;
    UFunction* ruf;
} Atomic_prop;

typedef struct {
    int left1;
    int left2;
    int right;
} Atomic_prop_num;

enum SmtPropBop {
    SMTPROP_AND, SMTPROP_OR, SMTPROP_IMPLY, SMTPROP_IFF
};

enum SmtPropUop {
    SMTPROP_NOT
};

enum SmtPropType {
    SMTB_PROP, SMTU_PROP, SMTAT_PROP, SMTATN_PROP, SMTBOOL_PROP, SMTTF_PROP // 后面四个类型：原子命题(如f(a,b)=c),变量编码后的原子命题(f(1,2)=2),将原子命题抽象成的命题变元，永真式或永假式
};

//定义命题
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
        Atomic_prop *at_prop;
        Atomic_prop_num *atn_prop;
        int propvar; //表示将未解释函数等式抽象成的命题变元对应的编号
        bool TF;       //true表示永真，false表示永假
    } p;
};


#endif