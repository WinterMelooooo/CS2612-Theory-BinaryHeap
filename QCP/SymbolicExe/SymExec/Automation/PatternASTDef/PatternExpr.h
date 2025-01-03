#ifndef __PATTERN_EXPR_H__
#define __PATTERN_EXPR_H__

#include "../../AsrtDef/AssDef.h"
#include "../Util/Error.h"
#include "PatternPolyType.h"
#include "PatternCType.h"
#include <stdlib.h>
#include <string.h>

enum PatternExprType {
    PATTERN_EXPR_CONST,
    PATTERN_EXPR_VAR,
    PATTERN_EXPR_EVAR, // for existential var only
    PATTERN_EXPR_SVAR, // for "single context var" only
    PATTERN_EXPR_GVAR, // for global var only
    PATTERN_EXPR_FIELD,
    PATTERN_EXPR_BINOP,
    PATTERN_EXPR_UNOP,
    PATTERN_EXPR_ARRIDX,
    PATTERN_EXPR_APP,
    PATTERN_EXPR_PATAPP,
    PATTERN_EXPR_SIZEOF
};

struct PatternExpr;
struct PatternExprList;

struct PatternExprField {
    struct PatternExpr * expr;
    char * struct_name;
    char * field_name;
};

struct PatternExprBinop {
    enum InnerBinaryOperation op;
    struct PatternExpr * left;
    struct PatternExpr * right;
};

struct PatternExprUnop {
    enum InnerUnaryOperation op;
    struct PatternExpr * expr;
};

struct PatternExprArridx {
    struct PatternExpr * array;
    struct PatternExpr * index;
};

struct PatternExprApp {
    int id;
    char * func;
    struct PatternPolyTypeList * type_list;
    struct PatternExprList * expr_list;
};

struct PatternExprPatApp {
    char * var;
    struct PatternExprList * expr_list;
};

struct PatternExpr {
    enum PatternExprType ty;
    union {
        // for CONST
        unsigned long long num;
        // for VAR || EVAR || SVAR || GVAR
        char * var;
        // for FIELD
        struct PatternExprField * field;
        // for BINOP
        struct PatternExprBinop * binop;
        // for UNOP
        struct PatternExprUnop * unop;
        // for ARRIDX
        struct PatternExprArridx * arridx;
        // for APP
        struct PatternExprApp * app;
        // for PATAPP
        struct PatternExprPatApp * papp;
        // for SIZEOF
        struct PatternCType * sizeof_expr;
    } data;
};

struct PatternExprList {
    struct PatternExpr * expr;
    struct PatternExprList * next;
};

struct PatternExpr * initPatternExprConst(unsigned long long num);
struct PatternExpr * initPatternExprVar(char * var);
struct PatternExpr * initPatternExprEVar(char * var);
struct PatternExpr * initPatternExprAtomVar(char * var);
struct PatternExpr * initPatternExprGlobalVar(char * var);
struct PatternExpr * initPatternExprField(struct PatternExpr * expr, char * struct_name, char * field_name);
struct PatternExpr * initPatternExprBinop(enum InnerBinaryOperation op, struct PatternExpr * left, struct PatternExpr * right);
struct PatternExpr * initPatternExprUnop(enum InnerUnaryOperation op, struct PatternExpr * expr);
struct PatternExpr * initPatternExprArridx(struct PatternExpr * array, struct PatternExpr * index);
struct PatternExpr * initPatternExprApp(char * func, struct PatternPolyTypeList * type_list, struct PatternExprList * expr_list);
struct PatternExpr * initPatternExprPatApp(char * var, struct PatternExprList * expr_list);
struct PatternExpr * initPatternExprSizeof(struct PatternCType * sizeof_expr);
void finiPatternExpr(struct PatternExpr * expr);

struct PatternExprList * initPatternExprList(struct PatternExpr * expr, struct PatternExprList * next);
void finiPatternExprList(struct PatternExprList * head);

struct PatternExpr * PatternExprDeepCopy(struct PatternExpr * expr);
struct PatternExprList * PatternExprListDeepCopy(struct PatternExprList * expr_list);

int PatternExprEqual(struct PatternExpr * expr1, struct PatternExpr * expr2);
int PatternExprListEqual(struct PatternExprList * expr_list1, struct PatternExprList * expr_list2);

#endif