#ifndef __PATTERN_SEP_H__
#define __PATTERN_SEP_H__

#include "PatternExpr.h"
#include "PatternCType.h"
#include "../../AsrtDef/SepDef.h"
#include "../Util/Error.h"
#include <stdlib.h>

enum PatternSepType {
    PATTERN_SEP_DATA_AT,
    PATTERN_SEP_UNDEF,
    PATTERN_SEP_ARR,
    PATTERN_SEP_PRED,
    PATTERN_SEP_PATPRED
};

struct PatternSep;

struct PatternSepDataAt {
    struct PatternExpr * addr;
    struct PatternCType * ty;
    struct PatternExpr * data;
};

struct PatternSepUndefDataAt {
    struct PatternExpr * addr;
    struct PatternCType * ty;
};

struct PatternSepArr {
    struct PatternExpr * addr;
    struct PatternCType * ty;
    struct PatternExpr * val;
    struct PatternExpr * size;
};

struct PatternSepPred {
    int id;
    char * name;
    struct PatternPolyTypeList * types;
    struct PatternExprList * args;
};

struct PatternSepPatPred {
    char * var;
    struct PatternExprList * args;
};

struct PatternSep {
    enum PatternSepType ty;
    union {
        struct PatternSepDataAt * data_at;
        struct PatternSepUndefDataAt * undef_data_at;
        struct PatternSepArr * arr;
        struct PatternSepPred * pred;
        struct PatternSepPatPred * ppred;
    } data;
};

struct PatternSepList {
    struct PatternSep * head;
    struct PatternSepList * next;
};

struct PatternSepLList {
    int ty; // 0 for &&, 1 for ||
    struct PatternSepList * head;
    struct PatternSepLList * next;
};

struct PatternSep * initPatternSepDataAt(struct PatternExpr * addr, struct PatternCType * ty, struct PatternExpr * data);
struct PatternSep * initPatternSepUndefDataAt(struct PatternExpr * addr, struct PatternCType * ty);
struct PatternSep * initPatternSepArr(struct PatternExpr * addr, struct PatternCType * ty, struct PatternExpr * val, struct PatternExpr * size);
struct PatternSep * initPatternSepPred(char * name, struct PatternPolyTypeList * types, struct PatternExprList * args);
struct PatternSep * initPatternSepPatPred(char * var, struct PatternExprList * args);

struct PatternSepList * initPatternSepList(struct PatternSep * head, struct PatternSepList * next);
struct PatternSepLList * initPatternSepLList(int ty, struct PatternSepList * head, struct PatternSepLList * next);
void finiPatternSepList(struct PatternSepList * sl);
void finiPatternSepLList(struct PatternSepLList * sll);

void finiPatternSep(struct PatternSep * sep);

struct PatternSep * PatternSepDeepCopy(struct PatternSep * sep);
struct PatternSepList * PatternSepListDeepCopy(struct PatternSepList * sl);
struct PatternSepLList * PatternSepLListDeepCopy(struct PatternSepLList * sll);

int PatternSepEqual(struct PatternSep * sep1, struct PatternSep * sep2);
int PatternSepListEqual(struct PatternSepList * sl1, struct PatternSepList * sl2);
int PatternSepLListEqual(struct PatternSepLList * sll1, struct PatternSepLList * sll2);

int PatternSepListFind(struct PatternSepList * sl, struct PatternSep * sep);
int PatternSepLListFind(struct PatternSepLList * sll, struct PatternSepList * sep);

struct PatternSepList * PatternSepListErase(struct PatternSepList * sl, struct PatternSep * sep);
struct PatternSepLList * PatternSepLListErase(struct PatternSepLList * sll, struct PatternSepList * sep);

#endif