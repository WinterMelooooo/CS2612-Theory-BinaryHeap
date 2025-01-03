#ifndef __PATTERN_PROP_H__
#define __PATTERN_PROP_H__

#include "PatternExpr.h"
#include "../../AsrtDef/PropDef.h"
#include "../Util/Error.h"
#include "PatternPolyType.h"
#include <stdlib.h>

enum PatternPropType {
    PATTERN_PROP_TRUE,
    PATTERN_PROP_FALSE,
    PATTERN_PROP_UNOP,
    PATTERN_PROP_BINOP,
    PATTERN_PROP_PTR,
    PATTERN_PROP_COMPARE,
    PATTERN_PROP_PRED,
    PATTERN_PROP_PATPRED
};

struct PatternProp;

struct PatternPropUnop {
    enum PropUOP op;
    struct PatternProp * prop;
};

struct PatternPropBinop {
    enum PropBinOP op;
    struct PatternProp * left;
    struct PatternProp * right;
};

struct PatternPropPtr {
    enum PropPtrOP op;
    struct PatternExpr * expr;
};

struct PatternPropCompare {
    enum PropCompOp op;
    struct PatternExpr * left;
    struct PatternExpr * right;
};

struct PatternPropPred {
    int id;
    char * name;
    struct PatternPolyTypeList * types;
    struct PatternExprList * args;
};

struct PatternPropPatPred {
    char * var;
    struct PatternExprList * args;
};

struct PatternProp {
    enum PatternPropType ty;
    union {
        struct PatternPropUnop * unop;
        struct PatternPropBinop * binop;
        struct PatternPropPtr * ptr;
        struct PatternPropCompare * comp;
        struct PatternPropPred * pred;
        struct PatternPropPatPred * ppred;
    } data;
};

struct PatternPropList { 
    struct PatternProp * head;
    struct PatternPropList * next;
};

struct PatternPropLList {
    int ty; // 0 for &&, 1 for ||
    struct PatternPropList * head;
    struct PatternPropLList * next;
};

struct PatternProp * initPatternPropTrue();
struct PatternProp * initPatternPropFalse();
struct PatternProp * initPatternPropUnop(enum PropUOP op, struct PatternProp * prop);
struct PatternProp * initPatternPropBinop(enum PropBinOP op, struct PatternProp * left, struct PatternProp * right);
struct PatternProp * initPatternPropPtr(enum PropPtrOP op, struct PatternExpr * expr);
struct PatternProp * initPatternPropComp(enum PropCompOp op, struct PatternExpr * left, struct PatternExpr * right);
struct PatternProp * initPatternPropPred(char * name, struct PatternPolyTypeList * types, struct PatternExprList * args);
struct PatternProp * initPatternPropPatPred(char * var, struct PatternExprList * args);

struct PatternPropList * initPatternPropList(struct PatternProp * head, struct PatternPropList * next);
struct PatternPropLList * initPatternPropLList(int ty, struct PatternPropList * head, struct PatternPropLList * next);

void finiPatternProp(struct PatternProp * prop);
void finiPatternPropList(struct PatternPropList * list);
void finiPatternPropLList(struct PatternPropLList * list);

struct PatternProp * PatternPropDeepCopy(struct PatternProp * prop);
struct PatternPropList * PatternPropListDeepCopy(struct PatternPropList * list);
struct PatternPropLList * PatternPropLListDeepCopy(struct PatternPropLList * list);

struct PatternPropList * PatternPropListApp(struct PatternPropList * l1, struct PatternPropList * l2);
struct PatternPropLList * PatternPropLListApp(struct PatternPropLList * l1, struct PatternPropLList * l2);

int PatternPropEqual(struct PatternProp * p1, struct PatternProp * p2);
int PatternPropListEqual(struct PatternPropList * l1, struct PatternPropList * l2);
int PatternPropLListEqual(struct PatternPropLList * l1, struct PatternPropLList * l2);

int PatternPropListFind(struct PatternPropList * list, struct PatternProp * prop);
int PatternPropLListFind(struct PatternPropLList * list, struct PatternPropList * prop);

struct PatternPropList * PatternPropListErase(struct PatternPropList * list, struct PatternProp * prop);
struct PatternPropLList * PatternPropLListErase(struct PatternPropLList * list, struct PatternPropList * prop);

#endif