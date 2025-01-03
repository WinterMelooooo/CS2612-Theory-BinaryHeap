#ifndef __PATTERN_POLY_TYPE_H__
#define __PATTERN_POLY_TYPE_H__

#include "../../AsrtDef/AssDef.h"
#include "../Util/Error.h"
#include <stdlib.h>
#include <string.h>

enum PatternPolyTypeType {
    PATTERN_POLY_VAR,  // for pattern variables to match any type
    PATTERN_POLY_APP,
    PATTERN_POLY_ARROW,
    PATTERN_POLY_CONST, // for specific type
    PATTERN_POLY_UNK  // for unification; should not appear after type inference
};

struct PatternPolyType;
struct PatternPolyTypeList;

struct PatternPolyTypeApp {
    char * func;
    struct PatternPolyTypeList * args;
};

struct PatternPolyTypeArrow {
    struct PatternPolyType * left;
    struct PatternPolyType * right;
};

struct PatternPolyType {
    enum PatternPolyTypeType ty;
    union {
        enum PrimitiveType type;
        // for POLY_VAR and POLY_CONST and POLY_UNK
        char * var;
        struct PatternPolyTypeApp * app;
        struct PatternPolyTypeArrow * arrow;
    } data;
};

struct PatternPolyTypeList {
    struct PatternPolyType * head;
    struct PatternPolyTypeList * next;
};

struct PatternPolyType * initPatternPolyTypeConst(char * var);
struct PatternPolyType * initPatternPolyTypeVar(char * var);
struct PatternPolyType * initPatternPolyTypeApp(char * func, struct PatternPolyTypeList * args);
struct PatternPolyType * initPatternPolyTypeArrow(struct PatternPolyType * left, struct PatternPolyType * right);
struct PatternPolyType * initPatternPolyTypeUnk(char * var);
void PatternPolyTypeFree(struct PatternPolyType * t);

struct PatternPolyTypeList * initPatternPolyTypeList(struct PatternPolyType * head, struct PatternPolyTypeList * next);
void PatternPolyTypeListFree(struct PatternPolyTypeList * l);

struct PatternPolyType * PatternPolyTypeDeepCopy(struct PatternPolyType * t);
struct PatternPolyTypeList * PatternPolyTypeListDeepCopy(struct PatternPolyTypeList * l);

int PatternPolyTypeEqual(struct PatternPolyType * t1, struct PatternPolyType * t2);
int PatternPolyTypeListEqual(struct PatternPolyTypeList * l1, struct PatternPolyTypeList * l2);

void PatternPolyTypePrint(FILE * fp, struct PatternPolyType * t);
void PatternPolyTypeListPrint(struct PatternPolyTypeList * l);

/*
 * Format :
 * - POLY_VAR x : "x"
 * - POLY_CONST Z : "Z"
 * - POLY_APP f [t1, t2, ..., tn] : "appn_t1_t2_..._tn"
 * - POLY_ARROW t1 -> t2 : "arrow_t1_t2"
 */
char * PatternPolyTypeToChar(struct PatternPolyType * t);

#endif