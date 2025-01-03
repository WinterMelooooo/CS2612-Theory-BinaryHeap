#ifndef __VAR_LIST_H__
#define __VAR_LIST_H__

#include <stdlib.h>
#include <string.h>
#include "../PatternASTDef/PatternASTDef.h"

struct VarType {
    char * name;
    struct PatternPolyType * type;
};

struct VarType * initVarType(char * name, struct PatternPolyType * type);
void finiVarType(struct VarType * vt);
struct VarType * VarTypeDeepCopy(struct VarType * vt);

struct VarList {
    struct VarType * head;
    struct VarList * next;
};

struct VarList * initVarList(struct VarType * head, struct VarList * next);
void finiVarList(struct VarList * vl);

int VarListIn(struct VarType * vt, struct VarList * vl);

/*
 * requires: own(vt, t) ** own(vl, l)
 * ensures: own(vt, t) **
 *          (if in(t, l) then own(__return, l) else own(__return, t :: l))
 */
struct VarList * VarListInsert(struct VarType * vt, struct VarList * vl);

/*
 * requires: own(vl1, l1) ** own(vl2, l2)
 * ensures: own(__return, fold(VarListInsert, l2, l1))
 */
struct VarList * VarListMerge(struct VarList * vl1, struct VarList * vl2);

/*
 * requires : own(vl1, l1) ** own(vl2, l2)
 * ensures : own(__return, l1 ++ l2)
 */
struct VarList * VarListApp(struct VarList * vl1, struct VarList * vl2);

/*
 * requires : own(vl1, l1) ** own(vl2, l2)
 * ensures : own(vl1, l1) ** own(vl2, l2) ** own(__return, minus(l1, l2))
 */
struct VarList * VarListMinus(struct VarList * vl1, struct VarList * vl2);

struct VarList * VarListDeepCopy(struct VarList * vl);
void finiVarList(struct VarList * vl);

#endif