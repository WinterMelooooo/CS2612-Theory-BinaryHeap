#ifndef SEPDEF_INCLUDED
#define SEPDEF_INCLUDED

#include <stdlib.h>
#include "ExprValDef.h"
#include "SimpleCtypeDef.h"

enum SepartionType {
   T_DATA_AT,
   T_UNDEF_DATA_AT,
   T_ARR,
   T_OTHER,
};

struct Separation {
   enum SepartionType t;
   union {
      struct { struct ExprVal * left; struct SimpleCtype * ty; struct ExprVal * right; } DATA_AT;
      struct { struct ExprVal * left; struct SimpleCtype * ty; } UNDEF_DATA_AT;
      struct { struct ExprVal * addr; struct SimpleCtype * ty; struct ExprVal * value; struct ExprVal * size; } ARR;
      struct { int sep_id; struct PolyTypeList * types; struct ExprValList * exprs; } OTHER;
   }d;
};

struct SepList {
   struct Separation * head;
   struct SepList * next;
};

struct Separation * SepDataAt(struct ExprVal * left, struct SimpleCtype * ty, struct ExprVal * right);
struct Separation * SepUndefDataAt(struct ExprVal * left, struct SimpleCtype * ty);
struct Separation * SepArr(struct ExprVal * addr, struct SimpleCtype * ty, struct ExprVal * value, struct ExprVal * size);
struct Separation * SepOther(int ident, struct PolyTypeList * types, struct ExprValList * exprs);
struct SepList* SepListNil();
struct SepList* SepListCons(struct Separation * sep, struct SepList * next);
struct SepList* SepListLink(struct SepList * left, struct SepList * right);
struct SepList* SepListRemove(struct SepList * pos, struct SepList * list);
int SeparationCheckEqual(struct Separation * sep1, struct Separation * sep2);
struct Separation * SepDeepCopy(struct Separation * sep);
struct SepList * SepListDeepCopy(struct SepList * sep_list);
struct Separation * SepSubst(struct Separation * sep, struct ExprVal * pre, struct ExprVal * post);
struct Separation * SepSubstPolyType(struct Separation * sep, struct PolyType * pre, struct PolyType * post);
struct SepList * SepListSubst(struct SepList * sep_list, struct ExprVal * pre, struct ExprVal * post);
struct SepList * SepListSubstPolyType(struct SepList * sep_list, struct PolyType * pre, struct PolyType * post);
struct SepList * FindPosOfAddr(struct SepList * sep_list, struct ExprVal * addr);
void SepFree(struct Separation * sep);
void SepListFree(struct SepList * sep_list);

#endif
