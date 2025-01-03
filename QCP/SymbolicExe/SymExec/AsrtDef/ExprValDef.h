#ifndef EXPRDEF_INCLUDED
#define EXPRDEF_INCLUDED

#include "../Utility/List.h"
#include "SimpleCtypeDef.h"
#include "PolyTypeDef.h"
#include "Constant.h"

struct persistent_env;



enum InnerUnaryOperation{
  Oneg,    // -
  Onint,   // ~
  Onot,    // !
};

enum InnerBinaryOperation {
  Oadd, // +
  Osub, // -
  Omul, // *
  Odiv, // /
  Omod, // %
  Oand, // &
  Oor,  // |
  Oxor, // ^
  Oshl, // <<
  Oshr, // >>
};

enum ExprVal_type {
   EZ_VAL,
   SIZE_OF,
   VFIELD_ADDRESS,
   VUOP,
   VBOP,
   FUNCAPP,
   LINDEX,
   TIME_COST,
};

struct ExprValList;

struct ExprVal {
   enum ExprVal_type t;
   union {
      struct { unsigned long long number; } EZ_VAL;
      struct { struct SimpleCtype * type; } SIZE_OF;
      struct { struct ExprVal * expr; int field_id; } VFIELD_ADDRESS;  // &(expr->field_id)
      struct { enum InnerUnaryOperation op; struct ExprVal * expr; } VUOP;
      struct { enum InnerBinaryOperation op; struct ExprVal * expr1, * expr2; } VBOP;
      struct { int id; struct PolyTypeList * types; struct ExprValList * args; } FUNCAPP; 
      // normal logic variables are seen as unary functions
      struct { struct ExprVal *list; struct ExprVal *index; } LINDEX;
      struct { } TIME_COST;
   }d;
};

struct ExprVal * ExprVal_EZ_VAL(unsigned long long number);
struct ExprVal * ExprVal_V_VARI(int id);
struct ExprVal * ExprVal_SIZE_OF(struct SimpleCtype * type);
struct ExprVal * ExprVal_VFIELD_ADDRESS(struct ExprVal * expr, int field_id);
struct ExprVal * ExprVal_VUOP(enum InnerUnaryOperation op, struct ExprVal * expr);
struct ExprVal * ExprVal_VBOP(enum InnerBinaryOperation op, struct ExprVal * expr1, struct ExprVal * expr2);
struct ExprVal * ExprVal_FUNCAPP(int id, struct PolyTypeList * types, struct ExprValList * args);
struct ExprVal * ExprVal_LINDEX(struct ExprVal *list, struct ExprVal *index);
struct ExprVal * ExprVal_TIME_COST();

int IsBitwiseOperator(enum InnerBinaryOperation op);

int ExprValCheckEqual(struct ExprVal * expr1, struct ExprVal * expr2);

void ExprValFree(struct ExprVal *val);

DECLARE_LIST(ExprValList, struct ExprVal *, data)

int ExprValListCheckEqual(struct ExprValList * list1, struct ExprValList * list2);

struct ExprVal * ExprValDeepCopy(struct ExprVal * val);

struct ExprVal * ExprValSubst(struct ExprVal * expr, struct ExprVal * pre, struct ExprVal * post);
struct ExprValList * ExprValListSubst(struct ExprValList * list, struct ExprVal * pre, struct ExprVal * post);

struct ExprVal * ExprValSubstPolyType(struct ExprVal * expr, struct PolyType * pre, struct PolyType * post);
struct ExprValList * ExprValListSubstPolyType(struct ExprValList * list, struct PolyType * pre, struct PolyType * post);

struct Constant *ConstantFold(struct ExprVal *expr, struct persistent_env *env);
struct ExprVal *ExprValConstantFold(struct ExprVal *expr, struct persistent_env *env);

struct ExprValList * ExprValListConstantFold(struct ExprValList * list, struct persistent_env * env);

int Used_ExprVal(struct ExprVal *expr, struct ExprVal *goal);
int Used_ExprValList(struct ExprValListNode *list, struct ExprVal *goal);

#endif
