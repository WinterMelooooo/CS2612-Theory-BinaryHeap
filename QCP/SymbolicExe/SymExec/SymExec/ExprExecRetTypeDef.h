#ifndef EXPREXEC_RET_TYPE_DEF_INCLUDED
#define EXPREXEC_RET_TYPE_DEF_INCLUDED

#include "../CDef/Cexpr.h"
#include "../AsrtDef/AssDef.h"
#include "./WitnessDef/Witness.h"
#include "../Utility/List.h"

struct ExprExecRetValue {
   struct Assertion * asrt;
   struct ExprVal * val;
   struct PropList * constraits;
   struct IntList * introed_vars;
   struct ExprExecRetValue * next;
};

struct ExprExecRetType {
   struct ExprExecRetValue * ret_value;
   struct Witness * witness;
};

struct ExprExecRetValue * ExprExecRetValueNil();
struct ExprExecRetValue * ExprExecRetValueCons(struct Assertion * asrt, struct ExprVal * val, struct PropList * constraits, struct IntList * vars,  struct ExprExecRetValue * next);
struct ExprExecRetValue * ExprExecRetValueLink(struct ExprExecRetValue * list1, struct ExprExecRetValue * list2);
void ExprExecRetValueFree(struct ExprExecRetValue * ret_value);
struct ExprExecRetType * NewExprExecRetType();

struct ExprExecRetValue * ExprValToBool(struct Assertion * asrt, struct ExprVal * val);
struct ExprExecRetType * ExprExecRetTypeToBool(struct ExprExecRetType * origin);

void ExprExecRetTypeFree(struct ExprExecRetType * ret_type);
int ExprExecRetValueEqual(struct ExprExecRetValue * v1, struct ExprExecRetValue * v2);

struct ExprListExecRetValue {
   struct Assertion * asrt;
   struct ExprValList * val;
   struct PropList * constraits;
   struct IntList * introed_vars;
   struct ExprListExecRetValue * next;
};

struct ExprListExecRetType {
   struct ExprListExecRetValue * ret_value;
   struct Witness * witness;
};

struct ExprListExecRetValue * ExprListExecRetValueNil();
struct ExprListExecRetValue * ExprListExecRetValueCons(struct Assertion * asrt, struct ExprValList * val, struct PropList * constraits, struct IntList * vars,  struct ExprListExecRetValue * next);
struct ExprListExecRetValue * ExprListExecRetValueLink(struct ExprListExecRetValue * list1, struct ExprListExecRetValue * list2);
void ExprListExecRetValueFree(struct ExprListExecRetValue * ret_value);
struct ExprListExecRetType * NewExprListExecRetType();
void ExprListExecRetTypeFree(struct ExprListExecRetType * ret_type);

#endif // EXPREXEC_RET_TYPE_DEF_INCLUDED