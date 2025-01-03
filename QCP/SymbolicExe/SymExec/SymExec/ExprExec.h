#ifndef EXPREXEC_INCLUDED
#define EXPREXEC_INCLUDED

#include "../AsrtDef/AssDef.h"
#include "../AsrtDef/ExprValDef.h"
#include "../CDef/Cexpr.h"
#include "ExprExecRetTypeDef.h"

// when satisfies constraits, the return value is val
struct CondExprRet {
   struct ExprVal * val;
   struct PropList * constraits;
   struct CondExprRet * next;
};

struct TrueFalseConditionPair {
   struct AsrtList * true_part;
   struct AsrtList * false_part;
   struct Witness * witness;
};

struct CondExprRet * CondExprRetNil();

struct CondExprRet * CondExprRetCons(struct ExprVal * val, struct PropList * constraits, struct CondExprRet * next);

struct CondExprRet * CondExprRetLink(struct CondExprRet * list1, struct CondExprRet * list2);

struct CondExprRet * CondExprRetFree(struct CondExprRet * list);

// arg of SafetyConstrait: the result logic expr, and the type of the result logic expr
struct ExprExecRetType * CondBinaryOpExec(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                        struct CondExprRet * (*OpSemantic)(struct ExprVal *, struct ExprVal *),
                                        struct PropList * (SafetyConstrait)(struct ExprVal *, struct ExprVal *),
                                        struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void *));

struct ExprExecRetType * PtrBinaryOpExecHelper
(struct ExprExecRetType * lret, void * expr_right,
 struct SimpleCtype * type, void *env,
 struct ExprVal * (*OpSemantic)(struct ExprVal *, struct ExprVal *, struct SimpleCtype *),
 struct PropList * (SafetyConstrait)(struct ExprVal *, struct ExprVal *),
 struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*));

struct ExprExecRetType * BinaryOpExecHelper
(struct ExprExecRetType * lret, void * expr_right, void *env,
 struct ExprVal * (*OpSemantic)(struct ExprVal *, struct ExprVal *),
 struct PropList * (SafetyConstrait)(struct ExprVal *, struct ExprVal *),
 struct ExprVal * (*UnsignedOp)(struct ExprVal *, struct environment *),
 struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*));

struct ExprExecRetType * BinaryOpExec(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                      struct ExprVal * (*OpSemantic)(struct ExprVal *, struct ExprVal *),
                                      struct PropList * (SafetyConstrait)(struct ExprVal *, struct ExprVal *),
                                      struct ExprVal * (*UnsignedOp)(struct ExprVal *, struct environment *),
                                      struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void *));

struct ExprExecRetType * ORExecShortCircuit(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void *));

struct ExprExecRetType * ANDExecShortCircuit(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void *));

struct ExprExecRetType * ORExecNoShortCircuit(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void *));

struct ExprExecRetType * ANDExecNoShortCircuit(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void *));

struct ExprExecRetType * UnaryOpExec(struct Assertion * asrt, void * expr, void * env,
                                        struct ExprVal * (*OpSemantic)(struct ExprVal *),
                                        struct PropList * (SafetyConstrait)(struct ExprVal *),
                                        struct ExprVal * (*UnsignedOp)(struct ExprVal *, struct environment *),
                                        struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void *));

struct ExprExecRetType * CondUnaryOpExec(struct Assertion * asrt, void * expr, void * env,
                                        struct CondExprRet * (*OpSemantic)(struct ExprVal *),
                                        struct PropList * (SafetyConstrait)(struct ExprVal *),
                                        struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void *));


#endif // EXPREXEC_INCLUDED