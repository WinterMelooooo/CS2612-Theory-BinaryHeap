#ifndef CEXPREXEC_INCLUDED
#define CEXPREXEC_INCLUDED

#include "../../compiler/env.h"
#include "../CDef/Cexpr.h"
#include "../AsrtDef/AssDef.h"
#include "ExprExecRetTypeDef.h"
#include "WitnessDef/Witness.h"
#include "../AsrtDef/SimpleCtypeDef.h"

struct AsrtList *DiscardFalseBranch(struct AsrtList *asrt, struct environment *env, struct Witness *witness);

struct Assertion * TryFold(struct Assertion * asrt, struct environment * env);

struct TrueFalseConditionPair CondExec(struct Assertion * asrt, struct Cexpr * condition, struct environment * env);

struct TrueFalseConditionPair AsrtListCondExec(struct AsrtList * asrt_list, struct Cexpr * condition, struct environment * env);

struct ExprExecRetType * ExprExecLeftValue(struct Assertion * asrt, struct Cexpr * expr, struct environment * env);

struct ExprExecRetType * ExprExecRightValue(struct Assertion * asrt, struct Cexpr * expr, struct environment * env);

struct ExprListExecRetType * ExprListExecRightValue(struct Assertion * asrt, struct CexprList * exprs, struct environment * env);

struct ExprExecRetType * AsrtListExprExecRightValue(struct AsrtList * asrt, struct Cexpr * expr, struct environment * env);

struct ExprExecRetType * AsrtListExprExecLeftValue(struct AsrtList * asrt_list, struct Cexpr * expr, struct environment * env);

int cast_from_low_to_high(struct SimpleCtype *from, struct SimpleCtype *to, struct Constant *c);

void GetBinarySemantics
(enum BinOpType op,
 struct SimpleCtype *expr_type, struct SimpleCtype *expr1_type, struct SimpleCtype *expr2_type,
 struct environment *env,
 struct ExprVal * (**OpSemantic)(struct ExprVal *, struct ExprVal *),
 struct ExprVal * (**PtrOpSemantic)(struct ExprVal *, struct ExprVal *, struct SimpleCtype *),
 struct PropList *(**SafetyConstrait)(struct ExprVal *, struct ExprVal *),
 struct ExprVal *(**UnsignedOp)(struct ExprVal *, struct environment *));

struct ExprExecRetType * DerefExecOne(struct ExprExecRetValue *inside, struct SimpleCtype * type, struct environment * env);

#endif // CEXPREXEC_INCLUDED
