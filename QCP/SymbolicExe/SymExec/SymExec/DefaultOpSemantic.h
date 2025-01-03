#ifndef DEFAULT_OP_SEMANTIC_H
#define DEFAULT_OP_SEMANTIC_H

#include "ExprExec.h"

struct ExprVal * OpSemanticPlus(struct ExprVal * expr1, struct ExprVal * expr2);

struct ExprVal * OpSemanticMinus(struct ExprVal * expr1, struct ExprVal * expr2);

struct ExprVal * OpSemanticMul(struct ExprVal * expr1, struct ExprVal * expr2);

struct ExprVal * OpSemanticDiv(struct ExprVal * expr1, struct ExprVal * expr2);

struct ExprVal * OpSemanticMod(struct ExprVal * expr1, struct ExprVal * expr2);

struct CondExprRet * OpSemanticLt(struct ExprVal * expr1, struct ExprVal * expr2);

struct CondExprRet * OpSemanticGt(struct ExprVal * expr1, struct ExprVal * expr2);

struct CondExprRet * OpSemanticLe(struct ExprVal * expr1, struct ExprVal * expr2);

struct CondExprRet * OpSemanticGe(struct ExprVal * expr1, struct ExprVal * expr2);

struct CondExprRet * OpSemanticEq(struct ExprVal * expr1, struct ExprVal * expr2);

struct CondExprRet * OpSemanticNe(struct ExprVal * expr1, struct ExprVal * expr2);

struct ExprVal * OpSemanticBitand(struct ExprVal * expr1, struct ExprVal * expr2);

struct ExprVal * OpSemanticBitor(struct ExprVal * expr1, struct ExprVal * expr2);

struct ExprVal * OpSemanticXor(struct ExprVal * expr1, struct ExprVal * expr2);

struct ExprVal * OpSemanticShl(struct ExprVal * expr1, struct ExprVal * expr2);

struct ExprVal * OpSemanticShr(struct ExprVal * expr1, struct ExprVal * expr2);

struct CondExprRet * OpSemanticNot(struct ExprVal * expr);

struct ExprVal * OpSemanticBitnot(struct ExprVal * expr);

struct ExprVal * OpSemanticNeg(struct ExprVal * expr);

struct ExprVal * OpSemanticPos(struct ExprVal * expr);

struct ExprVal * OpSemanticI(struct ExprVal * expr, struct environment * env);

struct ExprVal * OpSemanticU8(struct ExprVal * expr, struct environment * env);

struct ExprVal * OpSemanticU16(struct ExprVal * expr, struct environment * env);

struct ExprVal * OpSemanticU32(struct ExprVal * expr, struct environment * env);

struct ExprVal * OpSemanticU64(struct ExprVal * expr, struct environment * env);

struct PropList * SafetyConstraitInt8(struct ExprVal * expr);

struct PropList * SafetyConstraitUInt8(struct ExprVal * expr);

struct PropList * SafetyConstraitInt16(struct ExprVal * expr);

struct PropList * SafetyConstraitUInt16(struct ExprVal * expr);

struct PropList * SafetyConstraitInt32(struct ExprVal * expr);

struct PropList * SafetyConstraitUInt32(struct ExprVal * expr);

struct PropList * SafetyConstraitInt64(struct ExprVal * expr);

struct PropList * SafetyConstraitUInt64(struct ExprVal * expr);

struct PropList * BinPlusSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinPlusSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinPlusSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinPlusSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinPlusSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinPlusSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinPlusSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinPlusSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMinusSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMinusSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMinusSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMinusSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMinusSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMinusSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMinusSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMinusSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMulSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMulSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMulSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMulSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMulSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMulSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMulSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinMulSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinDivSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinDivSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinDivSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinDivSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinDivSafetyConstraitUnsigned(struct ExprVal *expr1, struct ExprVal *expr2);

struct PropList * BinModSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinModSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinModSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinModSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinModSafetyConstraitUnsigned(struct ExprVal *expr1, struct ExprVal *expr2);

struct PropList * BinShlSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShlSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShlSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShlSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShlSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShlSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShlSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShlSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShrSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShrSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShrSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShrSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShrSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShrSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShrSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * BinShrSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2);

struct PropList * UnNegSafetyConstraitInt8(struct ExprVal * expr);

struct PropList * UnNegSafetyConstraitInt16(struct ExprVal * expr);

struct PropList * UnNegSafetyConstraitInt32(struct ExprVal * expr);

struct PropList * UnNegSafetyConstraitInt64(struct ExprVal * expr);

struct PropList * SafetyConstraitNoConstrait(struct ExprVal * expr);

struct PropList * SafetyConstraitNoConstrait2(struct ExprVal * expr1, struct ExprVal * expr2);

#endif // DEFAULT_OP_SEMANTIC_H
