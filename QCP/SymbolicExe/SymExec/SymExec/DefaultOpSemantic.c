#include "DefaultOpSemantic.h"

#ifndef __INTERNAL_INT8_MIN
const long long __INTERNAL_INT8_MIN = -128;
const long long __INTERNAL_INT8_MAX = 127;
const long long __INTERNAL_INT16_MIN = -32768;
const long long __INTERNAL_INT16_MAX = 32767;
const long long __INTERNAL_INT32_MIN = -2147483648;
const long long __INTERNAL_INT32_MAX = 2147483647;
const long long __INTERNAL_INT64_MIN = -9223372036854775807ll - 1;
const long long __INTERNAL_INT64_MAX = 9223372036854775807ll;

const unsigned int __INTERNAL_UINT8_MAX = 255;
const unsigned int __INTERNAL_UINT16_MAX = 65535;
const unsigned int __INTERNAL_UINT32_MAX = 4294967295u;
const unsigned long long __INTERNAL_UINT64_MAX = 18446744073709551615uLL;
#endif


struct ExprVal * OpSemanticPlus(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Oadd, expr1, expr2);
}

struct ExprVal * OpSemanticMinus(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Osub, expr1, expr2);
}

struct ExprVal * OpSemanticMul(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Omul, expr1, expr2);
}

struct ExprVal * OpSemanticDiv(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Odiv, expr1, expr2);
}

struct ExprVal * OpSemanticMod(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Omod, expr1, expr2);
}

struct CondExprRet * OpSemanticLt(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct CondExprRet * res = CondExprRetNil();
   struct Proposition * constrait = PropCompare(PROP_LT, expr1, expr2);
   res = CondExprRetCons(ExprVal_EZ_VAL(1), PropListCons(constrait, PropListNil()), res);
   constrait = PropCompare(PROP_GE, ExprValDeepCopy(expr1), ExprValDeepCopy(expr2));
   res = CondExprRetCons(ExprVal_EZ_VAL(0), PropListCons(constrait, PropListNil()), res);
   return res;
}

struct CondExprRet * OpSemanticGt(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct CondExprRet * res = CondExprRetNil();
   struct Proposition * constrait = PropCompare(PROP_GT, expr1, expr2);
   res = CondExprRetCons(ExprVal_EZ_VAL(1), PropListCons(constrait, PropListNil()), res);
   constrait = PropCompare(PROP_LE, ExprValDeepCopy(expr1), ExprValDeepCopy(expr2));
   res = CondExprRetCons(ExprVal_EZ_VAL(0), PropListCons(constrait, PropListNil()), res);
   return res;
}

struct CondExprRet * OpSemanticLe(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct CondExprRet * res = CondExprRetNil();
   struct Proposition * constrait = PropCompare(PROP_LE, expr1, expr2);
   res = CondExprRetCons(ExprVal_EZ_VAL(1), PropListCons(constrait, PropListNil()), res);
   constrait = PropCompare(PROP_GT, ExprValDeepCopy(expr1), ExprValDeepCopy(expr2));
   res = CondExprRetCons(ExprVal_EZ_VAL(0), PropListCons(constrait, PropListNil()), res);
   return res;
}

struct CondExprRet * OpSemanticGe(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct CondExprRet * res = CondExprRetNil();
   struct Proposition * constrait = PropCompare(PROP_GE, expr1, expr2);
   res = CondExprRetCons(ExprVal_EZ_VAL(1), PropListCons(constrait, PropListNil()), res);
   constrait = PropCompare(PROP_LT, ExprValDeepCopy(expr1), ExprValDeepCopy(expr2));
   res = CondExprRetCons(ExprVal_EZ_VAL(0), PropListCons(constrait, PropListNil()), res);
   return res;
}

struct CondExprRet * OpSemanticEq(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct CondExprRet * res = CondExprRetNil();
   struct Proposition * constrait = PropCompare(PROP_EQ, expr1, expr2);
   res = CondExprRetCons(ExprVal_EZ_VAL(1), PropListCons(constrait, PropListNil()), res);
   constrait = PropCompare(PROP_NEQ, ExprValDeepCopy(expr1), ExprValDeepCopy(expr2));
   res = CondExprRetCons(ExprVal_EZ_VAL(0), PropListCons(constrait, PropListNil()), res);
   return res;
}

struct CondExprRet * OpSemanticNe(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct CondExprRet * res = CondExprRetNil();
   struct Proposition * constrait = PropCompare(PROP_NEQ, expr1, expr2);
   res = CondExprRetCons(ExprVal_EZ_VAL(1), PropListCons(constrait, PropListNil()), res);
   constrait = PropCompare(PROP_EQ, ExprValDeepCopy(expr1), ExprValDeepCopy(expr2));
   res = CondExprRetCons(ExprVal_EZ_VAL(0), PropListCons(constrait, PropListNil()), res);
   return res;
}

struct ExprVal * OpSemanticBitand(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Oand, expr1, expr2);
}

struct ExprVal * OpSemanticBitor(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Oor, expr1, expr2);
}

struct ExprVal * OpSemanticXor(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Oxor, expr1, expr2);
}

struct ExprVal * OpSemanticShl(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Oshl, expr1, expr2);
}

struct ExprVal * OpSemanticShr(struct ExprVal * expr1, struct ExprVal * expr2) {
   return ExprVal_VBOP(Oshr, expr1, expr2);
}

struct CondExprRet * OpSemanticNot(struct ExprVal * expr) {
   struct CondExprRet * res = CondExprRetNil();
   struct Proposition * constrait = PropCompare(PROP_EQ, expr, ExprVal_EZ_VAL(0));
   res = CondExprRetCons(ExprVal_EZ_VAL(1), PropListCons(constrait, PropListNil()), res);
   constrait = PropCompare(PROP_NEQ, ExprValDeepCopy(expr), ExprVal_EZ_VAL(0));
   res = CondExprRetCons(ExprVal_EZ_VAL(0), PropListCons(constrait, PropListNil()), res);
   return res;
}

struct ExprVal * OpSemanticBitnot(struct ExprVal * expr) {
   return ExprVal_VUOP(Onint, expr);
}

struct ExprVal * OpSemanticNeg(struct ExprVal * expr) {
   return ExprVal_VUOP(Oneg, expr);
}

struct ExprVal * OpSemanticPos(struct ExprVal * expr) {
   return expr;
}

struct ExprVal * OpSemanticI(struct ExprVal * expr, struct environment * env) {
  return expr;
}

struct ExprVal * OpSemanticU8(struct ExprVal * expr, struct environment * env) {
  struct Constant * c = ConstantFold(expr, &env->persist);
  if (c != NULL && c->pos) {
    struct Constant * c1 = Constant_number(__INTERNAL_UINT8_MAX);
    if (ConstantAbsCompare(c, c1) <= 0) {
      ConstantFree(c1);
      ConstantFree(c);
      return expr;
    }
    ConstantFree(c1);
  }
  ConstantFree(c);
  return ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(),
                         ExprValListCons(expr, ExprValListCons(ExprVal_EZ_VAL(8), ExprValListNil())));
}

struct ExprVal * OpSemanticU16(struct ExprVal * expr, struct environment * env) {
  struct Constant * c = ConstantFold(expr, &env->persist);
  if (c != NULL && c->pos) {
    struct Constant * c1 = Constant_number(__INTERNAL_UINT16_MAX);
    if (ConstantAbsCompare(c, c1) <= 0) {
      ConstantFree(c1);
      ConstantFree(c);
      return expr;
    }
    ConstantFree(c1);
  }
  ConstantFree(c);
  return ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(),
                         ExprValListCons(expr, ExprValListCons(ExprVal_EZ_VAL(16), ExprValListNil())));
}

struct ExprVal * OpSemanticU32(struct ExprVal * expr, struct environment * env) {
  struct Constant * c = ConstantFold(expr, &env->persist);
  if (c != NULL && c->pos) {
    struct Constant * c1 = Constant_number(__INTERNAL_UINT32_MAX);
    // printf("\n The constant is ");
    // ConstantPrint(c);
    if (ConstantAbsCompare(c, c1) <= 0) {
      ConstantFree(c1);
      ConstantFree(c);
      return expr;
    }
    ConstantFree(c1);
  }
  return ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(),
                         ExprValListCons(expr, ExprValListCons(ExprVal_EZ_VAL(32), ExprValListNil())));
}

struct ExprVal * OpSemanticU64(struct ExprVal * expr, struct environment * env) {
  struct Constant * c = ConstantFold(expr, &env->persist);
  if (c != NULL && c->pos) {
    struct Constant * c1 = Constant_number(__INTERNAL_UINT64_MAX);
    if (ConstantAbsCompare(c, c1) <= 0) {
      ConstantFree(c1);
      ConstantFree(c);
      return expr;
    }
    ConstantFree(c1);
  }
  return ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(),
                         ExprValListCons(expr, ExprValListCons(ExprVal_EZ_VAL(64), ExprValListNil())));
}

struct PropList * SafetyConstraitInt8(struct ExprVal * expr) {
   struct PropList * res;
   struct Proposition * constrait = PropCompare(PROP_LE, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT8_MIN)), expr);
   res = PropListCons(constrait, PropListNil());
   constrait = PropCompare(PROP_LE, ExprValDeepCopy(expr), ExprVal_EZ_VAL(__INTERNAL_INT8_MAX));
   res = PropListCons(constrait, res);
   return res;
}

struct PropList * SafetyConstraitUInt8(struct ExprVal * expr) {
   return PropListNil();
}

struct PropList * SafetyConstraitInt16(struct ExprVal * expr) {
   struct PropList * res;
   struct Proposition * constrait = PropCompare(PROP_LE, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT16_MIN)), expr);
   res = PropListCons(constrait, PropListNil());
   constrait = PropCompare(PROP_LE, ExprValDeepCopy(expr), ExprVal_EZ_VAL(__INTERNAL_INT16_MAX));
   res = PropListCons(constrait, res);
   return res;
}

struct PropList * SafetyConstraitUInt16(struct ExprVal * expr) {
   return PropListNil();
}

struct PropList * SafetyConstraitInt32(struct ExprVal * expr) {
   struct PropList * res;
   struct Proposition * constrait = PropCompare(PROP_LE, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT32_MIN)), expr);
   res = PropListCons(constrait, PropListNil());
   constrait = PropCompare(PROP_LE, ExprValDeepCopy(expr), ExprVal_EZ_VAL(__INTERNAL_INT32_MAX));
   res = PropListCons(constrait, res);
   return res;
}

struct PropList * SafetyConstraitUInt32(struct ExprVal * expr) {
   return PropListNil();
}

struct PropList * SafetyConstraitInt64(struct ExprVal * expr) {
   struct PropList * res;
   struct Proposition * constrait = PropCompare(PROP_LE, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(9223372036854775808llu)), expr);
   res = PropListCons(constrait, PropListNil());
   constrait = PropCompare(PROP_LE, ExprValDeepCopy(expr), ExprVal_EZ_VAL(__INTERNAL_INT64_MAX));
   res = PropListCons(constrait, res);
   return res;
}

struct PropList * SafetyConstraitUInt64(struct ExprVal * expr) {
   return PropListNil();
}

struct PropList * BinPlusSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt8(OpSemanticPlus(expr1, expr2));
}

struct PropList * BinPlusSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt8(OpSemanticPlus(expr1, expr2));
}

struct PropList * BinPlusSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt16(OpSemanticPlus(expr1, expr2));
}

struct PropList * BinPlusSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt16(OpSemanticPlus(expr1, expr2));
}

struct PropList * BinPlusSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt32(OpSemanticPlus(expr1, expr2));
}

struct PropList * BinPlusSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt32(OpSemanticPlus(expr1, expr2));
}

struct PropList * BinPlusSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt64(OpSemanticPlus(expr1, expr2));
}

struct PropList * BinPlusSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt64(OpSemanticPlus(expr1, expr2));
}

struct PropList * BinMinusSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt8(OpSemanticMinus(expr1, expr2));
}

struct PropList * BinMinusSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt8(OpSemanticMinus(expr1, expr2));
}

struct PropList * BinMinusSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt16(OpSemanticMinus(expr1, expr2));
}

struct PropList * BinMinusSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt16(OpSemanticMinus(expr1, expr2));
}

struct PropList * BinMinusSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt32(OpSemanticMinus(expr1, expr2));
}

struct PropList * BinMinusSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt32(OpSemanticMinus(expr1, expr2));
}

struct PropList * BinMinusSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt64(OpSemanticMinus(expr1, expr2));
}

struct PropList * BinMinusSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt64(OpSemanticMinus(expr1, expr2));
}

struct PropList * BinMulSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt8(OpSemanticMul(expr1, expr2));
}

struct PropList * BinMulSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt8(OpSemanticMul(expr1, expr2));
}

struct PropList * BinMulSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt16(OpSemanticMul(expr1, expr2));
}

struct PropList * BinMulSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt16(OpSemanticMul(expr1, expr2));
}

struct PropList * BinMulSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt32(OpSemanticMul(expr1, expr2));
}

struct PropList * BinMulSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt32(OpSemanticMul(expr1, expr2));
}

struct PropList * BinMulSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitInt64(OpSemanticMul(expr1, expr2));
}

struct PropList * BinMulSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   return SafetyConstraitUInt64(OpSemanticMul(expr1, expr2));
}

struct PropList * BinDivSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res;
   struct Proposition * constrait = PropCompare(PROP_NEQ, expr2, ExprVal_EZ_VAL(0));
   res = PropListCons(constrait, PropListNil());
   constrait = PropBinary(PROP_OR, 
                          PropCompare(PROP_NEQ, ExprValDeepCopy(expr1), ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT8_MIN))), 
                          PropCompare(PROP_NEQ, ExprValDeepCopy(expr2), ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(1))));
   res = PropListCons(constrait, res);
   return res;
}

struct PropList * BinDivSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res;
   struct Proposition * constrait = PropCompare(PROP_NEQ, expr2, ExprVal_EZ_VAL(0));
   res = PropListCons(constrait, PropListNil());
   constrait = PropBinary(PROP_OR, 
                          PropCompare(PROP_NEQ, ExprValDeepCopy(expr1), ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT16_MIN))), 
                          PropCompare(PROP_NEQ, ExprValDeepCopy(expr2), ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(1))));
   res = PropListCons(constrait, res);
   return res;
}

struct PropList * BinDivSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res;
   struct Proposition * constrait = PropCompare(PROP_NEQ, expr2, ExprVal_EZ_VAL(0));
   res = PropListCons(constrait, PropListNil());
   constrait = PropBinary(PROP_OR, 
                          PropCompare(PROP_NEQ, ExprValDeepCopy(expr1), ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT32_MIN))),
                          PropCompare(PROP_NEQ, ExprValDeepCopy(expr2), ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(1))));
   res = PropListCons(constrait, res);
   return res;
}

struct PropList * BinDivSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res;
   struct Proposition * constrait = PropCompare(PROP_NEQ, expr2, ExprVal_EZ_VAL(0));
   res = PropListCons(constrait, PropListNil());
   constrait = PropBinary(PROP_OR, 
                          PropCompare(PROP_NEQ, ExprValDeepCopy(expr1), ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(9223372036854775808ull))), 
                          PropCompare(PROP_NEQ, ExprValDeepCopy(expr2), ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(1))));
   res = PropListCons(constrait, res);
   return res;
}

struct PropList * BinDivSafetyConstraitUnsigned(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct Proposition * constrait = PropCompare(PROP_NEQ, expr2, ExprVal_EZ_VAL(0));
   ExprValFree(expr1);
   return PropListCons(constrait, PropListNil());
}

struct PropList * BinModSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   return BinDivSafetyConstraitInt8(expr1, expr2);
}

struct PropList * BinModSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   return BinDivSafetyConstraitInt16(expr1, expr2);
}

struct PropList * BinModSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   return BinDivSafetyConstraitInt32(expr1, expr2);
}

struct PropList * BinModSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   return BinDivSafetyConstraitInt64(expr1, expr2);
}

struct PropList * BinModSafetyConstraitUnsigned(struct ExprVal * expr1, struct ExprVal * expr2) {
   return BinDivSafetyConstraitUnsigned(expr1, expr2);
}

struct PropList * BinShlSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprValDeepCopy(expr2), ExprVal_EZ_VAL(7)), res);
   struct ExprVal * val = ExprVal_VBOP(Omul, expr1, 
                                       ExprVal_FUNCAPP(BUILTINVALUE_ZPOW, PolyTypeListNil(), 
                                                       ExprValListCons(ExprVal_EZ_VAL(2), 
                                                            ExprValListCons(expr2, ExprValListNil()))));
   res = PropListCons(PropCompare(PROP_LE, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT8_MIN)), ExprValDeepCopy(val)), res);
   res = PropListCons(PropCompare(PROP_LE, val, ExprVal_EZ_VAL(__INTERNAL_INT8_MAX)), res);
   return res;
}

struct PropList * BinShlSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprValDeepCopy(expr2), ExprVal_EZ_VAL(15)), res);
   struct ExprVal * val = ExprVal_VBOP(Omul, expr1, 
                                       ExprVal_FUNCAPP(BUILTINVALUE_ZPOW, PolyTypeListNil(), 
                                                       ExprValListCons(ExprVal_EZ_VAL(2), 
                                                            ExprValListCons(expr2, ExprValListNil()))));
   res = PropListCons(PropCompare(PROP_LE, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT16_MIN)), ExprValDeepCopy(val)), res);
   res = PropListCons(PropCompare(PROP_LE, val, ExprVal_EZ_VAL(__INTERNAL_INT16_MAX)), res);
   return res;
}

struct PropList * BinShlSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprValDeepCopy(expr2), ExprVal_EZ_VAL(31)), res);
   struct ExprVal * val = ExprVal_VBOP(Omul, expr1, 
                                       ExprVal_FUNCAPP(BUILTINVALUE_ZPOW, PolyTypeListNil(), 
                                                       ExprValListCons(ExprVal_EZ_VAL(2), 
                                                            ExprValListCons(expr2, ExprValListNil()))));
   res = PropListCons(PropCompare(PROP_LE, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT32_MIN)), ExprValDeepCopy(val)), res);
   res = PropListCons(PropCompare(PROP_LE, val, ExprVal_EZ_VAL(__INTERNAL_INT32_MAX)), res);
   return res;
}

struct PropList * BinShlSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprValDeepCopy(expr2), ExprVal_EZ_VAL(63)), res);
   struct ExprVal * val = ExprVal_VBOP(Omul, expr1, 
                                       ExprVal_FUNCAPP(BUILTINVALUE_ZPOW, PolyTypeListNil(), 
                                                       ExprValListCons(ExprVal_EZ_VAL(2), 
                                                            ExprValListCons(expr2, ExprValListNil()))));
   res = PropListCons(PropCompare(PROP_LE, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(9223372036854775808ull)), ExprValDeepCopy(val)), res);
   res = PropListCons(PropCompare(PROP_LE, val, ExprVal_EZ_VAL(__INTERNAL_INT64_MAX)), res);
   return res;
}

struct PropList * BinShlSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprValDeepCopy(expr2), ExprVal_EZ_VAL(7)), res);
   return res;
}

struct PropList * BinShlSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprValDeepCopy(expr2), ExprVal_EZ_VAL(15)), res);
   return res;
}

struct PropList * BinShlSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprValDeepCopy(expr2), ExprVal_EZ_VAL(31)), res);
   return res;
}

struct PropList * BinShlSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprValDeepCopy(expr2), ExprVal_EZ_VAL(63)), res);
   return res;
}

struct PropList * BinShrSafetyConstraitInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, expr2, ExprVal_EZ_VAL(7)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), expr1), res);
   return res;
}

struct PropList * BinShrSafetyConstraitInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, expr2, ExprVal_EZ_VAL(15)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), expr1), res);
   return res;
}

struct PropList * BinShrSafetyConstraitInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, expr2, ExprVal_EZ_VAL(31)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), expr1), res);
   return res;
}

struct PropList * BinShrSafetyConstraitInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, expr2, ExprVal_EZ_VAL(63)), res);
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), expr1), res);
   return res;
}


struct PropList * BinShrSafetyConstraitUInt8(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, expr2, ExprVal_EZ_VAL(7)), res);
   ExprValFree(expr1);
   return res;
}

struct PropList * BinShrSafetyConstraitUInt16(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, expr2, ExprVal_EZ_VAL(15)), res);
   ExprValFree(expr1);
   return res;
}

struct PropList * BinShrSafetyConstraitUInt32(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, expr2, ExprVal_EZ_VAL(31)), res);
   ExprValFree(expr1);
   return res;
}

struct PropList * BinShrSafetyConstraitUInt64(struct ExprVal * expr1, struct ExprVal * expr2) {
   struct PropList * res = PropListNil();
   res = PropListCons(PropCompare(PROP_LE, ExprVal_EZ_VAL(0), ExprValDeepCopy(expr2)), res);
   res = PropListCons(PropCompare(PROP_LE, expr2, ExprVal_EZ_VAL(63)), res);
   ExprValFree(expr1);
   return res;
}

struct PropList * UnNegSafetyConstraitInt8(struct ExprVal * expr) {
   return PropListCons(PropCompare(PROP_NEQ, expr, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT8_MIN))), PropListNil());
}

struct PropList * UnNegSafetyConstraitInt16(struct ExprVal * expr) {
   return PropListCons(PropCompare(PROP_NEQ, expr, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT16_MIN))), PropListNil());
}

struct PropList * UnNegSafetyConstraitInt32(struct ExprVal * expr) {
   return PropListCons(PropCompare(PROP_NEQ, expr, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(-__INTERNAL_INT32_MIN))), PropListNil());
}

struct PropList * UnNegSafetyConstraitInt64(struct ExprVal * expr) {
   return PropListCons(PropCompare(PROP_NEQ, expr, ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(9223372036854775808ull))), PropListNil());
}

struct PropList * SafetyConstraitNoConstrait(struct ExprVal * expr) {
   ExprValFree(expr);
   return NULL;
}

struct PropList * SafetyConstraitNoConstrait2(struct ExprVal * expr1, struct ExprVal * expr2) {
   ExprValFree(expr1);
   ExprValFree(expr2);
   return NULL;
}