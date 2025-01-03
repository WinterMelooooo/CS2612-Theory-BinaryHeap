#include "ExprExec.h"
#include "../Utility/List.h"
#include "../Utility/InnerAsrtPrinter.h"
#include <assert.h>

struct CondExprRet * CondExprRetNil() {
   return NULL;
}

struct CondExprRet * CondExprRetCons(struct ExprVal * val, struct PropList * constraits, struct CondExprRet * next) {
   struct CondExprRet * res = (struct CondExprRet *) malloc(sizeof(struct CondExprRet));
   res->val = val;
   res->constraits = constraits;
   res->next = next;
   return res;
}

struct CondExprRet * CondExprRetLink(struct CondExprRet * list1, struct CondExprRet * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct CondExprRet * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}

// val and constraits will not be freed
struct CondExprRet * CondExprRetFree(struct CondExprRet * list) {
   if (list == NULL) return NULL;
   struct CondExprRet * tmp = list->next;
   free(list);
   return CondExprRetFree(tmp);
}

// Attention: Opsemantic and SafetyConstrait will "own" the memory of the input ExprVal
struct ExprExecRetType * CondBinaryOpExec(struct Assertion * asrt, void * expr_left, void * expr_right, void *env,
                                      struct CondExprRet * (*OpSemantic)(struct ExprVal *, struct ExprVal *),
                                      struct PropList * (SafetyConstrait)(struct ExprVal *, struct ExprVal *),
                                      struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
   struct ExprExecRetType * ret;
   struct ExprExecRetType * lret, * rret;
   struct ExprExecRetValue * lside, * rside;
   struct CondExprRet * cond_expr_ret;
   ret = NewExprExecRetType();
   lret = ExprExecRightValue(asrt, expr_left, env);
   lside = lret->ret_value;
   ret->witness = WitnessMerge(lret->witness, ret->witness);
   while (lside != NULL) {
      rret = ExprExecRightValue(lside->asrt, expr_right, env);
      rside = rret->ret_value;
      ret->witness = WitnessMerge(rret->witness, ret->witness);
      while (rside != NULL) {
         struct ExprVal * lval;
         if (rside->next == NULL) {
            lval = lside->val;
         } else {
            lval = ExprValDeepCopy(lside->val);
         }
         cond_expr_ret = OpSemantic(ExprValDeepCopy(lval), ExprValDeepCopy(rside->val));
         struct SafetyCheckerWit * safety_checker_wit;
         struct PropList * constraits = SafetyConstrait(lval, rside->val);
         if (constraits != NULL) {
            safety_checker_wit = SafetyCheckerWitCons(AsrtDeepCopy(rside->asrt), constraits, SafetyCheckerWitNil());
            ret->witness->safety_checker_wit = SafetyCheckerWitLink(ret->witness->safety_checker_wit, safety_checker_wit);
         }
         while (cond_expr_ret != NULL) {
            struct Assertion * new_asrt;
            if (cond_expr_ret->next == NULL) {
               new_asrt = rside->asrt;
            } else {
               new_asrt = AsrtDeepCopy(rside->asrt);
            }
            struct PropList * constraits;
            struct IntList * introed;
            if (cond_expr_ret->next == NULL) {
               if (rside->next == NULL) {
                  constraits = PropListLink(lside->constraits, rside->constraits);
                  introed = IntListLink(lside->introed_vars, rside->introed_vars);
               } else {
                  constraits = PropListLink(PropListDeepCopy(lside->constraits), rside->constraits);
                  introed = IntListLink(IntListDeepCopy(lside->introed_vars), rside->introed_vars);
               }
            } else {
               constraits = PropListLink(PropListDeepCopy(lside->constraits), PropListDeepCopy(rside->constraits));
               introed = IntListLink(IntListDeepCopy(lside->introed_vars), IntListDeepCopy(rside->introed_vars));
            }
            constraits = PropListLink(constraits, PropListDeepCopy(cond_expr_ret->constraits));
            ret->ret_value = ExprExecRetValueCons(new_asrt, cond_expr_ret->val, constraits, introed, ret->ret_value);
            new_asrt->prop_list = PropListLink(cond_expr_ret->constraits, new_asrt->prop_list);
            cond_expr_ret = cond_expr_ret->next;
         }
         CondExprRetFree(cond_expr_ret);
         rside = rside->next;
      }
      ExprExecRetTypeFree(rret);
      lside = lside->next;
   }
   ExprExecRetTypeFree(lret);
   return ret;
}

struct ExprExecRetType * BinaryOpExecHelper
(struct ExprExecRetType * lret, void * expr_right, void *env,
 struct ExprVal * (*OpSemantic)(struct ExprVal *, struct ExprVal *),
 struct PropList * (SafetyConstrait)(struct ExprVal *, struct ExprVal *),
 struct ExprVal * (*UnsignedOp)(struct ExprVal *, struct environment *),
 struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
   struct ExprExecRetType * ret;
   struct ExprExecRetType * rret;
   struct ExprExecRetValue * lside, * rside;
   struct ExprVal * val;
   ret = NewExprExecRetType();
   lside = lret->ret_value;
   ret->witness = WitnessMerge(lret->witness, ret->witness);
   while (lside != NULL) {
      rret = ExprExecRightValue(lside->asrt, expr_right, env);
      rside = rret->ret_value;
      ret->witness = WitnessMerge(rret->witness, ret->witness);
      while (rside != NULL) {
         struct ExprVal * lval;
         if (rside->next == NULL) {
            lval = lside->val;
         } else {
            lval = ExprValDeepCopy(lside->val);
         }
         val = UnsignedOp(OpSemantic(ExprValDeepCopy(lval), ExprValDeepCopy(rside->val)), env);
         struct SafetyCheckerWit * safety_checker_wit;
         struct PropList * constraits = SafetyConstrait(lval, rside->val);
         if (constraits != NULL) {
            safety_checker_wit = SafetyCheckerWitCons(AsrtDeepCopy(rside->asrt), constraits, SafetyCheckerWitNil());
            ret->witness->safety_checker_wit = SafetyCheckerWitLink(ret->witness->safety_checker_wit, safety_checker_wit);
         }
         constraits = NULL;
         struct IntList * introed;
         if (rside->next == NULL) {
            constraits = PropListLink(lside->constraits, rside->constraits);
            introed = IntListLink(lside->introed_vars, rside->introed_vars);
         } else {
            constraits = PropListLink(PropListDeepCopy(lside->constraits), rside->constraits);
            introed = IntListLink(IntListDeepCopy(lside->introed_vars), rside->introed_vars);
         }
         ret->ret_value = ExprExecRetValueCons(rside->asrt, val, constraits, introed, ret->ret_value);
         rside = rside->next;
      }
      ExprExecRetTypeFree(rret);
      lside = lside->next;
   }
   ExprExecRetTypeFree(lret);
   return ret;
}

struct ExprExecRetType * BinaryOpExec(struct Assertion * asrt, void * expr_left, void * expr_right, void *env,
                                      struct ExprVal * (*OpSemantic)(struct ExprVal *, struct ExprVal *),
                                      struct PropList * (SafetyConstrait)(struct ExprVal *, struct ExprVal *),
                                      struct ExprVal * (*UnsignedOp)(struct ExprVal *, struct environment *),
                                      struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
  return BinaryOpExecHelper(ExprExecRightValue(asrt, expr_left, env), expr_right, env, OpSemantic, SafetyConstrait, UnsignedOp, ExprExecRightValue);
}

struct ExprExecRetType * ORExecShortCircuit(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
   struct ExprExecRetType * ret;
   struct ExprExecRetType * lret, * rret;
   struct ExprExecRetValue * lside, * rside;
   ret = NewExprExecRetType();
   lret = ExprExecRightValue(asrt, expr_left, env);
   lret = ExprExecRetTypeToBool(lret);
   lside = lret->ret_value;
   ret->witness = WitnessMerge(lret->witness, ret->witness);
   while (lside != NULL) {
      assert(lside->val->t == EZ_VAL);
      assert(lside->val->d.EZ_VAL.number == 0 || lside->val->d.EZ_VAL.number == 1);
      if (lside->val->d.EZ_VAL.number == 1) {
         ret->ret_value = ExprExecRetValueCons(lside->asrt, lside->val, lside->constraits, lside->introed_vars, ret->ret_value);
      } else {
         rret = ExprExecRightValue(lside->asrt, expr_right, env);
         rret = ExprExecRetTypeToBool(rret);
         rside = rret->ret_value;
         ret->witness = WitnessMerge(rret->witness, ret->witness);
         while (rside != NULL) {
            assert(rside->val->t == EZ_VAL);
            assert(rside->val->d.EZ_VAL.number == 0 || rside->val->d.EZ_VAL.number == 1);
            if (rside->next == NULL) {
               ret->ret_value = ExprExecRetValueCons(rside->asrt, rside->val,
                                                      PropListLink(lside->constraits, rside->constraits), 
                                                      IntListLink(lside->introed_vars, rside->introed_vars), ret->ret_value);
            } else {
               ret->ret_value = ExprExecRetValueCons(rside->asrt, rside->val,
                                                      PropListLink(PropListDeepCopy(lside->constraits), rside->constraits),
                                                      IntListLink(IntListDeepCopy(lside->introed_vars), rside->introed_vars), ret->ret_value);
            }
            rside = rside->next;
         }
         ExprValFree(lside->val);
         ExprExecRetTypeFree(rret);
      }
      lside = lside->next;
   }
   ExprExecRetTypeFree(lret);
   return ret;
}

struct ExprExecRetType * ORExecNoShortCircuit(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
   struct ExprExecRetType * ret;
   struct ExprExecRetType * lret, * rret;
   struct ExprExecRetValue * lside, * rside;
   ret = NewExprExecRetType();
   lret = ExprExecRightValue(asrt, expr_left, env);
   lret = ExprExecRetTypeToBool(lret);
   lside = lret->ret_value;
   ret->witness = WitnessMerge(lret->witness, ret->witness);
   while (lside != NULL) {
      assert(lside->val->t == EZ_VAL);
      assert(lside->val->d.EZ_VAL.number == 0 || lside->val->d.EZ_VAL.number == 1);
      rret = ExprExecRightValue(lside->asrt, expr_right, env);
      rret = ExprExecRetTypeToBool(rret);
      rside = rret->ret_value;
      ret->witness = WitnessMerge(rret->witness, ret->witness);
      while (rside != NULL) {
         assert(rside->val->t == EZ_VAL);
         assert(rside->val->d.EZ_VAL.number == 0 || rside->val->d.EZ_VAL.number == 1);
         int value = rside->val->d.EZ_VAL.number || lside->val->d.EZ_VAL.number;
         if (rside->next == NULL) {
            ret->ret_value = ExprExecRetValueCons(rside->asrt, ExprVal_EZ_VAL(value), 
                                                   PropListLink(lside->constraits, rside->constraits), 
                                                   IntListLink(lside->introed_vars, rside->introed_vars), ret->ret_value);
         } else {
            ret->ret_value = ExprExecRetValueCons(rside->asrt, ExprVal_EZ_VAL(value), 
                                                   PropListLink(PropListDeepCopy(lside->constraits), rside->constraits),
                                                   IntListLink(IntListDeepCopy(lside->introed_vars), rside->introed_vars), ret->ret_value);
         }
         ExprValFree(rside->val);
         rside = rside->next;
      }
      ExprExecRetTypeFree(rret);
      ExprValFree(lside->val);
      lside = lside->next;
   }
   ExprExecRetTypeFree(lret);
   return ret;
}

struct ExprExecRetType * ANDExecShortCircuit(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
   struct ExprExecRetType * ret;
   struct ExprExecRetType * lret, * rret;
   struct ExprExecRetValue * lside, * rside;
   ret = NewExprExecRetType();
   lret = ExprExecRightValue(asrt, expr_left, env);
   lret = ExprExecRetTypeToBool(lret);
   lside = lret->ret_value;
   ret->witness = WitnessMerge(lret->witness, ret->witness);
   while (lside != NULL) {
      assert(lside->val->t == EZ_VAL);
      assert(lside->val->d.EZ_VAL.number == 0 || lside->val->d.EZ_VAL.number == 1);
      if (lside->val->d.EZ_VAL.number == 0) {
         ret->ret_value = ExprExecRetValueCons(lside->asrt, ExprVal_EZ_VAL(0), lside->constraits, lside->introed_vars, ret->ret_value);
         ExprValFree(lside->val);
      } else {
         rret = ExprExecRightValue(lside->asrt, expr_right, env);
         rret = ExprExecRetTypeToBool(rret);
         rside = rret->ret_value;
         ret->witness = WitnessMerge(rret->witness, ret->witness);
         while (rside != NULL) {
            assert(rside->val->t == EZ_VAL);
            assert(rside->val->d.EZ_VAL.number == 0 || rside->val->d.EZ_VAL.number == 1);
            if (rside->next == NULL) {
               ret->ret_value = ExprExecRetValueCons(rside->asrt, rside->val, 
                                                      PropListLink(lside->constraits, rside->constraits), 
                                                      IntListLink(lside->introed_vars, rside->introed_vars), ret->ret_value);
            } else {
               ret->ret_value = ExprExecRetValueCons(rside->asrt, rside->val, 
                                                      PropListLink(PropListDeepCopy(lside->constraits), rside->constraits),
                                                      IntListLink(IntListDeepCopy(lside->introed_vars), rside->introed_vars), ret->ret_value);
            }
            rside = rside->next;
         }
         ExprValFree(lside->val);
         ExprExecRetTypeFree(rret);
      }
      lside = lside->next;
   }
   ExprExecRetTypeFree(lret);
   return ret;
}

struct ExprExecRetType * ANDExecNoShortCircuit(struct Assertion * asrt, void * expr_left, void * expr_right, void * env,
                                struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
   struct ExprExecRetType * ret;
   struct ExprExecRetType * lret, * rret;
   struct ExprExecRetValue * lside, * rside;
   ret = NewExprExecRetType();
   lret = ExprExecRightValue(asrt, expr_left, env);
   lret = ExprExecRetTypeToBool(lret);
   lside = lret->ret_value;
   ret->witness = WitnessMerge(lret->witness, ret->witness);
   while (lside != NULL) {
      assert(lside->val->t == EZ_VAL);
      assert(lside->val->d.EZ_VAL.number == 0 || lside->val->d.EZ_VAL.number == 1);
      rret = ExprExecRightValue(lside->asrt, expr_right, env);
      rret = ExprExecRetTypeToBool(rret);
      rside = rret->ret_value;
      ret->witness = WitnessMerge(rret->witness, ret->witness);
      while (rside != NULL) {
         assert(rside->val->t == EZ_VAL);
         assert(rside->val->d.EZ_VAL.number == 0 || rside->val->d.EZ_VAL.number == 1);
         int value = rside->val->d.EZ_VAL.number && lside->val->d.EZ_VAL.number;
         if (rside->next == NULL) {
            ret->ret_value = ExprExecRetValueCons(rside->asrt, ExprVal_EZ_VAL(value), 
                                                   PropListLink(lside->constraits, rside->constraits), 
                                                   IntListLink(lside->introed_vars, rside->introed_vars), ret->ret_value);
         } else {
            ret->ret_value = ExprExecRetValueCons(rside->asrt, ExprVal_EZ_VAL(value), 
                                                   PropListLink(PropListDeepCopy(lside->constraits), rside->constraits),
                                                   IntListLink(IntListDeepCopy(lside->introed_vars), rside->introed_vars), ret->ret_value);
         }
         ExprValFree(rside->val);
         rside = rside->next;
      }
      ExprValFree(lside->val);
      ExprExecRetTypeFree(rret);
      lside = lside->next;
   }
   ExprExecRetTypeFree(lret);
   return ret;
}

struct ExprExecRetType * UnaryOpExec(struct Assertion * asrt, void * expr, void * env,
                                     struct ExprVal * (*OpSemantic)(struct ExprVal *),
                                     struct PropList * (SafetyConstrait)(struct ExprVal *),
                                     struct ExprVal * (*UnsignedOp)(struct ExprVal *, struct environment *),
                                     struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
   struct ExprExecRetType * ret;
   struct ExprExecRetType * inside_ret;
   struct ExprExecRetValue * inside;
   struct ExprVal * val;
   ret = NewExprExecRetType();
   inside_ret = ExprExecRightValue(asrt, expr, env);
   inside = inside_ret->ret_value;
   ret->witness = WitnessMerge(inside_ret->witness, ret->witness);
   while (inside != NULL) {
      val = UnsignedOp(OpSemantic(ExprValDeepCopy(inside->val)), env);
      struct SafetyCheckerWit * safety_checker_wit;
      struct PropList * constraits = SafetyConstrait(inside->val);
      if (constraits != NULL) {
         safety_checker_wit = SafetyCheckerWitCons(AsrtDeepCopy(inside->asrt), constraits, SafetyCheckerWitNil());
         ret->witness->safety_checker_wit = SafetyCheckerWitLink(ret->witness->safety_checker_wit, safety_checker_wit);
      }
      ret->ret_value = ExprExecRetValueCons(inside->asrt, val, inside->constraits, inside->introed_vars, ret->ret_value);
      inside = inside->next;
   }
   ExprExecRetTypeFree(inside_ret);
   return ret;
}

struct ExprExecRetType * CondUnaryOpExec(struct Assertion * asrt, void * expr, void * env,
                                        struct CondExprRet * (*OpSemantic)(struct ExprVal *),
                                        struct PropList * (SafetyConstrait)(struct ExprVal *),
                                        struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
   struct ExprExecRetType * ret;
   struct ExprExecRetType * inside_ret;
   struct ExprExecRetValue * inside;
   struct CondExprRet * cond_expr_ret;
   ret = NewExprExecRetType();
   inside_ret = ExprExecRightValue(asrt, expr, env);
   inside = inside_ret->ret_value;
   ret->witness = WitnessMerge(inside_ret->witness, ret->witness);
   while (inside != NULL) {
      cond_expr_ret = OpSemantic(ExprValDeepCopy(inside->val));
      struct SafetyCheckerWit * safety_checker_wit;
      safety_checker_wit = SafetyCheckerWitNil();
      struct PropList * constraits = SafetyConstrait(inside->val);
      if (constraits != NULL) {
         safety_checker_wit = SafetyCheckerWitCons(AsrtDeepCopy(inside->asrt), constraits, SafetyCheckerWitNil());
         ret->witness->safety_checker_wit = SafetyCheckerWitLink(ret->witness->safety_checker_wit, safety_checker_wit);
      }
      while (cond_expr_ret != NULL) {
         struct Assertion * new_asrt;
         if (cond_expr_ret->next == NULL) {
            new_asrt = inside->asrt;
         } else {
            new_asrt = AsrtDeepCopy(inside->asrt);
         }
         struct PropList * constraits;
         struct IntList * introed;
         if (cond_expr_ret->next == NULL) {
            constraits = PropListLink(inside->constraits, PropListDeepCopy(cond_expr_ret->constraits));
            introed = inside->introed_vars;
         } else {
            constraits = PropListLink(PropListDeepCopy(inside->constraits), PropListDeepCopy(cond_expr_ret->constraits));
            introed = IntListDeepCopy(inside->introed_vars);
         }
         ret->ret_value = ExprExecRetValueCons(new_asrt, cond_expr_ret->val, constraits, introed, ret->ret_value);
         new_asrt->prop_list = PropListLink(cond_expr_ret->constraits, new_asrt->prop_list);
         cond_expr_ret = cond_expr_ret->next;
      }
      CondExprRetFree(cond_expr_ret);
      inside = inside->next;
   }
   ExprExecRetTypeFree(inside_ret);
   return ret;
}