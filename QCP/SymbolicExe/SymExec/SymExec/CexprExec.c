#include <assert.h>
#include "ExprExec.h"
#include "CexprExec.h"
#include "FuncCall.h"
#include "MemOracle.h"
#include "DefaultOpSemantic.h"
#include "../../compiler/cp.h"
#include "../../compiler/utils.h"
#include "../Automation/AutomationSolver/CustomSolver.h"
#include "../Utility/OperatorTranser.h"
#include "../Utility/InnerAsrtPrinter.h"
#include "../Utility/CexprPrinter.h"
#include "../Utility/List.h"

int TryEntailFalse(struct Assertion * asrt, struct environment * env) {
   struct PropList * prop = PropListCons(PropTrue(), PropListNil());
   struct Prop_solver_return * res = PropEntail(asrt->prop_list, prop, env);
   int ret = res->result;
   Prop_solver_return_free(res);
   PropListFree(prop);
   return ret == -1;
}

struct AsrtList * DiscardFalseBranch(struct AsrtList * asrt, struct environment * env, struct Witness * witness) {
   struct AsrtList * ret = AsrtListNil();
   struct AsrtList * tmp = asrt;
   int flag = 0;
   while (tmp != NULL) {
      if (TryEntailFalse(tmp->head, env) == 0) {
         ret = AsrtListCons(tmp->head, ret);
      }
      else {
        witness->safety_checker_wit = SafetyCheckerWitCons(tmp->head, PropListCons(PropFalse(), PropListNil()), witness->safety_checker_wit);
        witness->safety_checker_wit->auto_solved = 1;
        flag = 1;
      }
      tmp = tmp->next;
   }
   ret = AsrtListReverse(ret);
   if (flag && ret != NULL) {
      witness->entailment_checker_wit = CheckEntailment(asrt, ret, NULL, env, witness->entailment_checker_wit);
      witness->entailment_checker_wit->auto_solved = 1;
   }
   return ret;
}

struct func_info * FindFuncInfo(struct ExprVal * val, struct Assertion * asrt, struct environment * env) {
   struct func_info * ret = FPSpecListFind(val, asrt->fp_spec_list);
   if (ret != NULL) return ret;
   if (val->t == FUNCAPP && ExprValListIsEmpty(val->d.FUNCAPP.args) && PolyTypeListIsEmpty(val->d.FUNCAPP.types)) {
      ret = find_func_by_id(val->d.FUNCAPP.id, &env->persist);
   }
   if (ret != NULL) return ret;
   failwith("Error: FindFuncInfo: func_info not found\n");
}

struct ExprVal * OpSemanticPtrLeftPlus(struct ExprVal * left, struct ExprVal * right, struct SimpleCtype * type) {
   return ExprVal_VBOP(Oadd, left, ExprVal_VBOP(Omul, right, ExprVal_SIZE_OF(type)));
}

struct ExprVal * OpSemanticPtrRightPlus(struct ExprVal * left, struct ExprVal * right, struct SimpleCtype * type) {
   return ExprVal_VBOP(Oadd, ExprVal_VBOP(Omul, left, ExprVal_SIZE_OF(type)), right);
}

struct ExprVal * OpSemanticPtrMinusInt(struct ExprVal * left, struct ExprVal * right, struct SimpleCtype * type) {
   return ExprVal_VBOP(Osub, left, ExprVal_VBOP(Omul, right, ExprVal_SIZE_OF(type)));
}

struct ExprVal * OpSemanticPtrMinusPtr(struct ExprVal * left, struct ExprVal * right, struct SimpleCtype * type) {
   return ExprVal_VBOP(Odiv, ExprVal_VBOP(Osub, left, right), ExprVal_SIZE_OF(type));
}

struct ExprExecRetType * PtrBinaryOpExecHelper
(struct ExprExecRetType * lret, void * expr_right,
 struct SimpleCtype * type, void *env,
 struct ExprVal * (*OpSemantic)(struct ExprVal *, struct ExprVal *, struct SimpleCtype *),
 struct PropList * (SafetyConstrait)(struct ExprVal *, struct ExprVal *),
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
         val = OpSemantic(ExprValDeepCopy(lval), ExprValDeepCopy(rside->val), SimpleCtypeDeepCopy(type));
         struct SafetyCheckerWit * safety_checker_wit;
         struct PropList * constraits = SafetyConstrait(lval, rside->val);
         if (constraits != NULL) {
            safety_checker_wit = SafetyCheckerWitCons(AsrtDeepCopy(rside->asrt), constraits, SafetyCheckerWitNil());
            ret->witness->safety_checker_wit = SafetyCheckerWitLink(ret->witness->safety_checker_wit, safety_checker_wit);
         }
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

struct ExprExecRetType * PtrBinaryOpExec(struct Assertion * asrt, void * expr_left, void * expr_right, 
                                         struct SimpleCtype * type, void *env,
                                         struct ExprVal * (*OpSemantic)(struct ExprVal *, struct ExprVal *, struct SimpleCtype *),
                                         struct PropList * (SafetyConstrait)(struct ExprVal *, struct ExprVal *),
                                         struct ExprExecRetType * (*ExprExecRightValue)(struct Assertion *, void *, void*)) {
   return PtrBinaryOpExecHelper(ExprExecRightValue(asrt, expr_left, env), expr_right, type, env, OpSemantic, SafetyConstrait, ExprExecRightValue);
}

struct SafetyCheckerWit * SafetyConstrait(struct ExprVal * val, struct SimpleCtype * type, struct Assertion *asrt) {
   struct SafetyCheckerWit * ret = SafetyCheckerWitNil();
   struct PropList * constraits = PropListNil();
   switch (type->t) {
   case C_int8:
      if (type->d.CINT8.s == Signed) {
         constraits = SafetyConstraitInt8(val);
      }
      else constraits = SafetyConstraitUInt8(val);
      break;
   case C_int16:
      if (type->d.CINT16.s == Signed) {
         constraits = SafetyConstraitInt16(val);
      }
      else constraits = SafetyConstraitUInt16(val);
      break;
   case C_int32:
      if (type->d.CINT32.s == Signed) {
         constraits = SafetyConstraitInt32(val);
      }
      else constraits = SafetyConstraitUInt32(val);
      break;
   case C_int64:
      if (type->d.CINT64.s == Signed) {
         constraits = SafetyConstraitInt64(val);
      }
      else constraits = SafetyConstraitUInt64(val);
      break;
   default:
      break;
   }
   if (constraits != NULL) {
      ret = SafetyCheckerWitCons(asrt, constraits, ret);
   }
   return ret;
}

struct ExprVal * VarExec_l(struct Assertion * asrt, int id, struct environment *env) {
   struct prog_var_info * var_info = find_prog_var_by_id(id, &env->persist);
   if (var_info->category == PROG_LOCAL) {
      struct ExprVal * res = LocalFind(id, asrt->local_list);
      res = ExprValDeepCopy(res);
      if (res == NULL) {
        fprintf(stderr, "Error: VarExec_l: %d not found %s %d", id, __FILE__, __LINE__);
        exit(-1);
      }
      return res;
   } else {
      return ExprVal_V_VARI(var_info->address->id);
   }
}

struct ExprVal * VarExec_r(struct Assertion * asrt, int id, struct environment * env) {
   struct prog_var_info * var_info = find_prog_var_by_id(id, &env->persist);
   if (var_info->type->t == T_FUNCTION) {
      return ExprVal_V_VARI(var_info->func->id);
   }
   struct ExprVal * tmp = VarExec_l(asrt, id, env);
   if (var_info->type->t == T_ARRAY) {
      return tmp;
   }
   struct ExprVal * val = GetDataAtValue(asrt, tmp);
   ExprValFree(tmp);
   val = ExprValDeepCopy(val);
   return val;
}

struct ExprExecRetType * ConstExec(unsigned long long number, 
                                   struct SimpleCtype * type, struct Assertion * asrt) {
   struct ExprVal * val = ExprVal_EZ_VAL(number);
   struct SafetyCheckerWit * safety_checker_wit = SafetyConstrait(ExprValDeepCopy(val), type, AsrtDeepCopy(asrt));
   struct ExprExecRetType * ret = NewExprExecRetType();
   ret->ret_value = ExprExecRetValueCons(asrt, val, PropListNil(), IntListNil(), ret->ret_value);
   ret->witness->safety_checker_wit = SafetyCheckerWitLink(safety_checker_wit, ret->witness->safety_checker_wit);
   return ret;
}

struct TrueFalseConditionPair AsrtListCondExec(struct AsrtList * asrt_list, struct Cexpr * condition, struct environment * env) {
   struct TrueFalseConditionPair ret;
   ret.true_part = AsrtListNil();
   ret.false_part = AsrtListNil();
   ret.witness = NewWitness();
   struct ExprExecRetType * cond_ret = ExprExecRetTypeToBool(AsrtListExprExecRightValue(asrt_list, condition, env));
   struct ExprExecRetValue * expr_ret = cond_ret->ret_value;
   ret.witness = WitnessMerge(cond_ret->witness, ret.witness);
   while (expr_ret != NULL) {
      assert(expr_ret->val->t == EZ_VAL);
      assert(expr_ret->val->d.EZ_VAL.number == 0 || expr_ret->val->d.EZ_VAL.number == 1);
      if (expr_ret->val->d.EZ_VAL.number == 0) {
         ret.false_part = AsrtListCons(expr_ret->asrt, ret.false_part);
      } else {
         ret.true_part = AsrtListCons(expr_ret->asrt, ret.true_part);
      }
      ExprValFree(expr_ret->val);
      expr_ret = expr_ret->next;
   }
   ExprExecRetTypeFree(cond_ret);
   ret.true_part = DiscardFalseBranch(ret.true_part, env, ret.witness);
   ret.false_part = DiscardFalseBranch(ret.false_part, env, ret.witness);
   return ret;
}

struct TrueFalseConditionPair CondExec(struct Assertion * asrt, struct Cexpr * condition, struct environment * env) {
   struct TrueFalseConditionPair ret;
   ret.true_part = AsrtListNil();
   ret.false_part = AsrtListNil();
   ret.witness = NewWitness();
   struct ExprExecRetType * cond_ret = ExprExecRetTypeToBool(ExprExecRightValue(asrt, condition, env));
   struct ExprExecRetValue * expr_ret = cond_ret->ret_value;
   ret.witness = WitnessMerge(cond_ret->witness, ret.witness);
   while (expr_ret != NULL) {
      assert(expr_ret->val->t == EZ_VAL);
      assert(expr_ret->val->d.EZ_VAL.number == 0 || expr_ret->val->d.EZ_VAL.number == 1);
      if (expr_ret->val->d.EZ_VAL.number == 0) {
         ret.false_part = AsrtListCons(expr_ret->asrt, ret.false_part);
      } else {
         ret.true_part = AsrtListCons(expr_ret->asrt, ret.true_part);
      }
      ExprValFree(expr_ret->val);
      expr_ret = expr_ret->next;
   }
   ExprExecRetTypeFree(cond_ret);
   ret.true_part = DiscardFalseBranch(ret.true_part, env, ret.witness);
   ret.false_part = DiscardFalseBranch(ret.false_part, env, ret.witness);
   return ret;
}

struct Assertion * TryFold(struct Assertion * asrt, struct environment * env) {
   struct EntailRetType * tmp = post_solve(asrt, CreateAsrt(), env);
   // ExprExecRetTypeFree(tmp);
   return asrt;
}

struct ExprExecRetType * DerefExec(struct ExprExecRetType * inside_ret, struct SimpleCtype * type, struct environment * env) {
   struct ExprVal * val;
   struct ExprExecRetValue * inside;
   struct ExprExecRetValue * new_list;
   new_list = ExprExecRetValueNil();
   inside = inside_ret->ret_value;
   while (inside != NULL) {
      val = GetDataAtValue(inside->asrt, inside->val);
      val = ExprValDeepCopy(val);
      if (val != NULL) {
         new_list = ExprExecRetValueCons(inside->asrt, val, inside->constraits, inside->introed_vars, new_list);
         ExprValFree(inside->val);
      } else {
         struct Assertion * asrt = CreateAsrt();
         struct logic_var_info * var_info = add_anonymous_logic_var(LOGIC_FREE, "v", &env->persist);
         var_info->renaming = renaming_info_free_var("v");
         var_info->atype = ATZ(&env->persist);
         var_info->qv = NULL;
         int id = var_info->id;
         asrt->sep_list = SepListCons(SepDataAt(ExprValDeepCopy(inside->val), type, ExprVal_V_VARI(id)), asrt->sep_list);
         struct func_spec * spec = DeclareSpec(ExistListNil(), ExistListCons(id, ExistListNil()),
                                               AsrtListCons(AsrtDeepCopy(asrt), AsrtListNil()),
                                               AsrtListCons(asrt, AsrtListNil()),
                                               ExprVal_V_VARI(id), NULL);
         spec->name = "Deref";
         struct FuncCallRetType * func_call_ret = FuncCallExec(inside->asrt, env, VILNil(), spec, NULL, ExprValListNil(), FIELD_CALL, NULL);
         if (func_call_ret == NULL) {
            failwith("Cannot derive the precondition of Memory Read.\n");
         }
         inside_ret->witness = WitnessMerge(func_call_ret->ret->witness, inside_ret->witness);
         for (struct ExprExecRetValue * i = func_call_ret->ret->ret_value; i != NULL; i = i->next) {
            i->asrt = TryFold(i->asrt, env);
         }
         new_list = ExprExecRetValueLink(new_list, func_call_ret->ret->ret_value);
         free(func_call_ret);
      }
      inside = inside->next;
   }
   ExprExecRetValueFree(inside_ret->ret_value);
   inside_ret->ret_value = new_list;
   return inside_ret;
}

struct ExprExecRetType * DerefExecOne(struct ExprExecRetValue *inside, struct SimpleCtype * type, struct environment * env) {
   struct ExprExecRetType * ret = NewExprExecRetType();
   struct ExprExecRetValue * new_list = ExprExecRetValueNil();
   struct ExprVal *val = GetDataAtValue(inside->asrt, inside->val);
   val = ExprValDeepCopy(val);
   if (val != NULL) {
      new_list = ExprExecRetValueCons(inside->asrt, val, inside->constraits, inside->introed_vars, new_list);
   } else {
      struct Assertion * asrt = CreateAsrt();
      struct logic_var_info * var_info = add_anonymous_logic_var(LOGIC_FREE, "v", &env->persist);
      var_info->renaming = renaming_info_free_var("v");
      var_info->atype = ATZ(&env->persist);
      var_info->qv = NULL;
      int id = var_info->id;
      asrt->sep_list = SepListCons(SepDataAt(ExprValDeepCopy(inside->val), type, ExprVal_V_VARI(id)), asrt->sep_list);
      struct func_spec * spec = DeclareSpec(ExistListNil(), ExistListCons(id, ExistListNil()),
                                            AsrtListCons(AsrtDeepCopy(asrt), AsrtListNil()),
                                            AsrtListCons(asrt, AsrtListNil()),
                                            ExprVal_V_VARI(id), NULL);
      spec->name = "Deref";
      struct FuncCallRetType * func_call_ret = FuncCallExec(inside->asrt, env, VILNil(), spec, NULL, ExprValListNil(), FIELD_CALL, NULL);
      if (func_call_ret == NULL) {
         failwith("Cannot derive the precondition of Memory Read.\n");
      }
      ret->witness = WitnessMerge(func_call_ret->ret->witness, ret->witness);
      for (struct ExprExecRetValue * i = func_call_ret->ret->ret_value; i != NULL; i = i->next) {
         i->asrt = TryFold(i->asrt, env);
      }
      new_list = ExprExecRetValueLink(new_list, func_call_ret->ret->ret_value);
      free(func_call_ret);
   }
   ret->ret_value = new_list;
   return ret;
}

/*  old code
struct ExprExecRetType * StructFieldExecRightValue(
            struct ExprExecRetType * inside_ret, int field_id,
            struct environment * env, struct SimpleCtype * expr_type) {
   struct ExprVal * val;
   struct ExprExecRetValue * inside;
   struct ExprExecRetValue * new_list;
   new_list = ExprExecRetValueNil();
   inside = inside_ret->ret_value;
   while (inside != NULL) {
      struct ExprVal * left_value;
      left_value = ExprVal_VFIELD_ADDRESS(inside->val, field_id);
      val = GetDataAtValue(inside->asrt, left_value);
      val = ExprValDeepCopy(val);
      if (val != NULL) {
         new_list = ExprExecRetValueCons(inside->asrt, val, inside->constraits, inside->introed_vars, new_list);
         ExprValFree(inside->val);
      } else {
         struct Assertion * asrt = CreateAsrt();
         struct field_info * field_info = find_field_by_id(field_id, &env->persist);
         struct logic_var_info * var_info = add_anonymous_logic_var(LOGIC_EXISTS, field_info->name, &env->persist);
         var_info->renaming = renaming_info_free_var(field_info->name);
         var_info->atype = ATZ(&env->persist);
         var_info->qv = NULL;
         int id = var_info->id;
         asrt->sep_list = SepListCons(SepDataAt(ExprValDeepCopy(left_value), expr_type, ExprVal_V_VARI(id)), asrt->sep_list);
         struct func_spec * spec = DeclareSpec(ExistListNil(), ExistListCons(id, ExistListNil()),
                                               AsrtListCons(AsrtDeepCopy(asrt), AsrtListNil()),
                                               AsrtListCons(asrt, AsrtListNil()),
                                               ExprVal_V_VARI(id), NULL);
         struct FuncCallRetType * func_call_ret = FuncCallExec(inside->asrt, env, VILNil(), spec, NULL, ExprValListNil(), FIELD_CALL);
         inside_ret->witness = WitnessMerge(func_call_ret->ret->witness, inside_ret->witness);
         new_list = ExprExecRetValueLink(new_list, func_call_ret->ret->ret_value);
         free(func_call_ret);
      }
      inside = inside->next;
   }
   ExprExecRetValueFree(inside_ret->ret_value);
   inside_ret->ret_value = new_list;
   return inside_ret;
}

struct ExprExecRetType * UnionFieldExecRightValue(
            struct ExprExecRetType * inside_ret, int field_id,
            struct environment * env, struct SimpleCtype * expr_type) {
   struct ExprVal * val;
   struct ExprExecRetValue * inside;
   struct ExprExecRetValue * new_list;
   new_list = ExprExecRetValueNil();
   inside = inside_ret->ret_value;
   while (inside != NULL) {
      // need an oracle
      val = GetDataAtValue(inside->asrt, inside->val);
      val = ExprValDeepCopy(val);
      if (val == NULL) {
         fprintf(stderr, "Error: GetDataAtvalue return NULL %s %d\n", __FILE__, __LINE__);
         exit(-1);
      }
      new_list = ExprExecRetValueCons(inside->asrt, val, inside->constraits, inside->introed_vars, new_list);
      ExprValFree(inside->val);
      inside = inside->next;
   }
   ExprExecRetValueFree(inside_ret->ret_value);
   inside_ret->ret_value = new_list;
   return inside_ret;
}
*/

struct ExprVal * Cast_ExprVal(struct ExprVal *inside_val, struct SimpleCtype *type) {
  struct ExprVal *val = NULL;
  switch (type->t)
  {
    case C_int8:  {
      if (type->d.CINT8.s == Signed) {
        val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(8), ExprValListNil())));
      } else {
        val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(8), ExprValListNil())));
      }
      break;
    }
    case C_int16: {
      if (type->d.CINT16.s == Signed) {
        val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(16), ExprValListNil())));
      } else {
        val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(16), ExprValListNil())));
      }
      break;
    }
    case C_int32: {
      if (type->d.CINT32.s == Signed) {
        val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(32), ExprValListNil())));
      } else {
        val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(32), ExprValListNil())));
      }
      break;
    }
    case C_int64: {
      if (type->d.CINT64.s == Signed) {
        val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(64), ExprValListNil())));
      } else {
        val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(64), ExprValListNil())));
      }
      break;
    }
    default: val = ExprValDeepCopy(inside_val);
  }
  return val;
}

/* 考虑强制类型转化是否需要增加 unsigned_last_nbits 和 last_nbits
   * 大转小 : 需要考虑 signed -> unsigned ( > 0 , < Max) , unsigned -> signed ( < Max), signed -> signed ( > MIN && < Max ), unsigned -> unsigned ( < Max)
   * 小转大 : 需要考虑 signed -> unsigned ( > 0 ) , unsigned -> signed ( < Max)
   * 相同类型 : 需要考虑 signed -> unsigned ( > 0 ) , unsigned -> signed ( < Max)
*/
int cast_from_low_to_high(struct SimpleCtype *from, struct SimpleCtype *to, struct Constant *c) {
  if (from == NULL || to == NULL) {
    return false;
  }
  switch (from -> t) {
    case C_int8: {
      switch (to -> t) {
        case C_int8: { // 8 -> 8
          if (from -> d.CINT8.s == to -> d.CINT8.s) {
            return true;
          }
          if (from -> d.CINT8.s == Signed && c != NULL) {
            return c -> pos == 1;
          }
          if (from -> d.CINT8.s == Unsigned && c != NULL) {
            struct Constant *tmp = Constant_number(127);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return c -> pos == 1 && res != 1;
          }
          break;
        }
        case C_int16: {   // 8 -> 16
          if (from -> d.CINT8.s == Signed && to->d.CINT16.s == Unsigned) {
            return c != NULL && c -> pos == 1;
          }
          return true;
        }
        case C_int32: {   // 8 -> 32
          if (from -> d.CINT8.s == Signed && to->d.CINT32.s == Unsigned) {
            return c != NULL && c -> pos == 1;
          }
          return true;
        }
        case C_int64:  { // 8 -> 64
          if (from -> d.CINT8.s == Signed && to->d.CINT64.s == Unsigned) {
            return c != NULL && c -> pos == 1;
          }
          return true;
        }
        default:
          break;
      }
      break;
    }
    case C_int16: {
      switch (to -> t) {
        case C_int8: {  // 16 -> 8
          if (c != NULL) {
            unsigned long long number = c->pos ? (to->d.CINT8.s == Signed ? 127 : 255) : (to->d.CINT8.s == Signed ? 128 : 0);
            struct Constant *tmp = Constant_number(number);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return (to->d.CINT8.s == Unsigned && c -> pos == 1) && res != 1;
          }
          return false;
        }
        case C_int16: { // 16 -> 16
          if (from -> d.CINT16.s == to -> d.CINT16.s) {
            return true;
          }
          if (from -> d.CINT16.s == Signed && c != NULL) {
            return c -> pos == 1;
          }
          if (from -> d.CINT16.s == Unsigned && c != NULL) {
            struct Constant *tmp = Constant_number(32767);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return c -> pos == 1 && res != 1;
          }
          break;
        }
        case C_int32: { // 16 -> 32
          if (from -> d.CINT16.s == Signed && to->d.CINT32.s == Unsigned) {
            return c != NULL && c -> pos == 1;
          }
          return true;
        }
        case C_int64: { // 16 -> 64
          if (from -> d.CINT16.s == Signed && to->d.CINT64.s == Unsigned) {
            return c != NULL && c -> pos == 1;
          }
          return true;
        }
        default:
          break;
      }
    }
    case C_int32: {
      switch (to -> t) { 
        case C_int8: { // 32 -> 8
          if (c != NULL) {
            unsigned long long number = c->pos ? (to->d.CINT8.s == Signed ? 127 : 255) : (to->d.CINT8.s == Signed ? 128 : 0);
            struct Constant *tmp = Constant_number(number);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return (to->d.CINT8.s == Unsigned && c -> pos == 1) && res != 1;
          }
          return false;
        }
        case C_int16: { // 32 -> 16
          if (c != NULL) {
            unsigned long long number = c->pos ? (to->d.CINT16.s == Signed ? 32767 : 65535) : (to->d.CINT16.s == Signed ? 32768 : 0);
            struct Constant *tmp = Constant_number(number);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return (to->d.CINT16.s == Unsigned && c -> pos == 1) && res != 1;
          }
          return false;
        }
        case C_int32: {   // 32 -> 32
          if (from -> d.CINT32.s == to -> d.CINT32.s) {
            return true;
          }
          if (from -> d.CINT32.s == Signed && c != NULL) {
            return c -> pos == 1;
          }
          if (from -> d.CINT32.s == Unsigned && c != NULL) {
            struct Constant *tmp = Constant_number(2147483647);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return c -> pos == 1 && res != 1;
          }
          break;
        }
        case C_int64: {  // 32 -> 64
          if (from -> d.CINT32.s == Signed && to->d.CINT64.s == Unsigned) {
            return c != NULL && c -> pos == 1;
          }
          return true;
        }
        default:
          break;
      }
    }
    case C_int64: {
      switch (to -> t) {
        case C_int8: { // 64 -> 8
          if (c != NULL) {
            unsigned long long number = c->pos ? (to->d.CINT8.s == Signed ? 127 : 255) : (to->d.CINT8.s == Signed ? 128 : 0);
            struct Constant *tmp = Constant_number(number);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return (to->d.CINT8.s == Unsigned && c -> pos == 1) && res != 1;
          }
          return false;
        }
        case C_int16: { // 64 -> 16
          if (c != NULL) {
            unsigned long long number = c->pos ? (to->d.CINT16.s == Signed ? 32767 : 65535) : (to->d.CINT16.s == Signed ? 32768 : 0);
            struct Constant *tmp = Constant_number(number);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return (to->d.CINT16.s == Unsigned && c -> pos == 1) && res != 1;
          }
          return false;
        }
        case C_int32: { // 64 -> 32
          if (c != NULL) {
            unsigned long long number = c->pos ? (to->d.CINT32.s == Signed ? 2147483647 : 4294967295ll) : (to->d.CINT32.s == Signed ? 2147483648ll : 0);
            struct Constant *tmp = Constant_number(number);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return (to->d.CINT32.s == Unsigned && c -> pos == 1) && res != 1;
          }
          return false;
        }
        case C_int64: { // 64 -> 64
          if (from -> d.CINT64.s == to -> d.CINT64.s) {
            return true;
          }
          if (from -> d.CINT64.s == Signed && c != NULL) {
            return c -> pos == 1;
          }
          if (from -> d.CINT64.s == Unsigned && c != NULL) {
            struct Constant *tmp = Constant_number(9223372036854775807ll);
            int res = ConstantAbsCompare(c, tmp);
            ConstantFree(tmp);
            return c -> pos == 1 && res != 1;
          }
          break;
        }
        default:
          break;
      }
    }
    default:
      return false;
  }
  return false;
}

struct ExprVal * ExprVal_CAST(struct ExprVal *inside_val, struct SimpleCtype *type) {
  if (inside_val == NULL || type == NULL) {
    return NULL;
  }
  struct ExprVal *val;
  long long number;
  switch (inside_val->t) {
    case EZ_VAL: {
      switch (type->t) {
        case C_int8: {
          if (type->d.CINT8.s == Signed) {
            number = (char) inside_val->d.EZ_VAL.number;
            if (number != inside_val->d.EZ_VAL.number) {
              val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(8), ExprValListNil())));
            }
            else {
              val = ExprValDeepCopy(inside_val);
            }
          } else {
            number = (unsigned char) inside_val->d.EZ_VAL.number;
            if (number != inside_val->d.EZ_VAL.number) {
              val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(8), ExprValListNil())));
            }
            else {
              val = ExprValDeepCopy(inside_val);
            }
          }
          break;
        }
        case C_int16: {
          if (type->d.CINT16.s == Signed) {
            number = (short) inside_val->d.EZ_VAL.number;
            if (number != inside_val->d.EZ_VAL.number) {
              val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(16), ExprValListNil())));
            }
            else {
              val = ExprValDeepCopy(inside_val);
            }
          } else {
            number = (unsigned short) inside_val->d.EZ_VAL.number;
            if (number != inside_val->d.EZ_VAL.number) {
              val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(16), ExprValListNil())));
            }
            else {
              val = ExprValDeepCopy(inside_val);
            }
          }
          break;
        }
        case C_int32: {
          if (type->d.CINT32.s == Signed) {
            number = (int) inside_val->d.EZ_VAL.number;
            if (number != inside_val->d.EZ_VAL.number) {
              val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(32), ExprValListNil())));
            }
            else {
              val = ExprValDeepCopy(inside_val); 
            }
          } else {
            number = (unsigned int) inside_val->d.EZ_VAL.number;
            if (number != inside_val->d.EZ_VAL.number) {
              val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(32), ExprValListNil())));
            }
            else {
              val = ExprValDeepCopy(inside_val);
            }
          }
          break;
        }
        case C_int64: {
          if (type->d.CINT64.s == Signed) {
            if (inside_val->d.EZ_VAL.number > INT64_MAX) {
              val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),      
                                                            ExprValListCons(ExprVal_EZ_VAL(64), ExprValListNil())));
            }
            else {
              val = ExprValDeepCopy(inside_val);
            }
          } else {
            val = ExprValDeepCopy(inside_val);
          }
          break;
        }
       default: val = ExprValDeepCopy(inside_val);
      }
      break;
    }
    case VUOP: {
      if (inside_val->d.VUOP.op == Oneg && inside_val->d.VUOP.expr->t == EZ_VAL) {
        switch (type -> t) {
          case C_int8: {
            if (type->d.CINT8.s == Signed) {
              number = (char) (- inside_val->d.VUOP.expr->d.EZ_VAL.number);
              if (number != - inside_val->d.VUOP.expr->d.EZ_VAL.number) {
                val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(8), ExprValListNil())));
              }
              else {
                val = ExprValDeepCopy(inside_val);
              }
            } else {
              val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(8), ExprValListNil())));
            }
            break;
          }
          case C_int16: {
            if (type->d.CINT16.s == Signed) {
              number = (short) (- inside_val->d.VUOP.expr->d.EZ_VAL.number);
              if (number != - inside_val->d.VUOP.expr->d.EZ_VAL.number) {
                val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(16), ExprValListNil())));
              }
              else {
                val = ExprValDeepCopy(inside_val);
              }
            } else {
              val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(16), ExprValListNil())));
            }
            break;
          }
          case C_int32: {
            if (type->d.CINT32.s == Signed) {
              number = (int) (- inside_val->d.VUOP.expr->d.EZ_VAL.number);
              if (number != - inside_val->d.VUOP.expr->d.EZ_VAL.number) {
                val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(32), ExprValListNil())));
              }
              else {
                val = ExprValDeepCopy(inside_val);
              }
            } else {
              val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(32), ExprValListNil())));
            }
            break;
          }
          case C_int64: {
            if (type->d.CINT64.s == Signed) {
              if (inside_val->d.VUOP.expr->d.EZ_VAL.number > INT64_MAX) {
                val = ExprVal_FUNCAPP(BUILTINVALUE_LNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(64), ExprValListNil())));
              }
              else {
                val = ExprValDeepCopy(inside_val);
              }
            } else {
              val = ExprVal_FUNCAPP(BUILTINVALUE_ULNB, PolyTypeListNil(), 
                                                       ExprValListCons(ExprValDeepCopy(inside_val),
                                                            ExprValListCons(ExprVal_EZ_VAL(64), ExprValListNil())));
              return val;
            }
            break;
          }
          default: val = ExprValDeepCopy(inside_val);
        }
      } else {
        val = Cast_ExprVal(inside_val, type);
      }
      break;
    }
    default: val = Cast_ExprVal(inside_val, type);
  }
  return val;
}

struct ExprExecRetType * CastExec(struct ExprExecRetType * inside_ret, struct SimpleCtype *from, struct SimpleCtype * type, struct environment * env) {
  struct ExprVal *val;
  struct ExprExecRetValue *inside;
  struct ExprExecRetValue *new_list;
  new_list = ExprExecRetValueNil();
  inside = inside_ret->ret_value;
  while (inside != NULL)
  {
    struct Constant * c = ConstantFold(inside->val, &env->persist);
    if (cast_from_low_to_high(from, type, c)) {
      ConstantFree(c);
      val = ExprValDeepCopy(inside->val); 
    } else {
      
      ConstantFree(c);
      val = ExprVal_CAST(inside->val, type);
    }
    if (val == NULL)
    {
      fprintf(stderr, "Error: CastExec: fail to cast val.\n", __FILE__, __LINE__);
      exit(-1);
    }
    // Here we do not need to check the safety of the cast operation.
    // struct SafetyCheckerWit *safety_checker_wit;
    // safety_checker_wit = SafetyConstrait(ExprValDeepCopy(val), type, AsrtDeepCopy(inside->asrt));
    // inside_ret->witness->safety_checker_wit =
    //     SafetyCheckerWitLink(safety_checker_wit, inside_ret->witness->safety_checker_wit);
    new_list = ExprExecRetValueCons(inside->asrt, val, inside->constraits, inside->introed_vars, new_list);
    ExprValFree(inside->val);
    inside->val = val;
    inside = inside->next;
   }
   ExprExecRetValueFree(inside_ret->ret_value);
   inside_ret->ret_value = new_list;
   return inside_ret;
}

struct ExprExecRetType * SizeofExec(struct Assertion * asrt, struct SimpleCtype * type) {
   struct ExprExecRetType * ret;
   struct ExprVal * val;
   ret = NewExprExecRetType();
   val = ExprVal_SIZE_OF(SimpleCtypeDeepCopy(type));
   ret->ret_value = ExprExecRetValueCons(asrt, val, PropListNil(), IntListNil(), ret->ret_value);
   return ret;
}

/*  old code
struct ExprExecRetType * IndexExec(struct ExprExecRetType * inside_ret, struct SimpleCtype * type) {
   struct ExprExecRetValue * inside;
   struct ExprExecRetValue * new_list;
   new_list = ExprExecRetValueNil();
   inside = inside_ret->ret_value;
   while (inside != NULL) {
      new_list = ExprExecRetValueCons(inside->asrt, 
                                      AsrtReadMem(inside->asrt, inside->val, GetInnerTypeSize(type)), 
                                      inside->constraits, inside->introed_vars, new_list);
      inside = inside->next;
   }
   inside_ret->ret_value = new_list;
   return inside_ret;
}
*/

void GetBinarySemantics
(enum BinOpType op,
 struct SimpleCtype *expr_type, struct SimpleCtype *expr1_type, struct SimpleCtype *expr2_type,
 struct environment *env,
 struct ExprVal * (**OpSemantic)(struct ExprVal *, struct ExprVal *),
 struct ExprVal * (**PtrOpSemantic)(struct ExprVal *, struct ExprVal *, struct SimpleCtype *),
 struct PropList *(**SafetyConstrait)(struct ExprVal *, struct ExprVal *),
 struct ExprVal *(**UnsignedOp)(struct ExprVal *, struct environment *)) {
   *OpSemantic = NULL;
   *PtrOpSemantic = NULL;
   switch (op) {
   case T_PLUS: {
      if (SimpleCtypeIsIntType(expr_type)) {
         assert(SimpleCtypeIsIntType(expr1_type) && SimpleCtypeIsIntType(expr2_type));
         switch (expr_type->t) {
         case C_int8:
            if (expr_type->d.CINT8.s == Signed) {
               *SafetyConstrait = BinPlusSafetyConstraitInt8;
               *UnsignedOp = OpSemanticI;
            }
            else {
               *SafetyConstrait = BinPlusSafetyConstraitUInt8;
               *UnsignedOp = OpSemanticU8;
            }
            break;
         case C_int16:
            if (expr_type->d.CINT16.s == Signed) {
               *SafetyConstrait = BinPlusSafetyConstraitInt16;
               *UnsignedOp = OpSemanticI;
            }
            else {
               *SafetyConstrait = BinPlusSafetyConstraitUInt16;
               *UnsignedOp = OpSemanticU16;
            }
            break;
         case C_int32:
            if (expr_type->d.CINT32.s == Signed) {
               *SafetyConstrait = BinPlusSafetyConstraitInt32;
               *UnsignedOp = OpSemanticI;
            }
            else {
               *SafetyConstrait = BinPlusSafetyConstraitUInt32;
               *UnsignedOp = OpSemanticU32;
            }
            break;
         case C_int64:
            if (expr_type->d.CINT64.s == Signed) {
               *SafetyConstrait = BinPlusSafetyConstraitInt64;
               *UnsignedOp = OpSemanticI;
            }
            else {
               *SafetyConstrait = BinPlusSafetyConstraitUInt64;
               *UnsignedOp = OpSemanticU64;
            }
            break;
         default:
            fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
            fprintf(stderr, "type: ");
            PrintSimpleCtypeFile(expr_type, env, stderr);
            exit(-1);
         }
         *OpSemantic = OpSemanticPlus;
      } else if (SimpleCtypeIsPointer(expr_type)) {
         if (SimpleCtypeIsPointer(expr1_type)) {
            assert(SimpleCtypeIsIntType(expr2_type));
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *PtrOpSemantic = OpSemanticPtrLeftPlus;
         } else if (expr2_type->t == C_pointer) {
            assert(SimpleCtypeIsIntType(expr1_type));
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *PtrOpSemantic = OpSemanticPtrRightPlus;
         } else {
            fprintf(stderr, "Error: ExprExecRightValue: unknown pointer type %s %d\n", __FILE__, __LINE__);
            exit(-1);
         }
      } else {
         fprintf(stderr, "Error: ExprExecRightValue: type error %s %d\n", __FILE__, __LINE__);
         exit(-1);
      }
      break;
   }
   case T_MINUS: {
      if (SimpleCtypeIsPointer(expr1_type) && SimpleCtypeIsPointer(expr2_type)) {
         *SafetyConstrait = SafetyConstraitNoConstrait2;
         *PtrOpSemantic = OpSemanticPtrMinusPtr;
      } else if (SimpleCtypeIsPointer(expr1_type) && SimpleCtypeIsIntType(expr2_type)) {
         *SafetyConstrait = SafetyConstraitNoConstrait2;
         *PtrOpSemantic = OpSemanticPtrMinusInt;
      } else if (SimpleCtypeIsIntType(expr1_type) && SimpleCtypeIsIntType(expr2_type)) {
         switch (expr_type->t) {
         case C_int8:
            if (expr_type->d.CINT8.s == Signed) {
               *SafetyConstrait = BinMinusSafetyConstraitInt8;
               *UnsignedOp = OpSemanticI;
            }
            else {
               *SafetyConstrait = BinMinusSafetyConstraitUInt8;
               *UnsignedOp = OpSemanticU8;
            }
            break;
         case C_int16:
            if (expr_type->d.CINT16.s == Signed) {
               *SafetyConstrait = BinMinusSafetyConstraitInt16;
               *UnsignedOp = OpSemanticI;
            }
            else {
               *SafetyConstrait = BinMinusSafetyConstraitUInt16;
               *UnsignedOp = OpSemanticU16;
            }
            break;
         case C_int32:
            if (expr_type->d.CINT32.s == Signed) {
               *SafetyConstrait = BinMinusSafetyConstraitInt32;
               *UnsignedOp = OpSemanticI;
            }
            else {
               *SafetyConstrait = BinMinusSafetyConstraitUInt32;
               *UnsignedOp = OpSemanticU32;
            }
            break;
         case C_int64:
            if (expr_type->d.CINT64.s == Signed) {
               *SafetyConstrait = BinMinusSafetyConstraitInt64;
               *UnsignedOp = OpSemanticI;
            }
            else {
               *SafetyConstrait = BinMinusSafetyConstraitUInt64;
               *UnsignedOp = OpSemanticU64;
            }
            break;
         default:
            fprintf(stderr, "Error: ExprExecRightValue: type error %s %d\n", __FILE__, __LINE__);
            fprintf(stderr, "type: ");
            PrintSimpleCtypeFile(expr_type, env, stderr);
            exit(-1);
         }
         *OpSemantic = OpSemanticMinus;
      } else {
         fprintf(stderr, "Error: ExprExecRightValue: type error %s %d\n", __FILE__, __LINE__);
         exit(-1);
      }
      break;
   }
   case T_MUL:
      switch (expr_type->t) {
      case C_int8:
         if (expr_type->d.CINT8.s == Signed) {
            *SafetyConstrait = BinMulSafetyConstraitInt8;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinMulSafetyConstraitUInt8;
            *UnsignedOp = OpSemanticU8;
         }
         break;
      case C_int16:
         if (expr_type->d.CINT16.s == Signed) {
            *SafetyConstrait = BinMulSafetyConstraitInt16;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinMulSafetyConstraitUInt16;
            *UnsignedOp = OpSemanticU16;
         }
         break;
      case C_int32:
         if (expr_type->d.CINT32.s == Signed) {
            *SafetyConstrait = BinMulSafetyConstraitInt32;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinMulSafetyConstraitUInt32;
            *UnsignedOp = OpSemanticU32;
         }
         break;
      case C_int64:
         if (expr_type->d.CINT64.s == Signed) {
            *SafetyConstrait = BinMulSafetyConstraitInt64;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinMulSafetyConstraitUInt64;
            *UnsignedOp = OpSemanticU64;
         }
         break;
      default:
         fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
         exit(-1);
      }
      *OpSemantic = OpSemanticMul;
      break;
   case T_DIV:
      switch (expr_type->t) {
      case C_int8:
         if (expr_type->d.CINT8.s == Signed) {
            *SafetyConstrait = BinDivSafetyConstraitInt8;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinDivSafetyConstraitUnsigned;
            *UnsignedOp = OpSemanticI;
         }
         break;
      case C_int16:
         if (expr_type->d.CINT16.s == Signed) {
            *SafetyConstrait = BinDivSafetyConstraitInt16;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinDivSafetyConstraitUnsigned;
            *UnsignedOp = OpSemanticI;
         }
         break;
      case C_int32:
         if (expr_type->d.CINT32.s == Signed) {
            *SafetyConstrait = BinDivSafetyConstraitInt32;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinDivSafetyConstraitUnsigned;
            *UnsignedOp = OpSemanticI;
         }
         break;
      case C_int64:
         if (expr_type->d.CINT64.s == Signed) {
            *SafetyConstrait = BinDivSafetyConstraitInt64;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinDivSafetyConstraitUnsigned;
            *UnsignedOp = OpSemanticI;
         }
         break;
      default:
         fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
         exit(-1);
      }
      *OpSemantic = OpSemanticDiv;
      break;
   case T_MOD:
      switch (expr_type->t) {
      case C_int8:
         if (expr_type->d.CINT8.s == Signed) {
            *SafetyConstrait = BinModSafetyConstraitInt8;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinModSafetyConstraitUnsigned;
            *UnsignedOp = OpSemanticI;
         }
         break;
      case C_int16:
         if (expr_type->d.CINT16.s == Signed) {
            *SafetyConstrait = BinModSafetyConstraitInt16;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinModSafetyConstraitUnsigned;
            *UnsignedOp = OpSemanticI;
         }
         break;
      case C_int32:
         if (expr_type->d.CINT32.s == Signed) {
            *SafetyConstrait = BinModSafetyConstraitInt32;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinModSafetyConstraitUnsigned;
            *UnsignedOp = OpSemanticI;
         }
         break;
      case C_int64:
         if (expr_type->d.CINT64.s == Signed) {
            *SafetyConstrait = BinModSafetyConstraitInt64;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *SafetyConstrait = BinModSafetyConstraitUnsigned;
            *UnsignedOp = OpSemanticI;
         }
         break;
      default:
         fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
         exit(-1);
      }
      *OpSemantic = OpSemanticMod;
      break;
   case T_BAND:
      switch (expr_type->t) {
      case C_int8:
         if (expr_type->d.CINT8.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         } 
         break;
      case C_int16:
         if (expr_type->d.CINT16.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         }
         break;
      case C_int32:
         if (expr_type->d.CINT32.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         }
         break;
      case C_int64:
         if (expr_type->d.CINT64.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         }
         break;
      default:
         fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
         fprintf(stderr, "type: ");
         PrintSimpleCtypeFile(expr_type, env, stderr);
         exit(-1);
      }
      *OpSemantic = OpSemanticBitand;
      break;
   case T_BOR:
      switch (expr_type->t) {
      case C_int8:
         if (expr_type->d.CINT8.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         } 
         break;
      case C_int16:
         if (expr_type->d.CINT16.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         }
         break;
      case C_int32:
         if (expr_type->d.CINT32.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         }
         break;
      case C_int64:
         if (expr_type->d.CINT64.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         }
         break;
      default:
         fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
         fprintf(stderr, "type: ");
         PrintSimpleCtypeFile(expr_type, env, stderr);
         exit(-1);
      }
      *OpSemantic = OpSemanticBitor;
      break;
   case T_XOR:
      switch (expr_type->t) {
      case C_int8:
         if (expr_type->d.CINT8.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         } 
         break;
      case C_int16:
         if (expr_type->d.CINT16.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         }
         break;
      case C_int32:
         if (expr_type->d.CINT32.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         }
         break;
      case C_int64:
         if (expr_type->d.CINT64.s == Signed) {
            *SafetyConstrait = SafetyConstraitNoConstrait2;
            *UnsignedOp = OpSemanticI;
         }
         else {
            *UnsignedOp = OpSemanticI;
            *SafetyConstrait = SafetyConstraitNoConstrait2;
         }
         break;
      default:
         fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
         fprintf(stderr, "type: ");
         PrintSimpleCtypeFile(expr_type, env, stderr);
         exit(-1);
      }
      *OpSemantic = OpSemanticXor;
      break;
   case T_SHL: {
      switch (expr_type->t) {
      case C_int8: {
         if (expr_type->d.CINT8.s == Signed) {
            *SafetyConstrait = BinShlSafetyConstraitInt8;
            *UnsignedOp = OpSemanticI;
         } else {
            *SafetyConstrait = BinShlSafetyConstraitUInt8;
            *UnsignedOp = OpSemanticU8;
         }
         break;
      }
      case C_int16:
         if (expr_type->d.CINT16.s == Signed) {
            *SafetyConstrait = BinShlSafetyConstraitInt16;
            *UnsignedOp = OpSemanticI;
         } else {
            *SafetyConstrait = BinShlSafetyConstraitUInt16;
            *UnsignedOp = OpSemanticU16;
         }
         break;
      case C_int32: {
         if (expr_type->d.CINT32.s == Signed) {
            *SafetyConstrait = BinShlSafetyConstraitInt32;
            *UnsignedOp = OpSemanticI;
         } else {
            *SafetyConstrait = BinShlSafetyConstraitUInt32;
            *UnsignedOp = OpSemanticU32;
         }
         break;
      }
      case C_int64: {
         if (expr_type->d.CINT64.s == Signed) {
            *SafetyConstrait = BinShlSafetyConstraitInt64;
            *UnsignedOp = OpSemanticI;
         } else {
            *SafetyConstrait = BinShlSafetyConstraitUInt64;
            *UnsignedOp = OpSemanticU64;
         }
         break;
      }
      default:
         fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
         fprintf(stderr, "type: ");
         PrintSimpleCtypeFile(expr_type, env, stderr);
         exit(-1);
      }
      *OpSemantic = OpSemanticShl;
      break;
   }
   case T_SHR: {
      switch (expr_type->t) {
      case C_int8:
         if (expr_type->d.CINT8.s == Signed) {
            *SafetyConstrait = BinShrSafetyConstraitInt8;
            *UnsignedOp = OpSemanticI;
         } else {
            *SafetyConstrait = BinShrSafetyConstraitUInt8;
            *UnsignedOp = OpSemanticI;
         }
         break;
      case C_int16:
         if (expr_type->d.CINT16.s == Signed) {
            *SafetyConstrait = BinShrSafetyConstraitInt16;
            *UnsignedOp = OpSemanticI;
         } else {
            *SafetyConstrait = BinShrSafetyConstraitUInt16;
            *UnsignedOp = OpSemanticI;
         }
         break;
      case C_int32:
         if (expr_type->d.CINT32.s == Signed) {
            *SafetyConstrait = BinShrSafetyConstraitInt32;
            *UnsignedOp = OpSemanticI;
         } else {
            *SafetyConstrait = BinShrSafetyConstraitUInt32;
            *UnsignedOp = OpSemanticI;
         }
         break;
      case C_int64:
         if (expr_type->d.CINT64.s == Signed) {
            *SafetyConstrait = BinShrSafetyConstraitInt64;
            *UnsignedOp = OpSemanticI;
         } else {
            *SafetyConstrait = BinShrSafetyConstraitUInt64;
            *UnsignedOp = OpSemanticI;
         }
         break;
      default:
         fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
         exit(-1);
      }
      *OpSemantic = OpSemanticShr;
      break;
   }
   default:
      printf("Error: Unknown binary operator %s %d\n", __FILE__, __LINE__);
      break;
   }
}

struct ExprExecRetType * ExprExecRightValueBinop(struct Assertion * asrt,
                                                 struct Cexpr * expr,
                                                 struct environment * env) {
   struct ExprVal * (*OpSemantic)(struct ExprVal *, struct ExprVal *);
   struct ExprVal * (*PtrOpSemantic)(struct ExprVal *, struct ExprVal *, struct SimpleCtype *);
   struct PropList *(*SafetyConstrait)(struct ExprVal *, struct ExprVal *);
   struct ExprVal *(*UnsignedOp)(struct ExprVal *, struct environment *);
   GetBinarySemantics(expr->d.C_BINOP.op, expr->type, expr->d.C_BINOP.expr1->type,
                      expr->d.C_BINOP.expr2->type, env,
                      &OpSemantic, &PtrOpSemantic, &SafetyConstrait, &UnsignedOp);
   if (OpSemantic != NULL) {
      return BinaryOpExec(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, env, OpSemantic, SafetyConstrait, UnsignedOp, (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
   } else {
      return PtrBinaryOpExec(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, GetPointedType(expr->d.C_BINOP.expr1->type), env, PtrOpSemantic, SafetyConstrait, (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
   }
}

struct ExprExecRetType * ExprExecRightValue(struct Assertion * asrt, struct Cexpr * expr, struct environment * env) {
   struct ExprExecRetType * ret;
   struct ExprVal * val;
   struct ExprExecRetType * inside_ret;
   if (expr == NULL) {
      ret = NewExprExecRetType();
      ret->ret_value = ExprExecRetValueCons(asrt, NULL, PropListNil(), IntListNil(), ret->ret_value);
      return ret;
   }
   if (expr->type != NULL) { // ==NULL only for frontend
      if (expr->type->t == C_array) {
         return ExprExecLeftValue(asrt, expr, env);
      }
   }
   switch (expr->t) {
      case C_CONST:
         ret = ConstExec(expr->d.C_CONST.number, expr->type, asrt);
         break;
      case C_VAR:
         val = VarExec_r(asrt, expr->d.C_VAR.id, env);
         if (val == NULL) {
            failwith("Error: GetDataAtvalue return NULL\n");
         }
         ret = NewExprExecRetType();
         ret->ret_value = ExprExecRetValueCons(asrt, val, PropListNil(), IntListNil(), ret->ret_value);
         break;
      case C_DEREF:
         inside_ret = ExprExecRightValue(asrt, expr->d.C_DEREF.expr, env);
         ret = DerefExec(inside_ret, expr->type, env);
         break;
      case C_ADDROF:
         ret = ExprExecLeftValue(asrt, expr->d.C_DEREF.expr, env);
         break;
      case C_UNOP: {
         struct PropList *(*SafetyConstrait)(struct ExprVal *);
         struct ExprVal *(*UnsignedOp)(struct ExprVal *, struct environment *);
         switch (expr->d.C_UNOP.op) {
            case T_NOTBOOL:
               SafetyConstrait = SafetyConstraitNoConstrait;
               ret = CondUnaryOpExec(asrt, expr->d.C_UNOP.expr, env, OpSemanticNot, SafetyConstrait, 
                                 (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_NOTINT:
               switch (expr->type->t) {
                  case C_int8: {
                     if (expr->type->d.CINT8.s == Unsigned) {
                        UnsignedOp = OpSemanticI;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     }
                     else {
                        UnsignedOp = OpSemanticI;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     }
                     break;
                  }
                  case C_int16: {
                     if (expr->type->d.CINT16.s == Unsigned) {
                        UnsignedOp = OpSemanticI;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     }
                     else {
                        UnsignedOp = OpSemanticI;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     }
                     break;
                  }
                  case C_int32: {
                     if (expr->type->d.CINT32.s == Unsigned) {
                        UnsignedOp = OpSemanticI;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     }
                     else {
                        UnsignedOp = OpSemanticI;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     }
                     break;
                  }
                  case C_int64: {
                     if (expr->type->d.CINT64.s == Unsigned) {
                        UnsignedOp = OpSemanticI;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     }
                     else {
                        UnsignedOp = OpSemanticI;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     }
                     break;
                  }
                  default: {
                     fprintf(stderr, "Error: ExprExecRightValue: unknown expr type %s %d\n", __FILE__, __LINE__);
                     fprintf(stderr, "type: ");
                     PrintSimpleCtypeFile(expr->type, env, stderr);
                     exit(-1);
                  }
               }
               ret = UnaryOpExec(asrt, expr->d.C_UNOP.expr, env, OpSemanticBitnot, SafetyConstrait, UnsignedOp,
                                 (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_UMINUS:
               switch (expr->type->t) {
                  case C_int8:
                     if (expr->type->d.CINT8.s == Signed) {
                        SafetyConstrait = UnNegSafetyConstraitInt8;
                        UnsignedOp = OpSemanticI;
                     }
                     else {
                        UnsignedOp = OpSemanticU8;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     } 
                     break;
                  case C_int16:
                     if (expr->type->d.CINT16.s == Signed) {
                        SafetyConstrait = UnNegSafetyConstraitInt16;
                        UnsignedOp = OpSemanticI;
                     }
                     else {
                        UnsignedOp = OpSemanticU16;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                     }
                     break;
                  case C_int32:
                     if (expr->type->d.CINT32.s == Signed) {
                        SafetyConstrait = UnNegSafetyConstraitInt32;
                        UnsignedOp = OpSemanticI;
                     }
                      else {
                        UnsignedOp = OpSemanticU32;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                      }
                     break;
                  case C_int64:
                     if (expr->type->d.CINT64.s == Signed) {
                        SafetyConstrait = UnNegSafetyConstraitInt64;
                        UnsignedOp = OpSemanticI;
                     }
                      else {
                        UnsignedOp = OpSemanticU64;
                        SafetyConstrait = SafetyConstraitNoConstrait;
                      }
                     break;
                  default:
                     fprintf(stderr, "Error: ExprExecRightValue: unknown type %s %d\n", __FILE__, __LINE__);
                     fprintf(stderr, "type: ");
                     PrintSimpleCtypeFile(expr->type, env, stderr);
                     exit(-1);
               }
               ret = UnaryOpExec(asrt, expr->d.C_UNOP.expr, env, OpSemanticNeg, SafetyConstrait, UnsignedOp,
                                 (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_UPLUS:
               SafetyConstrait = SafetyConstraitNoConstrait;
               UnsignedOp = OpSemanticI;
               ret = UnaryOpExec(asrt, expr->d.C_UNOP.expr, env, OpSemanticPos, SafetyConstrait, UnsignedOp,
                                 (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            default:
               fprintf(stderr, "Error: ExprExecRightValue: unknown unary operator %s %d\n", __FILE__, __LINE__);
               exit(-1);
         }
         break;
      }
      case C_BINOP: {
         struct PropList *(*SafetyConstrait)(struct ExprVal *, struct ExprVal *);
         switch (expr->d.C_BINOP.op) {
            case T_OR:
               SafetyConstrait = SafetyConstraitNoConstrait2;
               ret = ORExecShortCircuit(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, env,
                                       (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_AND:
               SafetyConstrait = SafetyConstraitNoConstrait2;
               ret = ANDExecShortCircuit(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, env,
                                       (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_LT:
               SafetyConstrait = SafetyConstraitNoConstrait2;
               ret = CondBinaryOpExec(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, env,
                                  OpSemanticLt, SafetyConstrait,
                                  (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_GT:
                SafetyConstrait = SafetyConstraitNoConstrait2;
               ret = CondBinaryOpExec(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, env,
                                  OpSemanticGt, SafetyConstrait,
                                  (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_LE:
                SafetyConstrait = SafetyConstraitNoConstrait2;
               ret = CondBinaryOpExec(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, env,
                                  OpSemanticLe, SafetyConstrait,
                                  (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_GE:
                SafetyConstrait = SafetyConstraitNoConstrait2;
               ret = CondBinaryOpExec(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, env,
                                  OpSemanticGe, SafetyConstrait,
                                  (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_EQ:
                SafetyConstrait = SafetyConstraitNoConstrait2;
               ret = CondBinaryOpExec(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, env,
                                  OpSemanticEq, SafetyConstrait,
                                  (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            case T_NE:
                SafetyConstrait = SafetyConstraitNoConstrait2;
               ret = CondBinaryOpExec(asrt, expr->d.C_BINOP.expr1, expr->d.C_BINOP.expr2, env,
                                  OpSemanticNe, SafetyConstrait,
                                  (struct ExprExecRetType *(*)(struct Assertion *, void *, void *)) ExprExecRightValue);
               break;
            default:
               ret = ExprExecRightValueBinop(asrt, expr, env);
               break;
         }
         break;
      }
      case C_CAST:
         inside_ret = ExprExecRightValue(asrt, expr->d.C_CAST.expr, env);
         ret = CastExec(inside_ret, expr->d.C_CAST.expr->type, expr->type, env);
         break;
      case C_STRUCTFIELD: {
         inside_ret = ExprExecLeftValue(asrt, expr, env);
         ret = DerefExec(inside_ret, expr->type, env);
         break;
      }
      case C_UNIONFIELD:
         inside_ret = ExprExecLeftValue(asrt, expr, env);
         ret = DerefExec(inside_ret, expr->type, env);
         break;
      case C_SIZEOF:
         ret = SizeofExec(asrt, expr->d.C_SIZEOF.inner_type);
         break;
      case C_INDEX:
         inside_ret = ExprExecLeftValue(asrt, expr, env);
         ret = DerefExec(inside_ret, expr->type, env);
         break;
      case C_CALL: {
         ret = NewExprExecRetType();
         struct ExprExecRetType * func_expr = ExprExecRightValue(asrt, expr->d.C_CALL.func, env);
         ret->witness = WitnessMerge(func_expr->witness, ret->witness);
         for (struct ExprExecRetValue *i = func_expr->ret_value; i != NULL; i = i->next) {
            struct func_info * func = FindFuncInfo(i->val, i->asrt, env);
            struct func_spec * spec;
            if (expr->d.C_CALL.spec_name == NULL) {
               spec = func->spec;
            } else {
               for (spec = func->spec; spec != NULL && strcmp(spec->name, expr->d.C_CALL.spec_name) != 0; spec = spec->next);
            }
            if (spec == NULL) {
                failwith("Cannot find the function spec named %s\n", expr->d.C_CALL.spec_name);
            }
            struct ExprListExecRetType * args_calc = ExprListExecRightValue(i->asrt, expr->d.C_CALL.args_exprs, env);
            ret->witness = WitnessMerge(args_calc->witness, ret->witness);
            for (struct ExprListExecRetValue * j = args_calc->ret_value; j != NULL; j = j->next) {
               struct hashtbl * prefill = create_hashtbl(hash_string, string_equal);
               struct ExprExecRetType * prt = GetFuncPrefill(AsrtDeepCopy(j->asrt), expr->d.C_CALL.vargs, prefill, env);
               WitnessFree(prt->witness);
               AsrtFree(prt->ret_value->asrt);
               struct FuncCallRetType * tmp = FuncCallExec(j->asrt, env, func->param, spec, prefill, j->val, NORMAL_CALL, expr->d.C_CALL.scopes);
               if (tmp == NULL) {
                  failwith("Cannot derive the precondition of function %s\n", func->name);
               }
               free_hashtbl(prefill);
               ret->witness = WitnessMerge(tmp->ret->witness, ret->witness);
               ret->ret_value = ExprExecRetValueLink(ret->ret_value, tmp->ret->ret_value);
            }
         }
         break;
      }
      case C_TERNARY: {
         struct TrueFalseConditionPair cond_ret = CondExec(asrt, expr->d.C_TERNARY.cond, env);
         struct ExprExecRetType * true_ret = AsrtListExprExecRightValue(cond_ret.true_part, expr->d.C_TERNARY.true_expr, env);
         struct ExprExecRetType * false_ret = AsrtListExprExecRightValue(cond_ret.false_part, expr->d.C_TERNARY.false_expr, env);
         ret = NewExprExecRetType();
         ret->ret_value = ExprExecRetValueLink(true_ret->ret_value, false_ret->ret_value);
         ret->witness = WitnessMerge(true_ret->witness, false_ret->witness);
         break;
      }
   }
   return ret;
}

struct ExprListExecRetType * ExprListExecRightValue(struct Assertion * asrt, struct CexprList * exprs_list, struct environment * env) {
   struct ExprListExecRetType * ret;
   ret = NewExprListExecRetType();
   ret->ret_value = ExprListExecRetValueCons(asrt, ExprValListNil(), PropListNil(), IntListNil(), ret->ret_value);
   struct CexprListNode * expr = exprs_list->head;
   while (expr != NULL) {
      struct ExprListExecRetType * tmp = NewExprListExecRetType();
      tmp->witness = ret->witness;
      ret->witness = NULL;
      struct ExprListExecRetValue * iter = ret->ret_value;
      while (iter != NULL) {
         struct ExprExecRetType * single = ExprExecRightValue(AsrtDeepCopy(iter->asrt), expr->data, env);
         struct ExprExecRetValue * single_iter = single->ret_value;
         while (single_iter != NULL) {
            tmp->ret_value = ExprListExecRetValueCons(
               single_iter->asrt,
               ExprValListSnoc(single_iter->val, ExprValListDeepCopy(iter->val)),
               PropListLink(single_iter->constraits, PropListDeepCopy(iter->constraits)),
               IntListLink(single_iter->introed_vars, IntListDeepCopy(iter->introed_vars)),
               tmp->ret_value);
            single_iter = single_iter->next;
         }
         tmp->witness = WitnessMerge(single->witness, tmp->witness);
         iter = iter->next;
      }
      ExprListExecRetTypeFree(ret);
      ret = tmp;
      expr = expr->next;
   }
   return ret;
}

struct ExprExecRetType * StructFieldExecLeftValue(struct ExprExecRetType * inside_ret, int field_id) {
   struct ExprExecRetValue * new_list = ExprExecRetValueNil();
   struct ExprExecRetValue * inside = inside_ret->ret_value;
   while (inside != NULL) {
      new_list = ExprExecRetValueCons(inside->asrt, ExprVal_VFIELD_ADDRESS(inside->val, field_id), PropListNil(), IntListNil(), new_list);
      inside = inside->next;
   }
   ExprExecRetValueFree(inside_ret->ret_value);
   inside_ret->ret_value = new_list;
   return inside_ret;
}

struct ExprExecRetType * UnionFieldExecLeftValue(struct ExprExecRetType * inside_ret, int field_id) {
   struct ExprExecRetValue * new_list = ExprExecRetValueNil();
   struct ExprExecRetValue * inside = inside_ret->ret_value;
   while (inside != NULL) {
      new_list = ExprExecRetValueCons(inside->asrt, ExprVal_VFIELD_ADDRESS(inside->val, field_id), PropListNil(), IntListNil(), new_list);
      inside = inside->next;
   }
   ExprExecRetValueFree(inside_ret->ret_value);
   inside_ret->ret_value = new_list;
   return inside_ret;
}

struct ExprExecRetType * ExprExecLeftValue(struct Assertion * asrt, struct Cexpr * expr, struct environment * env) {
   assert(expr != NULL);
   assert(expr->t == C_DEREF || expr->t == C_VAR || expr->t == C_STRUCTFIELD || expr->t == C_UNIONFIELD || expr->t == C_INDEX);
   struct ExprExecRetType * ret;
   struct ExprExecRetType * inside;
   if (expr->t == C_VAR) {
      ret = NewExprExecRetType();
      ret->ret_value = ExprExecRetValueCons(asrt, VarExec_l(asrt, expr->d.C_VAR.id, env), PropListNil(), IntListNil(), ret->ret_value);
   } else if (expr->t == C_DEREF) {
      ret = ExprExecRightValue(asrt, expr->d.C_DEREF.expr, env);
   } else if (expr->t == C_STRUCTFIELD) {
      inside = ExprExecLeftValue(asrt, expr->d.C_STRUCTFIELD.expr, env);
      ret = StructFieldExecLeftValue(inside, expr->d.C_STRUCTFIELD.field_id);
   } else if (expr->t == C_UNIONFIELD) {
      inside = ExprExecLeftValue(asrt, expr->d.C_UNIONFIELD.expr, env);
      ret = UnionFieldExecLeftValue(inside, expr->d.C_UNIONFIELD.field_id);
   } else if (expr->t == C_INDEX) {
      ret = NewExprExecRetType();
      struct ExprExecRetType * base_addr = ExprExecRightValue(asrt, expr->d.C_INDEX.arr_expr, env);
      ret->witness = WitnessMerge(base_addr->witness, ret->witness);
      struct ExprExecRetValue * iter = base_addr->ret_value;
      while (iter != NULL) {
         inside = ExprExecRightValue(iter->asrt, expr->d.C_INDEX.inner_expr, env);
         ret->witness = WitnessMerge(inside->witness, ret->witness);
         struct ExprExecRetValue * iter2;
         iter2 = inside->ret_value;
         while (iter2 != NULL) {
            struct ExprVal * offset = ExprVal_VBOP(Omul, iter2->val, ExprVal_SIZE_OF(SimpleCtypeDeepCopy(expr->type)));
            struct ExprVal * addr = ExprVal_VBOP(Oadd, iter->val, offset);
            struct PropList * constraits;
            struct IntList * introd_vars;
            if (iter2->next == NULL) {
               constraits = PropListLink(iter->constraits, iter2->constraits);
               introd_vars = IntListLink(iter->introed_vars, iter2->introed_vars);
            } else {
               constraits = PropListLink(PropListDeepCopy(iter->constraits), iter2->constraits);
               introd_vars = IntListLink(IntListDeepCopy(iter->introed_vars), iter2->introed_vars);
            }
            ret->ret_value = ExprExecRetValueCons(iter2->asrt, addr, constraits, introd_vars, ret->ret_value);
            iter2 = iter2->next;
         }
         ExprExecRetTypeFree(inside);
         iter = iter->next;
      }
      ExprExecRetTypeFree(base_addr);
   }
   return ret;
}

struct ExprExecRetType * AsrtListExprExecRightValue(struct AsrtList * asrt_list, struct Cexpr * expr, struct environment * env) {
   struct ExprExecRetType * ret = NewExprExecRetType();
   while (asrt_list != NULL) {
      struct ExprExecRetType * tmp = ExprExecRightValue(asrt_list->head, expr, env);
      ret->ret_value = ExprExecRetValueLink(ret->ret_value, tmp->ret_value);
      ret->witness = WitnessMerge(tmp->witness, ret->witness);
      asrt_list->head = NULL;
      asrt_list = asrt_list->next;
   }
   AsrtListFree(asrt_list);
   return ret;
}

struct ExprExecRetType * AsrtListExprExecLeftValue(struct AsrtList * asrt_list, struct Cexpr * expr, struct environment * env) {
   struct ExprExecRetType * ret = NewExprExecRetType();
   while (asrt_list != NULL) {
      struct ExprExecRetType * tmp = ExprExecLeftValue(asrt_list->head, expr, env);
      ret->ret_value = ExprExecRetValueLink(ret->ret_value, tmp->ret_value);
      ret->witness = WitnessMerge(tmp->witness, ret->witness);
      asrt_list->head = NULL;
      asrt_list = asrt_list->next;
   }
   AsrtListFree(asrt_list);
   return ret;
}
