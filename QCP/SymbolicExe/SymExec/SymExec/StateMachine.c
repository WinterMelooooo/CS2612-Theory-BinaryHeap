#include <assert.h>
#include "StateDef.h"
#include "StateMachine.h"
#include "ExprExec.h"
#include "CexprExec.h"
#include "MemOracle.h"
#include "WitnessDef/Witness.h"
#include "FuncCall.h"
#include "../Trans/TypeTrans.h"
#include "../Trans/PropToSmtPropTrans.h"
#include "../CDef/PartialStmt.h"
#include "../AsrtDef/AssDef.h"
#include "../Utility/PSstmtPrinter.h"
#include "../Utility/OperatorTranser.h"
#include "../Utility/LogicNameManager.h"
#include "../Utility/InnerAsrtPrinter.h"
#include "../Automation/AutomationSolver/CustomSolver.h"
#include "../../compiler/utils.h"

int exec_outflag = 1;

extern void cpa_to_old(struct AsrtList *a, struct persistent_env *env);

struct AsrtList * CompleteInv(struct AsrtList * pre, struct AsrtList * inv, struct StringList * scopes, struct environment * env) {
   struct AsrtList * ret;
   delete_twin_assertion(inv, &env->persist);
   struct WhichImpliesRetType * res = PartialSolveInv(pre, inv, scopes, env);
   if (res == NULL) {
      fprintf(stderr, "Error: Partial Invariant Solve failed\n");
      exit(1);
   }
   ret = res->asrt;
   struct AsrtList * tmp = AsrtListDeepCopy(res->asrt);
   cpa_to_old(tmp, &env->persist);
   add_twin_assertion(res->asrt, tmp, &env->persist);
   AsrtListNormalizeName(res->asrt, env);
   WitnessFree(res->witness);
   free(res);
   if (exec_outflag) {
      printf("Partial Solved Invariant: \n");
      PrintAsrtList(ret, env);
      printf("\n");
   }
   return ret;
}

struct StateStack * StartStateMachineInFunc() {
   struct StateStack * state_stack;
   state_stack = StateStackPush(NULL, CreateState(In_func_block, NULL));
   return state_stack;
}

struct StateStack * StartStateMachineInStmt(struct PartialStmt * begin) {
   struct StateStack * state_stack;
   state_stack = StartStateMachineInFunc(); // to support return statement
   struct State * new_state;
   if (begin->t == PS_while_condition) {
      new_state = CreateState(In_while_block, state_stack);
      state_stack = StateStackPush(state_stack, new_state);
   } else if (begin->t == PS_do) {
      new_state = CreateState(In_do_block, state_stack);
      state_stack = StateStackPush(state_stack, new_state);
   } else if (begin->t == PS_for) {
      new_state = CreateState(In_for_block, state_stack);
      state_stack = StateStackPush(state_stack, new_state);
   } else if (begin->t == PS_block_begin) {
      new_state = CreateState(In_block, state_stack);
      state_stack = StateStackPush(state_stack, new_state);
   }
   return state_stack;
}

struct AsrtListWitnessPair WriteMem(struct Assertion * asrt, struct ExprVal * addr, struct SimpleCtype * type, struct ExprVal * val, struct environment * env) {
   if (ReplaceDataAtValue(asrt, addr, val) == 0) return MakeAsrtListWitnessPair(AsrtListCons(asrt, AsrtListNil()), NewWitness());
   struct Witness * witness = NewWitness();
   struct Assertion * tmp = CreateAsrt();
   tmp->sep_list = SepListCons(SepUndefDataAt(addr, type), tmp->sep_list);
   struct func_spec * spec = DeclareSpec(ExistListNil(), ExistListNil(),
                                          AsrtListCons(AsrtDeepCopy(tmp), AsrtListNil()),
                                          AsrtListCons(tmp, AsrtListNil()),
                                          NULL, NULL);
   struct FuncCallRetType * func_call_ret = FuncCallExec(asrt, env, VILNil(), spec, NULL, ExprValListNil(), FIELD_CALL, NULL);
   if (func_call_ret == NULL) {
      fprintf(stderr, "Assign Exec fail\n");
      exit(0);
   }
   witness = WitnessMerge(func_call_ret->ret->witness, witness);
   asrt = func_call_ret->ret->ret_value->asrt;
   func_call_ret->ret->ret_value->asrt = NULL;
   func_call_ret->ret->witness = NULL;
   FuncCallRetTypeFree(func_call_ret);
   if (ReplaceDataAtValue(asrt, addr, val) == 0) {
      asrt = TryFold(asrt, env);
      return MakeAsrtListWitnessPair(AsrtListCons(asrt, AsrtListNil()), witness);
   } else {
      fprintf(stderr, "Assign Exec fail\n");
      exit(0);
   }
}

struct AsrtListWitnessPair AssignExec(struct CSimpleCommand * comd, struct AsrtList * asrt_list, struct environment * env) {
   assert(comd->t == C_Assign);
   struct Witness * witness = NewWitness();
   struct AsrtList * ret = AsrtListNil();
   struct ExprExecRetType * lret = AsrtListExprExecLeftValue(asrt_list, comd->d.C_Assign.expr1, env);
   struct ExprExecRetValue * left = lret->ret_value;
   witness = WitnessMerge(lret->witness, witness);
   while (left != NULL) {
      struct ExprExecRetType * rret;
      if (comd->d.C_Assign.assign_type != T_ASSIGN) {
         struct ExprVal * (*OpSemantic)(struct ExprVal *, struct ExprVal *);
         struct ExprVal * (*PtrOpSemantic)(struct ExprVal *, struct ExprVal *, struct SimpleCtype *);
         struct PropList *(*SafetyConstrait)(struct ExprVal *, struct ExprVal *);
         struct ExprVal *(*UnsignedOp)(struct ExprVal *, struct environment *);
         GetBinarySemantics(InnerBinOpToUserBinOp(AriAsignOpTrans(comd->d.C_Assign.assign_type)),
                            comd->d.C_Assign.expr1->type,
                            comd->d.C_Assign.expr1->type,
                            comd->d.C_Assign.expr2->type,
                            env,
                            &OpSemantic, &PtrOpSemantic, &SafetyConstrait, &UnsignedOp);
         struct ExprExecRetType *rlret = DerefExecOne(left, comd->d.C_Assign.expr1->type, env);
         if (OpSemantic != NULL) {
            rret = BinaryOpExecHelper(rlret, comd->d.C_Assign.expr2, env, OpSemantic, SafetyConstrait, UnsignedOp, (void *)ExprExecRightValue);
         } else {
            rret = PtrBinaryOpExecHelper(rlret, comd->d.C_Assign.expr2, comd->d.C_Assign.expr1->type, env, PtrOpSemantic, SafetyConstrait, (void *)ExprExecRightValue);
         }
      } else {
         rret = ExprExecRightValue(left->asrt, comd->d.C_Assign.expr2, env);
      }
      struct ExprExecRetValue * right = rret->ret_value;
      witness = WitnessMerge(rret->witness, witness);
      while (right != NULL) {
         struct ExprVal * left_val;
         if (right->next == NULL) left_val = left->val;
         else left_val = ExprValDeepCopy(left->val);
         struct AsrtListWitnessPair pair = WriteMem(right->asrt, left_val, comd->d.C_Assign.expr1->type, right->val, env);
         right->asrt = pair.asrt_list->head;
         witness = WitnessMerge(pair.witness, witness);
         ret = AsrtListCons(right->asrt, ret);
         right = right->next;
      }
      left = left->next;
   }
   ExprExecRetTypeFree(lret);
   return MakeAsrtListWitnessPair(ret, witness);
}

struct AsrtListWitnessPair IncdecExec(struct CSimpleCommand * comd, struct AsrtList * asrt_list, struct environment * env) {
   enum AssignType assign_type;
   if (comd->d.C_Incdec.incdec_type == T_INC_F || comd->d.C_Incdec.incdec_type == T_INC_B) {
      assign_type = T_ADD_ASSIGN;
   } else {
      assign_type = T_SUB_ASSIGN;
   }
   struct CSimpleCommand * asgn_comd = CSimpleCommandAssign(assign_type, CexprDeepCopy(comd->d.C_Incdec.expr), CexprConst(1, SimpleCtypeInt32(Unsigned)));
   struct AsrtListWitnessPair ret = AssignExec(asgn_comd, asrt_list, env);
   CSimpleCommandFree(asgn_comd);
   return ret;
}

struct AsrtListWitnessPair ComputeExec(struct Cexpr * expr, struct AsrtList * asrt_list, struct environment * env) {
   struct Witness * witness = NewWitness();
   struct AsrtList * ret = AsrtListNil();
   struct ExprExecRetType * expr_ret_with_wit = AsrtListExprExecRightValue(asrt_list, expr, env);
   struct ExprExecRetValue * expr_ret = expr_ret_with_wit->ret_value;
   witness = WitnessMerge(expr_ret_with_wit->witness, witness);
   while (expr_ret != NULL) {
      ret = AsrtListCons(expr_ret->asrt, ret);
      ExprValFree(expr_ret->val);
      expr_ret = expr_ret->next;
   }
   ExprExecRetTypeFree(expr_ret_with_wit);
   return MakeAsrtListWitnessPair(ret, witness);
}

struct SymbolicExecRet StateMachineTransition(
            struct PartialStmt * ps, struct AsrtList * inv, 
            struct StateStack * state_stack, struct AsrtTuple * asrt,  
            struct environment * env, enum TransType trans_type) {
   struct State * new_state, * popped_state;
   struct ExprExecRetValue * expr_ret;
   struct ExprExecRetType * expr_ret_wit;
   struct TrueFalseConditionPair condition_ret;
   struct AsrtListWitnessPair asrt_wit_ret;
   struct Witness * witness = NewWitness();
   if (StateStackPeek(state_stack)->t == In_switch_block) {
      // Special Case: Statement before the first case should never be executed
      // See: https://en.cppreference.com/w/c/language/switch
      if (!(ps->t == PS_fst_case || ps->t == PS_default || ps->t == PS_vardef || ps->t == PS_block_begin || ps->t == PS_block_end)) {
         return MakeSymbolicExecRet(state_stack, asrt, inv, witness);
      }
   }
   switch (ps->t) {
      case PS_simple:
         switch (ps->d.PS_simple.comd->t) {
            case C_Skip:
               break;
            case C_Assign:
               asrt_wit_ret = AssignExec(ps->d.PS_simple.comd, asrt->nrm, env);
               asrt->nrm = asrt_wit_ret.asrt_list;
               witness = WitnessMerge(asrt_wit_ret.witness, witness);
               break;
            case C_Incdec:
               asrt_wit_ret = IncdecExec(ps->d.PS_simple.comd, asrt->nrm, env);
               asrt->nrm = asrt_wit_ret.asrt_list;
               witness = WitnessMerge(asrt_wit_ret.witness, witness);
               break;
            case C_Compute:
               asrt_wit_ret = ComputeExec(ps->d.PS_simple.comd->d.C_Compute.expr, asrt->nrm, env);
               asrt->nrm = asrt_wit_ret.asrt_list;
               witness = WitnessMerge(asrt_wit_ret.witness, witness);
               break;
         }
         break;
      case PS_break: {
         struct StateStack * stack_tmp = state_stack;
         while (1) {
            asrt->nrm = AsrtListVarPerish(asrt->nrm, stack_tmp->state, env);
            if (IsBreakRelatedType(stack_tmp->state->t)) {
               break;
            }
            stack_tmp = stack_tmp->next;
         }
         asrt->brk = AsrtListLink(asrt->brk, asrt->nrm);
         asrt->nrm = AsrtListNil();
         break;
      }
      case PS_continue: {
         struct StateStack * stack_tmp = state_stack;
         while (1) {
            asrt->nrm = AsrtListVarPerish(asrt->nrm, stack_tmp->state, env);
            if (IsContinueRelatedType(stack_tmp->state->t)) {
               break;
            }
            stack_tmp = stack_tmp->next;
         }
         asrt->cnt = AsrtListLink(asrt->cnt, asrt->nrm);
         asrt->nrm = AsrtListNil();
         break;
      }
      case PS_return: {
         struct StateStack * stack_tmp = state_stack;
         expr_ret_wit = AsrtListExprExecRightValue(asrt->nrm, ps->d.PS_return.ret_expr, env);
         expr_ret = expr_ret_wit->ret_value;
         witness = WitnessMerge(expr_ret_wit->witness, witness);
         while (1) {
            struct ExprExecRetValue * tmp = expr_ret;
            while (tmp != NULL) {
               tmp->asrt = AssertionVarPerish(tmp->asrt, stack_tmp->state, env);
               tmp = tmp->next;
            }
            if (stack_tmp->state->t == In_func_block) {
               break;
            }
            stack_tmp = stack_tmp->next;
         }
         asrt->nrm = AsrtListNil();
         struct FuncRetType * func_ret = FuncRetTypeNil();
         while (expr_ret != NULL) {
            func_ret = FuncRetTypeCons(expr_ret->asrt, expr_ret->val, func_ret);
            expr_ret = expr_ret->next;
         }
         ExprExecRetTypeFree(expr_ret_wit);
         asrt->ret = FuncRetTypeListCons(func_ret, ps->d.PS_return.scopes, asrt->ret);
         break;
      }
      case PS_while_condition: {
         if (trans_type == NormalTrans) {
            new_state = CreateState(In_while_block, state_stack);
            new_state->d.In_while_block.asrt->cnt = asrt->cnt;
            new_state->d.In_while_block.asrt->brk = asrt->brk;
            new_state->d.In_while_block.asrt->ret = asrt->ret;
            new_state->d.In_while_block.start = ps;
            new_state->d.In_while_block.inv = inv;
            inv = NULL;
            new_state->d.In_while_block.condition = ps->d.PS_while_condition.condition;
            asrt->cnt = AsrtListNil();
            asrt->brk = AsrtListNil();
            asrt->ret = FuncRetTypeListNil();
            if (new_state->d.In_while_block.inv == NULL) {
              //  printf("Warning: Invariant is not provided for while loop\n");
               new_state->d.In_while_block.inv_explicit = 0;
               new_state->d.In_while_block.precondition = AsrtListDeepCopy(asrt->nrm);
               condition_ret = AsrtListCondExec(asrt->nrm, ps->d.PS_while_condition.condition, env);
               new_state->d.In_while_block.asrt->nrm = condition_ret.false_part;
               asrt->nrm = condition_ret.true_part;
               witness = WitnessMerge(condition_ret.witness, witness);
            } else {
               new_state->d.In_while_block.inv_explicit = 1;
               witness->entailment_checker_wit = CheckEntailment(asrt->nrm, 
                                                                 new_state->d.In_while_block.inv, 
                                                                 ps->d.PS_while_condition.scopes, 
                                                                 env, witness->entailment_checker_wit);
               AsrtListFree(asrt->nrm);
               condition_ret = AsrtListCondExec(AsrtListDeepCopy(new_state->d.In_while_block.inv), ps->d.PS_while_condition.condition, env);
               asrt->nrm = condition_ret.true_part;
               new_state->d.In_while_block.asrt->nrm = condition_ret.false_part;
               witness = WitnessMerge(condition_ret.witness, witness);
            }
            state_stack = StateStackPush(state_stack, new_state);
            break;
         } else {
            witness->entailment_checker_wit = CheckEntailment(asrt->nrm, inv, 
                                                              ps->d.PS_while_condition.scopes, 
                                                              env, witness->entailment_checker_wit);
            AsrtListFree(asrt->nrm);
            asrt->nrm = AsrtListNil();
            break;
         }
      }
      case PS_if_condition:
         new_state = CreateState(In_if_then_block, state_stack);
         condition_ret = AsrtListCondExec(asrt->nrm, ps->d.PS_if_condition.condition, env);
         asrt->nrm = condition_ret.true_part;
         new_state->d.In_if_then_block.false_part_asrt = condition_ret.false_part;
         witness = WitnessMerge(condition_ret.witness, witness);
         state_stack = StateStackPush(state_stack, new_state);
         break;
      case PS_else:
         new_state = CreateState(In_if_else_block, state_stack);
         popped_state = StateStackPeek(state_stack);
         assert(popped_state->t == In_if_then_block);
         asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
         new_state->d.In_if_else_block.true_part_asrt = asrt->nrm;
         asrt->nrm = popped_state->d.In_if_then_block.false_part_asrt;
         state_stack = StateStackPop(state_stack);
         state_stack = StateStackPush(state_stack, new_state);
         break;
      case PS_do_while_condition: {
         popped_state = StateStackPeek(state_stack);
         assert(popped_state->t == In_do_block);
         if (ps->d.PS_do_while_condition.inv == NULL) {
            ps->d.PS_do_while_condition.inv = AsrtListDeepCopy(asrt->nrm);
            ps->d.PS_do_while_condition.inv_is_partial = 0;
         }
         if (ps->d.PS_do_while_condition.inv_is_partial) {
            ps->d.PS_do_while_condition.inv = CompleteInv(asrt->nrm, ps->d.PS_do_while_condition.inv, ps->d.PS_do_while_condition.scopes, env);
            ps->d.PS_do_while_condition.inv_is_partial = 0;
         }
         witness->entailment_checker_wit = CheckEntailment(asrt->nrm, 
                                                           ps->d.PS_do_while_condition.inv, 
                                                           ps->d.PS_do_while_condition.scopes,
                                                           env, witness->entailment_checker_wit);
         AsrtListFree(asrt->nrm);
         asrt->nrm = NULL;
         if (trans_type == TransForInvCheck) break;
         condition_ret = AsrtListCondExec(AsrtListDeepCopy(ps->d.PS_do_while_condition.inv),
                                          ps->d.PS_do_while_condition.condition, env);
         witness = WitnessMerge(condition_ret.witness, witness);
         struct StateStack * new_state_stack = 
            StartStateMachineInStmt(popped_state->d.In_do_block.start);
         new_state_stack->state->d.In_do_block.condition = ps->d.PS_do_while_condition.condition;
         struct SymbolicExecRet inv_check_ret =
             SymbolicExecForInvCheck(popped_state->d.In_while_block.start, ps, new_state_stack,
                                     CreateAsrtTuple(condition_ret.true_part, AsrtListNil(), AsrtListNil(), FuncRetTypeListNil()), env);
         witness = WitnessMerge(inv_check_ret.witness, witness);
         asrt->nrm = condition_ret.false_part;
         break;
      }
      case PS_block_begin:
         new_state = CreateState(In_block, state_stack);
         state_stack = StateStackPush(state_stack, new_state);
         break;
      case PS_block_end:
         popped_state = StateStackPeek(state_stack);
         switch (popped_state->t) {
            case In_func_block:
               asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
               break;
            case In_while_block:
               if (popped_state->d.In_while_block.inv_explicit == 0) {
                  struct AsrtList * real_inv;
                  struct AsrtList * tmp;
                  asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
                  tmp = AsrtListLink(asrt->nrm, asrt->cnt);
                  if (popped_state->d.In_while_block.condition == NULL) {
                    printf("Invalid Input for while condition.\n");
                    exit(1);
                  }
                  condition_ret = AsrtListCondExec(AsrtListDeepCopy(tmp), 
                                                popped_state->d.In_while_block.condition, env);
                  if (popped_state->d.In_while_block.start != NULL) {
                  struct StateStack * new_state_stack = 
                     StartStateMachineInStmt(popped_state->d.In_while_block.start);
                  new_state_stack->state->d.In_while_block.condition = popped_state->d.In_while_block.condition;
                  struct SymbolicExecRet inv_check_ret =
                      SymbolicExecForInvCheck(popped_state->d.In_while_block.start->next, ps, new_state_stack,
                                              CreateAsrtTuple(condition_ret.true_part, AsrtListNil(), AsrtListNil(), FuncRetTypeListNil()), env);
                  if (inv_check_ret.asrt->nrm != NULL) {
                     failwith("Error: Lack of assertions in some paths for the while loop!");
                  }
                  real_inv = AsrtListLink(tmp, popped_state->d.In_while_block.precondition);
                  witness->entailment_checker_wit = CheckEntailment(inv_check_ret.asrt->cnt, 
                                                                    real_inv, 
                                                                    popped_state->d.In_while_block.start->d.PS_while_condition.scopes,
                                                                    env, witness->entailment_checker_wit);
                  asrt->ret = FuncRetTypeListLink(asrt->ret, inv_check_ret.asrt->ret);
                  asrt->nrm = AsrtListLink(asrt->brk, inv_check_ret.asrt->brk);
                  }
                  asrt->nrm = AsrtListLink(asrt->nrm, condition_ret.false_part);
                  asrt->nrm = AsrtListLink(asrt->nrm, popped_state->d.In_while_block.asrt->nrm);
                  asrt->cnt = popped_state->d.In_while_block.asrt->cnt;
                  asrt->brk = popped_state->d.In_while_block.asrt->brk;
                  asrt->ret = FuncRetTypeListLink(asrt->ret, popped_state->d.In_while_block.asrt->ret);
               } else {
                  asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
                  struct AsrtList * end_asrt;
                  end_asrt = AsrtListLink(asrt->nrm, asrt->cnt);
                  if (popped_state->d.In_while_block.start != NULL)
                  witness->entailment_checker_wit = CheckEntailment(end_asrt, 
                                                                    popped_state->d.In_while_block.inv, 
                                                                    popped_state->d.In_while_block.start->d.PS_while_condition.scopes,
                                                                    env,
                                                                    witness->entailment_checker_wit);
                  asrt->nrm = AsrtListLink(popped_state->d.In_while_block.asrt->nrm, asrt->brk);
                  asrt->cnt = popped_state->d.In_while_block.asrt->cnt;
                  asrt->brk = popped_state->d.In_while_block.asrt->brk;
                  asrt->ret = FuncRetTypeListLink(asrt->ret, popped_state->d.In_while_block.asrt->ret);
               }
               break;
            case In_do_block:
               fprintf(stderr, "do-while loop should be ended with while condition\n");
               exit(1);
               break;
            case In_for_block: {
               struct PartialStmt * ps_simple = PartialStmtSimple(popped_state->d.In_for_block.afterthought);
               asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
               asrt->nrm = AsrtListLink(asrt->nrm, asrt->cnt);
               asrt->cnt = AsrtListNil();
               struct SymbolicExecRet ret = StateMachineTransition(ps_simple, inv, state_stack, asrt, env, trans_type);
               PartialStmtFree(ps_simple);
               inv = ret.inv;
               state_stack = ret.state_stack;
               asrt = ret.asrt;
               witness = WitnessMerge(ret.witness, witness);
               struct AsrtList * end_asrt = asrt->nrm;
               witness->entailment_checker_wit = CheckEntailment(end_asrt, 
                                                                 popped_state->d.In_for_block.inv, 
                                                                 popped_state->d.In_for_block.start->d.PS_for.scopes,
                                                                 env, witness->entailment_checker_wit);
               asrt->nrm = AsrtListLink(popped_state->d.In_for_block.asrt->nrm, asrt->brk);
               asrt->cnt = popped_state->d.In_for_block.asrt->cnt;
               asrt->brk = popped_state->d.In_for_block.asrt->brk;
               asrt->ret = FuncRetTypeListLink(asrt->ret, popped_state->d.In_for_block.asrt->ret);
               AsrtListFree(popped_state->d.In_for_block.inv);
               break;
            }
            case In_switch_block:
               asrt->nrm = AsrtListLink(asrt->nrm, asrt->brk);
               asrt->cnt = AsrtListLink(asrt->cnt, popped_state->d.In_switch_block.asrt->cnt);
               asrt->ret = FuncRetTypeListLink(asrt->ret, popped_state->d.In_switch_block.asrt->ret);
               asrt->brk = popped_state->d.In_switch_block.asrt->brk;
               asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
               asrt->nrm = DiscardFalseBranch(asrt->nrm, env, witness);
               break;
            case In_switch_cases_block:
               asrt->nrm = AsrtListLink(popped_state->d.In_switch_cases_block.asrt->nrm, asrt->nrm);
               asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
               break;
            case In_switch_default_block:
               asrt->nrm = AsrtListLink(popped_state->d.In_switch_default_block.asrt->nrm, asrt->nrm);
               asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
               break;
            case In_if_then_block:
               asrt->nrm = AsrtListLink(popped_state->d.In_if_then_block.false_part_asrt, asrt->nrm);
               asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
               asrt->nrm = DiscardFalseBranch(asrt->nrm, env, witness);
               break;
            case In_if_else_block:
               asrt->nrm = AsrtListLink(popped_state->d.In_if_else_block.true_part_asrt, asrt->nrm);
               asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
               asrt->nrm = DiscardFalseBranch(asrt->nrm, env, witness);
               break;
            case In_block:
               asrt->nrm = AsrtListVarPerish(asrt->nrm, popped_state, env);
               break;
            default:
               fprintf(stderr, "Error: unexpected state type %d\n", popped_state->t);
               exit(1);
         }
         state_stack = StateStackPop(state_stack);
         break;
      case PS_do:
         new_state = CreateState(In_do_block, state_stack);
         new_state->d.In_do_block.asrt->brk = asrt->brk;
         new_state->d.In_do_block.asrt->ret = asrt->ret;
         new_state->d.In_do_block.asrt->cnt = asrt->cnt;
         new_state->d.In_do_block.start = ps;
         asrt->brk = AsrtListNil();
         asrt->cnt = AsrtListNil();
         asrt->ret = FuncRetTypeListNil();
         state_stack = StateStackPush(state_stack, new_state);
         break;
      case PS_for: {
         if (trans_type == NormalTrans) {
            new_state = CreateState(In_for_block, state_stack);
            new_state->d.In_for_block.asrt->brk = asrt->brk;
            new_state->d.In_for_block.asrt->ret = asrt->ret;
            new_state->d.In_for_block.asrt->cnt = asrt->cnt;
            new_state->d.In_for_block.start = ps;
            new_state->d.In_for_block.inv = inv;
            new_state->d.In_for_block.condition = ps->d.PS_for.c2;
            new_state->d.In_for_block.afterthought = ps->d.PS_for.c3;
            asrt->brk = AsrtListNil();
            asrt->cnt = AsrtListNil();
            asrt->ret = FuncRetTypeListNil();
            struct PartialStmt * ps_simple = PartialStmtSimple(CSimpleCommandDeepCopy(ps->d.PS_for.c1));
            struct SymbolicExecRet ret = StateMachineTransition(ps_simple, inv, state_stack, asrt, env, trans_type);
            PartialStmtFree(ps_simple);
            inv = ret.inv;
            state_stack = ret.state_stack;
            asrt = ret.asrt;
            witness = WitnessMerge(ret.witness, witness);
            if (ps->d.PS_for.inv == NULL) {
               fprintf(stderr, "implicit invariant not supported\n");
               exit(1);
            } else {
               if (ps->d.PS_for.inv_is_partial) {
                  ps->d.PS_for.inv = CompleteInv(asrt->nrm, ps->d.PS_for.inv, ps->d.PS_for.scopes, env);
                  ps->d.PS_for.inv_is_partial = 0;
               }
               witness->entailment_checker_wit = CheckEntailment(asrt->nrm, 
                                                                 ps->d.PS_for.inv, 
                                                                 ps->d.PS_for.scopes,
                                                                 env, witness->entailment_checker_wit);
               AsrtListFree(asrt->nrm);
               condition_ret = AsrtListCondExec(AsrtListDeepCopy(ps->d.PS_for.inv), ps->d.PS_for.c2, env);
               asrt->nrm = condition_ret.true_part;
               new_state->d.In_for_block.asrt->nrm = condition_ret.false_part;
               new_state->d.In_for_block.inv = ps->d.PS_for.inv;
               witness = WitnessMerge(condition_ret.witness, witness);
            }
            state_stack = StateStackPush(state_stack, new_state);
            break;
         } else {
            struct PartialStmt * ps_simple = PartialStmtSimple(CSimpleCommandDeepCopy(ps->d.PS_for.c1));
            struct SymbolicExecRet ret = StateMachineTransition(ps_simple, ps->d.PS_for.inv, state_stack, asrt, env, trans_type);
            PartialStmtFree(ps_simple);
            inv = ret.inv;
            state_stack = ret.state_stack;
            asrt = ret.asrt;
            witness = WitnessMerge(ret.witness, witness);
            witness->entailment_checker_wit = CheckEntailment(asrt->nrm, 
                                                              ps->d.PS_for.inv, 
                                                              ps->d.PS_for.scopes,
                                                              env, witness->entailment_checker_wit);
            AsrtListFree(asrt->nrm);
            asrt->nrm = AsrtListNil();
            break;
         }
      }
      case PS_switch:
         new_state = CreateState(In_switch_block, state_stack);
         new_state->d.In_switch_block.asrt->brk = asrt->brk;
         new_state->d.In_switch_block.asrt->ret = asrt->ret;
         new_state->d.In_switch_block.asrt->cnt = asrt->cnt;
         asrt->brk = AsrtListNil();
         asrt->cnt = AsrtListNil();
         asrt->ret = FuncRetTypeListNil();
         new_state->d.In_switch_block.expr = ps->d.PS_switch.expr;
         state_stack = StateStackPush(state_stack, new_state);
         break;
      case PS_fst_case: {
         new_state = CreateState(In_switch_cases_block, state_stack);
         struct State * parent_state = StateStackPeek(state_stack);
         assert(parent_state->t == In_switch_block);
         new_state->d.In_switch_cases_block.expr = parent_state->d.In_switch_block.expr;
         struct Cexpr * condition = CexprBinop(T_EQ, 
                                               CexprDeepCopy(parent_state->d.In_switch_block.expr), 
                                               CexprDeepCopy(ps->d.PS_fst_case.expr), 
                                               SimpleCtypeInt32(Signed));
         expr_ret_wit = AsrtListExprExecRightValue(asrt->nrm, condition, env);
         expr_ret = expr_ret_wit->ret_value;
         witness = WitnessMerge(expr_ret_wit->witness, witness);
         asrt->nrm = AsrtListNil();
         while (expr_ret != NULL) {
            assert(expr_ret->val->t == EZ_VAL);
            assert(expr_ret->val->d.EZ_VAL.number == 0 || expr_ret->val->d.EZ_VAL.number == 1);
            if (expr_ret->val->d.EZ_VAL.number == 0) {
               new_state->d.In_switch_cases_block.asrt->nrm = 
                  AsrtListCons(expr_ret->asrt, new_state->d.In_switch_cases_block.asrt->nrm);
            } else {
               asrt->nrm = AsrtListCons(expr_ret->asrt, asrt->nrm);
            }
            ExprValFree(expr_ret->val);
            expr_ret = expr_ret->next;
         }
         CexprFree(condition);
         ExprExecRetTypeFree(expr_ret_wit);
         state_stack = StateStackPush(state_stack, new_state);
         break;
      }
      case PS_other_case: {
         new_state = CreateState(In_switch_cases_block, state_stack);
         popped_state = StateStackPeek(state_stack);
         assert(popped_state->t == In_switch_cases_block);
         new_state->d.In_switch_cases_block.expr = popped_state->d.In_switch_cases_block.expr;
         struct Cexpr * condition = CexprBinop(T_EQ, 
                                               CexprDeepCopy(popped_state->d.In_switch_cases_block.expr), 
                                               CexprDeepCopy(ps->d.PS_other_case.expr), 
                                               SimpleCtypeInt32(Signed));
         expr_ret_wit = AsrtListExprExecRightValue(popped_state->d.In_switch_cases_block.asrt->nrm, condition, env);
         expr_ret = expr_ret_wit->ret_value;
         witness = WitnessMerge(expr_ret_wit->witness, witness);
         while (expr_ret != NULL) {
            assert(expr_ret->val->t == EZ_VAL);
            assert(expr_ret->val->d.EZ_VAL.number == 0 || expr_ret->val->d.EZ_VAL.number == 1);
            if (expr_ret->val->d.EZ_VAL.number == 0) {
               new_state->d.In_switch_cases_block.asrt->nrm = 
                  AsrtListCons(expr_ret->asrt, new_state->d.In_switch_cases_block.asrt->nrm);
            } else {
               asrt->nrm = AsrtListCons(expr_ret->asrt, asrt->nrm);
            }
            ExprValFree(expr_ret->val);
            expr_ret = expr_ret->next;
         }
         CexprFree(condition);
         ExprExecRetTypeFree(expr_ret_wit);
         state_stack = StateStackPop(state_stack);
         state_stack = StateStackPush(state_stack, new_state);
         break;
      }
      case PS_default: {
         new_state = CreateState(In_switch_default_block, state_stack);
         struct State * parent_state = StateStackPeek(state_stack);
         assert(parent_state->t == In_switch_cases_block || parent_state->t == In_switch_block);
         if (parent_state->t == In_switch_cases_block) {
            asrt->nrm = AsrtListLink(parent_state->d.In_switch_cases_block.asrt->nrm, asrt->nrm);
            state_stack = StateStackPop(state_stack);
         } else {
            asrt->nrm = AsrtListLink(parent_state->d.In_switch_block.asrt->nrm, asrt->nrm);
         }
         state_stack = StateStackPush(state_stack, new_state);
         break;
      }
      case PS_inv:
         if (exec_outflag) {
            printf("Invariant Found: \n");
            PrintAsrtList(ps->d.PS_inv.asrt, env);
            printf("\n");
         }
         if (ps->d.PS_inv.is_partial) {
            ps->d.PS_inv.asrt = CompleteInv(asrt->nrm, ps->d.PS_inv.asrt, ps->d.PS_inv.scopes, env);
            ps->d.PS_inv.is_partial = 0;
         }
         inv = find_twin_assertion(ps->d.PS_inv.asrt, &env->persist);
         break;
      case PS_assert:
         if (ps->d.PS_assert.is_partial) {
            delete_twin_assertion(ps->d.PS_assert.asrt, &env->persist);
            struct WhichImpliesRetType * res = PartialSolveAssert(asrt->nrm, AsrtListDeepCopy(ps->d.PS_assert.asrt), ps->d.PS_assert.scopes, env);
            if (res == NULL) {
               fprintf(stderr, "Error : Partial Assert Solve Failed\n");
               exit(1);
            }
            ps->d.PS_assert.is_partial = 0;
            ps->d.PS_assert.asrt = res->asrt;
            struct AsrtList *tmp = AsrtListDeepCopy(res->asrt);
            cpa_to_old(tmp, &env->persist);
            add_twin_assertion(res->asrt, tmp, &env->persist);
            AsrtListNormalizeName(res->asrt, env);
            WitnessFree(res->witness);
            free(res);
            if (exec_outflag) {
               printf("Partial Solved Assertion: \n");
               PrintAsrtList(ps->d.PS_assert.asrt, env);
               printf("\n");
            }
         }
         if (trans_type == TransForInvCheck) {
            witness->entailment_checker_wit = CheckEntailment(asrt->nrm, ps->d.PS_assert.asrt, 
                                                              ps->d.PS_assert.scopes,
                                                              env, witness->entailment_checker_wit);
            AsrtListFree(asrt->nrm);
            asrt->nrm = AsrtListNil();
         } else { 
            witness->entailment_checker_wit = CheckEntailment(asrt->nrm, ps->d.PS_assert.asrt,
                                                              ps->d.PS_assert.scopes,
                                                              env, witness->entailment_checker_wit);
            AsrtListFree(asrt->nrm);
            asrt->nrm = AsrtListDeepCopy(find_twin_assertion(ps->d.PS_assert.asrt, &env->persist));
         }
         break;
      case PS_wi: {
         if (asrt -> nrm == NULL) {
            fprintf(stderr, "Error: this case will not occur, do not need which implies. \n");
            exit(1);
         }
         struct WhichImpliesRetType * ret = PartialSolveImplies(asrt->nrm, ps->d.PS_wi.specs, ps->d.PS_wi.pre_scopes, env);
         if (ret == NULL) {
            fprintf(stderr, "Error: Which Implies Failed\n");
            exit(1);
         }
         asrt->nrm = ret->asrt;
         witness = WitnessMerge(ret->witness, witness);
         free(ret);
         break;
      }
      case PS_do_strategy: {
         struct Assertion *DUMMY = CreateAsrt();
         struct AsrtList *before = AsrtListDeepCopy(asrt->nrm);
         struct StringList *single_scope = StringListCons(ps->d.PS_do_strategy.name,
                                                          StringListNil());
         for (struct AsrtList *i = asrt->nrm; i != NULL; i = i->next)
            custom_solve_no_core(i->head, DUMMY, env, single_scope);
         witness->entailment_checker_wit =
           EntailmentCheckerWitCons(before, AsrtListDeepCopy(asrt->nrm),
                                    StringListDeepCopy(single_scope),
                                    witness->entailment_checker_wit);
         break;
      }
      case PS_vardef: {
         struct PSVarDefList * vars;
         vars = ps->d.PS_vardef.vars;
         while (vars != NULL) {
            int id = vars->data->id;
            struct prog_var_info * info = find_prog_var_by_id(id, &(env->persist));
            if (vars->data->type->t == C_array) {
               int tmp_id = fresh(&env->persist);
               struct AsrtList * asrt_list = asrt->nrm;
               while (asrt_list != NULL) {
                  asrt_list->head->exist_list = ExistListCons(tmp_id, asrt_list->head->exist_list);
                  LocalInsert(vars->data->id, ExprVal_V_VARI(info->address->id), asrt_list->head->local_list);
                  asrt_list->head->sep_list = 
                     SepListCons(SepArr(ExprVal_V_VARI(info->address->id), 
                                        SimpleCtypeDeepCopy(vars->data->type->d.CARRAY.type), 
                                        ExprVal_V_VARI(tmp_id),
                                        ExprVal_EZ_VAL(vars->data->type->d.CARRAY.length)),
                                 asrt_list->head->sep_list);
                  asrt_list = asrt_list->next;
               }
            } else if (vars->data->type->t == C_struct) {
               int id = vars->data->id;
               struct prog_var_info * info = find_prog_var_by_id(id, &(env->persist));
               struct struct_union_info * struct_info = find_struct_by_id(vars->data->type->d.CSTRUCT.struct_id, &(env->persist));
               struct AsrtList * asrt_list = asrt->nrm;
               while (asrt_list != NULL) {
                  LocalInsert(vars->data->id, ExprVal_V_VARI(info->address->id), asrt_list->head->local_list);
                  struct field_info * field_iter = struct_info->first_field;
                  while (field_iter != NULL) {
                     struct Separation * sep = SepUndefDataAt(ExprVal_VFIELD_ADDRESS(ExprVal_V_VARI(info->address->id), field_iter->id),
                                                              TransType(field_iter->type));
                     asrt_list->head->sep_list = SepListCons(sep, asrt_list->head->sep_list);
                     field_iter = field_iter->next;
                  }
                  asrt_list = asrt_list->next;
               }
            } else {
               struct AsrtList * asrt_list = asrt->nrm;
               while (asrt_list != NULL) {
                  LocalInsert(vars->data->id, ExprVal_V_VARI(info->address->id), asrt_list->head->local_list);
                  struct Separation * sep;
                  if (vars->data->expr == NULL) {
                     sep = SepUndefDataAt(ExprVal_V_VARI(info->address->id), SimpleCtypeDeepCopy(vars->data->type));
                     asrt_list->head->sep_list = SepListCons(sep, asrt_list->head->sep_list);
                  } else {
                     fprintf(stderr, "not supported: vardef with expr\n");
                     exit(-1);
                     /* Attention: If going to support vardef with expr further, 
                        the initial statement in front the first case in switch block should not be executed */
                  }
                  asrt_list = asrt_list->next;
               }
            }
            state_stack->state->defined_vars = PSVarDefListCons(vars->data, state_stack->state->defined_vars);
            vars = vars->next;
         }
         break;
      }
   }
   return MakeSymbolicExecRet(state_stack, asrt, inv, witness);
}

struct SymbolicExecRet SymbolicExecForInvCheck(struct PartialStmt *begin, struct PartialStmt *end, 
                                               struct StateStack * state_machine, struct AsrtTuple *precondition,
                                               struct environment * env) {
   if (exec_outflag) {
      puts("Start Second Symbolic Execution (for invariant check)");   
      PrintAsrtTuple(precondition, env);
   }
   struct AsrtTuple * asrt_nbcr = precondition;
   struct AsrtList * inv = AsrtListNil();
   struct Witness * witness = NewWitness();
   struct PartialStmt * i = begin;
   while (i != NULL) {
      if (exec_outflag) {
         puts("");
         PrintPartialStmt(i, env);
         puts("");
      }
      struct SymbolicExecRet ret = StateMachineTransition(i, inv, state_machine, asrt_nbcr, env, TransForInvCheck);
      asrt_nbcr = ret.asrt;
      state_machine = ret.state_stack;
      inv = ret.inv;
      witness = WitnessMerge(ret.witness, witness);
      if (exec_outflag) {
         PrintAsrtTuple(asrt_nbcr, env);
      }
      if (i == end) {
         break;
      }
      i = i->next;
   }
   return MakeSymbolicExecRet(state_machine, asrt_nbcr, inv, witness);
}

struct SymbolicExecRet MakeSymbolicExecRet(struct StateStack * state_stack, 
                                 struct AsrtTuple * asrt, struct AsrtList * inv, struct Witness * witness) {
   struct SymbolicExecRet ret;
   ret.state_stack = state_stack;
   ret.asrt = asrt;
   ret.inv = inv;
   ret.witness = witness;
   return ret;
}

struct AsrtListWitnessPair MakeAsrtListWitnessPair(struct AsrtList * asrt_list, struct Witness * witness) {
   struct AsrtListWitnessPair ret;
   ret.asrt_list = asrt_list;
   ret.witness = witness;
   return ret;   
}

struct AsrtTuple * StateMachineFuncEnd(struct AsrtTuple * asrt, struct StateStack * state_stack, struct environment * env) {
   struct StateStack * stack_tmp;
   stack_tmp = state_stack;
   while (1) {
      asrt->nrm = AsrtListVarPerish(asrt->nrm, stack_tmp->state, env);
      if (stack_tmp->state->t == In_func_block) {
         break;
      }
      stack_tmp = stack_tmp->next;
   }
   struct FuncRetType * func_ret;
   func_ret = FuncRetTypeNil();
   struct AsrtList * asrt_iter = asrt->nrm;
   while (asrt_iter != NULL) {
      func_ret = FuncRetTypeCons(asrt_iter->head, NULL, func_ret);
      asrt_iter->head = NULL;
      asrt_iter = asrt_iter->next;
   }
   AsrtListFree(asrt->nrm);
   if (func_ret != NULL) {
      asrt->ret = FuncRetTypeListCons(func_ret, NULL, asrt->ret);
   }
   return asrt;
}