#include "WitnessTrySolve.h"

#include "../../Automation/AutomationSolver/solver.h"
#include "../../Trans/PropToSmtPropTrans.h"

#define WitnessTrySolveDebug 0

struct EntailRetType * (*SepSolver) (struct Assertion * pre, struct Assertion * post, struct StringList *scope, struct environment * env);
struct Prop_solver_return * (*PropSolver) (struct PropList *source_prop_list, struct PropList *target_prop_list, struct environment * env);

void EliminateLocal(struct Assertion * pre, struct AsrtList * post, struct environment * env) {
#ifdef WITNESS_TRY_SOLVE_DEBUG   
   printf("Eliminate Local: \n");
   PrintAsrt(pre, env);
   printf("==>\n");
   PrintAsrtList(post, env);
   printf("\n");
#endif
   struct LocalLinkedHashMapNode * node = ((struct LocalLinkedHashMap*) pre->local_list)->head;
   while (node != NULL) {
      struct ExprVal * addr = node->value;
      struct SepList * pre_sep = FindPosOfAddr(pre->sep_list, addr);
      if (pre_sep == NULL || (pre_sep->head->t != T_DATA_AT && pre_sep->head->t != T_UNDEF_DATA_AT)) {
         node = node->next;
         continue;
      }
      int all_found_in_post = 1;
      for (struct AsrtList * post_iter = post; post_iter != NULL; post_iter = post_iter->next) {
         struct SepList * post_sep = FindPosOfAddr(post_iter->head->sep_list, addr);
         if (post_sep == NULL || pre_sep->head->t != post_sep->head->t) {
            all_found_in_post = 0;
            break;
         }
         if (pre_sep->head->t == T_DATA_AT) {
            if (ExprValCheckEqual(pre_sep->head->d.DATA_AT.right, post_sep->head->d.DATA_AT.right)) {
               continue;
            } else if (post_sep->head->d.DATA_AT.right->t == FUNCAPP) {
               int id = post_sep->head->d.DATA_AT.right->d.FUNCAPP.id;
               if (!ExistListContains(id, post_iter->head->exist_list)) {
                  all_found_in_post = 0;
                  break;
               }
            } else {
               all_found_in_post = 0;
               break;
            }
         }
      }
      if (!all_found_in_post) {
         node = node->next;
         continue;
      }
      for (struct AsrtList * post_iter = post; post_iter != NULL; post_iter = post_iter->next) {
         struct SepList * post_sep = FindPosOfAddr(post_iter->head->sep_list, addr);
         if (pre_sep->head->t == T_UNDEF_DATA_AT) {
            post_iter->head->sep_list = SepListRemove(post_sep, post_iter->head->sep_list);
         } else if (pre_sep->head->t == T_DATA_AT) {
            if (ExprValCheckEqual(pre_sep->head->d.DATA_AT.right, post_sep->head->d.DATA_AT.right)) {
               post_iter->head->sep_list = SepListRemove(post_sep, post_iter->head->sep_list);
            } else {
               int id = post_sep->head->d.DATA_AT.right->d.FUNCAPP.id;
               post_iter->head->exist_list = ExistListRemove(id, post_iter->head->exist_list);
               struct ExprVal * post_val = ExprValDeepCopy(post_sep->head->d.DATA_AT.right);
               post_iter->head->sep_list = SepListRemove(post_sep, post_iter->head->sep_list);
               post_iter->head = AsrtSubst(post_iter->head, post_val, pre_sep->head->d.DATA_AT.right);
               ExprValFree(post_val);
            }
         }
      }
      pre->sep_list = SepListRemove(pre_sep, pre->sep_list);
      node = node->next;
   }
#ifdef WITNESS_TRY_SOLVE_DEBUG   
   printf("Eliminate Local Done: \n");
   PrintAsrt(pre, env);
   printf("==>\n");
   PrintAsrtList(post, env);
   printf("\n");
#endif
}

int NestedSolverSingleFull(struct Assertion * pre, struct Assertion * post, struct environment * env, struct StringList * scopes) {
   struct EntailRetType * sep_ret = SepSolver(pre, post, scopes, env);
   if (sep_ret == NULL || post->exist_list != NULL || post->sep_list != NULL || pre->sep_list != NULL) return 0;
   struct Prop_solver_return * prop_ret = PropSolver(pre->prop_list, post->prop_list, env);
   AsrtFree(pre);
   AsrtFree(post);
   if (prop_ret->result == 1) {
      return 1;
   } else {
      return 0;
   }
}

int NestedSolverSingle(struct Assertion * pre, struct Assertion * post, struct environment * env, struct StringList * scopes) {
   struct EntailRetType * sep_ret = SepSolver(pre, post, scopes, env);
   if (sep_ret == NULL || post->exist_list != NULL || post->sep_list != NULL) return 0;
   struct Prop_solver_return * prop_ret = PropSolver(pre->prop_list, post->prop_list, env);
   AsrtFree(pre);
   AsrtFree(post);
   if (prop_ret->result == 1) {
      return 1;
   } else {
      return 0;
   }
}

int NestedSolver(struct Assertion * pre, struct AsrtList * post, struct environment * env, struct StringList * scopes) {
   for (struct AsrtList * i = post; i != NULL; i = i->next) {
      if (NestedSolverSingleFull(AsrtDeepCopy(pre), i->head, env, scopes) == 1) {
         AsrtFree(pre);
         return 1;
      }
   }
   AsrtFree(pre);
   return 0;
}

void EntailmentCheckerWitTrySolve(struct EntailmentCheckerWit * entailment_checker_wit, struct environment * env) {
#ifdef WITNESS_TRY_SOLVE_DEBUG   
   printf("Try Entailment Checker Solve\n");
#endif
   struct EntailmentCheckerWit * tmp = entailment_checker_wit;
   while (tmp != NULL) {
      if (tmp->auto_solved == 1) {
         tmp = tmp->next;
         continue;
      }
      tmp->auto_solved = 1;
      for (struct AsrtList * i = tmp->pre; i != NULL; i = i->next) {
         struct Assertion * pre = AsrtDeepCopy(i->head);
         struct AsrtList * post = AsrtListDeepCopy(tmp->post);
         //EliminateLocal(pre, post, env);
         if (NestedSolver(pre, post, env, entailment_checker_wit->strategy_scopes) == 0) {
            tmp->auto_solved = 0;
            break;
         }
      }
      tmp = tmp->next;
   }
}

void ReturnCheckWitTrySolve(struct ReturnCheckWit * return_checker_wit, struct environment * env) {
#ifdef WITNESS_TRY_SOLVE_DEBUG      
   printf("Try Return Checker Solve\n");
#endif
   struct ReturnCheckWit * tmp = return_checker_wit;
   while (tmp != NULL) {
      tmp->auto_solved = IntListNil();
      for (struct FuncRetType * i = tmp->pre; i != NULL; i = i->next) {
         int solved = 0;
         for (struct FuncRetType * j = tmp->post; j != NULL; j = j->next) {
            struct Assertion * pre = AsrtDeepCopy(i->asrt);
            struct Assertion * post = AsrtDeepCopy(j->asrt);
            if (j->val == NULL && i ->val != NULL) {
              fprintf(stderr, "ReturnCheckWitTrySolve: Do not have __return in assertion. \n");
              exit(1);
            }
            if (i -> val == NULL && j->val != NULL) {
              fprintf(stderr, "ReturnCheckWitTrySolve: This is a non-void function, do not have return command \n");
              exit(1);
            }
            if (i->val != NULL) {
               post->exist_list = ExistListRemove(j->val->d.FUNCAPP.id, post->exist_list);
               post = AsrtSubst(post, j->val, i->val);
            }
            if (NestedSolverSingleFull(pre, post, env, return_checker_wit->strategy_scopes) == 1) {
               solved = 1;
               break;
            }
         }
         tmp->auto_solved = IntListCons(solved, tmp->auto_solved);
      }
      tmp->auto_solved = IntListReverse(tmp->auto_solved);
      tmp = tmp->next;
   }
}

struct IntList * WhichImpliesWitTrySolveDfs(struct AsrtList * ppre, struct AsrtList * ppost, struct StringList * scopes, struct environment * env) {
   if (ppre == NULL) return IntListNil();
   struct Assertion * pre = AsrtDeepCopy(ppre->head);
   struct Assertion * post = AsrtDeepCopy(ppost->head);
   int ret = NestedSolverSingleFull(pre, post, env, scopes);
   return IntListCons(ret, WhichImpliesWitTrySolveDfs(ppre->next, ppost->next, scopes, env));
}

void WhichImpliesWitTrySolve(struct WhichImpliesWit * which_implies_wit, struct environment * env) {
#ifdef WITNESS_TRY_SOLVE_DEBUG   
   printf("Try Which Implies Wit Solve\n");
#endif
   struct WhichImpliesWit * tmp = which_implies_wit;
   while (tmp != NULL) {
      if (tmp->auto_solved == 1) {
         tmp = tmp->next;
         continue;
      }
      tmp->auto_solved = WhichImpliesWitTrySolveDfs(tmp->pre, tmp->post, which_implies_wit->strategy_scopes, env);
      tmp = tmp->next;
   }
}

void SafetyCheckerWitTrySolve(struct SafetyCheckerWit * safety_checker_wit, struct environment * env) {
#ifdef WITNESS_TRY_SOLVE_DEBUG   
   printf("Try Safety Checker Solve\n");
#endif
   struct SafetyCheckerWit * tmp = safety_checker_wit;
   while (tmp != NULL) {
      if (tmp->auto_solved == 1) {
         tmp = tmp->next;
         continue;
      }
      struct PropList * pre = PropListDeepCopy(tmp->asrt->prop_list);
      struct PropList * post = PropListDeepCopy(tmp->constraits);
      struct Prop_solver_return * prop_ret = PropSolver(pre, post, env);
      if (prop_ret->result == 1) {
         tmp->auto_solved = 1;
      } else {
         tmp->auto_solved = 0;
      }
      PropListFree(pre);
      PropListFree(post);
      Prop_solver_return_free(prop_ret);
      tmp = tmp->next;
   }
}

void PartialSolveWitTrySolve(struct PartialSolveWit * partial_solve_wit, struct environment * env) {
#ifdef WITNESS_TRY_SOLVE_DEBUG   
   printf("Try Partial Solve Wit Solve\n");
#endif
   struct PartialSolveWit * tmp = partial_solve_wit;
   while (tmp != NULL) {
      if (tmp->auto_solved == 1) {
         tmp = tmp->next;
         continue;
      }
      struct Assertion * pre = AsrtDeepCopy(tmp->pre);
      struct Assertion * post = AsrtDeepCopy(tmp->post);
      SepListFree(post->sep_list);
      post->sep_list = NULL;
      if (NestedSolverSingle(pre, post, env, partial_solve_wit->strategy_scopes) == 1) {
         tmp->auto_solved = 1;
      } else {
         tmp->auto_solved = 0;
      }
      tmp = tmp->next;
   }
}

void WitnessTrySolve(struct Witness * wit, struct environment * env) {
   int pre_set = exec_info;
   exec_info = WitnessTrySolveDebug;
   EntailmentCheckerWitTrySolve(wit->entailment_checker_wit, env);
   ReturnCheckWitTrySolve(wit->return_checker_wit, env);
   WhichImpliesWitTrySolve(wit->which_implies_wit, env);
   SafetyCheckerWitTrySolve(wit->safety_checker_wit, env);
   PartialSolveWitTrySolve(wit->partial_solve_wit, env);
   exec_info = pre_set;
}