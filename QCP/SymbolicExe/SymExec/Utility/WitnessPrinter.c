#include "WitnessPrinter.h"
#include "InnerAsrtPrinter.h"
#include "../../compiler/env.h"
#include "../../compiler/lang.h"

void PrintSafetyCheckerWit(struct SafetyCheckerWit * safety_checker_wit, struct environment * env) {
   struct SafetyCheckerWit * tmp = safety_checker_wit;
   while (tmp != NULL) {
      puts("precondition:");
      PrintAsrt(tmp->asrt, env);
      puts("constraits:");
      PrintPropList(tmp->constraits, env);
      puts("-----------------");
      tmp = tmp->next;
   }
}

void PrintEntailmentCheckerWit(struct EntailmentCheckerWit * entailment_checker_wit, struct environment * env) {
   struct EntailmentCheckerWit * tmp = entailment_checker_wit;
   while (tmp != NULL) {
      puts("{{precondition}}");
      PrintAsrtList(tmp->pre, env);
      puts("{{postcondition}}");
      PrintAsrtList(tmp->post, env);
      puts("-------------------------------");
      tmp = tmp->next;
   }
}

void PrintReturnCheckerWit(struct ReturnCheckWit * return_checker_wit, struct environment * env) {
   struct ReturnCheckWit * tmp = return_checker_wit;
   while (tmp != NULL) {
      puts("{{precondition}}");
      PrintFuncRetType(tmp->pre, env);
      puts("{{postcondition}}");
      PrintFuncRetType(tmp->post, env);
      puts("-------------------------------");
      tmp = tmp->next;
   }
}

void PrintWhichImpliesWit(struct WhichImpliesWit * which_implies_wit, struct environment * env) {
   struct WhichImpliesWit * tmp = which_implies_wit;
   while (tmp != NULL) {
      struct AsrtList * i1, * i2;
      for (i1 = tmp->pre, i2 = tmp->post; i1 != NULL && i2 != NULL; i1 = i1->next, i2 = i2->next) {
         puts("{{precondition}}");
         PrintAsrt(i1->head, env);
         puts("{{postcondition}}");
         PrintAsrt(i2->head, env);
         puts("-------------------------------");
      }
      tmp = tmp->next;
   }
}

void PrintEntailmentCheckerWit2(struct EntailmentCheckerWit * entailment_checker_wit, struct environment * env) {
   struct EntailmentCheckerWit * tmp = entailment_checker_wit;
   while (tmp != NULL) {
      puts("{{precondition}}");
      print_assertion(tmp->pre, 1, &env->persist);
      puts("{{postcondition}}");
      print_assertion(tmp->post, 1, &env->persist);
      puts("-------------------------------");
      tmp = tmp->next;
   }
}

void PrintPartialSolveWit(struct PartialSolveWit * partial_solve_wit, struct environment * env) {
   struct PartialSolveWit * tmp = partial_solve_wit;
   while (tmp != NULL) {
      puts("pre:");
      PrintAsrt(tmp->pre, env);
      puts("post:");
      PrintAsrt(tmp->post, env);
      puts("frame:");
      PrintAsrt(tmp->frame, env);
      puts("-------------------------------");
      tmp = tmp->next;
   }
}

void PrintFuncCallWit(struct FuncCallWit * func_call_wit, struct environment * env) {
   struct FuncCallWit * tmp = func_call_wit;
   while (tmp != NULL) {
      puts("spec:");
      print_spec(tmp->spec, &env->persist);
      puts("args:");
      PrintExprValList(tmp->args, env);
      puts("\nparam:");
      PrintExprValList(tmp->param, env);
      puts("\nwith_vals:");
      PrintExprValList(tmp->with_vals, env);
      puts("\npre:");
      PrintAsrt(tmp->pre, env);
      puts("frame:");
      PrintAsrt(tmp->frame, env);
      puts("recover post:");
      PrintAsrtList(FuncCallWitRecoverPost(tmp, env), env);
      puts("-------------------------------");
      tmp = tmp->next;
   }
}

void PrintWitness(struct Witness * witness, struct environment * env) {
   puts("EntailmentCheckerWit:");
   PrintEntailmentCheckerWit2(witness->entailment_checker_wit, env);
   puts("ReturnCheckerWit:");
   PrintReturnCheckerWit(witness->return_checker_wit, env);
   puts("WhichImpliesWit:");
   PrintWhichImpliesWit(witness->which_implies_wit, env);
   puts("SafetyCheckerWit:");
   PrintSafetyCheckerWit(witness->safety_checker_wit, env);
   puts("PartialSolveWit:");
   PrintPartialSolveWit(witness->partial_solve_wit, env);
   puts("FuncCallWit:");
   PrintFuncCallWit(witness->func_call_wit, env);
}