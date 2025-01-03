#include "CoqWitnessPrinter.h"
#include "CoqInnerAsrtPrinter.h"

void CoqEntailmentCheckerWitPrinter(struct EntailmentCheckerWit * entail, struct environment * env, FILE * fp) {
   if (entail == NULL) {
      fprintf(fp, "nil");
   } else {
      fprintf(fp, "(");
      struct EntailmentCheckerWit * list;
      list = entail;
      while (list != NULL) {
         fprintf(fp, "(");
         CoqInnerAsrtListPrinter(list->pre, env, fp);
         fprintf(fp, ", ");
         CoqInnerAsrtListPrinter(list->post, env, fp);
         fprintf(fp, ")");
         list = list->next;
         if (list != NULL) {
            fprintf(fp, "::");
         } else {
            fprintf(fp, "::nil)");
         }
      }
   }
}

int CoqEntailmentCheckerProofPrinter(int id, struct EntailmentCheckerWit * entail, struct environment * env, FILE * fp) {
  if (entail == NULL) {
      return 0;
   } else {
      struct EntailmentCheckerWit * list;
      int ans = 0;
      list = entail;
      while (list != NULL) {
         ans ++;
         fprintf(fp, "Lemma Entailment%d_proof%d : Sound_single_entailment_checker env Funcpred_denote Seppred_denote\n",id,ans);
         CoqInnerAsrtListPrinter(list->pre, env, fp);
         fprintf(fp, "\n");
         CoqInnerAsrtListPrinter(list->post, env, fp);
         fprintf(fp, ".\n");
         fprintf(fp, "Proof. Admitted.\n");
         // list_solve(list->pre->head, list->post->head, env);
         fprintf(fp, "Lemma Entailment%d_proof%d_simplified : Sound_single_entailment_checker env Funcpred_denote Seppred_denote\n",id,ans);
         CoqInnerAsrtListPrinter(list->pre, env, fp);
         fprintf(fp, "\n");
         CoqInnerAsrtListPrinter(list->post, env, fp);
         fprintf(fp, ".\n");
         fprintf(fp, "Proof. Admitted.\n");
         list = list->next;
      }
      return ans;
   }
}

int CoqEntailmentCheckerWitRetProofPrinter(int id, struct ReturnCheckWit * wit, struct environment * env, FILE * fp) {
   if (wit == NULL) {
      return 0;
   } else {
      struct ReturnCheckWit * list;
      int ans = 0;
      list = wit;
      while (list != NULL) {
         ans ++;
         fprintf(fp, "Lemma Entailment_Ret%d_proof%d : Sound_single_entailment_checker_with_ret env Funcpred_denote Seppred_denote\n",id,ans);
         CoqFuncRetTypePrinter(list->pre, env, fp);
         fprintf(fp, "\n");
         CoqFuncRetTypePrinter(list->post, env, fp);
         fprintf(fp, ".\n");
         fprintf(fp, "Proof. Admitted.\n");
         if (list->pre->val != NULL && list->post->val != NULL) {
            struct Proposition * ret_prop;
            ret_prop = PropCompare(PROP_EQ, ExprValDeepCopy(list->pre->val), ExprValDeepCopy(list->post->val));
            list->post->asrt->prop_list = PropListCons(ret_prop, list->post->asrt->prop_list);
         }
         // list_solve(list->pre->asrt, list->post->asrt, env);
         fprintf(fp, "Lemma Entailment_Ret%d_proof%d_simplified : Sound_single_entailment_checker_with_ret env Funcpred_denote Seppred_denote\n",id,ans);
         CoqFuncRetTypePrinter(list->pre, env, fp);
         fprintf(fp, "\n");
         CoqFuncRetTypePrinter(list->post, env, fp);
         fprintf(fp, ".\n");
         fprintf(fp, "Proof. Admitted.\n");
         list = list->next;
      }
      return ans;
   }
}

void CoqSafetyCheckerWitPrinter(struct SafetyCheckerWit * wit, struct environment * env, FILE * fp) {
   if (wit == NULL) {
      fprintf(fp, "nil");
   } else {
      fprintf(fp, "(");
      struct SafetyCheckerWit * list;
      list = wit;
      while (list != NULL) {
         fprintf(fp, "(");
         CoqInnerAsrtPrinter(list->asrt, env, fp);
         fprintf(fp, ", ");
         CoqPropListPrinter(list->constraits, env, fp);
         fprintf(fp, ")");
         list = list->next;
         if (list != NULL) {
            fprintf(fp, "::");
         } else {
            fprintf(fp, "::nil)");
         }
      }
   }
}

int CoqSafetyCheckerProofPrinter(int id, struct SafetyCheckerWit * wit, struct environment * env, FILE * fp) {
   if (wit == NULL) {
      return 0;
   } else {
      struct SafetyCheckerWit * list;
      int ans = 0;
      list = wit;
      while (list != NULL) {
         ans ++;
         fprintf(fp, "Lemma Safety_checker%d_proof%d : Sound_single_safety_checker env Funcpred_denote Seppred_denote\n",id,ans);
         CoqInnerAsrtPrinter(list->asrt, env, fp);
         fprintf(fp, "\n");
         CoqPropListPrinter(list->constraits, env, fp);
         fprintf(fp, ".\n");
         fprintf(fp, "Proof. Admitted.\n");
         list = list->next;
      }
      return ans;
   }
}

void CoqReturnCheckerWitPrinter(struct ReturnCheckWit * wit, struct environment * env, FILE * fp) {
   if (wit == NULL) {
      fprintf(fp, "nil");
   } else {
      fprintf(fp, "(");
      struct ReturnCheckWit * list;
      list = wit;
      while (list != NULL) {
         fprintf(fp, "(");
         CoqFuncRetTypePrinter(list->pre, env, fp);
         fprintf(fp, ", ");
         CoqFuncRetTypePrinter(list->post, env, fp);
         fprintf(fp, ")");
         list = list->next;
         if (list != NULL) {
            fprintf(fp, "::");
         } else {
            fprintf(fp, "::nil)");
         }
      }
   }
}

void CoqWitnessPrinter(int id, struct Witness * witness, struct environment * env, FILE * fp) {
   fprintf(fp, "Definition Witness%d := \n", id);
   fprintf(fp, "{|\n");
   fprintf(fp, "   Split_assert_wit := ");
   // Need to add this wit 
   // CoqSplitAssertWitPrinter(witness->split_assert_wit, env, fp);
   fprintf(fp, "nil");
   fprintf(fp, ";\n   ");
   fprintf(fp, "Call_oracle_wit := ");
   // Need to add this wit 
   // CoqCallOracleWitPrinter(witness->call_oracle_wit, env, fp);
   fprintf(fp, "nil");
   fprintf(fp, ";\n   ");
   fprintf(fp, "Safety_checker_wit := ");
   CoqSafetyCheckerWitPrinter(witness->safety_checker_wit, env, fp);
   fprintf(fp, ";\n   ");
   fprintf(fp, "entailment_checker_wit := ");
   CoqEntailmentCheckerWitPrinter(witness->entailment_checker_wit, env, fp);
   fprintf(fp, ";\n   ");
   fprintf(fp, "entailment_checker_with_ret_wit := ");
   // Need to add this wit 
   CoqReturnCheckerWitPrinter(witness->return_checker_wit, env, fp);
   // fprintf(fp, "nil");
   fprintf(fp, ";\n");
   fprintf(fp, "|}.\n");
}

void CoqWitnessProofPrinter(int id, struct Witness *witness, struct environment * env, FILE *fp) {
  int cnt;
  // print soundness lemma of Split_assert_wit
  // cnt = CoqSplitAssertProofPrinter(id, witness -> split_assert_wit, env, fp);
  cnt = 0;
  fprintf(fp, "Theorem Soundness_of_Split_witness%d : Sound_Split_assert env Funcpred_denote Seppred_denote (Split_assert_wit Witness%d).\n", id, id);
  fprintf(fp, "Proof.\n");
  fprintf(fp, "  hnf.\n");
  for (int i = 1; i <= cnt ; ++i) {
      fprintf(fp, "  apply List_proof_cons3.\n");
      fprintf(fp, "  apply Split_assert%d_proof%d.\n",id,i);
   }
   fprintf(fp, "  apply List_proof_nil3.\n");
   fprintf(fp, "Qed.\n");

   // print soundness lemma of Call_oracle_wit
   // cnt = CoqCallOracleProofPrinter(id, witness -> call_oracle_wit, env, fp);
   cnt = 0;
   fprintf(fp, "Theorem Soundness_of_Call_witness%d : Sound_Call_oracle env Funcpred_denote Seppred_denote callees (Call_oracle_wit Witness%d).\n", id, id);
   fprintf(fp, "Proof.\n");
   fprintf(fp, "  hnf.\n");
   for (int i = 1; i <= cnt ; ++i) {
      fprintf(fp, "  apply List_proof_cons3.\n");
      fprintf(fp, "  apply Call_oracle%d_proof%d.\n",id,i);
   }
   fprintf(fp, "  apply List_proof_nil3.\n");
   fprintf(fp, "Qed.\n");

   // print soundness lemma of Safety_checker_wit
   cnt = CoqSafetyCheckerProofPrinter(id, witness->safety_checker_wit, env, fp);
   fprintf(fp, "Theorem Soundness_of_Safety_checker%d : Sound_safety_checker env Funcpred_denote Seppred_denote (Safety_checker_wit Witness%d).\n", id, id);
   fprintf(fp, "Proof.\n");
   fprintf(fp, "  hnf.\n");
   for (int i = 1; i <= cnt ; ++i) {
      fprintf(fp, "  apply List_proof_cons2.\n");
      fprintf(fp, "  apply Safety_checker%d_proof%d.\n",id,i);
   }
   fprintf(fp, "  apply List_proof_nil2.\n");
   fprintf(fp, "Qed.\n");

   // print soundness lemma of Entailment_checker_wit
   cnt = CoqEntailmentCheckerProofPrinter(id, witness->entailment_checker_wit, env, fp);
   fprintf(fp, "Theorem Soundness_of_entailment%d : Sound_entailment_checker env Funcpred_denote Seppred_denote (entailment_checker_wit Witness%d).\n", id,id);
   fprintf(fp, "Proof.\n");
   fprintf(fp, "  hnf.\n");
   for (int i = 1; i <= cnt ; ++i) {
      fprintf(fp, "  apply List_proof_cons2.\n");
      fprintf(fp, "  apply Entailment%d_proof%d.\n",id,i);
   }
   fprintf(fp, "  apply List_proof_nil2.\n");
   fprintf(fp, "Qed.\n");

   // print soundness lemma of Entailment_checker_with_ret_wit
   cnt = CoqEntailmentCheckerWitRetProofPrinter(id, witness->return_checker_wit, env, fp);
   fprintf(fp, "Theorem Soundness_of_entailment_ret%d : Sound_entailment_checker_with_ret env Funcpred_denote Seppred_denote (entailment_checker_with_ret_wit Witness%d).\n", id,id);
   fprintf(fp, "Proof.\n");
   fprintf(fp, "  hnf.\n");
   for (int i = 1; i <= cnt ; ++i) {
      fprintf(fp, "  apply List_proof_cons2.\n");
      fprintf(fp, "  apply Entailment_Ret%d_proof%d.\n",id,i);
   }
   fprintf(fp, "  apply List_proof_nil2.\n");
   fprintf(fp, "Qed.\n");

   // print full soundness lemma 
   fprintf(fp, "Theorem Soundness_of_witness%d : Sound_witness env Funcpred_denote Seppred_denote callees Witness%d.\n",id,id);
   fprintf(fp, "Proof.\n");
   fprintf(fp, "  repeat split.\n");
   fprintf(fp, "  apply Soundness_of_Split_witness%d.\n",id);
   fprintf(fp, "  apply Soundness_of_Call_witness%d.\n",id);
   fprintf(fp, "  apply Soundness_of_Safety_checker%d.\n",id);
   fprintf(fp, "  apply Soundness_of_entailment%d.\n",id);
   fprintf(fp, "  apply Soundness_of_entailment_ret%d.\n",id);
   fprintf(fp, "Qed.\n");
}