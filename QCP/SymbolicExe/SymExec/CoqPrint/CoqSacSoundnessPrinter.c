#include "CoqSacSoundnessPrinter.h"

void PrintWitnessHeader(FILE *fp) {
   fprintf(fp, "From SimpleC.ASRT Require Import DefFiles.\n");
   fprintf(fp, "From compcert.lib Require Import Coqlib.\n");
   fprintf(fp, "From SimpleC.CSE Require Import Cexpr_def Cstate_def Ceval_sound.\n");
   fprintf(fp, "From SimpleC.PT Require Import test_annots.\n\n");
}

void PrintAnnotsHeader(FILE *fp) {
   fprintf(fp, "From SimpleC.ASRT Require Import DefFiles.\n");
   fprintf(fp, "From compcert.lib Require Import Coqlib Integers.\n");
   fprintf(fp, "From SimpleC.CSE Require Import Cexpr_def Cstate_def.\n\n");
}

void PrintAnnots(FILE *fp) {
   fprintf(fp, "Definition env : prog_env :=\n");
   fprintf(fp, "  {|\n");
   fprintf(fp, "    Structdef := nil;\n");
   fprintf(fp, "    Uniondef := nil;\n");
   fprintf(fp, "    struct_pos := fun start struct_name field_name =>\n");
   fprintf(fp, "    match struct_name, field_name with\n");
   fprintf(fp, "    | _, _ => None\n");
   fprintf(fp, "    end;\n");
   fprintf(fp, "    union_pos := fun start union_name field_name =>\n");
   fprintf(fp, "    match union_name, field_name with\n");
   fprintf(fp, "    | _, _ => None\n");
   fprintf(fp, "    end;\n");
   fprintf(fp, "    pred_size := fun name => match name with\n");
   fprintf(fp, "    | _ => 0\n");
   fprintf(fp, "    end\n");
   fprintf(fp, "  |}.\n\n");
   fprintf(fp, "Definition env_s : All_Env :=\n");
   fprintf(fp, "{|\n");
   fprintf(fp, "  Structure_def := env;\n");
   fprintf(fp, "  Predicate_def :=\n");
   fprintf(fp, "  {|\n");
   fprintf(fp, "    Funcspecs := nil;\n");
   fprintf(fp, "    Funcpreds := nil;\n");
   fprintf(fp, "    Seppreds := nil\n");
   fprintf(fp, "  |}\n");
   fprintf(fp, "|}.\n\n");
   fprintf(fp, "Parameter callees : val -> prog_state -> list val -> prog_state -> val -> Prop.\n\n");
   fprintf(fp, "Parameter return_val : int64.\n");
   fprintf(fp, "Parameter Funcpred_denote : ident -> list int64 -> int64.\n");
   fprintf(fp, "Parameter Seppred_denote : ident -> list int64 -> Prop.\n\n");
   fprintf(fp, "Parameter state_t : StateType.\n\n");
}

void PrintHeaderMain(FILE *fp) {
   fprintf(fp, "From SimpleC.ASRT Require Import DefFiles.\n");
   fprintf(fp, "From compcert.lib Require Import Coqlib.\n");
   fprintf(fp, "From SimpleC.CSE Require Import Cexpr_def Cstate_def Cstatement_semantics Cexpr_StateMachine.\n\n");
   fprintf(fp, "From SimpleC.PT Require Import test_annots test_witness.\n");
}

void PrintHeaderExecSoundness(FILE * fp) {
   fprintf(fp, "From SimpleC.ASRT Require Import DefFiles.\n");
   fprintf(fp, "From compcert.lib Require Import Coqlib.\n");
   fprintf(fp, "From SimpleC.CSE Require Import Cexpr_def Ceval_sound Cexpr_StateMachine Cstate_def SymExec_sound Cstatement_semantics.\n");
   fprintf(fp, "From SimpleC.PT Require Import test_annots test_witness test.\n");
}

void PrintTransSoundness(int func_count, FILE *fp) {
   for (int i = 1; i <= func_count; ++i) {
      fprintf(fp, "Theorem ACStmt_to_ps_correctness%d :\n", i);
      fprintf(fp, "   Some ps_stmt%d = (ACStmt_to_ps ACStatement%d).\n", i, i);
      fprintf(fp, "Proof. reflexivity. Qed.\n\n");
   }
   for (int i = 1; i <= func_count; ++i) {
      fprintf(fp, "Theorem ACStmt_to_CStmt_corretness%d :\n", i);
      fprintf(fp, "   Some (Remove_skip CStatement%d) = Remove_skip_option (ACStmt_to_CStmt ACStatement%d).\n", i, i);
      fprintf(fp, "Proof. reflexivity. Qed.\n\n");
   }
}

void PrintExecCorrectness(FILE *fp, struct environment *env) {
   int i = 0;
   struct blist *it;
   for (it = env->persist.func.top; it != NULL; it = it->down) {
      struct func_info * info = it->val;
      if (info->defined == 0) continue;
      ++i;
      fprintf(fp, "Theorem Exec_correctness%d: \n", i);
      fprintf(fp, "Machine_exec env_s Pre%d Witness%d ps_stmt%d = Some (mk_Mpara state_t execPost%d nil nil (mk_wit nil nil nil nil nil )).\n",i,i,i,i);
      fprintf(fp,"Proof. Admitted.\n\n");
   }
}