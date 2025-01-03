Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE Require Import bst_fp_strategy_goal.
Require Import bst_fp_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma bst_fp_strategy0_correctness : bst_fp_strategy0.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma bst_fp_strategy1_correctness : bst_fp_strategy1.
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma bst_fp_strategy2_correctness : bst_fp_strategy2.
  pre_process_default.
  entailer!.
  apply shallow_allp_right; intros tr0.
  apply shallow_allp_right; intros tr1.
  apply shallow_allp_right; intros v.
  apply shallow_allp_right; intros tr2.
  apply shallow_allp_right; intros k.
  apply shallow_allp_right; intros l.
  apply shallow_allp_right; intros r.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros.
  subst.
  simpl.
  entailer!.
  Exists l r.
  entailer!.
Qed.