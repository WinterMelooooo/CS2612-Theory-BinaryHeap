Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.concur_fine_grained Require Import common_strategy_goal.
Require Import fine_grained_sll_lib.
Import sll_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma common_strategy0_correctness : common_strategy0.
  pre_process_default.
Qed.

Lemma common_strategy1_correctness : common_strategy1.
  pre_process_default.
Qed.

Lemma common_strategy6_correctness : common_strategy6.
  pre_process_default.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma common_strategy3_correctness : common_strategy3.
  pre_process_default.
Qed.

Lemma common_strategy12_correctness : common_strategy12.
  pre_process_default.
Qed.

Lemma common_strategy13_correctness : common_strategy13.
  pre_process_default.
Qed.

Lemma common_strategy7_correctness : common_strategy7.
  pre_process_default.
Qed.

Lemma common_strategy8_correctness : common_strategy8.
  pre_process_default.
  entailer!.
  subst x.
  entailer!.
Qed.

Lemma common_strategy9_correctness : common_strategy9.
  pre_process_default.
  apply poly_store_poly_undef_store.
Qed.

Lemma common_strategy10_correctness : common_strategy10.
  pre_process_default.
Qed.

Lemma common_strategy11_correctness : common_strategy11.
  pre_process_default.
  rewrite (coq_prop_orp_coq_prop (p = q) (q = p)).
  entailer!.
  apply shallow_allp_right.
  intros x0.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  destruct H; subst; entailer!.
Qed.
