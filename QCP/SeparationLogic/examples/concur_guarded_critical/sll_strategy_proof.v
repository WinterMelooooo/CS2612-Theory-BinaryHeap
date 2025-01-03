Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.concur_guarded_critical Require Import sll_strategy_goal.
Require Import guarded_critical_sll_lib.
Import sll_C_Rules.
Require Import guarded_critical_sll_lib.
Import sll_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_strategy3_correctness : sll_strategy3.
  pre_process_default.
  simpl sll.
  entailer!.
Qed.

Lemma sll_strategy4_correctness : sll_strategy4.
  pre_process_default.
  simpl sll.
  entailer!.
Qed.

Lemma sll_strategy5_correctness : sll_strategy5.
  pre_process_default.
  entailer!.
  subst; simpl.
  entailer!.
Qed.

Lemma sll_strategy6_correctness : sll_strategy6.
  pre_process_default.
  Intros.
  subst.
  entailer!.
Qed.

Lemma sll_strategy20_correctness : sll_strategy20.
  pre_process_default.
  rewrite coq_prop_orp_coq_prop.
  Intros.
  assert (p = 0) by (destruct H;congruence).
  clear H.
  subst p.
  entailer!.
  apply shallow_allp_right.
  intros.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst x.
  cbn [sll].
  entailer!.
Qed.

Lemma sll_strategy7_correctness : sll_strategy7.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma sll_strategy10_correctness : sll_strategy10.
  pre_process_default.
  simpl.
  Intros y.
  Exists y.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma sll_strategy11_correctness : sll_strategy11.
  pre_process_default.
  simpl.
  Exists y.
  entailer!.
Qed.

Lemma sll_strategy8_correctness : sll_strategy8.
  pre_process_default.
  rewrite (coq_prop_orp_coq_prop (p <> 0) (0 <> p)).
  Intros.
  sep_apply (sll_not_zero p); [ | destruct H; intuition].
  Intros y a l0.
  Exists a l0.
  rewrite (coq_prop_orp_coq_prop (p <> 0) (0 <> p)).
  entailer!.
  simpl.
  Exists y.
  entailer!.
  apply shallow_allp_right.
  intros x.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma sll_strategy9_correctness : sll_strategy9.
  pre_process_default.
  rewrite (coq_prop_orp_coq_prop (p <> 0) (0 <> p)).
  entailer!.
  apply shallow_allp_right; intros l.
  apply shallow_allp_right; intros x.
  apply shallow_allp_right; intros l0.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
  subst.
  entailer!.
Qed.
