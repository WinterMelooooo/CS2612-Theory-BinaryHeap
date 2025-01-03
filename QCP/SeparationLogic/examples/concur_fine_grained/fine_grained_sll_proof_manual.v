Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.concur_fine_grained Require Import fine_grained_sll_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import fine_grained_sll_lib.
Import sll_C_Rules.
Require Import fine_grained_sll_lib.
Import sll_C_Rules.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import fine_grained_sll_lib.
Import sll_C_Rules.
Local Open Scope stmonad.
Require Import fine_grained_sll_lib.
Local Open Scope sac.

Lemma proof_of_atomic_rev_C_return_wit_1_1 : atomic_rev_C_return_wit_1_1.
Proof.
  pre_process.
  Exists (rev l0).
  entailer!.
  revert H1; apply highstepend_derive.
  exists tt.
  hnf.
  intros.
  exists (RTrans (rev l0)).
  unfold LastSeen in H1.
  unfold atomic_rev, atomic_cmd.
  split.
  + exists l0, (rev l0).
    split; [ | split].
    - sets_unfold in H1.
      rewrite <- H1.
      tauto.
    - reflexivity.
    - reflexivity.
  + unfold LastSeen.
    reflexivity.
Qed.

Lemma proof_of_atomic_rev_C_return_wit_1_2 : atomic_rev_C_return_wit_1_2.
Proof.
  pre_process.
  Exists (rev l0).
  entailer!.
  revert H1; apply highstepend_derive.
  exists tt.
  hnf.
  intros.
  exists (RTrans (rev l0)).
  unfold LastSeen in H1.
  unfold atomic_rev, atomic_cmd.
  split.
  + exists l0, (rev l0).
    split; [ | split].
    - sets_unfold in H1.
      rewrite <- H1.
      tauto.
    - reflexivity.
    - reflexivity.
  + unfold LastSeen.
    reflexivity.
Qed.

Lemma proof_of_atomic_rev_C_partial_solve_wit_3_pure : atomic_rev_C_partial_solve_wit_3_pure.
Proof. 
  pre_process.
  unfold conditionally_store_sll.
  rewrite orp_sepcon_left_equiv.
  rewrite orp_sepcon_right_equiv.
  apply derivable1_orp_elim.
  - Intros x q. congruence.
  - Intros x q. entailer!.
Qed.

Lemma proof_of_atomic_rev_C_which_implies_wit_1 : atomic_rev_C_which_implies_wit_1.
Proof.
  pre_process.
  unfold os_inv.
  apply derivable1_orp_elim.
  + Exists 0.
    entailer!.
  + Exists 1.
    entailer!.
Qed.

Lemma proof_of_atomic_rev_C_which_implies_wit_2 : atomic_rev_C_which_implies_wit_2.
Proof.
  pre_process.
  unfold os_inv.
  subst flag.
  rewrite <- derivable1_orp_intros1.
  sep_apply conditionally_store_sll_1_0.
  entailer!.
Qed.

Lemma proof_of_atomic_rev_C_which_implies_wit_3 : atomic_rev_C_which_implies_wit_3.
Proof.
  pre_process.
  unfold os_inv.
  subst flag.
  rewrite <- derivable1_orp_intros2.
  sep_apply conditionally_store_sll_0_1.
  entailer!.
Qed.

Lemma proof_of_atomic_push_C_entail_wit_1_1 : atomic_push_C_entail_wit_1_1.
Proof.
  pre_process.
  Exists retval p_2 0 l0.
  rewrite rev_involutive.
  entailer!.
Qed.

Lemma proof_of_atomic_push_C_entail_wit_1_2 : atomic_push_C_entail_wit_1_2.
Proof.
  pre_process.
  subst flag_2.
  rewrite conditionally_store_sll_0.
  Intros p_v q.
  Exists q p_v 0 l0.
  entailer!.
Qed.

Lemma proof_of_atomic_push_C_return_wit_1 : atomic_push_C_return_wit_1.
Proof.
  pre_process.
  Exists (x :: l2_2).
  entailer!.
  revert H; apply highstepend_derive.
  exists tt.
  hnf.
  intros.
  exists (RTrans (x :: l2_2)).
  unfold LastSeen in H.
  unfold atomic_rev, atomic_cmd.
  split.
  + exists l2_2, (x :: l2_2).
    split; [ | split].
    - sets_unfold in H.
      rewrite <- H.
      tauto.
    - reflexivity.
    - reflexivity.
  + unfold LastSeen.
    reflexivity.
Qed.

Lemma proof_of_atomic_push_C_partial_solve_wit_3_pure : atomic_push_C_partial_solve_wit_3_pure.
Proof. 
  pre_process.
  unfold conditionally_store_sll.
  rewrite orp_sepcon_left_equiv.
  rewrite orp_sepcon_right_equiv.
  apply derivable1_orp_elim.
  - Intros x q. congruence.
  - Intros x q. entailer!.
Qed.

Lemma proof_of_atomic_push_C_which_implies_wit_1 : atomic_push_C_which_implies_wit_1.
Proof.
  pre_process.
  unfold os_inv.
  apply derivable1_orp_elim.
  + Exists 0.
    entailer!.
  + Exists 1.
    entailer!.
Qed.

Lemma proof_of_atomic_push_C_which_implies_wit_2 : atomic_push_C_which_implies_wit_2.
Proof.
  pre_process.
  rewrite conditionally_store_sll_1.
  Intros p_v q.
  Exists q p_v.
  entailer!.
Qed.

Lemma proof_of_atomic_push_C_which_implies_wit_3 : atomic_push_C_which_implies_wit_3.
Proof.
  pre_process.
  subst flag.
  unfold os_inv.
  rewrite <-derivable1_orp_intros1.
  rewrite conditionally_store_sll_0.
  Exists p p_v.
  entailer!.
Qed.

Lemma proof_of_atomic_pop_C_entail_wit_1_1 : atomic_pop_C_entail_wit_1_1.
Proof.
  pre_process.
  Exists retval p_2.
  Exists 0 l0.
  entailer!.
  rewrite rev_involutive.
  entailer!.
Qed.

Lemma proof_of_atomic_pop_C_entail_wit_1_2 : atomic_pop_C_entail_wit_1_2.
Proof.
  pre_process.
  subst flag_2.
  rewrite conditionally_store_sll_0.
  Intros p_v q.
  Exists q p_v 0 l0.
  entailer!.
Qed.

Lemma proof_of_atomic_pop_C_return_wit_1_1 : atomic_pop_C_return_wit_1_1.
Proof.
  pre_process.
  Right.
  Exists l0 x_pre_v_2.
  entailer!.
  revert H1.
  refine (highstependret_derive _ _ _ (fun _ => LastSeen l0) _ _).
  hnf.
  exists (RTrans l0).
  unfold LastSeen in H1.
  unfold atomic_pop, atomic_cmd.
  split.
  + exists l2_3, l0; subst.
    split; [ | split].
    - sets_unfold in H1.
      rewrite <- H1.
      tauto.
    - split; reflexivity.
    - reflexivity.
  + unfold LastSeen.
    reflexivity.
Qed.

Lemma proof_of_atomic_pop_C_return_wit_1_2 : atomic_pop_C_return_wit_1_2.
Proof.
  pre_process.
  Left.
  Exists nil.
  entailer!.
  revert H1.
  refine (highstependret_derive _ _ _ (fun _ => LastSeen nil) _ _).
  hnf.
  exists (RTrans nil).
  unfold LastSeen in H1.
  unfold atomic_pop, atomic_cmd.
  split.
  + exists l2_3, nil; subst.
    split; [ | split].
    - sets_unfold in H1.
      rewrite <- H1.
      tauto.
    - split; reflexivity.
    - reflexivity.
  + unfold LastSeen.
    reflexivity.
Qed.

Lemma proof_of_atomic_pop_C_partial_solve_wit_3_pure : atomic_pop_C_partial_solve_wit_3_pure.
Proof. 
  pre_process.
  unfold conditionally_store_sll.
  rewrite orp_sepcon_left_equiv.
  rewrite orp_sepcon_right_equiv.
  apply derivable1_orp_elim.
  - Intros x q. congruence.
  - Intros x q. entailer!.
Qed.

Lemma proof_of_atomic_pop_C_which_implies_wit_1 : atomic_pop_C_which_implies_wit_1.
Proof.
  pre_process.
  unfold os_inv.
  apply derivable1_orp_elim.
  + Exists 0.
    entailer!.
  + Exists 1.
    entailer!.
Qed.

Lemma proof_of_atomic_pop_C_which_implies_wit_2 : atomic_pop_C_which_implies_wit_2.
Proof.
  pre_process.
  rewrite conditionally_store_sll_1.
  Intros p_v q.
  Exists q p_v.
  entailer!.
Qed.

Lemma proof_of_atomic_pop_C_which_implies_wit_3 : atomic_pop_C_which_implies_wit_3.
Proof.
  pre_process.
  subst flag.
  unfold os_inv.
  rewrite <-derivable1_orp_intros1.
  rewrite conditionally_store_sll_0.
  Exists p p_v.
  entailer!.
Qed.

Lemma proof_of_pop_add_push_C_safety_wit_4 : pop_add_push_C_safety_wit_4.
Proof.
  pre_process.
  prop_apply valid_store_int.
  entailer!.
  destruct H3.
  change Integers.Int.min_signed with (-2147483648) in H3.
  change Integers.Int.max_signed with (2147483647) in H3.
  lia.
Qed.

Lemma proof_of_pop_add_push_C_safety_wit_6 : pop_add_push_C_safety_wit_6.
Proof.
  pre_process.
  prop_apply valid_store_int.
  entailer!.
  destruct H3.
  change Int.min_signed with (-2147483648) in H3.
  change Int.max_signed with (2147483647) in H3.
  lia.
Qed.

Lemma proof_of_pop_add_push_C_entail_wit_1 : pop_add_push_C_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_pop_add_push_C_entail_wit_4 : pop_add_push_C_entail_wit_4.
Proof.
  pre_process.
  Exists l2_2.
  unfold pop_add_push_loc0 in H2.
  entailer!.
  apply safeExec_choice_l in H2.
  revert H2; apply safeExec_test_bind.
  tauto.
Qed.

Lemma proof_of_pop_add_push_C_entail_wit_5 : pop_add_push_C_entail_wit_5.
Proof.
  pre_process.
  Exists l2_2.
  unfold pop_add_push_loc0 in H2.
  entailer!.
  apply safeExec_choice_r in H2.
  revert H2; apply safeExec_test_bind.
  lia.
Qed.

Lemma proof_of_pop_add_push_C_return_wit_1_1 : pop_add_push_C_return_wit_1_1.
Proof.
  pre_process.
  Exists l2_2.
  entailer!.
Qed.

Lemma proof_of_pop_add_push_C_partial_solve_wit_2_pure : pop_add_push_C_partial_solve_wit_2_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_pop_add_push_C_partial_solve_wit_3_pure : pop_add_push_C_partial_solve_wit_3_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_atomic_pop_C_derive_aux_spec_by_normal_spec : atomic_pop_C_derive_aux_spec_by_normal_spec.
Proof.
  pre_process.
  Exists l1.
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists X'.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros.
  apply _orp_proper_derivable1.
  + Intros l2 x_v ret.
    Exists l2 x_v ret.
    entailer!.
    revert H2; apply (H0 (fun _ => LastSeen l2)).
  + Intros l2 ret.
    Exists l2 ret.
    entailer!.
    revert H2; apply (H0 (fun _ => LastSeen l2)).
Qed.
