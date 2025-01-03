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
From SimpleC.EE.concur_triple_critical Require Import triple_grained_sll_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import triple_critical_sll_lib.
Import sll_TC_Rules.
Require Import triple_critical_sll_lib.
Import sll_TC_Rules.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import triple_critical_sll_lib.
Import sll_TC_Rules.
Local Open Scope stmonad.
Require Import triple_critical_sll_lib.
Local Open Scope sac.

Lemma proof_of_atomic_rev1_which_implies_wit_1 : atomic_rev1_which_implies_wit_1.
Proof.
pre_process.
unfold os_inv.
destruct q as [[p q] r].
destruct l as [[l1 l2] l3].
Intros p_v q_v r_v. simpl.
Exists r_v q_v p_v.
simpl.
entailer!.
Qed. 

Lemma proof_of_atomic_rev1_which_implies_wit_2 : atomic_rev1_which_implies_wit_2.
Proof.
  pre_process.
  unfold os_inv.
  destruct q as [[p q] r].
  simpl.
  Exists v_3 v_2 v.
  entailer!.
Qed. 

Lemma proof_of_atomic_rev1_2_return_wit_1 : atomic_rev1_2_return_wit_1.
Proof. 
  pre_process.
  subst. unfold prod3.
  Exists (fst (fst q0_2)).
  Exists (rev (fst (fst l0)), snd (fst l0),
  snd l0).
  entailer!.
  revert H1; apply highstepend_derive.
  exists tt.
  hnf.
  intros.
  exists (RTrans_Abs (rev (fst (fst l0)), snd (fst l0), snd l0)).
  unfold LastSeen in H0.
  unfold atomic_1_rev, atomic_1_cmd.
  split.
  - exists (l0) , (rev (fst (fst l0)), snd (fst l0), snd l0).
    split; [ | split].
    + sets_unfold in H0.
      rewrite <- H0.
      tauto.
    + reflexivity.
    + simpl. split ; [ reflexivity | split ; reflexivity].
  - unfold LastSeen.
    reflexivity.
Qed.

Lemma proof_of_atomic_rev1_2_which_implies_wit_1 : atomic_rev1_2_which_implies_wit_1.
Proof.
  pre_process.
  unfold os_inv.
  destruct q0 as [[p q] r].
  destruct l as [[l1 l2] l3].
  Intros p_v q_v r_v. simpl.
  Exists r_v q_v p_v.
  simpl.
  entailer!.
Qed. 

Lemma proof_of_atomic_rev1_2_which_implies_wit_2 : atomic_rev1_2_which_implies_wit_2.
Proof. 
  pre_process.
  unfold os_inv.
  destruct q0 as [[p q] r].
  simpl.
  Exists v_3 v_2 v.
  entailer!.
Qed.

Lemma proof_of_atomic_pop2_2_return_wit_1_1 : atomic_pop2_2_return_wit_1_1.
Proof.
  pre_process. subst.
  Right. 
  Exists (snd (fst q0_2)) (prod3 (fst (fst l0)) l0_2 (snd l0)).
  Exists x_pre_v_2.
  entailer!. 
  revert H3.
  refine (highstependret_derive _ _ _ (fun _ => LastSeen l0) _ _).
  hnf.
  intros.
  unfold LastSeen in H.
  exists (RTrans_Abs l0).
  unfold atomic_2_pop, atomic_2_cmd.
  split.
  - exists l0, (fst(fst l0), l0_2, snd(l0)).
    split; [ | split].
    + sets_unfold in H.
      rewrite <- H.
      tauto.
    + rewrite H0. split ; auto.
    + repeat split ; auto.
  - unfold LastSeen.
    reflexivity.
Qed. 

Lemma proof_of_atomic_pop2_2_return_wit_1_2 : atomic_pop2_2_return_wit_1_2.
Proof.
  pre_process. subst.
  Left. 
  Exists (snd (fst q0_2)) l0.
  entailer!. 
  revert H3.
  refine (highstependret_derive _ _ _ (fun _ => LastSeen l0) _ _).
  hnf.
  intros.
  unfold LastSeen in H.
  exists (RTrans_Abs l0).
  unfold atomic_2_pop, atomic_2_cmd.
  split.
  - exists l0 , l0.
    split; [ | split].
    + sets_unfold in H.
      rewrite <- H.
      tauto.
    + rewrite H0. auto.
    + repeat split ; auto.
  - unfold LastSeen.
    reflexivity.
Qed.

Lemma proof_of_atomic_pop2_2_which_implies_wit_1 : atomic_pop2_2_which_implies_wit_1.
Proof.
  pre_process.
  unfold os_inv.
  destruct q0 as [[p q] r].
  destruct l as [[l1 l2] l3].
  Intros p_v q_v r_v. simpl.
  Exists r_v q_v p_v.
  simpl.
  entailer!.
Qed.

Lemma proof_of_atomic_pop2_2_which_implies_wit_2 : atomic_pop2_2_which_implies_wit_2.
Proof.
  pre_process.
  unfold os_inv.
  destruct q0 as [[p q] r].
  simpl.
  Exists v_3 v_2 v.
  entailer!.
Qed. 

Lemma proof_of_atomic_push2_3_return_wit_1 : atomic_push2_3_return_wit_1.
Proof.
  pre_process.
  subst.
  Exists (snd q0_2) (prod3 (fst (fst l0)) (snd (fst l0)) (x_pre :: snd l0)).
  entailer!. 
  revert H2.
  refine (highstependret_derive _ _ _ (fun _ => LastSeen (prod3 (fst (fst l0)) (snd (fst l0)) (x_pre :: snd l0))) _ _).
  hnf.
  intros.
  unfold LastSeen in H1.
  exists (RTrans_Abs (prod3 (fst (fst l0)) (snd (fst l0)) (x_pre :: snd l0))).
  unfold atomic_3_push, atomic_3_cmd.
  split.
  - exists l0, (fst(fst l0), snd (fst l0), x_pre :: snd l0).
    split; [ | split].
    + sets_unfold in H1.
      rewrite <- H1.
      tauto.
    + simpl. auto.
    + repeat split ; simpl ; auto.
      rewrite <- surjective_pairing. auto.
  - unfold LastSeen.
    reflexivity.
Qed. 

Lemma proof_of_atomic_push2_3_which_implies_wit_1 : atomic_push2_3_which_implies_wit_1.
Proof.
  pre_process.
  unfold os_inv.
  destruct q0 as [[p q] r].
  destruct l as [[l1 l2] l3].
  Intros p_v q_v r_v. simpl.
  Exists r_v q_v p_v.
  simpl.
  entailer!.
Qed. 

Lemma proof_of_atomic_push2_3_which_implies_wit_2 : atomic_push2_3_which_implies_wit_2.
Proof.
  pre_process.
  unfold os_inv.
  destruct q0 as [[p q] r].
  unfold prod3. simpl.
  Exists v_3 v_2 v.
  entailer!.
Qed. 

Lemma proof_of_triple_work_C_entail_wit_1 : triple_work_C_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_triple_work_C_entail_wit_2 : triple_work_C_entail_wit_2.
Proof.
  pre_process.
  Exists l2. 
  entailer!.
Qed. 

Lemma proof_of_triple_work_C_entail_wit_5 : triple_work_C_entail_wit_5.
Proof.
  pre_process.
  Exists l2. 
  entailer!.
Qed. 

Lemma proof_of_triple_work_C_return_wit_1_1 : triple_work_C_return_wit_1_1.
Proof.
  pre_process.
  subst.
  Exists (snd q0) (snd (fst q0)) (fst (fst q0)) l2_2.
  entailer!.
Qed.

Lemma proof_of_triple_work_C_partial_solve_wit_2_pure : triple_work_C_partial_solve_wit_2_pure.
Proof.
  pre_process.
Qed. 

Lemma proof_of_triple_work_C_partial_solve_wit_3_pure : triple_work_C_partial_solve_wit_3_pure.
Proof.
  pre_process.
Qed. 

Lemma proof_of_atomic_push2_3_derive_aux_push_spec_by_normal_push_spec : atomic_push2_3_derive_aux_push_spec_by_normal_push_spec.
Proof.
  pre_process. Intros r.
  subst.
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists q0 l1 X' (snd q0).
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros r_4 l2_2.
  subst.
  Exists (snd q0) l2_2.
  entailer!.
  apply (H0 (fun _ => LastSeen l2_2) tt H1).
Qed. 

Lemma proof_of_atomic_pop2_2_derive_aux_pop_spec_by_normal_pop_spec : atomic_pop2_2_derive_aux_pop_spec_by_normal_pop_spec.
Proof.
  pre_process. Intros q.
  eapply safeExec_bind in H as (X' & ? & ?).
  subst.
  Exists q0 l1 X' (snd (fst q0)).
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  asrt_simpl.
  Split.
  - Left. Intros q_5 l2_3 x_pre_v retval.
    subst.
    Exists (snd (fst q0)) l2_3 x_pre_v 1.
    entailer!.
    apply (H1 (fun _ => LastSeen l2_3) _ H2).
  - Right. Intros q_5 l2_3 retval.
    subst.
    Exists (snd (fst q0)) l2_3 0.
    entailer!.
    apply (H1 (fun _ => LastSeen l2_3) _ H2).
Qed. 

Lemma proof_of_atomic_rev1_2_derive_aux_rev_spec_by_normal_rev_spec : atomic_rev1_2_derive_aux_rev_spec_by_normal_rev_spec.
Proof.
  pre_process. Intros p.
  eapply safeExec_bind in H as (X' & ? & ?).
  subst.
  Exists q0 l1 X' (fst (fst q0)).
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  Intros r_4 l2_2.
  subst.
  Exists (fst (fst q0)) l2_2.
  entailer!.
  apply (H1 (fun _ => LastSeen l2_2) tt H0).
Qed. 
