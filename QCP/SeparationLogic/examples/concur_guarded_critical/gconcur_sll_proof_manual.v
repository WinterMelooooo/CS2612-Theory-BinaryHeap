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
From SimpleC.EE.concur_guarded_critical Require Import gconcur_sll_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import guarded_critical_sll_lib.
Import sll_C_Rules.
Require Import guarded_critical_sll_lib.
Import sll_C_Rules.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import guarded_critical_sll_lib.
Import sll_C_Rules.
Local Open Scope stmonad.
Require Import guarded_critical_sll_lib.
Local Open Scope sac.

Lemma proof_of_atomic_rev1_which_implies_wit_1 : atomic_rev1_which_implies_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_atomic_rev1_which_implies_wit_2 : atomic_rev1_which_implies_wit_2.
Proof.
  pre_process.
  unfold os_inv.
  Exists q_v.
  entailer!.
Qed.

Lemma proof_of_atomic_rev2_return_wit_1 : atomic_rev2_return_wit_1.
Proof.
  pre_process.
  Exists (rev l0).
  entailer!.
  clear H0.
  revert H1; apply highstepend_derive.
  exists tt.
  hnf.
  intros.
  exists (RTrans_Abs (rev l0)).
  unfold LastSeen in H0.
  unfold atomic_rev, atomic_cmd.
  split.
  + exists l0, (rev l0).
    split; [ | split].
    - sets_unfold in H0.
      rewrite <- H0.
      tauto.
    - reflexivity.
    - reflexivity.
  + unfold LastSeen.
    reflexivity.
Qed.

Lemma proof_of_atomic_rev2_which_implies_wit_1 : atomic_rev2_which_implies_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_atomic_rev2_which_implies_wit_2 : atomic_rev2_which_implies_wit_2.
Proof.
  pre_process.
  unfold os_inv.
  Exists q_v.
  entailer!.
Qed.

Lemma proof_of_atomic_rev_twice1_which_implies_wit_1 : atomic_rev_twice1_which_implies_wit_1.
Proof.
    pre_process.
Qed.

Lemma proof_of_atomic_rev_twice1_which_implies_wit_2 : atomic_rev_twice1_which_implies_wit_2.
Proof.
    pre_process.
    unfold os_inv.
    Exists q_v.
    entailer!.
Qed.

Lemma proof_of_atomic_rev_twice1_which_implies_wit_3 : atomic_rev_twice1_which_implies_wit_3.
Proof.
    pre_process.
Qed.

Lemma proof_of_atomic_rev_twice1_which_implies_wit_4 : atomic_rev_twice1_which_implies_wit_4.
Proof.
    pre_process.
    unfold os_inv.
    Exists q_v.
    entailer!.
Qed.

Lemma proof_of_atomic_rev_twice2_return_wit_1 : atomic_rev_twice2_return_wit_1.
Proof.
    pre_process.
    Exists (rev l0_2).
    entailer!.
    revert H3.
    unfold atomic_rev_twice. 
    apply highstepend_derive.
    exists tt.
    hnf.
    intros.
    exists (RTrans_Abs(rev l0_2)).
    unfold LastSeen in H3.
    unfold bind.
    split.
    - exists tt,(RTrans_Abs (rev l0)).
      unfold atomic_rev, atomic_cmd.
      split.
      + exists l0,(rev l0).
        split;[ | split].
        * sets_unfold in H3. 
          rewrite H3 in H1.
          tauto.
        * reflexivity.
        * reflexivity.
      + exists l0_2,(rev l0_2).
      split;[ tauto| split;reflexivity].
    - unfold LastSeen.
      reflexivity.
Qed.

Lemma proof_of_atomic_rev_twice2_which_implies_wit_1 : atomic_rev_twice2_which_implies_wit_1.
Proof.
    pre_process.
Qed.

Lemma proof_of_atomic_rev_twice2_which_implies_wit_2 : atomic_rev_twice2_which_implies_wit_2.
Proof.
    pre_process.
    unfold os_inv.
    exists q_v.
    tauto.
Qed.

Lemma proof_of_atomic_rev_twice2_which_implies_wit_3 : atomic_rev_twice2_which_implies_wit_3.
Proof.
    pre_process.
Qed.

Lemma proof_of_atomic_rev_twice2_which_implies_wit_4 : atomic_rev_twice2_which_implies_wit_4.
Proof.
    pre_process.
    unfold os_inv.
    exists q_v.
    tauto.
Qed.

