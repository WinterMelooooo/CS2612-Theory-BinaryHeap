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
From SimpleC.EE.concur_nested_critical Require Import nconcur_sll_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
Local Open Scope stmonad.
Require Import nested_critical_sll_lib.
Local Open Scope sac.

Lemma proof_of_atomic_rev1_which_implies_wit_1 : atomic_rev1_which_implies_wit_1.
Proof.
  pre_process.
  unfold os_inv.
  Intros p_v q.
  Exists q p_v.
  entailer!.
Qed.

Lemma proof_of_atomic_rev1_which_implies_wit_2 : atomic_rev1_which_implies_wit_2.
Proof.
  pre_process.
  unfold os_inv.
  Exists p.
  Exists p_v.
  entailer!.
Qed.

Lemma proof_of_atomic_rev2_return_wit_1 : atomic_rev2_return_wit_1.
Proof.
  pre_process.
  Exists (rev l0).
  entailer!.
  revert H0; apply highstepend_derive.
  exists tt.
  hnf.
  intros.
  exists (RTrans (rev l0)).
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
  unfold os_inv.
  Intros p_v q.
  Exists q p_v.
  entailer!.
Qed.

Lemma proof_of_atomic_rev2_which_implies_wit_2 : atomic_rev2_which_implies_wit_2.
Proof.
  pre_process.
  unfold os_inv.
  Exists p.
  Exists p_v.
  entailer!.
Qed.
