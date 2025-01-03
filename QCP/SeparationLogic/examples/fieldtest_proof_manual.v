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
From SimpleC.EE Require Import fieldtest_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import fieldtest_lib.
Local Open Scope sac.

Lemma proof_of_f_return_wit_1 : f_return_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_g_return_wit_1 : g_return_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_g2_return_wit_1 : g2_return_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_g3_return_wit_1 : g3_return_wit_1.
Proof.
  pre_process.
Qed.


