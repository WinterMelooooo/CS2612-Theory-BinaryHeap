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
From SimpleC.EE.simple_arith Require Import Signed_unsigned_test_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_local_safety_wit_2 : local_safety_wit_2.
Proof.
  pre_process.
  entailer! ; 
  lastnbits_eq.
Qed.

Lemma proof_of_local_return_wit_1 : local_return_wit_1.
Proof.
  pre_process.
  entailer! ; 
  lastnbits_eq.
Qed.

Lemma proof_of_local2_return_wit_1 : local2_return_wit_1.
Proof.
  pre_process.
  entailer!.
  lastnbits_simpl.
Qed.  

