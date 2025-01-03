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

Lemma proof_of_local_safety_wit_1 : local_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_local_safety_wit_3 : local_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_local_safety_wit_4 : local_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_local_entail_wit_1 : local_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_local_return_wit_2_1 : local_return_wit_2_1.
Proof. Admitted. 

Lemma proof_of_local_return_wit_2_2 : local_return_wit_2_2.
Proof. Admitted. 

