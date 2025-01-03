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
From SimpleC.EE Require Import sll_split_while_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Require Import sll_merge_rel_lib.
Local Open Scope stmonad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
Local Open Scope sac.

Lemma proof_of_split_while_safety_wit_1 : split_while_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_split_while_safety_wit_2 : split_while_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_split_while_entail_wit_1 : split_while_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_split_while_partial_solve_wit_1_pure : split_while_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_split_while_partial_solve_wit_1 : split_while_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_split_while_partial_solve_wit_2 : split_while_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_split_while_partial_solve_wit_3_pure : split_while_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_split_while_partial_solve_wit_3 : split_while_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_split_while_partial_solve_wit_4 : split_while_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_split_while_which_implies_wit_1 : split_while_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_split_while_which_implies_wit_3 : split_while_which_implies_wit_3.
Proof. Admitted. 

