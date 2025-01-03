Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.

Export naive_C_Rules.
Local Open Scope sac.

Record IntPair := { a: Z -> Z; b: Z -> Z }.

Record Pair {A : Type} := Build_Pair { a1 : A -> Z ; b1 : A -> Z }.

Record Pair0 := Build_Pair0 { a2 : Z ; b2 : Z }.


Definition IntPairSep (x y: Z) (p: IntPair) :=
  (poly_store FET_int x (@a p 1)) **
  (poly_store FET_int y (@b p 1)).

Definition IntPairSep2 (x : Z) (p: IntPair) :=
  (poly_store FET_int x (@a p 1)) **
  (poly_store FET_int &( "z" ) (@b p 1)).

Definition IntPairSep3 {A : Type} (x : Z) (p: Pair) (a0 b0 : A):=
  (poly_store FET_int x (p.(a1) a0)) **
  (poly_store FET_int &( "z" ) (p.(b1) b0)).

Definition IntPairSep4 (x : Z) (p: Pair0) :=
  (poly_store FET_int x (@a2 p)) **
  (poly_store FET_int &( "z" ) (@b2 p)).