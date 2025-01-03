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
Import ListNotations.
Local Open Scope list.

Export naive_C_Rules.
Local Open Scope sac.

Definition store_char_array_rec (x: addr) (lo hi: Z) (l: list Z): Assertion :=
  store_array_rec (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a) x lo hi l. 

Lemma store_char_array_rec_length: forall x lo hi l,
  store_char_array_rec x lo hi l |-- [| Z.of_nat (length l) = hi - lo |].
Proof.
  intros.
  unfold store_char_array_rec.
  sep_apply (store_array_rec_length (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a)). entailer!.
Qed.

Definition store_char_array_missing_i_rec (x: addr) (i lo hi: Z) (l: list Z): Assertion := 
  store_array_missing_i_rec (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a) x i lo hi l.

Definition store_char_array (x: addr) (n: Z) (l: list Z): Assertion :=
  store_array (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a) x n l.

Lemma store_char_array_length: forall x n l,
  store_char_array x n l |-- [| Z.of_nat (length l) = n |].
Proof.
  intros.
  unfold store_char_array.
  sep_apply store_char_array_rec_length.
  entailer!. 
Qed.

Lemma store_char_array_Zlength: forall x n l,
  store_char_array x n l |-- [| Zlength l = n |].
Proof.
  intros; unfold store_char_array.
  apply store_array_Zlength.
Qed.

Lemma store_char_array_split: forall x n m l,
  0 <= n < m ->
  store_char_array x m l |-- store_char (x + n * sizeof(CHAR)) (Znth n l 0) ** store_char_array_missing_i_rec x n 0 m l.
Proof.
  intros.
  unfold store_char_array, store_char_array_missing_i_rec.
  sep_apply (store_array_split (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a)). entailer!.
  lia.
Qed.

Lemma store_char_array_merge: forall x n m a l,
  0 <= n < m ->
  store_char (x + n * sizeof(CHAR)) a ** store_char_array_missing_i_rec x n 0 m l |-- store_char_array x m (replace_Znth n a l).
Proof.
  intros.
  unfold store_char_array, store_char_array_missing_i_rec.
  sep_apply (store_array_merge (fun x lo a => (x + lo * sizeof(CHAR)) # Char |-> a)). entailer!.
  lia.
Qed.
