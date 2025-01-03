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
From compcert.lib Require Import Integers.
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

Definition store_int_array_rec (x: addr) (lo hi: Z) (l: list Z): Assertion :=
  store_array_rec (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a) x lo hi l. 

Lemma store_int_array_rec_length: forall x lo hi l,
  store_int_array_rec x lo hi l |-- [| Z.of_nat (length l) = hi - lo |].
Proof.
  intros.
  unfold store_int_array_rec.
  sep_apply (store_array_rec_length (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
Qed.

Lemma store_int_array_rec_Zlength: forall x lo hi l,
  store_int_array_rec x lo hi l |-- [| Zlength l = hi - lo |].
Proof.
  intros.
  sep_apply store_int_array_rec_length.
  rewrite Zlength_correct.
  entailer!.
Qed.


Definition store_int_array_missing_i_rec (x: addr) (i lo hi: Z) (l: list Z): Assertion := 
  store_array_missing_i_rec (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a) x i lo hi l.

Definition store_int_array (x: addr) (n: Z) (l: list Z): Assertion :=
  store_array (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a) x n l.

Lemma store_int_array_length: forall x n l,
  store_int_array x n l |-- [| Z.of_nat (length l) = n |].
Proof.
  intros.
  unfold store_int_array.
  sep_apply store_int_array_rec_length.
  entailer!. 
Qed.

Lemma store_int_array_Zlength: forall x n l,
  store_int_array x n l |-- [| Zlength l = n |].
Proof.
  intros.
  unfold store_int_array.
  apply store_array_Zlength.
Qed.

Lemma store_int_array_range : forall x n l,
  store_int_array x n l |-- [| forall a, In a l -> Int.min_signed <= a <= Int.max_signed |].
Proof.
  intros.
  unfold store_int_array.
  unfold store_array.
  remember 0 as lo.
  rename n into hi.
  clear Heqlo. revert lo hi. 
  induction l ; intros. 
  - entailer!.
  - simpl. prop_apply IHl.
    prop_apply store_int_range.
    entailer!.
    intros. destruct H1 ; auto.
    subst. auto. 
Qed.

Lemma store_int_array_rec_split: forall x lo n m l,
  lo <= n < m ->
  store_int_array_rec x lo m l |-- store_int (x + n * sizeof(INT)) (Znth (n -lo) l 0) ** store_int_array_missing_i_rec x n lo m l.
Proof.
  intros.
  unfold store_int_array_rec, store_int_array_missing_i_rec.
  sep_apply (store_array_rec_split (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
  lia.
Qed.

Lemma store_int_array_rec_merge: forall x lo n m a l,
  lo <= n < m ->
  store_int (x + n * sizeof(INT)) a ** store_int_array_missing_i_rec x n lo m l |-- store_int_array_rec x lo m (replace_Znth (n -lo) a l).
Proof.
  intros.
  unfold store_int_array_rec, store_int_array_missing_i_rec.
  sep_apply (store_array_rec_merge (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
  lia.
Qed.

Lemma store_int_array_rec_divide:
  forall x lo n l m,
    lo <= m <= n -> Zlength l = n -lo ->
    store_int_array_rec x lo n l --||-- 
    store_int_array_rec x lo m (sublist 0 (m - lo) l) ** store_int_array_rec x m n (sublist (m -lo) (n -lo) l).
Proof.
  intros; unfold store_int_array_rec. 
  eapply store_array_rec_divide_aux with (storeA := store_int); eauto.
Qed.

Lemma store_int_array_rec_divide_rev:
  forall x lo n l1 l2 m,
    lo <= m <= n -> 
    store_int_array_rec x lo m l1 ** store_int_array_rec x m n l2 |-- 
    store_int_array_rec x lo n (l1 ++ l2).
Proof.
  intros.
  prop_apply (store_int_array_rec_Zlength x lo).
  prop_apply (store_int_array_rec_Zlength x m).
  Intros.
  rewrite (store_int_array_rec_divide x lo n (l1 ++ l2) m);[ | lia | ].
  rewrite <- H0.
  rewrite sublist_app_exact1 by lia.
  rewrite sublist_split_app_r with (len := Zlength l1) by lia.
  replace (Zlength l1 - Zlength l1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_app. lia.
Qed.

Lemma store_int_array_rec_head:
  forall x lo hi l,
    lo < hi -> 
    store_int_array_rec x lo hi l  |-- 
    (x + lo * sizeof ( INT )) # Int |-> (Znth 0 l 0) ** 
    store_int_array_rec x (lo + 1) hi (sublist 1 (hi - lo) l).
Proof.
  intros.
  destruct l.
  - unfold store_int_array_rec. simpl.
    entailer!.
  - prop_apply (store_int_array_rec_Zlength x lo hi).
  Intros.
  rewrite (store_int_array_rec_divide x lo hi ((z :: nil) ++ l) (lo + 1));[ | lia | easy ].
  replace (lo + 1 - lo) with 1 by lia.
  assert (Zlength (z::nil) = 1). { rewrite Zlength_cons, Zlength_nil. lia. }
  rewrite <- H1 at 2.
  rewrite sublist_app_exact1.
  replace (z::l) with (app (z :: nil) l)  by easy.
  rewrite sublist_split_app_r with (len := 1) by lia.
  replace (1 - 1) with 0 by lia.
  rewrite sublist_self.
  entailer!.
  unfold store_int_array_rec. simpl.
  Intros.
  rewrite Znth0_cons.
  entailer!.
  rewrite Zlength_cons in H0. lia. 
Qed.


Lemma store_int_array_rec_head_merge:
  forall x lo hi z l,
    lo < hi -> 
    (x + lo * sizeof ( INT )) # Int |-> z ** 
    store_int_array_rec x (lo + 1) hi l |-- 
    store_int_array_rec x lo hi (z :: l).
Proof.
  intros.
  prop_apply (store_int_array_rec_Zlength x (lo + 1) hi).
  Intros.
  rewrite (store_int_array_rec_divide x lo hi ((z :: nil) ++ l) (lo + 1));[ | lia |  ].
  replace (lo + 1 - lo) with 1 by lia.
  assert (Zlength (z::nil) = 1). { rewrite Zlength_cons, Zlength_nil. lia. }
  rewrite <- H1 at 3.
  rewrite sublist_app_exact1.
  rewrite sublist_split_app_r with (len := 1) by lia.
  replace (1 - 1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  unfold store_int_array_rec. simpl.
  entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.  lia. 
Qed.

Lemma store_int_array_rec_tail_merge:
  forall x lo hi z l,
    lo <= hi -> 
    (x + hi * sizeof ( INT )) # Int |-> z ** 
    store_int_array_rec x lo hi l |-- 
    store_int_array_rec x lo (hi + 1) (l ++ [z]).
Proof.
  intros.
  prop_apply (store_int_array_rec_Zlength x lo hi).
  Intros.
  rewrite (store_int_array_rec_divide x lo (hi + 1) (l ++ [z]) hi);[ | lia |  ].
  rewrite <- H0 at 1.
  rewrite sublist_app_exact1.
  rewrite sublist_split_app_r with (len := hi - lo) by lia.
  replace (hi - lo - (hi - lo)) with 0 by lia.
  rewrite sublist_self.
  entailer!.
  unfold store_int_array_rec. simpl.
  entailer!.
  rewrite Zlength_cons, Zlength_nil. lia.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.  lia. 
Qed.

Lemma store_int_array_rec_cons:
  forall x lo hi z l,
    lo < hi -> 
    store_int_array_rec x lo hi (z::l)  |-- 
    (x + lo * sizeof ( INT )) # Int |-> z ** 
    store_int_array_rec x (lo + 1) hi l.
Proof.
  intros.
  prop_apply store_int_array_rec_Zlength.
  Intros.
  rewrite Zlength_cons in H0.
  sep_apply store_int_array_rec_head;[ | lia].
  rewrite Znth0_cons.
  replace (z :: l) with ([z] ++ l) by easy.
  rewrite sublist_split_app_r with (len := 1).
  replace (1-1) with 0 by lia.
  rewrite sublist_self by lia.
  entailer!.
  rewrite Zlength_cons,Zlength_nil. lia.
  lia.
Qed.

Lemma store_int_array_split: forall x n m l,
  0 <= n < m ->
  store_int_array x m l |-- store_int (x + n * sizeof(INT)) (Znth n l 0) ** store_int_array_missing_i_rec x n 0 m l.
Proof.
  intros.
  unfold store_int_array, store_int_array_missing_i_rec.
  sep_apply (store_array_split (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
  lia.
Qed.

Lemma store_int_array_merge: forall x n m a l,
  0 <= n < m ->
  store_int (x + n * sizeof(INT)) a ** store_int_array_missing_i_rec x n 0 m l |-- store_int_array x m (replace_Znth n a l).
Proof.
  intros.
  unfold store_int_array, store_int_array_missing_i_rec.
  sep_apply (store_array_merge (fun x lo a => (x + lo * sizeof(INT)) # Int |-> a)). entailer!.
  lia.
Qed.

Lemma store_int_array_divide:
  forall x n l m,
    0 <= m <= n -> Zlength l = n ->
    store_int_array x n l --||-- 
    store_int_array x m (sublist 0 m l) ** store_int_array (x + m*sizeof(INT)) (n-m) (sublist m n l).
Proof.
  intros; unfold store_int_array. 
  eapply store_array_divide with (storeA := store_int); eauto.
  auto.
Qed.

Lemma store_int_array_divide_rec:
  forall x n l m,
    0 <= m <= n -> Zlength l = n ->
    store_int_array x n l --||-- 
    store_int_array_rec x 0 m (sublist 0 m l) ** store_int_array_rec x m n (sublist m n l).
Proof.
  intros; unfold store_int_array, store_array. 
  eapply store_array_rec_divide with (storeA := store_int); eauto.
Qed.
