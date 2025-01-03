Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem Assertion.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope sac.
Import CRules.
Require Import String.
Local Open Scope string.

Definition sll {A: Type} (storeA: addr -> A -> Assertion) (x : addr) (l: list A): Assertion :=
  (fix sll x l :=
     match l with
     | nil     => [| x = 0 |] && emp
     | a :: l0 => EX z: addr,
                    storeA x a **
                    &(x # "LIST" ->ₛ "tail") # Ptr |-> z ** 
                    sll z l0
     end) x l.

Definition sllseg {A: Type} (storeA: addr -> A -> Assertion) (x y: addr) (l: list A): Assertion :=
  (fix sllseg x y l :=
     match l with
     | nil     => [| x = y |] && emp
     | a :: l0 => EX z: addr,
                    storeA x a **
                    &(x # "LIST" ->ₛ "tail") # Ptr |-> z **
                    sllseg z y l0
     end) x y l.

Lemma Reverse_Assert_Entailment_in_while:
   forall {A : Type} (storeA : addr -> A -> Assertion) (v w : addr) (l : list A),
   forall (l1 l2 : list A),
   [| l = app (rev l1) l2 |] && sll storeA w l1 ** sll storeA v l2 |-- 
   (EX h t l3, 
   [| l2 = h :: l3 /\ l = app (rev l1) l2 |] && &(v # "LIST" ->ₛ "tail") # Ptr |-> t
   ** sll storeA w l1 ** storeA v h ** sll storeA t l3).
Proof.
Admitted.

Lemma Reverse_Partial_Entailment_in_while_1:
 forall {A : Type} (storeA : addr -> A -> Assertion) (l : list A) (v w : addr),
 forall (l1 l2 : list A),
   [| l = app (rev l1) l2 /\ v <> 0 |] && sll storeA w l1 ** sll storeA v l2 |--
   [| v <> 0 |] && sll storeA v l2 ** TT.
Proof.
Admitted.

Lemma Reverse_Which_implies_Entailment_in_while_1:
  forall {A : Type} (storeA : addr -> A -> Assertion) (l2 : list A) (v : addr),
   [| v <> 0 |] && sll storeA v l2 |--
   EX x xs t, 
   [| l2 = x :: xs |] && &(v # "LIST" ->ₛ "tail") # Ptr |-> t ** storeA v x ** sll storeA t xs.
Proof.
Admitted.

Inductive ordered {A : Type} (le : A -> A -> Prop) : list A -> Prop :=
  | ordered_nil : ordered le nil
  | ordered_singleton : forall x, ordered le (x :: nil)
  | ordered_cons : forall x y l, le x y -> ordered le (y :: l) -> ordered le (x :: y :: l)
 .

Definition storeZ : addr -> Z -> Assertion := fun x z => &(x # "LIST" ->ₛ "head") # Int |-> z.

Definition Le : Z -> Z -> Prop := Z.le.


Lemma Main_Entailment_in_call_merge: 
  forall (x y : addr) (l1 l2 : list Z),
      [| ordered Le l1 /\ ordered Le l2 |] && 
      sll storeZ x l1 ** sll storeZ y l2 
  |--
  (EX (A : Type) (storeA : addr -> A -> Assertion) (le : A -> A -> Prop),
   EX l1 l2, 
    [| ordered le l1 /\ ordered le l2 |] &&
    sll storeA x l1 ** sll storeA y l2).
Proof.
Admitted.

Lemma Main_Entailment_in_call_merge_with_Where : 
  forall (x y : addr) (l1 l2 : list Z),
      [| ordered Le l1 /\ ordered Le l2 |] && 
      sll storeZ x l1 ** sll storeZ y l2 
  |--
   EX l1 l2, 
    [| ordered Le l1 /\ ordered Le l2 |] && 
    sll storeZ x l1 ** sll storeZ y l2.
Proof.
Admitted.