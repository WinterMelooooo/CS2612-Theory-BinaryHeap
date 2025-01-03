Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
Require Import SL.ConAssertion SL.CriticalSTS SL.NestedCriticalSTS.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Local Open Scope stmonad.

Definition sll_CS_C : critical_STS := {|
  critical_STS_state := (Z * Z * Z) * (list Z * list Z * list Z);
  critical_STS_transition := fun s1 s2 => fst s1 = fst s2
|}.

Definition sll_CS_Abs : critical_STS := {|
  critical_STS_state := list Z * list Z * list Z;
  critical_STS_transition := fun _ _ => 0 = 0 (* not to true, to prevent some related tacitcs **)
|}.

Module C_STS_sll_C <: critical_STS_def.
  Definition c_sts: critical_STS := sll_CS_C.
End C_STS_sll_C.

Module sll_TC_Rules <: SeparationLogicSig.
  Include C_STS_sll_C.
  Include critical_STS_to_STS_def.
  Include ConAssertion.CSL.
  Include DerivedPredSig.
  Include StoreLibSig.
  Include ArrayLibSig.
  Include CriticalCSL.
End sll_TC_Rules.

Module C_STS_sll_Abs <: critical_STS_def.
  Definition c_sts: critical_STS := sll_CS_Abs.
End C_STS_sll_Abs.

Module STS_sll_Abs.
  Include C_STS_sll_Abs.
  Include critical_STS_to_STS_def.
End STS_sll_Abs.

Export sll_TC_Rules.

Local Open Scope sac.

Fixpoint sll (x: addr) (l: list Z): Assertion :=
  match l with
    | nil     => [| x = NULL |] && emp
    | a :: l0 => [| x <> NULL |] && 
                 EX y: addr,
                   &(x # "list" ->ₛ "data") # Int |-> a **
                   &(x # "list" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.

Definition InsideCritical p l: Assertion :=
  sll_TC_Rules.InsideCritical (p, l).

Definition OutsideCritical p l: Assertion :=
  sll_TC_Rules.OutsideCritical (p, l).

Definition RTrans_C (p1: Z * Z * Z) (l1: list Z * list Z * list Z) (p2: Z * Z * Z) (l2: list Z * list Z * list Z): Prop :=
  sll_TC_Rules.RTrans (p1, l1) (p2, l2).

Definition GTrans_C (p1: Z * Z * Z) (l1: list Z * list Z * list Z) (p2: Z * Z * Z) (l2: list Z * list Z * list Z): Prop :=
  sll_TC_Rules.GTrans (p1, l1) (p2, l2).

Definition RTrans_Abs (l1 l2: list Z * list Z * list Z): Prop :=
  STS_sll_Abs.RTrans l1 l2.

Definition GTrans_Abs (l1 l2: list Z * list Z * list Z): Prop :=
  STS_sll_Abs.GTrans l1 l2.

Definition os_inv (a : Z * Z * Z) l: Assertion :=
  let '(l1 , l2 , l3) := l in
  let '(p , q , r) := a in
  EX p_v q_v r_v,
    p # Ptr |-> p_v ** sll p_v l1 ** 
    q # Ptr |-> q_v ** sll q_v l2 **
    r # Ptr |-> r_v ** sll r_v l3.

Definition atomic_cmd {A} (c: program (list Z * list Z * list Z) A): program (list Z * list Z * list Z -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c l1 a l2 /\
    X2 == (RTrans_Abs l2).

(* Seem useless


Definition Signle_RTrans (l1 l2 : list Z) : Prop := 1 = 1.

Definition Signle_GTrans (l1 l2 : list Z) : Prop := 1 = 1.

Definition atomic_single_cmd {A} (c: program (list Z) A): program (list Z -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c l1 a l2 /\ X2 == (Signle_RTrans l2).

Definition atomic_single_rev: program (list Z -> Prop) unit :=
  atomic_single_cmd (fun s1 _ s2 => s2 = rev s1).

Definition atomic_single_push (x: Z): program (list Z -> Prop) unit :=
  atomic_single_cmd (fun s1 _ s2 => s2 = cons x s1).

Definition atomic_single_pop: program (list Z -> Prop) (option Z) :=
  atomic_single_cmd (fun s1 r s2 => match s1 with
                             | nil => r = None
                             | cons z s1' => r = Some z /\ s1' = s2
                             end).

Definition Signle_LastSeen (l: list Z): (list Z -> Prop) -> Prop :=
  fun B => (Signle_RTrans l) == B.
*)

Definition atomic_1_cmd {A} (c: program (list Z) A): program (list Z * list Z * list Z -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (fst (fst l1)) a (fst (fst l2)) /\
    snd (fst l1) = snd (fst l2) /\ snd l1 = snd l2 /\
    X2 == (RTrans_Abs l2).

Definition atomic_2_cmd {A} (c: program (list Z) A): program (list Z * list Z * list Z -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (snd (fst l1)) a (snd (fst l2)) /\
    fst (fst l1) = fst (fst l2) /\ snd l1 = snd l2 /\
    X2 == (RTrans_Abs l2).

Definition atomic_3_cmd {A} (c: program (list Z) A): program (list Z * list Z * list Z -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c (snd l1) a (snd l2) /\
    fst l1 = fst l2 /\ snd (fst l1) = snd (fst l2) /\
    X2 == (RTrans_Abs l2).

Definition atomic_1_rev : program (list Z * list Z * list Z -> Prop) unit :=
  atomic_1_cmd (fun s1 _ s2 => s2 = rev s1).

Definition atomic_2_rev : program (list Z * list Z * list Z -> Prop) unit :=
  atomic_2_cmd (fun s1 _ s2 => s2 = rev s1).

Definition atomic_3_rev : program (list Z * list Z * list Z -> Prop) unit :=
  atomic_3_cmd (fun s1 _ s2 => s2 = rev s1).

Definition atomic_1_push (x: Z): program (list Z * list Z * list Z -> Prop) unit :=
  atomic_1_cmd (fun s1 _ s2 => s2 = cons x s1).

Definition atomic_2_push (x: Z): program (list Z * list Z * list Z -> Prop) unit :=
  atomic_2_cmd (fun s1 _ s2 => s2 = cons x s1).

Definition atomic_3_push (x: Z): program (list Z * list Z * list Z -> Prop) unit :=
  atomic_3_cmd (fun s1 _ s2 => s2 = cons x s1).

Definition atomic_1_pop: program (list Z * list Z * list Z -> Prop) (option Z) :=
  atomic_1_cmd (fun s1 r s2 => match s1 with
                                | nil => r = None
                                | cons z s1' => r = Some z /\ s1' = s2
                               end).

Definition atomic_2_pop: program (list Z * list Z * list Z -> Prop) (option Z) :=
  atomic_2_cmd (fun s1 r s2 => match s1 with
                                | nil => r = None
                                | cons z s1' => r = Some z /\ s1' = s2
                               end).

Definition atomic_3_pop: program (list Z * list Z * list Z -> Prop) (option Z) :=
  atomic_3_cmd (fun s1 r s2 => match s1 with
                                | nil => r = None
                                | cons z s1' => r = Some z /\ s1' = s2
                               end).

Definition atomic_3_push_loc0 (x : option Z) : program (list Z * list Z * list Z -> Prop) unit :=
  match x with 
    | Some x => atomic_3_push x
    | None => return tt
  end.

Definition pop2_push3 : unit -> program (list Z * list Z * list Z -> Prop) unit :=
  fun _ => x <- atomic_2_pop;; atomic_3_push_loc0 x.

Definition triple_work : program (list Z * list Z * list Z -> Prop) unit :=
  atomic_1_rev ;; x <- atomic_2_pop;; atomic_3_push_loc0 x.

Definition LastSeen (l: list Z * list Z * list Z): (list Z * list Z * list Z -> Prop) -> Prop :=
  fun B => (RTrans_Abs l) == B.

Lemma sll_zero: forall x l,
  x = NULL ->
  sll x l |-- [| l = nil |] && emp.
Proof.
  intros.
  destruct l.
  + entailer!.
  + simpl.
    Intros. Intros x0.
    entailer!.
Qed.

Lemma sll_not_zero: forall x l,
  x <> NULL ->
  sll x l |--
    EX y a l0,
      [| l = a :: l0 |] &&
      &(x # "list" ->ₛ "data") # Int |-> a **
      &(x # "list" ->ₛ "next") # Ptr |-> y **
      sll y l0.
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl. Intros.
    Intros y.
    Exists y z l.
    entailer!.
Qed.

Lemma sll_not_zero': forall x l,
  x <> NULL ->
  sll x l |-- [| l <> nil |].
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl. Intros.
    Intros y.
    entailer!.
    congruence.
Qed.

Definition prod3 {A B C} (a : A) (b : B) (c : C): (A * B * C) :=
  (a, b, c).