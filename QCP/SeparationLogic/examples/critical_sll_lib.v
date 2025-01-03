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
Require Import SL.ConAssertion SL.CriticalSTS.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.

Definition sll_CS : critical_STS := {|
  critical_STS_state := list Z;
  critical_STS_transition := fun _ _ => 0 = 0 (* not to true, to prevent some related tacitcs **)
|}.

Module C_STS_sll <: critical_STS_def.
  Definition c_sts: critical_STS := sll_CS.
End C_STS_sll.

Module sll_C_Rules <: SeparationLogicSig.
  Include C_STS_sll.
  Include critical_STS_to_STS_def.
  Include ConAssertion.CSL.
  Include DerivedPredSig.
  Include StoreLibSig.
  Include ArrayLibSig.
  Include CriticalCSL.
End sll_C_Rules.

Export sll_C_Rules.

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

Definition InsideCritical l: Assertion :=
  sll_C_Rules.InsideCritical l.

Definition OutsideCritical l: Assertion :=
  sll_C_Rules.OutsideCritical l.

Definition RTrans (l1 l2: list Z): Prop :=
  sll_C_Rules.RTrans l1 l2.

Definition GTrans (l1 l2: list Z): Prop :=
  sll_C_Rules.GTrans l1 l2.

Definition os_inv l: Assertion :=
  EX p_v q, &("p") # Ptr |-> p_v ** p_v # Ptr |-> q ** sll q l.

Definition atomic_cmd {A} (c: program (list Z) A): program (list Z -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c l1 a l2 /\
    X2 == (RTrans l2).

Definition atomic_rev: program (list Z -> Prop) unit :=
  atomic_cmd (fun s1 _ s2 => s2 = rev s1).

Definition LastSeen (l: list Z): (list Z -> Prop) -> Prop :=
  fun B => (RTrans l) == B.

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
