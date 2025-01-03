Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import fine_grained_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition critical_strategy1 :=
  forall (l1 : (@list Z)),
    TT &&
    emp **
    ((InsideCritical l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((InsideCritical l2))
      ).

Definition critical_strategy2 :=
  forall (l1 : (@list Z)),
    TT &&
    emp **
    ((OutsideCritical l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((OutsideCritical l2))
      ).

Definition critical_strategy3 :=
  forall (l1 : (@list Z)),
    TT &&
    emp **
    ((os_inv l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((os_inv l2))
      ).

Definition critical_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l2 : (@list Z)) (l1 : (@list Z)),
    TT &&
    emp -*
    TT &&
    ([| (GTrans l1 l2) |]) &&
    emp
    ).

Definition critical_strategy10 :=
  forall (x1 : Z) (l1 : (@list Z)),
    TT &&
    emp **
    ((conditionally_store_sll x1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (x2 : Z),
      TT &&
      ([| (x1 = x2) |]) &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((conditionally_store_sll x2 l2))
      ).

Module Type critical_Strategy_Correct.

  Axiom critical_strategy1_correctness : critical_strategy1.
  Axiom critical_strategy2_correctness : critical_strategy2.
  Axiom critical_strategy3_correctness : critical_strategy3.
  Axiom critical_strategy4_correctness : critical_strategy4.
  Axiom critical_strategy10_correctness : critical_strategy10.

End critical_Strategy_Correct.
