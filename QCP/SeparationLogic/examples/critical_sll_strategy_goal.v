Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import critical_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition critical_sll_strategy1 :=
  forall (l1 : (list Z)),
    TT &&
    emp **
    ((InsideCritical l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (list Z)),
      TT &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((InsideCritical l2))
      ).

Definition critical_sll_strategy2 :=
  forall (l1 : (list Z)),
    TT &&
    emp **
    ((OutsideCritical l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (list Z)),
      TT &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((OutsideCritical l2))
      ).

Definition critical_sll_strategy3 :=
  forall (l1 : (list Z)),
    TT &&
    emp **
    ((os_inv l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (list Z)),
      TT &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((os_inv l2))
      ).

Definition critical_sll_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l2 : (list Z)) (l1 : (list Z)),
    TT &&
    emp -*
    TT &&
    ([| (GTrans l1 l2) |]) &&
    emp
    ).

Module Type critical_sll_Strategy_Correct.

  Axiom critical_sll_strategy1_correctness : critical_sll_strategy1.
  Axiom critical_sll_strategy2_correctness : critical_sll_strategy2.
  Axiom critical_sll_strategy3_correctness : critical_sll_strategy3.
  Axiom critical_sll_strategy4_correctness : critical_sll_strategy4.

End critical_sll_Strategy_Correct.
