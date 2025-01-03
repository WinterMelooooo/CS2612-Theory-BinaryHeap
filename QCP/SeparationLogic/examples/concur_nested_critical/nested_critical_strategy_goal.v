Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import nested_critical_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition nested_critical_strategy1 :=
  forall (r1 : (@list Z)) (l1 : (@list Z)),
    TT &&
    emp **
    ((Critical r1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (r2 : (@list Z)),
      TT &&
      ([| (r1 = r2) |]) &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((Critical r2 l2))
      ).

Definition nested_critical_strategy3 :=
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

Definition nested_critical_strategy4 :=
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

Module Type nested_critical_Strategy_Correct.

  Axiom nested_critical_strategy1_correctness : nested_critical_strategy1.
  Axiom nested_critical_strategy3_correctness : nested_critical_strategy3.
  Axiom nested_critical_strategy4_correctness : nested_critical_strategy4.

End nested_critical_Strategy_Correct.
