Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import guarded_critical_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition guarded_critical_strategy1 :=
  forall (p1 : Z) (l1 : (@list Z)),
    TT &&
    emp **
    ((InsideCritical p1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (p2 : Z),
      TT &&
      ([| (p1 = p2) |]) &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((InsideCritical p2 l2))
      ).

Definition guarded_critical_strategy2 :=
  forall (p1 : Z) (l1 : (@list Z)),
    TT &&
    emp **
    ((OutsideCritical p1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (p2 : Z),
      TT &&
      ([| (p1 = p2) |]) &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((OutsideCritical p2 l2))
      ).

Definition guarded_critical_strategy3 :=
  forall (p1 : Z) (l1 : (@list Z)),
    TT &&
    emp **
    ((os_inv p1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)) (p2 : Z),
      TT &&
      ([| (p1 = p2) |]) &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((os_inv p2 l2))
      ).

Definition guarded_critical_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l2 : (@list Z)) (l1 : (@list Z)) (q2 : Z) (q1 : Z),
    TT &&
    ([| (q1 = q2) |]) &&
    ([| (GTrans_Abs l1 l2) |]) &&
    emp -*
    TT &&
    ([| (GTrans_C q1 l1 q2 l2) |]) &&
    emp
    ).

Definition guarded_critical_strategy5 :=
  forall (l1 : (@list Z)) (l2 : (@list Z)) (q2 : Z) (q1 : Z),
    TT &&
    ([| (RTrans_C q1 l1 q2 l2) |]) &&
    emp
    |--
    (
    TT &&
    ([| (q1 = q2) |]) &&
    ([| (RTrans_Abs l1 l2) |]) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition guarded_critical_strategy6 :=
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
    ([| (GTrans_Abs l1 l2) |]) &&
    emp
    ).

Module Type guarded_critical_Strategy_Correct.

  Axiom guarded_critical_strategy1_correctness : guarded_critical_strategy1.
  Axiom guarded_critical_strategy2_correctness : guarded_critical_strategy2.
  Axiom guarded_critical_strategy3_correctness : guarded_critical_strategy3.
  Axiom guarded_critical_strategy4_correctness : guarded_critical_strategy4.
  Axiom guarded_critical_strategy5_correctness : guarded_critical_strategy5.
  Axiom guarded_critical_strategy6_correctness : guarded_critical_strategy6.

End guarded_critical_Strategy_Correct.
