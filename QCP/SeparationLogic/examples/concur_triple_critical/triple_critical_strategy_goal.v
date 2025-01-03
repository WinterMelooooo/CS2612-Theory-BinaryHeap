Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import triple_critical_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition triple_critical_strategy1 :=
  forall (p1 : (@prod (@prod Z Z) Z)) (l1 : (@prod (@prod (@list Z) (@list Z)) (@list Z))),
    TT &&
    emp **
    ((InsideCritical p1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@prod (@prod (@list Z) (@list Z)) (@list Z))) (p2 : (@prod (@prod Z Z) Z)),
      TT &&
      ([| (p1 = p2) |]) &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((InsideCritical p2 l2))
      ).

Definition triple_critical_strategy2 :=
  forall (p1 : (@prod (@prod Z Z) Z)) (l1 : (@prod (@prod (@list Z) (@list Z)) (@list Z))),
    TT &&
    emp **
    ((OutsideCritical p1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@prod (@prod (@list Z) (@list Z)) (@list Z))) (p2 : (@prod (@prod Z Z) Z)),
      TT &&
      ([| (p1 = p2) |]) &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((OutsideCritical p2 l2))
      ).

Definition triple_critical_strategy3 :=
  forall (p1 : (@prod (@prod Z Z) Z)) (l1 : (@prod (@prod (@list Z) (@list Z)) (@list Z))),
    TT &&
    emp **
    ((os_inv p1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@prod (@prod (@list Z) (@list Z)) (@list Z))) (p2 : (@prod (@prod Z Z) Z)),
      TT &&
      ([| (p1 = p2) |]) &&
      ([| (l1 = l2) |]) &&
      emp -*
      TT &&
      emp **
      ((os_inv p2 l2))
      ).

Definition triple_critical_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l2 : (@prod (@prod (@list Z) (@list Z)) (@list Z))) (l1 : (@prod (@prod (@list Z) (@list Z)) (@list Z))) (q2 : (@prod (@prod Z Z) Z)) (q1 : (@prod (@prod Z Z) Z)),
    TT &&
    ([| (q1 = q2) |]) &&
    ([| (GTrans_Abs l1 l2) |]) &&
    emp -*
    TT &&
    ([| (GTrans_C q1 l1 q2 l2) |]) &&
    emp
    ).

Definition triple_critical_strategy5 :=
  forall (l1 : (@prod (@prod (@list Z) (@list Z)) (@list Z))) (l2 : (@prod (@prod (@list Z) (@list Z)) (@list Z))) (q2 : (@prod (@prod Z Z) Z)) (q1 : (@prod (@prod Z Z) Z)),
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

Definition triple_critical_strategy6 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l2 : (@prod (@prod (@list Z) (@list Z)) (@list Z))) (l1 : (@prod (@prod (@list Z) (@list Z)) (@list Z))),
    TT &&
    emp -*
    TT &&
    ([| (GTrans_Abs l1 l2) |]) &&
    emp
    ).

Module Type triple_critical_Strategy_Correct.

  Axiom triple_critical_strategy1_correctness : triple_critical_strategy1.
  Axiom triple_critical_strategy2_correctness : triple_critical_strategy2.
  Axiom triple_critical_strategy3_correctness : triple_critical_strategy3.
  Axiom triple_critical_strategy4_correctness : triple_critical_strategy4.
  Axiom triple_critical_strategy5_correctness : triple_critical_strategy5.
  Axiom triple_critical_strategy6_correctness : triple_critical_strategy6.

End triple_critical_Strategy_Correct.
