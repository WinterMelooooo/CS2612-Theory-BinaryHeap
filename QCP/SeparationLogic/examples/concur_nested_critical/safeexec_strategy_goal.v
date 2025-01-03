Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
Local Open Scope stmonad.
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition safeexec_strategy5 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (Sigma : Type) (B : Type) (A : Type) (c12 : (A -> (@program Sigma B))) (c22 : (A -> (@program Sigma B))) (c21 : (@program Sigma A)) (c11 : (@program Sigma A)),
    TT &&
    ([| (c11 = c21) |]) &&
    ([| (c12 = c22) |]) &&
    emp -*
    TT &&
    ([| ((@bind Sigma A B c11 c12) = (@bind Sigma A B c21 c22)) |]) &&
    emp
    ).

Definition safeexec_strategy1 :=
  forall (Sigma : Type) (A : Type) (c : (@program Sigma A)) (X : (A -> (Sigma -> Prop))) (P : (Sigma -> Prop)),
    TT &&
    ([| (safeExec P c X) |]) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (B : Type) (c2 : (@program Sigma B)) (X2 : (B -> (Sigma -> Prop))) (P2 : (Sigma -> Prop)),
      TT &&
      ([| (safeExec P2 c2 X2) |]) &&
      emp -*
      TT &&
      ([| (safeExec P c X) |]) &&
      ([| (safeExec P2 c2 X2) |]) &&
      emp
      ).

Definition safeexec_strategy2 :=
  forall (Sigma : Type) (A : Type) (c : (@program Sigma A)) (X : (A -> (Sigma -> Prop))) (P : (Sigma -> Prop)),
    TT &&
    ([| (safeExec P c X) |]) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (c2 : (@program Sigma A)),
      TT &&
      ([| (c = c2) |]) &&
      emp -*
      TT &&
      ([| (safeExec P c2 X) |]) &&
      emp
      ).

Module Type safeexec_Strategy_Correct.

  Axiom safeexec_strategy5_correctness : safeexec_strategy5.
  Axiom safeexec_strategy1_correctness : safeexec_strategy1.
  Axiom safeexec_strategy2_correctness : safeexec_strategy2.

End safeexec_Strategy_Correct.
