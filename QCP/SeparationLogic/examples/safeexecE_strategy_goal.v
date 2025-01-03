Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import kmp_rel_lib.
Local Open Scope stmonad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition safeexecE_strategy3 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (B : Type) (Sigma : Type) (c22 : (A -> (@program Sigma B))) (c12 : (A -> (@program Sigma B))) (c11 : (@program Sigma A)) (c21 : (@program Sigma A)),
    TT &&
    ([| (equiv c11 c21) |]) &&
    ([| (equiv c12 c22) |]) &&
    emp -*
    TT &&
    ([| (equiv (@bind Sigma A B c11 c12) (@bind Sigma A B c21 c22)) |]) &&
    emp
    ).

Definition safeexecE_strategy4 :=
  forall (Sigma : Type) (A : Type) (x : (@program Sigma A)),
    TT &&
    ([| (equiv x x) |]) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition safeexecE_strategy5 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (Sigma : Type) (A : Type) (x : (@program Sigma A)),
    TT &&
    emp -*
    TT &&
    ([| (equiv x x) |]) &&
    emp
    ).

Definition safeexecE_strategy1 :=
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

Definition safeexecE_strategy6 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (Sigma : Type) (A : Type) (x : (@program Sigma A)) (y : (@program Sigma A)),
    TT &&
    ([| (equiv x y) |] || [| (equiv y x) |]) &&
    emp -*
    TT &&
    ([| (equiv x y) |] || [| (equiv y x) |]) &&
    emp
    ).

Definition safeexecE_strategy7 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (B : Type) (Sigma : Type) (x : (A -> (@program Sigma B))) (y : (A -> (@program Sigma B))),
    TT &&
    ([| (equiv x y) |] || [| (equiv y x) |]) &&
    emp -*
    TT &&
    ([| (equiv x y) |] || [| (equiv y x) |]) &&
    emp
    ).

Definition safeexecE_strategy8 :=
  forall (Sigma : Type) (A : Type) (B : Type) (g : (B -> (@program Sigma A))) (f : (@program Sigma B)) (X : (A -> (Sigma -> Prop))) (P : (Sigma -> Prop)),
    TT &&
    ([| (safeExec P (@bind Sigma B A f g) X) |]) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (h : (B -> (@program Sigma A))),
      TT &&
      ([| (equiv g h) |]) &&
      emp -*
      TT &&
      ([| (safeExec P (@bind Sigma B A f h) X) |]) &&
      emp
      ).

Definition safeexecE_strategy9 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (e : Z) (e0 : Z) (c : Z) (c0 : Z) (a : A) (a0 : A) (b0 : (@list A)) (b : (@list A)) (d0 : (@list Z)) (d : (@list Z)),
    TT &&
    ([| (a = a0) |]) &&
    ([| (b = b0) |]) &&
    ([| (c = c0) |]) &&
    ([| (d = d0) |]) &&
    ([| (e = e0) |]) &&
    emp -*
    TT &&
    ([| (equiv (@constr_loop_from A a b c d e) (@constr_loop_from A a0 b0 c0 d0 e0)) |]) &&
    emp
    ).

Definition safeexecE_strategy2 :=
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
      ([| (equiv c c2) |]) &&
      emp -*
      TT &&
      ([| (safeExec P c2 X) |]) &&
      emp
      ).

Module Type safeexecE_Strategy_Correct.

  Axiom safeexecE_strategy3_correctness : safeexecE_strategy3.
  Axiom safeexecE_strategy4_correctness : safeexecE_strategy4.
  Axiom safeexecE_strategy5_correctness : safeexecE_strategy5.
  Axiom safeexecE_strategy1_correctness : safeexecE_strategy1.
  Axiom safeexecE_strategy6_correctness : safeexecE_strategy6.
  Axiom safeexecE_strategy7_correctness : safeexecE_strategy7.
  Axiom safeexecE_strategy8_correctness : safeexecE_strategy8.
  Axiom safeexecE_strategy9_correctness : safeexecE_strategy9.
  Axiom safeexecE_strategy2_correctness : safeexecE_strategy2.

End safeexecE_Strategy_Correct.
