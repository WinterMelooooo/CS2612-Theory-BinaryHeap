Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
Require Import nested_critical_sll_lib.
Import sll_NC_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sll_strategy3 :=
  forall (p : Z),
    TT &&
    emp **
    ((sll p (@nil Z)))
    |--
    (
    TT &&
    ([| (p = 0) |]) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sll_strategy4 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z),
    TT &&
    ([| (p = 0) |]) &&
    emp -*
    TT &&
    emp **
    ((sll p (@nil Z)))
    ).

Definition sll_strategy5 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)),
    TT &&
    ([| (l = (@nil Z)) |]) &&
    emp -*
    TT &&
    emp **
    ((sll 0 l))
    ).

Definition sll_strategy6 :=
  forall (p : Z) (x0 : Z) (l0 : (@list Z)),
    TT &&
    emp **
    ((sll p (@cons Z x0 l0)))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)) (x1 : Z),
      TT &&
      ([| (x0 = x1) |]) &&
      ([| (l0 = l1) |]) &&
      emp -*
      TT &&
      emp **
      ((sll p (@cons Z x1 l1)))
      ).

Definition sll_strategy20 :=
  forall (p : Z),
    TT &&
    ([| (p = 0) |] || [| (0 = p) |]) &&
    emp
    |--
    (
    TT &&
    ([| (p = 0) |] || [| (0 = p) |]) &&
    emp
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      ([| (l = (@nil Z)) |]) &&
      emp -*
      TT &&
      emp **
      ((sll p l))
      ).

Definition sll_strategy7 :=
  forall (p : Z) (l0 : (@list Z)),
    TT &&
    emp **
    ((sll p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list Z)),
      TT &&
      ([| (l0 = l1) |]) &&
      emp -*
      TT &&
      emp **
      ((sll p l1))
      ).

Definition sll_strategy10 :=
  forall (p : Z) (x : Z) (l : (@list Z)),
    TT &&
    emp **
    ((sll p (@cons Z x l)))
    |--
    EX (y : Z),
      (
      TT &&
      emp **
      ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
      ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
      ((sll y l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition sll_strategy11 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z) (x : Z) (y : Z) (l : (@list Z)),
    TT &&
    ([| (p <> 0) |]) &&
    emp **
    ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") x)) **
    ((poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") y)) **
    ((sll y l)) -*
    TT &&
    emp **
    ((sll p (@cons Z x l)))
    ).

Definition sll_strategy8 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    ([| (p <> 0) |] || [| (0 <> p) |]) &&
    emp **
    ((sll p l))
    |--
    EX (x : Z) (l0 : (@list Z)),
      (
      TT &&
      ([| (p <> 0) |] || [| (0 <> p) |]) &&
      ([| (l = (@cons Z x l0)) |]) &&
      emp **
      ((sll p (@cons Z x l0)))
      ) ** (
      ALL (q : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((p)) # "list" ->ₛ "data") q) || (poly_store FET_ptr &( ((p)) # "list" ->ₛ "next") q))
        ).

Definition sll_strategy9 :=
  forall (p : Z),
    TT &&
    ([| (p <> 0) |] || [| (0 <> p) |]) &&
    emp
    |--
    (
    TT &&
    ([| (p <> 0) |] || [| (0 <> p) |]) &&
    emp
    ) ** (
    ALL (l : (@list Z)) (x : Z) (l0 : (@list Z)),
      TT &&
      ([| (l = (@cons Z x l0)) |]) &&
      emp **
      ((sll p (@cons Z x l0))) -*
      TT &&
      emp **
      ((sll p l))
      ).

Module Type sll_Strategy_Correct.

  Axiom sll_strategy3_correctness : sll_strategy3.
  Axiom sll_strategy4_correctness : sll_strategy4.
  Axiom sll_strategy5_correctness : sll_strategy5.
  Axiom sll_strategy6_correctness : sll_strategy6.
  Axiom sll_strategy20_correctness : sll_strategy20.
  Axiom sll_strategy7_correctness : sll_strategy7.
  Axiom sll_strategy10_correctness : sll_strategy10.
  Axiom sll_strategy11_correctness : sll_strategy11.
  Axiom sll_strategy8_correctness : sll_strategy8.
  Axiom sll_strategy9_correctness : sll_strategy9.

End sll_Strategy_Correct.
