Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import fieldtest_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition fieldtest_strategy1 :=
  forall (x : Z) (p : IntPair) (y : Z),
    TT &&
    emp **
    ((IntPairSep x y p))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int x (@a p 1))) **
    ((poly_store FET_int y (@b p 1)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition fieldtest_strategy2 :=
  forall (x : Z) (p : IntPair),
    TT &&
    emp **
    ((IntPairSep2 x p))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int x (@a p 1))) **
    ((poly_store FET_int  &("z")  (@b p 1)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition fieldtest_strategy3 :=
  forall (x : Z) (p : Pair0),
    TT &&
    emp **
    ((IntPairSep4 x p))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int x (@a2 p))) **
    ((poly_store FET_int  &("z")  (@b2 p)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition fieldtest_strategy4 :=
  forall (A : Type) (x : Z) (a0 : A) (b0 : A) (p : (@Pair A)),
    TT &&
    emp **
    ((IntPairSep3 x p a0 b0))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int x (@a1 A p a0))) **
    ((poly_store FET_int  &("z")  (@b1 A p b0)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type fieldtest_Strategy_Correct.

  Axiom fieldtest_strategy1_correctness : fieldtest_strategy1.
  Axiom fieldtest_strategy2_correctness : fieldtest_strategy2.
  Axiom fieldtest_strategy3_correctness : fieldtest_strategy3.
  Axiom fieldtest_strategy4_correctness : fieldtest_strategy4.

End fieldtest_Strategy_Correct.
