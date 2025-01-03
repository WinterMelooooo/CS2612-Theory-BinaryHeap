Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE Require Import fieldtest_strategy_goal.
Import naive_C_Rules.
Require Import fieldtest_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma fieldtest_strategy1_correctness : fieldtest_strategy1.
  pre_process_default.
Qed.

Lemma fieldtest_strategy2_correctness : fieldtest_strategy2.
  pre_process_default.
Qed.

Lemma fieldtest_strategy3_correctness : fieldtest_strategy3.
  pre_process_default.
Qed.

Lemma fieldtest_strategy4_correctness : fieldtest_strategy4.
  pre_process_default.
Qed.