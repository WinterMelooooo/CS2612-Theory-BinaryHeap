Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.concur_fine_grained Require Import critical_strategy_goal.
Require Import fine_grained_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma critical_strategy1_correctness : critical_strategy1.
  pre_process_default.
  Intros.
  subst.
  entailer!.
Qed.

Lemma critical_strategy2_correctness : critical_strategy2.
  pre_process_default.
Qed.

Lemma critical_strategy3_correctness : critical_strategy3.
  pre_process_default.
  Intros.
  subst.
  entailer!.
Qed.

Lemma critical_strategy4_correctness : critical_strategy4.
  pre_process_default.
Qed.

Lemma critical_strategy10_correctness : critical_strategy10.
  pre_process_default.
  Intros.
  subst.
  entailer!.
Qed.
