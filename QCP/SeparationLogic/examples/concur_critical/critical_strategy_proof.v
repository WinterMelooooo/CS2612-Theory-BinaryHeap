Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.concur_critical Require Import critical_strategy_goal.
Require Import critical_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma critical_strategy1_correctness : critical_strategy1.
Proof. pre_process. Intros. subst. entailer!. Qed.

Lemma critical_strategy2_correctness : critical_strategy2.
Proof. pre_process. Qed.

Lemma critical_strategy3_correctness : critical_strategy3.
Proof. pre_process. Intros. subst. entailer!. Qed.

Lemma critical_strategy4_correctness : critical_strategy4.
Proof. pre_process. Qed.
