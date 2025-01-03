Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.concur_nested_critical Require Import nested_critical_strategy_goal.
Require Import nested_critical_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma nested_critical_strategy1_correctness : nested_critical_strategy1.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma nested_critical_strategy3_correctness : nested_critical_strategy3.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma nested_critical_strategy4_correctness : nested_critical_strategy4.
  pre_process_default.
Qed.
