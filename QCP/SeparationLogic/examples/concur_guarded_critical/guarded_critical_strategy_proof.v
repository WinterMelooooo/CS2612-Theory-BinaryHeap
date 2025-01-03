Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.concur_guarded_critical Require Import guarded_critical_strategy_goal.
Require Import guarded_critical_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma guarded_critical_strategy1_correctness : guarded_critical_strategy1.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma guarded_critical_strategy2_correctness : guarded_critical_strategy2.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma guarded_critical_strategy3_correctness : guarded_critical_strategy3.
  pre_process_default.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma guarded_critical_strategy4_correctness : guarded_critical_strategy4.
  pre_process_default.
Qed.

Lemma guarded_critical_strategy5_correctness : guarded_critical_strategy5.
  pre_process_default.
Qed.

Lemma guarded_critical_strategy6_correctness : guarded_critical_strategy6.
  pre_process_default.
Qed.
