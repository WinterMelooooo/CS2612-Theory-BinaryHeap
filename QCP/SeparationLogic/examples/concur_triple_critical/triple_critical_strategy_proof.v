Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.concur_triple_critical Require Import triple_critical_strategy_goal.
Require Import triple_critical_sll_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma triple_critical_strategy1_correctness : triple_critical_strategy1.
  pre_process_default.
  Intros.
  subst. entailer!.
Qed.

Lemma triple_critical_strategy2_correctness : triple_critical_strategy2.
  pre_process_default.
  Intros. subst. entailer!.
Qed.

Lemma triple_critical_strategy3_correctness : triple_critical_strategy3.
  pre_process_default.
  Intros. subst. entailer!.
Qed.

Lemma triple_critical_strategy4_correctness : triple_critical_strategy4.
  pre_process_default.
Qed.

Lemma triple_critical_strategy5_correctness : triple_critical_strategy5.
  pre_process_default.
Qed.

Lemma triple_critical_strategy6_correctness : triple_critical_strategy6.
  pre_process_default.
Qed.
