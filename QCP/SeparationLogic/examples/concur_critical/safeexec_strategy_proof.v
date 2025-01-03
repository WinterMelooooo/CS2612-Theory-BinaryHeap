Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.concur_critical Require Import safeexec_strategy_goal.
From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Require Import critical_sll_lib.
Import sll_C_Rules.
Local Open Scope stmonad.
Require Import critical_sll_lib.
Import sll_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma safeexec_strategy5_correctness : safeexec_strategy5.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma safeexec_strategy1_correctness : safeexec_strategy1.
  pre_process_default.
Qed.

Lemma safeexec_strategy2_correctness : safeexec_strategy2.
  pre_process_default.
  Intros; subst; entailer!.
Qed.
