From SimpleC.EE.concur_guarded_critical Require Import gconcur_sll_goal gconcur_sll_proof_auto gconcur_sll_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sll_strategy_proof.
  Include safeexec_strategy_proof.
  Include guarded_critical_strategy_proof.
  Include gconcur_sll_proof_auto.
  Include gconcur_sll_proof_manual.
End VC_Correctness.
