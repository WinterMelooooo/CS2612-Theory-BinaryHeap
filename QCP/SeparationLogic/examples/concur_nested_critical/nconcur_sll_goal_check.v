From SimpleC.EE.concur_nested_critical Require Import nconcur_sll_goal nconcur_sll_proof_auto nconcur_sll_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sll_strategy_proof.
  Include safeexec_strategy_proof.
  Include nested_critical_strategy_proof.
  Include nconcur_sll_proof_auto.
  Include nconcur_sll_proof_manual.
End VC_Correctness.
