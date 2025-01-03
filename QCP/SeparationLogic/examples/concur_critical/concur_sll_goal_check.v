From SimpleC.EE.concur_critical Require Import concur_sll_goal concur_sll_proof_auto concur_sll_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sll_strategy_proof.
  Include safeexec_strategy_proof.
  Include critical_strategy_proof.
  Include concur_sll_proof_auto.
  Include concur_sll_proof_manual.
End VC_Correctness.
