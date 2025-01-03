From SimpleC.EE.concur_fine_grained Require Import fine_grained_sll_goal fine_grained_sll_proof_auto fine_grained_sll_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sll_strategy_proof.
  Include safeexec_strategy_proof.
  Include critical_strategy_proof.
  Include fine_grained_sll_proof_auto.
  Include fine_grained_sll_proof_manual.
End VC_Correctness.
