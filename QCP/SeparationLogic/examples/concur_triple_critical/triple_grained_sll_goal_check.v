From SimpleC.EE.concur_triple_critical Require Import triple_grained_sll_goal triple_grained_sll_proof_auto triple_grained_sll_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sll_strategy_proof.
  Include safeexec_strategy_proof.
  Include triple_critical_strategy_proof.
  Include triple_grained_sll_proof_auto.
  Include triple_grained_sll_proof_manual.
End VC_Correctness.
