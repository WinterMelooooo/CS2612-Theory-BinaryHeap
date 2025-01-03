From SimpleC.EE Require Import global_vars_goal global_vars_proof_auto global_vars_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include sll_strategy_proof.
  Include global_vars_proof_auto.
  Include global_vars_proof_manual.
End VC_Correctness.
