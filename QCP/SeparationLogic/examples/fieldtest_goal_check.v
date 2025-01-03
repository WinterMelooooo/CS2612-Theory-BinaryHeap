From SimpleC.EE Require Import fieldtest_goal fieldtest_proof_auto fieldtest_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include fieldtest_strategy_proof.
  Include fieldtest_proof_auto.
  Include fieldtest_proof_manual.
End VC_Correctness.
