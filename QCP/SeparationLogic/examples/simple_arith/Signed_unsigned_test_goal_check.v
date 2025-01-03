From SimpleC.EE.simple_arith Require Import Signed_unsigned_test_goal Signed_unsigned_test_proof_auto Signed_unsigned_test_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include Signed_unsigned_test_proof_auto.
  Include Signed_unsigned_test_proof_manual.
End VC_Correctness.
