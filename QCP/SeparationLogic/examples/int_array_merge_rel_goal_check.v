Require Import int_array_merge_rel_goal int_array_merge_rel_proof_auto int_array_merge_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_merge_rel_proof_auto.
  Include int_array_merge_rel_proof_manual.
End VC_Correctness.
