Require Import char_array_strategy_goal char_array_strategy_proof.

Module char_array_Strategy_Correctness : char_array_Strategy_Correct.
  Include char_array_strategy_proof.
End char_array_Strategy_Correctness.
