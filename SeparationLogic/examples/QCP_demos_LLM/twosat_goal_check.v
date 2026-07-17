From SimpleC.EE.QCP_demos_LLM Require Import twosat_goal twosat_proof_auto twosat_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexecE_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include twosat_proof_auto.
  Include twosat_proof_manual.
End VC_Correctness.
