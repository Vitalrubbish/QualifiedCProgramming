From SimpleC.EE.QCP_demos_LLM Require Import kosaraju_rel_goal kosaraju_rel_proof_auto kosaraju_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include kosaraju_rel_proof_auto.
  Include kosaraju_rel_proof_manual.
End VC_Correctness.
