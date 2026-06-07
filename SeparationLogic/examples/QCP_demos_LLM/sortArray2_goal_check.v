From SimpleC.EE.QCP_demos_LLM Require Import sortArray2_goal sortArray2_proof_auto sortArray2_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sortArray2_proof_auto.
  Include sortArray2_proof_manual.
End VC_Correctness.
