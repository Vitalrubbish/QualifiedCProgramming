From SimpleC.EE.QCP_demos_LLM Require Import sortArray3_goal sortArray3_proof_auto sortArray3_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sortArray3_proof_auto.
  Include sortArray3_proof_manual.
End VC_Correctness.
