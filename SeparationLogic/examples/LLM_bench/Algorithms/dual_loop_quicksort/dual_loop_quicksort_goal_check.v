From SimpleC.EE.LLM_bench.Algorithms.dual_loop_quicksort Require Import dual_loop_quicksort_goal dual_loop_quicksort_proof_auto dual_loop_quicksort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include dual_loop_quicksort_proof_auto.
  Include dual_loop_quicksort_proof_manual.
End VC_Correctness.
