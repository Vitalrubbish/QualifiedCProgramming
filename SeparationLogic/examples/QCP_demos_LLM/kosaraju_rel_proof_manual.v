Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import kosaraju_rel_goal.
From SimpleC.EE.QCP_demos_LLM Require Import kosaraju_rel_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Require Import SimpleC.EE.QCP_demos_LLM.SllPtrArrayLib.
Require Import SimpleC.EE.QCP_demos_LLM.kosaraju_rel_lib.
Local Open Scope sac.

Lemma proof_of_kosaraju_get_visited1_return_wit_1_split_goal_1 : kosaraju_get_visited1_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_get_visited1_return_wit_1 : kosaraju_get_visited1_return_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_safety_wit_6_split_goal_1 : dfs1_safety_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs1_safety_wit_6_split_goal_2 : dfs1_safety_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs1_safety_wit_6 : dfs1_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_1 : dfs1_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_2_split_goal_1 : dfs1_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_2_split_goal_2 : dfs1_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_2_split_goal_spatial : dfs1_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_2 : dfs1_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_3_split_goal_1 : dfs1_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_2 : dfs1_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_3 : dfs1_entail_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_4 : dfs1_entail_wit_3_split_goal_4.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_5 : dfs1_entail_wit_3_split_goal_5.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_6 : dfs1_entail_wit_3_split_goal_6.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_7 : dfs1_entail_wit_3_split_goal_7.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_8 : dfs1_entail_wit_3_split_goal_8.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_9 : dfs1_entail_wit_3_split_goal_9.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_10 : dfs1_entail_wit_3_split_goal_10.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_11 : dfs1_entail_wit_3_split_goal_11.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_12 : dfs1_entail_wit_3_split_goal_12.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3_split_goal_spatial : dfs1_entail_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_3 : dfs1_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_4_1 : dfs1_entail_wit_4_1.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_4_2 : dfs1_entail_wit_4_2.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_5 : dfs1_entail_wit_5.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_6 : dfs1_entail_wit_6.
Proof. Admitted. 

Lemma proof_of_dfs1_return_wit_1 : dfs1_return_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_1 : dfs2_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_2_split_goal_1 : dfs2_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_2_split_goal_2 : dfs2_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_2_split_goal_spatial : dfs2_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_2 : dfs2_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_3_split_goal_1 : dfs2_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_2 : dfs2_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_3 : dfs2_entail_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_4 : dfs2_entail_wit_3_split_goal_4.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_5 : dfs2_entail_wit_3_split_goal_5.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_6 : dfs2_entail_wit_3_split_goal_6.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_7 : dfs2_entail_wit_3_split_goal_7.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_8 : dfs2_entail_wit_3_split_goal_8.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_9 : dfs2_entail_wit_3_split_goal_9.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_10 : dfs2_entail_wit_3_split_goal_10.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_11 : dfs2_entail_wit_3_split_goal_11.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_12 : dfs2_entail_wit_3_split_goal_12.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_13 : dfs2_entail_wit_3_split_goal_13.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_14 : dfs2_entail_wit_3_split_goal_14.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_split_goal_spatial : dfs2_entail_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3 : dfs2_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_4_1 : dfs2_entail_wit_4_1.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_4_2 : dfs2_entail_wit_4_2.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_5 : dfs2_entail_wit_5.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_6_split_goal_1 : dfs2_entail_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_6_split_goal_spatial : dfs2_entail_wit_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_6 : dfs2_entail_wit_6.
Proof. Admitted. 

Lemma proof_of_dfs2_return_wit_1_split_goal_spatial : dfs2_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_dfs2_return_wit_1 : dfs2_return_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_entail_wit_1 : kosaraju_finish_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_entail_wit_2_split_goal_1 : kosaraju_finish_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_finish_entail_wit_2_split_goal_2 : kosaraju_finish_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_finish_entail_wit_2 : kosaraju_finish_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_entail_wit_3_1 : kosaraju_finish_entail_wit_3_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_entail_wit_3_2 : kosaraju_finish_entail_wit_3_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_return_wit_1 : kosaraju_finish_return_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_safety_wit_5_split_goal_1 : kosaraju_scc_safety_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_scc_safety_wit_5_split_goal_2 : kosaraju_scc_safety_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_scc_safety_wit_5 : kosaraju_scc_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_entail_wit_1 : kosaraju_scc_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_entail_wit_2_split_goal_1 : kosaraju_scc_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_scc_entail_wit_2_split_goal_2 : kosaraju_scc_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_scc_entail_wit_2_split_goal_3 : kosaraju_scc_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_kosaraju_scc_entail_wit_2 : kosaraju_scc_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_entail_wit_3_split_goal_1 : kosaraju_scc_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_scc_entail_wit_3 : kosaraju_scc_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_entail_wit_4_1 : kosaraju_scc_entail_wit_4_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_entail_wit_4_2 : kosaraju_scc_entail_wit_4_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_return_wit_1 : kosaraju_scc_return_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_partial_solve_wit_7_pure_split_goal_1 : kosaraju_scc_partial_solve_wit_7_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_scc_partial_solve_wit_7_pure_split_goal_2 : kosaraju_scc_partial_solve_wit_7_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_scc_partial_solve_wit_7_pure : kosaraju_scc_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_kosaraju_run_return_wit_1 : kosaraju_run_return_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_run_partial_solve_wit_1_pure_split_goal_1 : kosaraju_run_partial_solve_wit_1_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_run_partial_solve_wit_1_pure : kosaraju_run_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_kosaraju_run_partial_solve_wit_2_pure_split_goal_1 : kosaraju_run_partial_solve_wit_2_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_run_partial_solve_wit_2_pure_split_goal_2 : kosaraju_run_partial_solve_wit_2_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_run_partial_solve_wit_2_pure : kosaraju_run_partial_solve_wit_2_pure.
Proof. Admitted. 

