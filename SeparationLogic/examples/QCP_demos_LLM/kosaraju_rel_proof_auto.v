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

Lemma proof_of_kosaraju_num_vertices_return_wit_1 : kosaraju_num_vertices_return_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_get_visited1_partial_solve_wit_1 : kosaraju_get_visited1_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_safety_wit_1 : dfs1_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_safety_wit_2 : dfs1_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs1_safety_wit_3 : dfs1_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_dfs1_safety_wit_4 : dfs1_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_dfs1_safety_wit_5 : dfs1_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_dfs1_safety_wit_7 : dfs1_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_1 : dfs1_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_2 : dfs1_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_3 : dfs1_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_4_pure : dfs1_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_4 : dfs1_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_5 : dfs1_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_6 : dfs1_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_7 : dfs1_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_dfs2_safety_wit_1 : dfs2_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs2_safety_wit_2 : dfs2_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs2_safety_wit_3 : dfs2_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_1 : dfs2_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_2 : dfs2_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_3 : dfs2_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_4 : dfs2_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_5 : dfs2_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_6_pure : dfs2_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_6 : dfs2_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_safety_wit_1 : kosaraju_finish_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_safety_wit_2 : kosaraju_finish_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_safety_wit_3 : kosaraju_finish_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_safety_wit_4 : kosaraju_finish_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_partial_solve_wit_1 : kosaraju_finish_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_partial_solve_wit_2_pure : kosaraju_finish_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_kosaraju_finish_partial_solve_wit_2 : kosaraju_finish_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_safety_wit_1 : kosaraju_scc_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_safety_wit_2 : kosaraju_scc_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_safety_wit_3 : kosaraju_scc_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_safety_wit_4 : kosaraju_scc_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_safety_wit_6 : kosaraju_scc_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_safety_wit_7 : kosaraju_scc_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_safety_wit_8 : kosaraju_scc_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_safety_wit_9 : kosaraju_scc_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_partial_solve_wit_1 : kosaraju_scc_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_partial_solve_wit_2 : kosaraju_scc_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_partial_solve_wit_3 : kosaraju_scc_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_partial_solve_wit_4 : kosaraju_scc_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_partial_solve_wit_5 : kosaraju_scc_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_partial_solve_wit_6 : kosaraju_scc_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_kosaraju_scc_partial_solve_wit_7 : kosaraju_scc_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_kosaraju_run_partial_solve_wit_1 : kosaraju_run_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_run_partial_solve_wit_2 : kosaraju_run_partial_solve_wit_2.
Proof. Admitted. 

