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
From SimpleC.EE.QCP_demos_LLM Require Import twosat_goal.
From SimpleC.EE.QCP_demos_LLM Require Import twosat_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_LLM.kosaraju_rel_lib.
Require Import SimpleC.EE.QCP_demos_LLM.twosat_lib.
Local Open Scope sac.

Lemma proof_of_dfs1_safety_wit_11_split_goal_1 : dfs1_safety_wit_11_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs1_safety_wit_11_split_goal_2 : dfs1_safety_wit_11_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs1_safety_wit_11 : dfs1_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_1 : dfs1_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_2_split_goal_1 : dfs1_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_2_split_goal_2 : dfs1_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_2_split_goal_3 : dfs1_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_dfs1_entail_wit_2 : dfs1_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_3_1 : dfs1_entail_wit_3_1.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_3_2 : dfs1_entail_wit_3_2.
Proof. Admitted. 

Lemma proof_of_dfs1_return_wit_1 : dfs1_return_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_6_pure_split_goal_1 : dfs1_partial_solve_wit_6_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs1_partial_solve_wit_6_pure_split_goal_2 : dfs1_partial_solve_wit_6_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs1_partial_solve_wit_6_pure : dfs1_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_1_split_goal_1 : dfs2_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_2 : dfs2_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_3 : dfs2_entail_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_4 : dfs2_entail_wit_1_split_goal_4.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_5 : dfs2_entail_wit_1_split_goal_5.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_6 : dfs2_entail_wit_1_split_goal_6.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_7 : dfs2_entail_wit_1_split_goal_7.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_8 : dfs2_entail_wit_1_split_goal_8.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_9 : dfs2_entail_wit_1_split_goal_9.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_10 : dfs2_entail_wit_1_split_goal_10.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_11 : dfs2_entail_wit_1_split_goal_11.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_12 : dfs2_entail_wit_1_split_goal_12.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1 : dfs2_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_2_split_goal_1 : dfs2_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_2_split_goal_2 : dfs2_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_2_split_goal_3 : dfs2_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_2 : dfs2_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_1 : dfs2_entail_wit_3_1_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_2 : dfs2_entail_wit_3_1_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_3 : dfs2_entail_wit_3_1_split_goal_3.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_4 : dfs2_entail_wit_3_1_split_goal_4.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_5 : dfs2_entail_wit_3_1_split_goal_5.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_1 : dfs2_entail_wit_3_1.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_1 : dfs2_entail_wit_3_2_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_2 : dfs2_entail_wit_3_2_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_2 : dfs2_entail_wit_3_2.
Proof. Admitted. 

Lemma proof_of_dfs2_return_wit_1_split_goal_1 : dfs2_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_return_wit_1_split_goal_2 : dfs2_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_dfs2_return_wit_1 : dfs2_return_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_8_pure_split_goal_1 : dfs2_partial_solve_wit_8_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_partial_solve_wit_8_pure : dfs2_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_lit_vertex_safety_wit_3_split_goal_1 : lit_vertex_safety_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_lit_vertex_safety_wit_3_split_goal_2 : lit_vertex_safety_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_lit_vertex_safety_wit_3 : lit_vertex_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_lit_vertex_safety_wit_4_split_goal_1 : lit_vertex_safety_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_lit_vertex_safety_wit_4_split_goal_2 : lit_vertex_safety_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_lit_vertex_safety_wit_4 : lit_vertex_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_lit_vertex_safety_wit_5_split_goal_1 : lit_vertex_safety_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_lit_vertex_safety_wit_5_split_goal_2 : lit_vertex_safety_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_lit_vertex_safety_wit_5 : lit_vertex_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_lit_vertex_safety_wit_6_split_goal_1 : lit_vertex_safety_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_lit_vertex_safety_wit_6_split_goal_2 : lit_vertex_safety_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_lit_vertex_safety_wit_6 : lit_vertex_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_neg_vertex_return_wit_1_split_goal_1 : neg_vertex_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_neg_vertex_return_wit_1 : neg_vertex_return_wit_1.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_17_split_goal_1 : main_safety_wit_17_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_17_split_goal_2 : main_safety_wit_17_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_17 : main_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_25_split_goal_1 : main_safety_wit_25_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_25_split_goal_2 : main_safety_wit_25_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_25 : main_safety_wit_25.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_26_split_goal_1 : main_safety_wit_26_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_26_split_goal_2 : main_safety_wit_26_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_26 : main_safety_wit_26.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_30_split_goal_1 : main_safety_wit_30_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_30_split_goal_2 : main_safety_wit_30_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_30 : main_safety_wit_30.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_31_split_goal_1 : main_safety_wit_31_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_31_split_goal_2 : main_safety_wit_31_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_31 : main_safety_wit_31.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_35_split_goal_1 : main_safety_wit_35_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_35_split_goal_2 : main_safety_wit_35_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_35 : main_safety_wit_35.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_36_split_goal_1 : main_safety_wit_36_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_36_split_goal_2 : main_safety_wit_36_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_36 : main_safety_wit_36.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_40_split_goal_1 : main_safety_wit_40_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_40_split_goal_2 : main_safety_wit_40_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_40 : main_safety_wit_40.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_41_split_goal_1 : main_safety_wit_41_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_41_split_goal_2 : main_safety_wit_41_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_41 : main_safety_wit_41.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_45_split_goal_1 : main_safety_wit_45_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_45_split_goal_2 : main_safety_wit_45_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_45 : main_safety_wit_45.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_46_split_goal_1 : main_safety_wit_46_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_46_split_goal_2 : main_safety_wit_46_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_46 : main_safety_wit_46.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_50_split_goal_1 : main_safety_wit_50_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_50_split_goal_2 : main_safety_wit_50_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_50 : main_safety_wit_50.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_51_split_goal_1 : main_safety_wit_51_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_51_split_goal_2 : main_safety_wit_51_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_51 : main_safety_wit_51.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_56_split_goal_1 : main_safety_wit_56_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_56_split_goal_2 : main_safety_wit_56_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_56 : main_safety_wit_56.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_62_split_goal_1 : main_safety_wit_62_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_62_split_goal_2 : main_safety_wit_62_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_62 : main_safety_wit_62.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_69_split_goal_1 : main_safety_wit_69_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_69_split_goal_2 : main_safety_wit_69_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_69 : main_safety_wit_69.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_70_split_goal_1 : main_safety_wit_70_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_70_split_goal_2 : main_safety_wit_70_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_70 : main_safety_wit_70.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_76_split_goal_1 : main_safety_wit_76_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_76_split_goal_2 : main_safety_wit_76_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_76 : main_safety_wit_76.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_77_split_goal_1 : main_safety_wit_77_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_77_split_goal_2 : main_safety_wit_77_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_77 : main_safety_wit_77.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_82_split_goal_1 : main_safety_wit_82_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_82_split_goal_2 : main_safety_wit_82_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_82 : main_safety_wit_82.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_89_split_goal_1 : main_safety_wit_89_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_89_split_goal_2 : main_safety_wit_89_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_89 : main_safety_wit_89.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_90_split_goal_1 : main_safety_wit_90_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_90_split_goal_2 : main_safety_wit_90_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_90 : main_safety_wit_90.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_95_split_goal_1 : main_safety_wit_95_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_95_split_goal_2 : main_safety_wit_95_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_95 : main_safety_wit_95.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_102_split_goal_1 : main_safety_wit_102_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_102_split_goal_2 : main_safety_wit_102_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_102 : main_safety_wit_102.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_103_split_goal_1 : main_safety_wit_103_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_103_split_goal_2 : main_safety_wit_103_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_103 : main_safety_wit_103.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_109_split_goal_1 : main_safety_wit_109_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_109_split_goal_2 : main_safety_wit_109_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_109 : main_safety_wit_109.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_113_split_goal_1 : main_safety_wit_113_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_113_split_goal_2 : main_safety_wit_113_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_113 : main_safety_wit_113.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_117_split_goal_1 : main_safety_wit_117_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_117_split_goal_2 : main_safety_wit_117_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_117 : main_safety_wit_117.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_121_split_goal_1 : main_safety_wit_121_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_121_split_goal_2 : main_safety_wit_121_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_121 : main_safety_wit_121.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_127_split_goal_1 : main_safety_wit_127_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_127_split_goal_2 : main_safety_wit_127_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_127 : main_safety_wit_127.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_130_split_goal_1 : main_safety_wit_130_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_130_split_goal_2 : main_safety_wit_130_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_130 : main_safety_wit_130.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_133_split_goal_1 : main_safety_wit_133_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_133_split_goal_2 : main_safety_wit_133_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_133 : main_safety_wit_133.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_135_split_goal_1 : main_safety_wit_135_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_135_split_goal_2 : main_safety_wit_135_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_135 : main_safety_wit_135.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_136_split_goal_1 : main_safety_wit_136_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_136_split_goal_2 : main_safety_wit_136_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_136 : main_safety_wit_136.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_140_split_goal_1 : main_safety_wit_140_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_140_split_goal_2 : main_safety_wit_140_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_140 : main_safety_wit_140.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_141_split_goal_1 : main_safety_wit_141_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_141_split_goal_2 : main_safety_wit_141_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_141 : main_safety_wit_141.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_145_split_goal_1 : main_safety_wit_145_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_145_split_goal_2 : main_safety_wit_145_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_145 : main_safety_wit_145.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_146_split_goal_1 : main_safety_wit_146_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_146_split_goal_2 : main_safety_wit_146_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_146 : main_safety_wit_146.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_150_split_goal_1 : main_safety_wit_150_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_150_split_goal_2 : main_safety_wit_150_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_150 : main_safety_wit_150.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_151_split_goal_1 : main_safety_wit_151_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_151_split_goal_2 : main_safety_wit_151_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_151 : main_safety_wit_151.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_155_split_goal_1 : main_safety_wit_155_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_155_split_goal_2 : main_safety_wit_155_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_155 : main_safety_wit_155.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_156_split_goal_1 : main_safety_wit_156_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_156_split_goal_2 : main_safety_wit_156_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_156 : main_safety_wit_156.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_160_split_goal_1 : main_safety_wit_160_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_160_split_goal_2 : main_safety_wit_160_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_160 : main_safety_wit_160.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_161_split_goal_1 : main_safety_wit_161_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_161_split_goal_2 : main_safety_wit_161_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_161 : main_safety_wit_161.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_166_split_goal_1 : main_safety_wit_166_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_166_split_goal_2 : main_safety_wit_166_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_166 : main_safety_wit_166.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_172_split_goal_1 : main_safety_wit_172_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_172_split_goal_2 : main_safety_wit_172_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_172 : main_safety_wit_172.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_179_split_goal_1 : main_safety_wit_179_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_179_split_goal_2 : main_safety_wit_179_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_179 : main_safety_wit_179.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_180_split_goal_1 : main_safety_wit_180_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_180_split_goal_2 : main_safety_wit_180_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_180 : main_safety_wit_180.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_186_split_goal_1 : main_safety_wit_186_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_186_split_goal_2 : main_safety_wit_186_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_186 : main_safety_wit_186.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_187_split_goal_1 : main_safety_wit_187_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_187_split_goal_2 : main_safety_wit_187_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_187 : main_safety_wit_187.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_192_split_goal_1 : main_safety_wit_192_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_192_split_goal_2 : main_safety_wit_192_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_192 : main_safety_wit_192.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_199_split_goal_1 : main_safety_wit_199_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_199_split_goal_2 : main_safety_wit_199_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_199 : main_safety_wit_199.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_200_split_goal_1 : main_safety_wit_200_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_200_split_goal_2 : main_safety_wit_200_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_200 : main_safety_wit_200.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_205_split_goal_1 : main_safety_wit_205_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_205_split_goal_2 : main_safety_wit_205_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_205 : main_safety_wit_205.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_212_split_goal_1 : main_safety_wit_212_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_212_split_goal_2 : main_safety_wit_212_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_212 : main_safety_wit_212.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_213_split_goal_1 : main_safety_wit_213_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_213_split_goal_2 : main_safety_wit_213_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_213 : main_safety_wit_213.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_217_split_goal_1 : main_safety_wit_217_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_217_split_goal_2 : main_safety_wit_217_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_217 : main_safety_wit_217.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_218_split_goal_1 : main_safety_wit_218_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_218_split_goal_2 : main_safety_wit_218_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_218 : main_safety_wit_218.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_221_split_goal_1 : main_safety_wit_221_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_221_split_goal_2 : main_safety_wit_221_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_221 : main_safety_wit_221.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_222_split_goal_1 : main_safety_wit_222_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_222_split_goal_2 : main_safety_wit_222_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_222 : main_safety_wit_222.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_225_split_goal_1 : main_safety_wit_225_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_225_split_goal_2 : main_safety_wit_225_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_225 : main_safety_wit_225.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_226_split_goal_1 : main_safety_wit_226_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_226_split_goal_2 : main_safety_wit_226_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_226 : main_safety_wit_226.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_2_split_goal_1 : main_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_2_split_goal_2 : main_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_2 : main_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_3_split_goal_1 : main_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_3_split_goal_2 : main_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_3_split_goal_3 : main_entail_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_3 : main_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_4_split_goal_1 : main_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_4_split_goal_2 : main_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_4_split_goal_3 : main_entail_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_4_split_goal_4 : main_entail_wit_4_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_4 : main_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_5_split_goal_1 : main_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_5_split_goal_2 : main_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_5_split_goal_3 : main_entail_wit_5_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_5_split_goal_4 : main_entail_wit_5_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_5 : main_entail_wit_5.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_6_1_split_goal_1 : main_entail_wit_6_1_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_2 : main_entail_wit_6_1_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_3 : main_entail_wit_6_1_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_4 : main_entail_wit_6_1_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_5 : main_entail_wit_6_1_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_6 : main_entail_wit_6_1_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_7 : main_entail_wit_6_1_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_8 : main_entail_wit_6_1_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_9 : main_entail_wit_6_1_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_10 : main_entail_wit_6_1_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_11 : main_entail_wit_6_1_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_12 : main_entail_wit_6_1_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_13 : main_entail_wit_6_1_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1_split_goal_14 : main_entail_wit_6_1_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_1 : main_entail_wit_6_1.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_6_2_split_goal_1 : main_entail_wit_6_2_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_2 : main_entail_wit_6_2_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_3 : main_entail_wit_6_2_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_4 : main_entail_wit_6_2_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_5 : main_entail_wit_6_2_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_6 : main_entail_wit_6_2_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_7 : main_entail_wit_6_2_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_8 : main_entail_wit_6_2_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_9 : main_entail_wit_6_2_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_10 : main_entail_wit_6_2_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2_split_goal_11 : main_entail_wit_6_2_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_2 : main_entail_wit_6_2.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_6_3_split_goal_1 : main_entail_wit_6_3_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_2 : main_entail_wit_6_3_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_3 : main_entail_wit_6_3_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_4 : main_entail_wit_6_3_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_5 : main_entail_wit_6_3_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_6 : main_entail_wit_6_3_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_7 : main_entail_wit_6_3_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_8 : main_entail_wit_6_3_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_9 : main_entail_wit_6_3_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_10 : main_entail_wit_6_3_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3_split_goal_11 : main_entail_wit_6_3_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_3 : main_entail_wit_6_3.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_6_4_split_goal_1 : main_entail_wit_6_4_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_4_split_goal_2 : main_entail_wit_6_4_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_4_split_goal_3 : main_entail_wit_6_4_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_4_split_goal_4 : main_entail_wit_6_4_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_4_split_goal_5 : main_entail_wit_6_4_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_4_split_goal_6 : main_entail_wit_6_4_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_4_split_goal_7 : main_entail_wit_6_4_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_4_split_goal_8 : main_entail_wit_6_4_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_6_4 : main_entail_wit_6_4.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_7_split_goal_1 : main_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_7 : main_entail_wit_7.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_8_split_goal_1 : main_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_8 : main_entail_wit_8.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_9_split_goal_1 : main_entail_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_9_split_goal_2 : main_entail_wit_9_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_9 : main_entail_wit_9.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_10_split_goal_1 : main_entail_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_10 : main_entail_wit_10.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_11_split_goal_1 : main_entail_wit_11_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_11 : main_entail_wit_11.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_12_split_goal_1 : main_entail_wit_12_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_12_split_goal_2 : main_entail_wit_12_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_12 : main_entail_wit_12.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_13_split_goal_1 : main_entail_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_2 : main_entail_wit_13_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_3 : main_entail_wit_13_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_4 : main_entail_wit_13_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_5 : main_entail_wit_13_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_6 : main_entail_wit_13_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_7 : main_entail_wit_13_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_8 : main_entail_wit_13_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_9 : main_entail_wit_13_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_10 : main_entail_wit_13_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_11 : main_entail_wit_13_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_12 : main_entail_wit_13_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_13 : main_entail_wit_13_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_14 : main_entail_wit_13_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_13_split_goal_15 : main_entail_wit_13_split_goal_15.
Proof. Abort.

Lemma proof_of_main_entail_wit_13 : main_entail_wit_13.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_14_1_split_goal_1 : main_entail_wit_14_1_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_2 : main_entail_wit_14_1_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_3 : main_entail_wit_14_1_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_4 : main_entail_wit_14_1_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_5 : main_entail_wit_14_1_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_6 : main_entail_wit_14_1_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_7 : main_entail_wit_14_1_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_8 : main_entail_wit_14_1_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_9 : main_entail_wit_14_1_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_10 : main_entail_wit_14_1_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_11 : main_entail_wit_14_1_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_12 : main_entail_wit_14_1_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_13 : main_entail_wit_14_1_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_14 : main_entail_wit_14_1_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_15 : main_entail_wit_14_1_split_goal_15.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_16 : main_entail_wit_14_1_split_goal_16.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_17 : main_entail_wit_14_1_split_goal_17.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_18 : main_entail_wit_14_1_split_goal_18.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_19 : main_entail_wit_14_1_split_goal_19.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_20 : main_entail_wit_14_1_split_goal_20.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_21 : main_entail_wit_14_1_split_goal_21.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_22 : main_entail_wit_14_1_split_goal_22.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_23 : main_entail_wit_14_1_split_goal_23.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_24 : main_entail_wit_14_1_split_goal_24.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_25 : main_entail_wit_14_1_split_goal_25.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_26 : main_entail_wit_14_1_split_goal_26.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_27 : main_entail_wit_14_1_split_goal_27.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1_split_goal_28 : main_entail_wit_14_1_split_goal_28.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_1 : main_entail_wit_14_1.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_14_2_split_goal_1 : main_entail_wit_14_2_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_2 : main_entail_wit_14_2_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_3 : main_entail_wit_14_2_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_4 : main_entail_wit_14_2_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_5 : main_entail_wit_14_2_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_6 : main_entail_wit_14_2_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_7 : main_entail_wit_14_2_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_8 : main_entail_wit_14_2_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_9 : main_entail_wit_14_2_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_10 : main_entail_wit_14_2_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_11 : main_entail_wit_14_2_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_12 : main_entail_wit_14_2_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_13 : main_entail_wit_14_2_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_14 : main_entail_wit_14_2_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_15 : main_entail_wit_14_2_split_goal_15.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_16 : main_entail_wit_14_2_split_goal_16.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_17 : main_entail_wit_14_2_split_goal_17.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_18 : main_entail_wit_14_2_split_goal_18.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_19 : main_entail_wit_14_2_split_goal_19.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_20 : main_entail_wit_14_2_split_goal_20.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_21 : main_entail_wit_14_2_split_goal_21.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_22 : main_entail_wit_14_2_split_goal_22.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_23 : main_entail_wit_14_2_split_goal_23.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_24 : main_entail_wit_14_2_split_goal_24.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2_split_goal_25 : main_entail_wit_14_2_split_goal_25.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_2 : main_entail_wit_14_2.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_14_3_split_goal_1 : main_entail_wit_14_3_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_2 : main_entail_wit_14_3_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_3 : main_entail_wit_14_3_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_4 : main_entail_wit_14_3_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_5 : main_entail_wit_14_3_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_6 : main_entail_wit_14_3_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_7 : main_entail_wit_14_3_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_8 : main_entail_wit_14_3_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_9 : main_entail_wit_14_3_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_10 : main_entail_wit_14_3_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_11 : main_entail_wit_14_3_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_12 : main_entail_wit_14_3_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_13 : main_entail_wit_14_3_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_14 : main_entail_wit_14_3_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_15 : main_entail_wit_14_3_split_goal_15.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_16 : main_entail_wit_14_3_split_goal_16.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_17 : main_entail_wit_14_3_split_goal_17.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_18 : main_entail_wit_14_3_split_goal_18.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_19 : main_entail_wit_14_3_split_goal_19.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_20 : main_entail_wit_14_3_split_goal_20.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_21 : main_entail_wit_14_3_split_goal_21.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_22 : main_entail_wit_14_3_split_goal_22.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_23 : main_entail_wit_14_3_split_goal_23.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_24 : main_entail_wit_14_3_split_goal_24.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3_split_goal_25 : main_entail_wit_14_3_split_goal_25.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_3 : main_entail_wit_14_3.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_14_4_split_goal_1 : main_entail_wit_14_4_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_2 : main_entail_wit_14_4_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_3 : main_entail_wit_14_4_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_4 : main_entail_wit_14_4_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_5 : main_entail_wit_14_4_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_6 : main_entail_wit_14_4_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_7 : main_entail_wit_14_4_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_8 : main_entail_wit_14_4_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_9 : main_entail_wit_14_4_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_10 : main_entail_wit_14_4_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_11 : main_entail_wit_14_4_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_12 : main_entail_wit_14_4_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_13 : main_entail_wit_14_4_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_14 : main_entail_wit_14_4_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_15 : main_entail_wit_14_4_split_goal_15.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_16 : main_entail_wit_14_4_split_goal_16.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_17 : main_entail_wit_14_4_split_goal_17.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_18 : main_entail_wit_14_4_split_goal_18.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_19 : main_entail_wit_14_4_split_goal_19.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_20 : main_entail_wit_14_4_split_goal_20.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_21 : main_entail_wit_14_4_split_goal_21.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4_split_goal_22 : main_entail_wit_14_4_split_goal_22.
Proof. Abort.

Lemma proof_of_main_entail_wit_14_4 : main_entail_wit_14_4.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_15_1_split_goal_1 : main_entail_wit_15_1_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_2 : main_entail_wit_15_1_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_3 : main_entail_wit_15_1_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_4 : main_entail_wit_15_1_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_5 : main_entail_wit_15_1_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_6 : main_entail_wit_15_1_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_7 : main_entail_wit_15_1_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_8 : main_entail_wit_15_1_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_9 : main_entail_wit_15_1_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_10 : main_entail_wit_15_1_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_11 : main_entail_wit_15_1_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_12 : main_entail_wit_15_1_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_13 : main_entail_wit_15_1_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_14 : main_entail_wit_15_1_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_15 : main_entail_wit_15_1_split_goal_15.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_16 : main_entail_wit_15_1_split_goal_16.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1_split_goal_17 : main_entail_wit_15_1_split_goal_17.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_1 : main_entail_wit_15_1.
Proof.
  right; intros; pre_process; entailer!; try assumption; try lia; try congruence.
  all: unfold twosat_processed_prefix in PreH15; tauto.
Qed.

Lemma proof_of_main_entail_wit_15_2_split_goal_1 : main_entail_wit_15_2_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_2 : main_entail_wit_15_2_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_3 : main_entail_wit_15_2_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_4 : main_entail_wit_15_2_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_5 : main_entail_wit_15_2_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_6 : main_entail_wit_15_2_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_7 : main_entail_wit_15_2_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_8 : main_entail_wit_15_2_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_9 : main_entail_wit_15_2_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_10 : main_entail_wit_15_2_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_11 : main_entail_wit_15_2_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_12 : main_entail_wit_15_2_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_13 : main_entail_wit_15_2_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_14 : main_entail_wit_15_2_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_15 : main_entail_wit_15_2_split_goal_15.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_16 : main_entail_wit_15_2_split_goal_16.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2_split_goal_17 : main_entail_wit_15_2_split_goal_17.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_2 : main_entail_wit_15_2.
Proof.
  right; intros; pre_process; entailer!; try assumption; try lia; try congruence.
  all: unfold twosat_processed_prefix in PreH15; tauto.
Qed.

Lemma proof_of_main_entail_wit_15_3_split_goal_1 : main_entail_wit_15_3_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_2 : main_entail_wit_15_3_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_3 : main_entail_wit_15_3_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_4 : main_entail_wit_15_3_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_5 : main_entail_wit_15_3_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_6 : main_entail_wit_15_3_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_7 : main_entail_wit_15_3_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_8 : main_entail_wit_15_3_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_9 : main_entail_wit_15_3_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_10 : main_entail_wit_15_3_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_11 : main_entail_wit_15_3_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_12 : main_entail_wit_15_3_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_13 : main_entail_wit_15_3_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_14 : main_entail_wit_15_3_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_15 : main_entail_wit_15_3_split_goal_15.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_16 : main_entail_wit_15_3_split_goal_16.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3_split_goal_17 : main_entail_wit_15_3_split_goal_17.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_3 : main_entail_wit_15_3.
Proof.
  right; intros; pre_process; entailer!; try assumption; try lia; try congruence.
  all: unfold twosat_processed_prefix in PreH15; tauto.
Qed.

Lemma proof_of_main_entail_wit_15_4_split_goal_1 : main_entail_wit_15_4_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_2 : main_entail_wit_15_4_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_3 : main_entail_wit_15_4_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_4 : main_entail_wit_15_4_split_goal_4.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_5 : main_entail_wit_15_4_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_6 : main_entail_wit_15_4_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_7 : main_entail_wit_15_4_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_8 : main_entail_wit_15_4_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_9 : main_entail_wit_15_4_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_10 : main_entail_wit_15_4_split_goal_10.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_11 : main_entail_wit_15_4_split_goal_11.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_12 : main_entail_wit_15_4_split_goal_12.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_13 : main_entail_wit_15_4_split_goal_13.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_14 : main_entail_wit_15_4_split_goal_14.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_15 : main_entail_wit_15_4_split_goal_15.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_16 : main_entail_wit_15_4_split_goal_16.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4_split_goal_17 : main_entail_wit_15_4_split_goal_17.
Proof. Abort.

Lemma proof_of_main_entail_wit_15_4 : main_entail_wit_15_4.
Proof.
  right; intros; pre_process; entailer!; try assumption; try lia; try congruence.
  all: unfold twosat_processed_prefix in PreH15; tauto.
Qed.

Lemma proof_of_main_entail_wit_16_split_goal_1 : main_entail_wit_16_split_goal_1.
Proof.
  intros; pre_process; entailer!.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    destruct (Z.eq_dec 0 va) as [Hva|Hva].
    + subst va. rewrite Znth_replace_Znth_Same by (try rewrite Zlength_replace_Znth; lia). lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec 0 vb) as [Hvb|Hvb].
      * subst vb. rewrite Znth_replace_Znth_Same by lia. lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        specialize (PreH62 0). lia.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    destruct (Z.eq_dec (verts - 1) va) as [Hva|Hva].
    + subst va. rewrite Znth_replace_Znth_Same by (try rewrite Zlength_replace_Znth; lia). lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec (verts - 1) vb) as [Hvb|Hvb].
      * subst vb. rewrite Znth_replace_Znth_Same by lia. lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        specialize (PreH62 (verts - 1)). lia.
Qed.

Lemma proof_of_main_entail_wit_16_split_goal_2 : main_entail_wit_16_split_goal_2.
Proof.
  intros; pre_process; entailer!.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    destruct (Z.eq_dec 0 va) as [Hva|Hva].
    + subst va.
      assert (Hsame : Znth 0 (replace_Znth 0 (s + 1)
          (replace_Znth vb (q + 1) rcl_2)) 0 = s + 1).
      { apply Znth_replace_Znth_Same. rewrite Zlength_replace_Znth; lia. }
      rewrite Hsame. lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec 0 vb) as [Hvb|Hvb].
      * subst vb. rewrite Znth_replace_Znth_Same by lia. lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        specialize (PreH62 0). lia.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    destruct (Z.eq_dec 0 va) as [Hva|Hva].
    + subst va.
      assert (Hsame : Znth 0 (replace_Znth 0 (s + 1)
          (replace_Znth vb (q + 1) rcl_2)) 0 = s + 1).
      { apply Znth_replace_Znth_Same. rewrite Zlength_replace_Znth; lia. }
      rewrite Hsame. lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec 0 vb) as [Hvb|Hvb].
      * subst vb. rewrite Znth_replace_Znth_Same by lia. lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        specialize (PreH62 0). lia.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    replace (verts + 1 - 1) with verts by lia.
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
        specialize (PreH62 verts). lia.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    replace (verts + 1 - 1) with verts by lia.
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
        specialize (PreH62 verts). lia.
Qed.

Lemma proof_of_main_entail_wit_16_split_goal_3 : main_entail_wit_16_split_goal_3.
Proof.
  intros; pre_process; entailer!.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    destruct (Z.eq_dec 0 nb) as [Hnb|Hnb].
    + subst nb. rewrite Znth_replace_Znth_Same by (try rewrite Zlength_replace_Znth; lia). lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec 0 na) as [Hna|Hna].
      * subst na. rewrite Znth_replace_Znth_Same by lia. lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        specialize (PreH60 0). lia.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    destruct (Z.eq_dec (verts - 1) nb) as [Hnb|Hnb].
    + subst nb. rewrite Znth_replace_Znth_Same by (try rewrite Zlength_replace_Znth; lia). lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec (verts - 1) na) as [Hna|Hna].
      * subst na. rewrite Znth_replace_Znth_Same by lia. lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        specialize (PreH60 (verts - 1)). lia.
Qed.

Lemma proof_of_main_entail_wit_16_split_goal_4 : main_entail_wit_16_split_goal_4.
Proof.
  intros; pre_process; entailer!.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    destruct (Z.eq_dec 0 nb) as [Hnb|Hnb].
    + subst nb.
      assert (Hsame : Znth 0 (replace_Znth 0 (r + 1)
          (replace_Znth na (p + 1) fcl_2)) 0 = r + 1).
      { apply Znth_replace_Znth_Same. rewrite Zlength_replace_Znth; lia. }
      rewrite Hsame. lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec 0 na) as [Hna|Hna].
      * subst na. rewrite Znth_replace_Znth_Same by lia. lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        specialize (PreH60 0). lia.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    destruct (Z.eq_dec 0 nb) as [Hnb|Hnb].
    + subst nb.
      assert (Hsame : Znth 0 (replace_Znth 0 (r + 1)
          (replace_Znth na (p + 1) fcl_2)) 0 = r + 1).
      { apply Znth_replace_Znth_Same. rewrite Zlength_replace_Znth; lia. }
      rewrite Hsame. lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec 0 na) as [Hna|Hna].
      * subst na. rewrite Znth_replace_Znth_Same by lia. lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        specialize (PreH60 0). lia.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    replace (verts + 1 - 1) with verts by lia.
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    specialize (PreH60 verts). lia.
  - unfold twosat_cursor_bounds in PreH15.
    destruct PreH14 as [Hflen [Hrlen [Hfbounds Hrbounds]]].
    replace (verts + 1 - 1) with verts by lia.
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    specialize (PreH60 verts). lia.
Qed.

Lemma proof_of_main_entail_wit_16_split_goal_5 : main_entail_wit_16_split_goal_5.
Proof. Abort.

Lemma proof_of_main_entail_wit_16_split_goal_6 : main_entail_wit_16_split_goal_6.
Proof. Abort.

Lemma proof_of_main_entail_wit_16_split_goal_7 : main_entail_wit_16_split_goal_7.
Proof. Abort.

Lemma proof_of_main_entail_wit_16_split_goal_8 : main_entail_wit_16_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_16_split_goal_9 : main_entail_wit_16_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_16 : main_entail_wit_16.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_17_split_goal_1 : main_entail_wit_17_split_goal_1.
Proof.
  intros; pre_process; entailer!.
  assert (Hi : i = m_pre) by lia.
  subst i.
  pose proof PreH7 as Hprefix.
  pose proof PreH10 as Hrows_consistent.
  assert (Hcur : forall u, 0 <= u < 2 * n_pre ->
      Znth u fcl_2 0 = csr_hi u fadj_l_2 /\
      Znth u rcl_2 0 = csr_hi u radj_l_2).
  {
    intros u Hu.
    unfold twosat_cursor_occupancy in PreH11.
    destruct PreH11 as [_ [_ [_ [_ Hocc]]]].
    unfold twosat_rows_degree_consistent in PreH10.
    destruct PreH10 as [_ [_ Hrows]].
    specialize (Hocc u Hu).
    specialize (Hrows u Hu).
    lia.
  }
  assert (Hcsr : twosat_csr_wf n_pre fcol_l_2 fadj_l_2
      rcol_l_2 radj_l_2).
  {
    eapply twosat_partial_csr_bridge_complete; eauto.
  }
  assert (Hinput : twosat_clause_input_wf n_pre m_pre lit1_l lit2_l).
  {
    unfold twosat_processed_prefix in PreH7.
    destruct PreH7 as [_ [_ [Hlit1 [Hlit2 _]]]].
    unfold twosat_rows_prefix_step in PreH6.
    destruct PreH6 as [Hverts_nonneg _].
    unfold twosat_clause_input_wf.
    split; [lia|].
    split; [lia|].
    split; [exact Hlit1|].
    split; [exact Hlit2|].
    intros kk Hk.
    specialize (PreH14 kk Hk).
    specialize (PreH15 kk Hk).
    destruct PreH14 as [[Ha0 Halo] Hahi].
    destruct PreH15 as [[Hb0 Hblo] Hbhi].
    split.
    - destruct (Z_le_gt_dec (Znth kk lit1_l 0) 0) as [Ha|Ha].
      + rewrite Z.abs_neq by lia; lia.
      + rewrite Z.abs_eq by lia; lia.
    - destruct (Z_le_gt_dec (Znth kk lit2_l 0) 0) as [Hb|Hb].
      + rewrite Z.abs_neq by lia; lia.
      + rewrite Z.abs_eq by lia; lia.
  }
  assert (Hcomplete : twosat_processed_complete n_pre m_pre lit1_l lit2_l
      fcol_l_2 fadj_l_2 rcol_l_2 radj_l_2 fcl_2 rcl_2).
  {
    unfold twosat_processed_complete.
    exact (conj Hprefix (conj PreH9 (conj Hrows_consistent
      (conj Hcur (conj PreH12 PreH13))))).
  }
  eapply twosat_kosaraju_graph_canonical; eauto.
Qed.

Lemma proof_of_main_entail_wit_17_split_goal_2 : main_entail_wit_17_split_goal_2.
Proof.
  intros; pre_process; entailer!.
Qed.

Lemma proof_of_main_entail_wit_17 : main_entail_wit_17.
Proof.
  right; intros; pre_process; entailer!.
  assert (Hi : i = m_pre) by lia.
  subst i.
  assert (Hcur : forall u, 0 <= u < 2 * n_pre ->
      Znth u fcl_2 0 = csr_hi u fadj_l_2 /\
      Znth u rcl_2 0 = csr_hi u radj_l_2).
  {
    intros u Hu.
    pose proof PreH11 as Hocc_source.
    pose proof PreH10 as Hrows_source.
    unfold twosat_cursor_occupancy in Hocc_source.
    destruct Hocc_source as [_ [_ [_ [_ Hocc]]]].
    unfold twosat_rows_degree_consistent in Hrows_source.
    destruct Hrows_source as [_ [_ Hrows]].
    specialize (Hocc u Hu).
    specialize (Hrows u Hu).
    lia.
  }
  assert (Hcomplete : twosat_processed_complete n_pre m_pre lit1_l lit2_l
      fcol_l_2 fadj_l_2 rcol_l_2 radj_l_2 fcl_2 rcl_2).
  {
    unfold twosat_processed_complete.
    exact (conj PreH7 (conj PreH9 (conj PreH10
      (conj Hcur (conj PreH12 PreH13))))).
  }
  - exact Hcomplete.
  - eapply proof_of_main_entail_wit_17_split_goal_1; eauto; entailer!.
    constructor.
    + exact I.
    + apply ConAssertion.empty_state_is_empty.
Qed.

Lemma proof_of_main_entail_wit_18 : main_entail_wit_18.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_19 : main_entail_wit_19.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_20_1 : main_entail_wit_20_1.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_20_2 : main_entail_wit_20_2.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_20_3 : main_entail_wit_20_3.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_20_4 : main_entail_wit_20_4.
Proof. Admitted. 

Lemma proof_of_main_return_wit_1_split_goal_emp : main_return_wit_1_split_goal_emp.
Proof. Abort.

Lemma proof_of_main_return_wit_1 : main_return_wit_1.
Proof. Admitted. 

Lemma proof_of_main_return_wit_2_split_goal_emp : main_return_wit_2_split_goal_emp.
Proof. Abort.

Lemma proof_of_main_return_wit_2 : main_return_wit_2.
Proof. Admitted. 

Lemma proof_of_main_return_wit_3_split_goal_emp : main_return_wit_3_split_goal_emp.
Proof. Abort.

Lemma proof_of_main_return_wit_3 : main_return_wit_3.
Proof. Admitted. 

Lemma proof_of_dfs2_derive_bind_spec_by_low_level_spec : dfs2_derive_bind_spec_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_dfs1_derive_bind_spec_by_low_level_spec : dfs1_derive_bind_spec_by_low_level_spec.
Proof. Admitted. 
