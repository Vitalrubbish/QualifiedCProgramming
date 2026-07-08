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
Require Import SimpleC.EE.QCP_demos_LLM.kosaraju_rel_lib.
Local Open Scope sac.

Lemma proof_of_dfs1_safety_wit_11_split_goal_1 : dfs1_safety_wit_11_split_goal_1.
Proof. pre_process. match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H end. pose proof (count_nonzero_le_Zlength vis1_m) as Hc. assert (count_nonzero vis1_m <= n_pre) by lia. entailer!. cbv [Znth nth Z.to_nat]. lia. Qed.

Lemma proof_of_dfs1_safety_wit_11_split_goal_2 : dfs1_safety_wit_11_split_goal_2.
Proof. pre_process; entailer!; cbv [Znth nth Z.to_nat]; lia. Qed.

Lemma proof_of_dfs1_safety_wit_11 : dfs1_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_1 : dfs1_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_2_split_goal_1 : dfs1_entail_wit_2_split_goal_1.
Proof. intros; pre_process; entailer!. Qed.

Lemma proof_of_dfs1_entail_wit_2_split_goal_2 : dfs1_entail_wit_2_split_goal_2.
Proof. intros; pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 C9]]]]]]]] end; assert (Hb : (0 <= i < m_of radj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs1_entail_wit_2_split_goal_3 : dfs1_entail_wit_2_split_goal_3.
Proof. intros; pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 C9]]]]]]]] end; assert (Hb : (0 <= i < m_of radj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs1_entail_wit_2 : dfs1_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_3_1 : dfs1_entail_wit_3_1.
Proof. pre_process; cbv [applyf dfs_finish_fromK] in *; Exists timer_v_. Exists vis1_l_. Exists fin_l_; entailer!; lia. Qed.

Lemma proof_of_dfs1_entail_wit_3_2 : dfs1_entail_wit_3_2.
Proof. Admitted. 

Lemma proof_of_dfs1_return_wit_1 : dfs1_return_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_partial_solve_wit_6_pure_split_goal_1 : dfs1_partial_solve_wit_6_pure_split_goal_1.
Proof. intros; pre_process; cbv [applyf dfs_finish_fromK] in *; entailer!; assert (Hi : (i < csr_hi u_pre radj_row_l_low_level_spec)%Z) by (rewrite <- PreH18; exact PreH21); pose proof (dfs_finish_from_step g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec u_pre i Hi) as Heq; apply safeExec_proequiv with (c1 := dfs_finish_from g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec u_pre i); [rewrite PreH30; exact Heq | exact PreH16]. Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure_split_goal_2 : dfs1_partial_solve_wit_6_pure_split_goal_2.
Proof. pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H | H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure : dfs1_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_1_split_goal_1 : dfs2_entail_wit_1_split_goal_1.
Proof. pre_process. match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end. assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia. pose proof (C6 u_pre Hb) as Hlo. pose proof (C7 u_pre Hb) as Hhi. pose proof (C9 u_pre Hb) as Hmon. cbv [csr_lo csr_hi] in *. entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_2 : dfs2_entail_wit_1_split_goal_2.
Proof. pre_process. match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end. assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia. pose proof (C6 u_pre Hb) as Hlo. pose proof (C7 u_pre Hb) as Hhi. pose proof (C9 u_pre Hb) as Hmon. cbv [csr_lo csr_hi] in *. entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_3 : dfs2_entail_wit_1_split_goal_3.
Proof. pre_process. match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end. assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia. pose proof (C6 u_pre Hb) as Hlo. pose proof (C7 u_pre Hb) as Hhi. pose proof (C9 u_pre Hb) as Hmon. cbv [csr_lo csr_hi] in *. entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_4 : dfs2_entail_wit_1_split_goal_4.
Proof. pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H | H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_5 : dfs2_entail_wit_1_split_goal_5.
Proof. pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H | H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_6 : dfs2_entail_wit_1_split_goal_6.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_1_split_goal_7 : dfs2_entail_wit_1_split_goal_7.
Proof. intros; pre_process; entailer!; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; unfold csr_wf2 in *; repeat (rewrite Zlength_replace_Znth in * |- *); repeat (split; try assumption; try lia; try congruence). Qed.

Lemma proof_of_dfs2_entail_wit_1 : dfs2_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_2_split_goal_1 : dfs2_entail_wit_2_split_goal_1.
Proof. intros; pre_process; entailer!. Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_2 : dfs2_entail_wit_2_split_goal_2.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 C9]]]]]]]] end; assert (Hb : (0 <= i < m_of fadj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_3 : dfs2_entail_wit_2_split_goal_3.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (Hb : (0 <= i < m_of fadj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs2_entail_wit_2 : dfs2_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_1 : dfs2_entail_wit_3_1_split_goal_1.
Proof. pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H | H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs2_entail_wit_3_1 : dfs2_entail_wit_3_1.
Proof. pre_process; cbv [applyf dfs_scc_fromK] in *; Exists vis2_l_. Exists sid_l_; entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_1 : dfs2_entail_wit_3_2_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_entail_wit_3_2 : dfs2_entail_wit_3_2.
Proof. Admitted. 

Lemma proof_of_dfs2_return_wit_1_split_goal_1 : dfs2_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_dfs2_return_wit_1 : dfs2_return_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_8_pure_split_goal_1 : dfs2_partial_solve_wit_8_pure_split_goal_1.
Proof. intros; pre_process; cbv [applyf dfs_scc_fromK] in *; entailer!; assert (Hi : (i < csr_hi u_pre fadj_row_l_low_level_spec)%Z) by (rewrite <- PreH20; exact PreH23); pose proof (dfs_scc_from_step g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec root_pre u_pre i Hi) as Heq; apply safeExec_proequiv with (c1 := dfs_scc_from g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec root_pre u_pre i); [rewrite PreH32; exact Heq | exact PreH18]. Qed.

Lemma proof_of_dfs2_partial_solve_wit_8_pure : dfs2_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_dfs2_derive_bind_spec_by_low_level_spec : dfs2_derive_bind_spec_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_dfs1_derive_bind_spec_by_low_level_spec : dfs1_derive_bind_spec_by_low_level_spec.
Proof. Admitted. 

