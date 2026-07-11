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
From MonadLib.MonadErr Require Export StateRelMonadErr.
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
Proof. intros; pre_process; entailer!; repeat match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; intros Hne Hvis; assert (HLu : (0 <= u_pre)%Z) by lia; match goal with |- Znth ?k ?L 0 = _ => assert (HL : (0 <= k < Zlength sid_l_low_level_spec)%Z) by lia; symmetry; rewrite (Znth_replace_neq sid_l_low_level_spec k u_pre (Znth root_pre sid_l_low_level_spec 0) 0 HL HLu Hne); reflexivity end. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_2 : dfs2_entail_wit_1_split_goal_2.
Proof. intros; pre_process; entailer!; repeat match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; intros Hvis; assert (HLu : (0 <= u_pre < Zlength vis2_l_low_level_spec)%Z) by lia; match goal with |- Znth ?k (replace_Znth ?j 1 ?L) 0 <> 0 => assert (HL : (0 <= k < Zlength vis2_l_low_level_spec)%Z) by lia; destruct (Z.eqb k j) eqn:E; [ apply Z.eqb_eq in E; rewrite <- E; rewrite (Znth_replace_eq vis2_l_low_level_spec k 1 0 HL); lia | apply Z.eqb_neq in E; rewrite (Znth_replace_neq vis2_l_low_level_spec k j 1 0 HL (proj1 HLu) E); exact Hvis ] end. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_3 : dfs2_entail_wit_1_split_goal_3.
Proof. intros; pre_process; entailer!; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (HLu : (0 <= u_pre < Zlength vis2_l_low_level_spec)%Z) by lia; assert (HLr : (0 <= root_pre < Zlength vis2_l_low_level_spec)%Z) by lia; destruct (Z.eqb root_pre u_pre) eqn:E; [ apply Z.eqb_eq in E; rewrite E; rewrite (Znth_replace_eq vis2_l_low_level_spec u_pre 1 0 HLu); lia | apply Z.eqb_neq in E; rewrite (Znth_replace_neq vis2_l_low_level_spec root_pre u_pre 1 0 HLr (proj1 HLu) E); assumption ]. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_4 : dfs2_entail_wit_1_split_goal_4.
Proof. intros; pre_process; entailer!; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (HLu : (0 <= u_pre < Zlength sid_l_low_level_spec)%Z) by lia; assert (HLr : (0 <= root_pre < Zlength sid_l_low_level_spec)%Z) by lia; rewrite (Znth_replace_eq sid_l_low_level_spec u_pre (Znth root_pre sid_l_low_level_spec 0) 0 HLu); destruct (Z.eqb root_pre u_pre) eqn:E; [ apply Z.eqb_eq in E; rewrite E; rewrite (Znth_replace_eq sid_l_low_level_spec u_pre (Znth u_pre sid_l_low_level_spec 0) 0 HLu); reflexivity | apply Z.eqb_neq in E; rewrite (Znth_replace_neq sid_l_low_level_spec root_pre u_pre (Znth root_pre sid_l_low_level_spec 0) 0 HLr PreH5 E); reflexivity ]. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_5 : dfs2_entail_wit_1_split_goal_5.
Proof. intros; pre_process; entailer!; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (HLu : (0 <= u_pre < Zlength vis2_l_low_level_spec)%Z) by lia; rewrite (Znth_replace_eq vis2_l_low_level_spec u_pre 1 0 HLu); lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_6 : dfs2_entail_wit_1_split_goal_6.
Proof. pre_process. match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end. assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia. pose proof (C6 u_pre Hb) as Hlo. pose proof (C7 u_pre Hb) as Hhi. pose proof (C9 u_pre Hb) as Hmon. cbv [csr_lo csr_hi] in *. entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_7 : dfs2_entail_wit_1_split_goal_7.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia; pose proof (C9 u_pre Hb); cbv [csr_lo csr_hi] in *; entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_8 : dfs2_entail_wit_1_split_goal_8.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia; pose proof (C6 u_pre Hb); cbv [csr_lo csr_hi] in *; entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_9 : dfs2_entail_wit_1_split_goal_9.
Proof. pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H | H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_10 : dfs2_entail_wit_1_split_goal_10.
Proof. intros; pre_process; entailer!; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; unfold csr_wf2 in *; repeat (rewrite Zlength_replace_Znth in * |- *); repeat (split; try assumption; try lia; try congruence). Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_11 : dfs2_entail_wit_1_split_goal_11.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_1_split_goal_12 : dfs2_entail_wit_1_split_goal_12.
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
Proof. intros; pre_process; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_2 : dfs2_entail_wit_3_1_split_goal_2.
Proof. intros; pre_process; entailer!; [ destruct (Z.eqb lo i) eqn:E; [ apply Z.eqb_eq in E; rewrite E; rewrite <- PreH31; exact PreH4 | apply Z.eqb_neq in E; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (Hlli : (lo <= lo < i)%Z) by lia; assert (Hblo : (0 <= lo < m_of fadj_row_l_low_level_spec)%Z) by lia; destruct (C8 lo Hblo) as [Hlo' Hhi']; assert (Hw : (0 <= Znth lo fadj_col_l_low_level_spec 0 < n_pre)%Z) by lia; exact (PreH6 (Znth lo fadj_col_l_low_level_spec 0) Hw (PreH25 lo Hlli)) ] | replace (i + 1 - 1)%Z with i by lia; rewrite <- PreH31; exact PreH4 ]. Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_3 : dfs2_entail_wit_3_1_split_goal_3.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_4 : dfs2_entail_wit_3_1_split_goal_4.
Proof. pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H | H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_5 : dfs2_entail_wit_3_1_split_goal_5.
Proof. pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H | H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs2_entail_wit_3_1 : dfs2_entail_wit_3_1.
Proof. Admitted. 

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_1 : dfs2_entail_wit_3_2_split_goal_1.
Proof. intros; pre_process; entailer!; [ destruct (Z.eqb lo i) eqn:E; [ apply Z.eqb_eq in E; rewrite E; rewrite <- PreH25; exact PreH1 | apply Z.eqb_neq in E; assert (Hlli : (lo <= lo < i)%Z) by lia; exact (PreH19 lo Hlli) ] | replace (i + 1 - 1)%Z with i by lia; rewrite <- PreH25; exact PreH1 ]. Qed.

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_2 : dfs2_entail_wit_3_2_split_goal_2.
Proof. intros; pre_process; entailer!; apply (dfs2_skip_close g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec root_pre u_pre i vis2_m_2 sid_m_2 root_v_low_level_spec X_low_level_spec); [ rewrite <- PreH7; exact PreH10 | rewrite <- PreH25; lia | rewrite <- PreH25; exact PreH1 | exact PreH5 ]. Qed.

Lemma proof_of_dfs2_entail_wit_3_2 : dfs2_entail_wit_3_2.
Proof. right; intros; pre_process; entailer!. all: repeat (first [ match goal with | Hvi : ?v = Znth ?ii ?fc 0, Hvisv : Znth ?v ?vis 0 <> 0 |- Znth (Znth (?ii + 1 - 1)%Z ?fc 0) ?vis 0 <> 0 => replace (ii + 1 - 1)%Z with ii by lia; rewrite <- Hvi; exact Hvisv end | (eapply dfs2_scanned_lo_close; [ match goal with H : forall j, ((?lo <= j)%Z /\ (j < ?i)%Z) -> Znth (Znth j ?fc 0) ?vis 0 <> 0 |- _ => exact H end | lia | match goal with H : ?v = Znth ?i ?fc 0 |- _ => exact H end | match goal with H : Znth ?v ?vis 0 <> 0 |- Znth ?v ?vis 0 <> 0 => exact H end ]) | (apply dfs2_skip_close; [ match goal with H1 : ?i < ?hi, H2 : ?hi = csr_hi ?u ?fr |- _ => rewrite <- H2; exact H1 end | match goal with H : ?v = Znth ?i ?fc 0 |- _ => rewrite <- H; lia end | match goal with H : ?v = Znth ?i ?fc 0 |- _ => rewrite <- H; match goal with H2 : Znth ?v ?vis 0 <> 0 |- _ => exact H2 end end | match goal with H : safeExec (pre_dfs2 ?g ?fc ?fr ?vis ?sid ?rv) (dfs_scc_from ?g ?fc ?fr ?root ?u ?i) ?X |- _ => exact H end ]) | split | assumption | lia | congruence | entailer! ]). Qed.

Lemma proof_of_dfs2_return_wit_1_split_goal_1 : dfs2_return_wit_1_split_goal_1.
Proof. Admitted. 

Lemma proof_of_dfs2_return_wit_1_split_goal_2 : dfs2_return_wit_1_split_goal_2.
Proof. Admitted. 

Lemma proof_of_dfs2_return_wit_1 : dfs2_return_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs2_partial_solve_wit_8_pure_split_goal_1 : dfs2_partial_solve_wit_8_pure_split_goal_1.
Proof. intros; pre_process; entailer!; rewrite PreH39; apply (dfs2_recurse_close g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec root_pre u_pre i vis2_m sid_m root_v_low_level_spec X_low_level_spec); [ rewrite <- PreH21; exact PreH24 | rewrite <- PreH39; lia | rewrite <- PreH39; exact PreH15 | exact PreH19 ]. Qed.

Lemma proof_of_dfs2_partial_solve_wit_8_pure : dfs2_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_dfs2_derive_bind_spec_by_low_level_spec : dfs2_derive_bind_spec_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_dfs1_derive_bind_spec_by_low_level_spec : dfs1_derive_bind_spec_by_low_level_spec.
Proof. Admitted. 

