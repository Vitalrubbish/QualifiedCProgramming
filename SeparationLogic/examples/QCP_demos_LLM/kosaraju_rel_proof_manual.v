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
Proof. left; intros; pre_process. match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H end. pose proof (count_nonzero_le_Zlength vis1_m) as Hc. assert (count_nonzero vis1_m <= n_pre) by lia. entailer!. all: cbv [Znth nth Z.to_nat]; lia. Qed.

Lemma proof_of_dfs1_entail_wit_1 : dfs1_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_dfs1_entail_wit_2_split_goal_1 : dfs1_entail_wit_2_split_goal_1.
Proof. intros; pre_process; entailer!. Qed.

Lemma proof_of_dfs1_entail_wit_2_split_goal_2 : dfs1_entail_wit_2_split_goal_2.
Proof. intros; pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 C9]]]]]]]] end; assert (Hb : (0 <= i < m_of radj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs1_entail_wit_2_split_goal_3 : dfs1_entail_wit_2_split_goal_3.
Proof. intros; pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 C9]]]]]]]] end; assert (Hb : (0 <= i < m_of radj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs1_entail_wit_2 : dfs1_entail_wit_2.
Proof. right; intros. pose proof (proof_of_dfs1_entail_wit_2_split_goal_1) as H1. pose proof (proof_of_dfs1_entail_wit_2_split_goal_2) as H2. pose proof (proof_of_dfs1_entail_wit_2_split_goal_3) as H3. unfold dfs1_entail_wit_2_split_goal_1 in H1. unfold dfs1_entail_wit_2_split_goal_2 in H2. unfold dfs1_entail_wit_2_split_goal_3 in H3. apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ solve [eapply H1; repeat eassumption] | solve [eapply H2; repeat eassumption] ] | solve [eapply H3; repeat eassumption] ] | pre_process; entailer! ]. Qed.

Lemma proof_of_dfs1_entail_wit_3_1 : dfs1_entail_wit_3_1.
Proof. pre_process; cbv [applyf dfs_finish_fromK] in *; Exists timer_v_. Exists vis1_l_. Exists fin_l_; entailer!; lia. Qed.

Lemma proof_of_dfs1_entail_wit_3_2 : dfs1_entail_wit_3_2.
Proof. right; intros; pre_process; Exists timer_m_2; entailer!; subst v; apply (dfs1_skip_close g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec u_pre i vis1_m_2 fin_m_2 timer_m_2 X_low_level_spec); [ rewrite <- PreH6; exact PreH9 | split; [ exact PreH17 | rewrite PreH3; exact PreH18 ] | exact PreH1 | exact PreH4 ]. Qed.

Lemma proof_of_dfs1_return_wit_1 : dfs1_return_wit_1.
Proof. right; intros; pre_process; Exists (timer_m + 1)%Z; entailer!. - destruct PreH2 as [D1 [D2 [D3 [D4 [D5 [D6 [D7 [D8 [D9 D10]]]]]]]]]; apply (dfs1_return_close g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec u_pre i vis1_m fin_m timer_m X_low_level_spec); [ split; [ exact PreH11 | rewrite PreH3; exact PreH12 ] | exact PreH14 | exact D4 | rewrite <- PreH6; lia | exact PreH4 ]. - unfold csr_wf1, AdjGraphValid in *; destruct PreH2 as [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 A10]]]]]]]]]; destruct A1 as [B1 [B2 [B3 [B4 B5]]]]; repeat (rewrite Zlength_replace_Znth in * |- *); repeat (split; try assumption; try lia; try congruence; try (symmetry; assumption)). Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure_split_goal_1 : dfs1_partial_solve_wit_6_pure_split_goal_1.
Proof. intros; pre_process; cbv [applyf dfs_finish_fromK] in *; entailer!; subst v; apply (dfs1_recurse_close g_low_level_spec radj_col_l_low_level_spec radj_row_l_low_level_spec u_pre i vis1_m fin_m timer_m X_low_level_spec); [ rewrite <- PreH18; exact PreH21 | split; [ exact PreH29 | rewrite PreH15; exact PreH30 ] | exact PreH13 | exact PreH16 ]. Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure_split_goal_2 : dfs1_partial_solve_wit_6_pure_split_goal_2.
Proof. pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H | H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure : dfs1_partial_solve_wit_6_pure.
Proof. right; intros. pose proof (proof_of_dfs1_partial_solve_wit_6_pure_split_goal_1) as H1. pose proof (proof_of_dfs1_partial_solve_wit_6_pure_split_goal_2) as H2. unfold dfs1_partial_solve_wit_6_pure_split_goal_1 in H1. unfold dfs1_partial_solve_wit_6_pure_split_goal_2 in H2. apply _derivable1_andp_intros; [ solve [eapply H1; repeat eassumption] | solve [eapply H2; repeat eassumption] ]. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_1 : dfs2_entail_wit_1_split_goal_1.
Proof. intros; pre_process. repeat match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end. assert (HLu : (0 <= u_pre < Zlength vis2_l_low_level_spec)%Z) by lia. assert (HL0 : (0 <= 0 < Zlength vis2_l_low_level_spec)%Z) by lia. assert (HLn : (0 <= n_pre - 1 < Zlength vis2_l_low_level_spec)%Z) by lia. entailer!. all: intros Hv; match goal with | |- (Znth ?k (replace_Znth ?j 1 ?L) 0 <> 0) => assert (HLk : (0 <= k < Zlength L)%Z) by lia; destruct (Z.eqb k j) eqn:E; [ apply Z.eqb_eq in E; subst j; rewrite (Znth_replace_eq L k 1 0 HLk); lia | apply Z.eqb_neq in E; rewrite (Znth_replace_neq L k j 1 0 HLk (proj1 (HLu)) E); exact Hv ] end. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_2 : dfs2_entail_wit_1_split_goal_2.
Proof. intros; pre_process; entailer!; repeat match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (HLu : (0 <= u_pre < Zlength vis2_l_low_level_spec)%Z) by lia; assert (HLr : (0 <= root_pre < Zlength vis2_l_low_level_spec)%Z) by lia; destruct (Z.eqb root_pre u_pre) eqn:E; [ apply Z.eqb_eq in E; rewrite E; rewrite (Znth_replace_eq vis2_l_low_level_spec u_pre 1 0 HLu); lia | apply Z.eqb_neq in E; rewrite (Znth_replace_neq vis2_l_low_level_spec root_pre u_pre 1 0 HLr (proj1 HLu) E); assumption ]. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_3 : dfs2_entail_wit_1_split_goal_3.
Proof. intros; pre_process; entailer!; repeat match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (HLu : (0 <= u_pre < Zlength vis2_l_low_level_spec)%Z) by lia; rewrite (Znth_replace_eq vis2_l_low_level_spec u_pre 1 0 HLu); lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_4 : dfs2_entail_wit_1_split_goal_4.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia; pose proof (C9 u_pre Hb); cbv [csr_lo csr_hi] in *; entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_5 : dfs2_entail_wit_1_split_goal_5.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia; pose proof (C7 u_pre Hb); cbv [csr_lo csr_hi] in *; entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_6 : dfs2_entail_wit_1_split_goal_6.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia; pose proof (C9 u_pre Hb); cbv [csr_lo csr_hi] in *; entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_7 : dfs2_entail_wit_1_split_goal_7.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (Hb : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by lia; pose proof (C6 u_pre Hb); cbv [csr_lo csr_hi] in *; entailer!; lia. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_8 : dfs2_entail_wit_1_split_goal_8.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; cbv [csr_lo csr_hi]; entailer!; reflexivity. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_9 : dfs2_entail_wit_1_split_goal_9.
Proof. intros; pre_process; entailer!; apply (dfs2_entry_close g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec vis2_l_low_level_spec sid_l_low_level_spec root_pre u_pre root_v_low_level_spec X_low_level_spec); [ exact PreH1 | exact PreH2 | split; [ exact PreH5 | rewrite PreH3; exact PreH6 ] | split; [ exact PreH7 | rewrite PreH3; exact PreH8 ] | exact PreH10 | exact PreH4 ]. Qed.

Lemma proof_of_dfs2_entail_wit_1_split_goal_10 : dfs2_entail_wit_1_split_goal_10.
Proof. intros; pre_process; entailer!; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; unfold csr_wf2 in *; repeat (rewrite Zlength_replace_Znth in * |- *); repeat (split; try assumption; try lia; try congruence). Qed.

Lemma proof_of_dfs2_entail_wit_1 : dfs2_entail_wit_1.
Proof. right; intros. pose proof (proof_of_dfs2_entail_wit_1_split_goal_1) as H1. pose proof (proof_of_dfs2_entail_wit_1_split_goal_2) as H2. pose proof (proof_of_dfs2_entail_wit_1_split_goal_3) as H3. pose proof (proof_of_dfs2_entail_wit_1_split_goal_4) as H4. pose proof (proof_of_dfs2_entail_wit_1_split_goal_5) as H5. pose proof (proof_of_dfs2_entail_wit_1_split_goal_6) as H6. pose proof (proof_of_dfs2_entail_wit_1_split_goal_7) as H7. pose proof (proof_of_dfs2_entail_wit_1_split_goal_8) as H8. pose proof (proof_of_dfs2_entail_wit_1_split_goal_9) as H9. pose proof (proof_of_dfs2_entail_wit_1_split_goal_10) as H10. unfold dfs2_entail_wit_1_split_goal_1 in H1. unfold dfs2_entail_wit_1_split_goal_2 in H2. unfold dfs2_entail_wit_1_split_goal_3 in H3. unfold dfs2_entail_wit_1_split_goal_4 in H4. unfold dfs2_entail_wit_1_split_goal_5 in H5. unfold dfs2_entail_wit_1_split_goal_6 in H6. unfold dfs2_entail_wit_1_split_goal_7 in H7. unfold dfs2_entail_wit_1_split_goal_8 in H8. unfold dfs2_entail_wit_1_split_goal_9 in H9. unfold dfs2_entail_wit_1_split_goal_10 in H10. apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ solve [eapply H1; repeat eassumption] | solve [eapply H2; repeat eassumption] ] | solve [eapply H3; repeat eassumption] ] | solve [eapply H4; repeat eassumption] ] | solve [eapply H5; repeat eassumption] ] | solve [eapply H6; repeat eassumption] ] | solve [eapply H7; repeat eassumption] ] | solve [eapply H8; repeat eassumption] ] | solve [eapply H9; repeat eassumption] ] | solve [eapply H10; repeat eassumption] ] | pre_process; entailer! ]. Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_1 : dfs2_entail_wit_2_split_goal_1.
Proof. intros; pre_process; entailer!. Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_2 : dfs2_entail_wit_2_split_goal_2.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 C9]]]]]]]] end; assert (Hb : (0 <= i < m_of fadj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs2_entail_wit_2_split_goal_3 : dfs2_entail_wit_2_split_goal_3.
Proof. intros; pre_process; match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end; assert (Hb : (0 <= i < m_of fadj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs2_entail_wit_2 : dfs2_entail_wit_2.
Proof. right; intros. pose proof (proof_of_dfs2_entail_wit_2_split_goal_1) as H1. pose proof (proof_of_dfs2_entail_wit_2_split_goal_2) as H2. pose proof (proof_of_dfs2_entail_wit_2_split_goal_3) as H3. unfold dfs2_entail_wit_2_split_goal_1 in H1. unfold dfs2_entail_wit_2_split_goal_2 in H2. unfold dfs2_entail_wit_2_split_goal_3 in H3. apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ solve [eapply H1; repeat eassumption] | solve [eapply H2; repeat eassumption] ] | solve [eapply H3; repeat eassumption] ] | pre_process; entailer! ]. Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_1 : dfs2_entail_wit_3_1_split_goal_1.
Proof. intros; pre_process. match goal with H : csr_wf2 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]] end. entailer!. - destruct (Z.eqb lo i) eqn:E; [ apply Z.eqb_eq in E; rewrite E; rewrite <- PreH27; exact PreH4 | apply Z.eqb_neq in E; assert (Hlli : (lo <= lo < i)%Z) by lia; pose proof (PreH22 lo Hlli) as Hsc; apply (PreH5 (Znth lo fadj_col_l_low_level_spec 0)); [ assert (Hblo : (0 <= lo < m_of fadj_row_l_low_level_spec)%Z) by lia; pose proof (C8 lo Hblo) as Hw; rewrite PreH2 in Hw; exact Hw | exact Hsc ] ]. - replace (i + 1 - 1)%Z with i by lia; rewrite <- PreH27; exact PreH4. Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_2 : dfs2_entail_wit_3_1_split_goal_2.
Proof. intros; pre_process. Qed.

Lemma proof_of_dfs2_entail_wit_3_1_split_goal_3 : dfs2_entail_wit_3_1_split_goal_3.
Proof. intros; pre_process. Qed.

Lemma proof_of_dfs2_entail_wit_3_1 : dfs2_entail_wit_3_1.
Proof. right; intros. pose proof (proof_of_dfs2_entail_wit_3_1_split_goal_1) as H1. pose proof (proof_of_dfs2_entail_wit_3_1_split_goal_2) as H2. pose proof (proof_of_dfs2_entail_wit_3_1_split_goal_3) as H3. unfold dfs2_entail_wit_3_1_split_goal_1 in H1. unfold dfs2_entail_wit_3_1_split_goal_2 in H2. unfold dfs2_entail_wit_3_1_split_goal_3 in H3. apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ solve [eapply H1; repeat eassumption] | solve [eapply H2; repeat eassumption] ] | solve [eapply H3; repeat eassumption] ] | pre_process; entailer! ]. Qed.

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_1 : dfs2_entail_wit_3_2_split_goal_1.
Proof. intros; pre_process. entailer!. - destruct (Z.eqb lo i) eqn:E; [ apply Z.eqb_eq in E; rewrite E; rewrite <- PreH23; exact PreH1 | apply Z.eqb_neq in E; assert (Hlli : (lo <= lo < i)%Z) by lia; exact (PreH18 lo Hlli) ]. - replace (i + 1 - 1)%Z with i by lia; rewrite <- PreH23; exact PreH1. Qed.

Lemma proof_of_dfs2_entail_wit_3_2_split_goal_2 : dfs2_entail_wit_3_2_split_goal_2.
Proof. intros; pre_process; entailer!. apply dfs2_skip_close; [ match goal with H1 : ?i < ?hi, H2 : ?hi = csr_hi ?u ?fr |- _ => rewrite <- H2; exact H1 end | match goal with H : ?v = Znth ?i ?fc 0 |- _ => rewrite <- H; lia end | match goal with H : ?v = Znth ?i ?fc 0 |- _ => rewrite <- H; match goal with H2 : Znth ?v ?vis 0 <> 0 |- _ => exact H2 end end | match goal with H : safeExec (pre_dfs2 ?g ?fc ?fr ?vis ?sid ?rv) (dfs_scc_from ?g ?fc ?fr ?root ?u ?i) ?X |- _ => exact H end ]. Qed.

Lemma proof_of_dfs2_entail_wit_3_2 : dfs2_entail_wit_3_2.
Proof. right; intros; pre_process; entailer!. all: repeat (first [ match goal with | Hvi : ?v = Znth ?ii ?fc 0, Hvisv : Znth ?v ?vis 0 <> 0 |- Znth (Znth (?ii + 1 - 1)%Z ?fc 0) ?vis 0 <> 0 => replace (ii + 1 - 1)%Z with ii by lia; rewrite <- Hvi; exact Hvisv end | (eapply dfs2_scanned_lo_close; [ match goal with H : forall j, ((?lo <= j)%Z /\ (j < ?i)%Z) -> Znth (Znth j ?fc 0) ?vis 0 <> 0 |- _ => exact H end | lia | match goal with H : ?v = Znth ?i ?fc 0 |- _ => exact H end | match goal with H : Znth ?v ?vis 0 <> 0 |- Znth ?v ?vis 0 <> 0 => exact H end ]) | (apply dfs2_skip_close; [ match goal with H1 : ?i < ?hi, H2 : ?hi = csr_hi ?u ?fr |- _ => rewrite <- H2; exact H1 end | match goal with H : ?v = Znth ?i ?fc 0 |- _ => rewrite <- H; lia end | match goal with H : ?v = Znth ?i ?fc 0 |- _ => rewrite <- H; match goal with H2 : Znth ?v ?vis 0 <> 0 |- _ => exact H2 end end | match goal with H : safeExec (pre_dfs2 ?g ?fc ?fr ?vis ?sid ?rv) (dfs_scc_from ?g ?fc ?fr ?root ?u ?i) ?X |- _ => exact H end ]) | split | assumption | lia | congruence | entailer! ]). Qed.

Lemma proof_of_dfs2_return_wit_1_split_goal_1 : dfs2_return_wit_1_split_goal_1.
Proof. intros; pre_process; entailer!; apply (dfs2_return_close g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec root_pre u_pre i vis2_m sid_m root_v_low_level_spec X_low_level_spec); [ rewrite <- PreH7; lia | exact PreH5 ]. Qed.

Lemma proof_of_dfs2_return_wit_1 : dfs2_return_wit_1.
Proof. right; intros. pose proof (proof_of_dfs2_return_wit_1_split_goal_1) as H1. unfold dfs2_return_wit_1_split_goal_1 in H1. apply _derivable1_andp_intros; [ eapply H1; repeat eassumption | pre_process; entailer! ]. Qed.

Lemma proof_of_dfs2_partial_solve_wit_8_pure_split_goal_1 : dfs2_partial_solve_wit_8_pure_split_goal_1.
Proof. intros; pre_process; entailer!; subst v; apply (dfs2_recurse_close g_low_level_spec fadj_col_l_low_level_spec fadj_row_l_low_level_spec root_pre u_pre i vis2_m sid_m root_v_low_level_spec X_low_level_spec); [ rewrite <- PreH21; exact PreH24 | split; [ exact PreH35 | rewrite PreH18; exact PreH36 ] | exact PreH15 | exact PreH19 ]. Qed.

Lemma proof_of_dfs2_partial_solve_wit_8_pure : dfs2_partial_solve_wit_8_pure.
Proof. right; intros. pose proof (proof_of_dfs2_partial_solve_wit_8_pure_split_goal_1) as H1. unfold dfs2_partial_solve_wit_8_pure_split_goal_1 in H1. eapply H1; repeat eassumption. Qed.

Lemma proof_of_dfs2_derive_bind_spec_by_low_level_spec : dfs2_derive_bind_spec_by_low_level_spec.
Proof. intros; pre_process. apply safeExec_bind in H2 as (X_low_level_spec & Hsafe_first & Hsafe_cont). Exists g_bind_spec. Exists fadj_col_l_bind_spec. Exists fadj_row_l_bind_spec. Exists vis2_l_bind_spec. Exists sid_l_bind_spec. Exists root_v_bind_spec. Exists X_low_level_spec. split_pure_spatial. - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_bind_spec) fadj_col_l_bind_spec). cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_bind_spec). cancel (IntArray.full vis2_pre n_pre vis2_l_bind_spec). cancel (IntArray.full sid_pre n_pre sid_l_bind_spec). apply derivable1_wand_sepcon_adjoint. Intros vis2_l__2 sid_l__2. Exists vis2_l__2. Exists sid_l__2. split_pure_spatial. + cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_bind_spec) fadj_col_l_bind_spec). cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_bind_spec). cancel (IntArray.full vis2_pre n_pre vis2_l__2). cancel (IntArray.full sid_pre n_pre sid_l__2). + split_pures; dump_pre_spatial. exact H2. exact H9. unfold applyf. apply (Hsafe_cont (pre_dfs2 g_bind_spec fadj_col_l_bind_spec fadj_row_l_bind_spec vis2_l__2 sid_l__2 root_v_bind_spec) tt). exact H10. exact H11. exact H12. - split_pures; dump_pre_spatial. exact H. exact H0. exact H1. exact Hsafe_first. exact H3. exact H4. exact H5. exact H6. exact H7. exact H8. Qed.

Lemma proof_of_dfs1_derive_bind_spec_by_low_level_spec : dfs1_derive_bind_spec_by_low_level_spec.
Proof. intros; pre_process. apply safeExec_bind in H1 as (X_low_level_spec & Hsafe_first & Hsafe_cont). Exists g_bind_spec. Exists radj_col_l_bind_spec. Exists radj_row_l_bind_spec. Exists vis1_l_bind_spec. Exists fin_l_bind_spec. Exists timer_v_bind_spec. Exists X_low_level_spec. split_pure_spatial. - cancel (IntArray.full radj_col_pre (m_of radj_row_l_bind_spec) radj_col_l_bind_spec). cancel (IntArray.full radj_row_pre (n_pre + 1) radj_row_l_bind_spec). cancel (IntArray.full vis1_pre n_pre vis1_l_bind_spec). cancel (IntArray.full fin_pre n_pre fin_l_bind_spec). cancel (IntArray.full timer_p_pre 1 (timer_v_bind_spec :: nil)). apply derivable1_wand_sepcon_adjoint. Intros timer_v__2 vis1_l__2 fin_l__2. Exists timer_v__2. Exists vis1_l__2. Exists fin_l__2. split_pure_spatial. + cancel (IntArray.full radj_col_pre (m_of radj_row_l_bind_spec) radj_col_l_bind_spec). cancel (IntArray.full radj_row_pre (n_pre + 1) radj_row_l_bind_spec). cancel (IntArray.full vis1_pre n_pre vis1_l__2). cancel (IntArray.full fin_pre n_pre fin_l__2). cancel (IntArray.full timer_p_pre 1 (timer_v__2 :: nil)). + split_pures; dump_pre_spatial. exact H1. exact H0. unfold applyf. apply (Hsafe_cont (pre_dfs1 g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec vis1_l__2 fin_l__2 timer_v__2) tt). exact H9. exact H10. exact H11. - split_pures; dump_pre_spatial. exact H. exact H0. exact Hsafe_first. exact H2. exact H3. exact H4. exact H5. exact H6. exact H7. Qed.

