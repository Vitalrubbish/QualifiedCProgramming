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
Proof.
  intros timer_p_pre fin_pre vis1_pre radj_row_pre radj_col_pre n_pre u_pre
        X_low_level_spec timer_v_low_level_spec fin_l_low_level_spec vis1_l_low_level_spec
        radj_row_l_low_level_spec radj_col_l_low_level_spec
        g_low_level_spec hi lo timer_m i vis1_m fin_m
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
        PreH19 PreH20 PreH21.
  pre_process. entailer!. cbv [Znth nth Z.to_nat] in *.
  destruct PreH2 as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]].
  pose proof (count_nonzero_le_Zlength vis1_m).
  rewrite C3, PreH4 in H. lia.
Qed.

Lemma proof_of_dfs1_safety_wit_11_split_goal_2 : dfs1_safety_wit_11_split_goal_2.
Proof.
  intros timer_p_pre fin_pre vis1_pre radj_row_pre radj_col_pre n_pre u_pre
        X_low_level_spec timer_v_low_level_spec fin_l_low_level_spec vis1_l_low_level_spec
        radj_row_l_low_level_spec radj_col_l_low_level_spec
        g_low_level_spec hi lo timer_m i vis1_m fin_m
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
        PreH19 PreH20 PreH21.
  pre_process; entailer!; cbv [Znth nth Z.to_nat]; lia.
Qed.

Lemma proof_of_dfs1_safety_wit_11 : dfs1_safety_wit_11.
Proof.
  left. intros timer_p_pre fin_pre vis1_pre radj_row_pre radj_col_pre n_pre u_pre
        X_low_level_spec timer_v_low_level_spec fin_l_low_level_spec vis1_l_low_level_spec
        radj_row_l_low_level_spec radj_col_l_low_level_spec
        g_low_level_spec hi lo timer_m i vis1_m fin_m
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
        PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
        PreH19 PreH20 PreH21.
  split.
  - eapply proof_of_dfs1_safety_wit_11_split_goal_1; eassumption.
  - eapply proof_of_dfs1_safety_wit_11_split_goal_2; eassumption.
Qed.

Lemma proof_of_dfs1_entail_wit_1 : dfs1_entail_wit_1.
Proof.
  right; intros n_pre u_pre X_low_level_spec timer_v_low_level_spec
        fin_l_low_level_spec vis1_l_low_level_spec radj_row_l_low_level_spec
        radj_col_l_low_level_spec g_low_level_spec
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  pre_process. Exists timer_v_low_level_spec. entailer!.
  all: pose proof PreH1 as Hwf;
       destruct Hwf as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]];
       assert (Hub : (0 <= u_pre < adj_verts g_low_level_spec)%Z) by (rewrite PreH3; lia);
       first
       [ exact PreH4
       | exact (C7 u_pre Hub)
       | exact (C9 u_pre Hub)
       | exact (C6 u_pre Hub)
       | change (Znth u_pre radj_row_l_low_level_spec 0) with
           (csr_lo u_pre radj_row_l_low_level_spec);
         apply (dfs1_entry_close g_low_level_spec radj_col_l_low_level_spec
                   radj_row_l_low_level_spec vis1_l_low_level_spec
                   fin_l_low_level_spec u_pre timer_v_low_level_spec X_low_level_spec);
         [ exact PreH1 | exact PreH2 | exact Hub | exact PreH5 ]
       | rewrite (count_nonzero_replace_Znth01 u_pre vis1_l_low_level_spec)
           by (try (rewrite C3, PreH3; lia); try exact PreH9); lia
       | unfold dfs1_active_timer_surplus; intros spare Hsp Hbudget;
         rewrite (count_nonzero_replace_Znth01 u_pre vis1_l_low_level_spec)
           by (try (rewrite C3, PreH3; lia); try exact PreH9); lia
       | unfold csr_wf1 in *; repeat (rewrite Zlength_replace_Znth in * |- *);
         repeat (split; try assumption; try lia; try congruence) ].
Qed. 

Lemma proof_of_dfs1_entail_wit_2_split_goal_1 : dfs1_entail_wit_2_split_goal_1.
Proof. intros; pre_process; entailer!. Qed.

Lemma proof_of_dfs1_entail_wit_2_split_goal_2 : dfs1_entail_wit_2_split_goal_2.
Proof. intros; pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 C9]]]]]]]] end; assert (Hb : (0 <= i < m_of radj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs1_entail_wit_2_split_goal_3 : dfs1_entail_wit_2_split_goal_3.
Proof. intros; pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 C9]]]]]]]] end; assert (Hb : (0 <= i < m_of radj_row_l_low_level_spec)%Z) by lia; pose proof (C8 i Hb) as Hc; destruct Hc as [Hc1 Hc2]; entailer!; try exact Hc1; try lia. Qed.

Lemma proof_of_dfs1_entail_wit_2 : dfs1_entail_wit_2.
Proof. right; intros. pose proof (proof_of_dfs1_entail_wit_2_split_goal_1) as H1. pose proof (proof_of_dfs1_entail_wit_2_split_goal_2) as H2. pose proof (proof_of_dfs1_entail_wit_2_split_goal_3) as H3. unfold dfs1_entail_wit_2_split_goal_1 in H1. unfold dfs1_entail_wit_2_split_goal_2 in H2. unfold dfs1_entail_wit_2_split_goal_3 in H3. apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ apply _derivable1_andp_intros; [ solve [eapply H1; repeat eassumption] | solve [eapply H2; repeat eassumption] ] | solve [eapply H3; repeat eassumption] ] | pre_process; entailer! ]. Qed.

Lemma proof_of_dfs1_entail_wit_3_1 : dfs1_entail_wit_3_1.
Proof.
  right; intros; pre_process; cbv [applyf dfs_finish_fromK] in *.
  Exists timer_v_. entailer!.
  all: try lia; try eassumption.
  - unfold dfs1_active_timer_surplus in *.
    intros spare Hspare Hbudget.
    unfold dfs1_timer_surplus_preserved in PreH7.
    specialize (PreH29 spare Hspare Hbudget).
    specialize (PreH7 (spare + 1)).
    assert (0 <= spare + 1) by lia.
    assert (timer_m_2 + (spare + 1) <= count_nonzero vis1_m_2) by lia.
    specialize (PreH7 H H0). lia.
  - unfold dfs1_timer_surplus_preserved in PreH7.
    specialize (PreH7 1).
    assert (0 <= 1) by lia.
    assert (timer_m_2 + 1 <= count_nonzero vis1_m_2) by lia.
    specialize (PreH7 H H0). lia.
Qed.

Lemma proof_of_dfs1_entail_wit_3_2 : dfs1_entail_wit_3_2.
Proof.
  right; intros; pre_process. Exists timer_m_2. entailer!.
  apply dfs1_skip_close.
  - lia.
  - match goal with H : v = Znth i radj_col_l_low_level_spec 0 |- _ =>
      rewrite <- H; lia
    end.
  - match goal with H : v = Znth i radj_col_l_low_level_spec 0 |- _ =>
      rewrite <- H; exact PreH1
    end.
  - exact PreH7.
Qed.

Lemma proof_of_dfs1_return_wit_1 : dfs1_return_wit_1.
Proof.
  right; intros; pre_process. Exists (timer_m + 1). entailer!.
  all: replace (Znth 0 (timer_m :: nil) 0) with timer_m by reflexivity.
  all: pose proof PreH2 as Hwf; destruct Hwf as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]].
  all: try lia; try eassumption.
  - unfold fin_values_in_int_range.
    first
      [ unfold fin_values_in_int_range in PreH6;
        destruct PreH6 as [_ Hfin_range]
      | pose proof PreH6 as Hfin_range ].
    intros w Hw.
    destruct (Z.eq_dec w u_pre) as [-> | Hne].
    + rewrite Znth_replace_eq by (rewrite C4, PreH4; lia).
      pose proof (count_nonzero_le_Zlength vis1_m).
      rewrite C3, PreH4 in H. lia.
    + rewrite Znth_replace_neq by (try (rewrite C4, PreH4); lia).
      apply Hfin_range; lia.
  - unfold dfs1_timer_surplus_preserved.
    intros spare Hspare Hbudget.
    unfold dfs1_active_timer_surplus in PreH21.
    specialize (PreH21 spare Hspare Hbudget). lia.
  - apply (dfs1_return_close g_low_level_spec radj_col_l_low_level_spec
             radj_row_l_low_level_spec u_pre i vis1_m fin_m timer_m
             X_low_level_spec).
    + split; [ exact PreH14 | rewrite PreH4; exact PreH15 ].
    + exact PreH17.
    + exact C4.
    + pose proof PreH1 as H1; rewrite PreH9 in H1; lia.
    + exact PreH7.
  - unfold csr_wf1 in *; repeat (rewrite Zlength_replace_Znth in * |- *);
    repeat (split; try assumption; try lia; try congruence).
Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure_split_goal_1 : dfs1_partial_solve_wit_6_pure_split_goal_1.
Proof.
  intros; pre_process. entailer!.
  rewrite PreH36.
  eapply (dfs1_recurse_close g_low_level_spec radj_col_l_low_level_spec
            radj_row_l_low_level_spec u_pre i vis1_m fin_m timer_m
            X_low_level_spec).
  - rewrite <- PreH21; exact PreH24.
  - destruct PreH14 as [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 C10]]]]]]]]];
    assert (Hb : (0 <= i < m_of radj_row_l_low_level_spec)%Z) by lia;
    pose proof (C8 i Hb) as Hc; exact Hc.
  - rewrite <- PreH36; exact PreH13.
  - exact PreH19.
Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure_split_goal_2 : dfs1_partial_solve_wit_6_pure_split_goal_2.
Proof. pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H | H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; entailer!; try lia; try congruence; try assumption. Qed.

Lemma proof_of_dfs1_partial_solve_wit_6_pure : dfs1_partial_solve_wit_6_pure.
Proof.
  right. intros. apply _derivable1_andp_intros.
  - eapply proof_of_dfs1_partial_solve_wit_6_pure_split_goal_1; eassumption.
  - eapply proof_of_dfs1_partial_solve_wit_6_pure_split_goal_2; eassumption.
Qed.

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

Lemma proof_of_transpose_safety_wit_5_split_goal_1 : transpose_safety_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_transpose_safety_wit_5_split_goal_2 : transpose_safety_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_transpose_safety_wit_5 : transpose_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_transpose_safety_wit_10_split_goal_1 : transpose_safety_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_transpose_safety_wit_10_split_goal_2 : transpose_safety_wit_10_split_goal_2.
Proof. Abort.

Lemma proof_of_transpose_safety_wit_10 : transpose_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_transpose_safety_wit_15_split_goal_1 : transpose_safety_wit_15_split_goal_1.
Proof. Abort.

Lemma proof_of_transpose_safety_wit_15_split_goal_2 : transpose_safety_wit_15_split_goal_2.
Proof. Abort.

Lemma proof_of_transpose_safety_wit_15 : transpose_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_3_split_goal_1 : transpose_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_3_split_goal_2 : transpose_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_3 : transpose_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_4_split_goal_1 : transpose_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_4_split_goal_2 : transpose_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_4_split_goal_3 : transpose_entail_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_4 : transpose_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_6_split_goal_emp : transpose_entail_wit_6_split_goal_emp.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_6 : transpose_entail_wit_6.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_7_split_goal_1 : transpose_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_7 : transpose_entail_wit_7.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_8_split_goal_spatial : transpose_entail_wit_8_split_goal_spatial.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_8 : transpose_entail_wit_8.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_9_split_goal_1 : transpose_entail_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_9_split_goal_2 : transpose_entail_wit_9_split_goal_2.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_9_split_goal_3 : transpose_entail_wit_9_split_goal_3.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_9_split_goal_4 : transpose_entail_wit_9_split_goal_4.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_9_split_goal_5 : transpose_entail_wit_9_split_goal_5.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_9 : transpose_entail_wit_9.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_10_split_goal_1 : transpose_entail_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_10_split_goal_2 : transpose_entail_wit_10_split_goal_2.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_10_split_goal_3 : transpose_entail_wit_10_split_goal_3.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_10_split_goal_4 : transpose_entail_wit_10_split_goal_4.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_10_split_goal_5 : transpose_entail_wit_10_split_goal_5.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_10_split_goal_6 : transpose_entail_wit_10_split_goal_6.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_10 : transpose_entail_wit_10.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_11 : transpose_entail_wit_11.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_12_split_goal_1 : transpose_entail_wit_12_split_goal_1.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_12_split_goal_2 : transpose_entail_wit_12_split_goal_2.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_12_split_goal_3 : transpose_entail_wit_12_split_goal_3.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_12_split_goal_4 : transpose_entail_wit_12_split_goal_4.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_12_split_goal_spatial : transpose_entail_wit_12_split_goal_spatial.
Proof. Abort.

Lemma proof_of_transpose_entail_wit_12 : transpose_entail_wit_12.
Proof. Admitted. 

Lemma proof_of_transpose_entail_wit_13 : transpose_entail_wit_13.
Proof. Admitted. 

Lemma proof_of_transpose_return_wit_1 : transpose_return_wit_1.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_entail_wit_4_split_goal_1 : sort_by_fin_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_4_split_goal_2 : sort_by_fin_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_4_split_goal_3 : sort_by_fin_entail_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_4 : sort_by_fin_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_entail_wit_5_split_goal_1 : sort_by_fin_entail_wit_5_split_goal_1.
Proof. intros; pre_process; entailer!. Qed.

Lemma proof_of_sort_by_fin_entail_wit_5_split_goal_2 : sort_by_fin_entail_wit_5_split_goal_2.
Proof.
  intros; pre_process; entailer!.
  first
    [ unfold fin_values_in_int_range in PreH5;
      destruct PreH5 as [_ Hrange]
    | pose proof PreH5 as Hrange ].
  pose proof (Hrange keyv ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_by_fin_entail_wit_5_split_goal_3 : sort_by_fin_entail_wit_5_split_goal_3.
Proof.
  intros; pre_process; entailer!.
  first
    [ unfold fin_values_in_int_range in PreH5;
      destruct PreH5 as [_ Hrange]
    | pose proof PreH5 as Hrange ].
  pose proof (Hrange keyv ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sort_by_fin_entail_wit_5 : sort_by_fin_entail_wit_5.
Proof.
  right; intros; pre_process; entailer!.
  all: first
    [ reflexivity
    | match goal with
      | H : fin_values_in_int_range _ _ |- _ =>
          first
            [ unfold fin_values_in_int_range in H;
              destruct H as [_ Hrange]
            | pose proof H as Hrange ];
          pose proof (Hrange keyv ltac:(lia)); lia
      end
    | lia ].
Qed.

Lemma proof_of_sort_by_fin_entail_wit_8_split_goal_1 : sort_by_fin_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_8_split_goal_2 : sort_by_fin_entail_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_8_split_goal_3 : sort_by_fin_entail_wit_8_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_8 : sort_by_fin_entail_wit_8.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_entail_wit_9_split_goal_1 : sort_by_fin_entail_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_9_split_goal_2 : sort_by_fin_entail_wit_9_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_9_split_goal_3 : sort_by_fin_entail_wit_9_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_9 : sort_by_fin_entail_wit_9.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_entail_wit_10_split_goal_1 : sort_by_fin_entail_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_10 : sort_by_fin_entail_wit_10.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_entail_wit_11_split_goal_1 : sort_by_fin_entail_wit_11_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_11_split_goal_2 : sort_by_fin_entail_wit_11_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_11 : sort_by_fin_entail_wit_11.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_entail_wit_12_split_goal_1 : sort_by_fin_entail_wit_12_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_12_split_goal_2 : sort_by_fin_entail_wit_12_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_12 : sort_by_fin_entail_wit_12.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_1 : sort_by_fin_entail_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_2 : sort_by_fin_entail_wit_13_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_3 : sort_by_fin_entail_wit_13_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_4 : sort_by_fin_entail_wit_13_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_5 : sort_by_fin_entail_wit_13_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_6 : sort_by_fin_entail_wit_13_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_7 : sort_by_fin_entail_wit_13_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_8 : sort_by_fin_entail_wit_13_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_9 : sort_by_fin_entail_wit_13_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_10 : sort_by_fin_entail_wit_13_split_goal_10.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_11 : sort_by_fin_entail_wit_13_split_goal_11.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_12 : sort_by_fin_entail_wit_13_split_goal_12.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13_split_goal_13 : sort_by_fin_entail_wit_13_split_goal_13.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_13 : sort_by_fin_entail_wit_13.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_entail_wit_14_1_split_goal_1 : sort_by_fin_entail_wit_14_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_14_1_split_goal_2 : sort_by_fin_entail_wit_14_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_by_fin_entail_wit_14_1 : sort_by_fin_entail_wit_14_1.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_return_wit_1 : sort_by_fin_return_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_safety_wit_1_split_goal_1 : kosaraju_safety_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_safety_wit_1_split_goal_2 : kosaraju_safety_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_safety_wit_1 : kosaraju_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_safety_wit_13_split_goal_1 : kosaraju_safety_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_safety_wit_13_split_goal_2 : kosaraju_safety_wit_13_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_safety_wit_13 : kosaraju_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_kosaraju_safety_wit_18_split_goal_1 : kosaraju_safety_wit_18_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_safety_wit_18_split_goal_2 : kosaraju_safety_wit_18_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_safety_wit_18 : kosaraju_safety_wit_18.
Proof. Admitted. 

Lemma proof_of_kosaraju_safety_wit_19_split_goal_1 : kosaraju_safety_wit_19_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_safety_wit_19_split_goal_2 : kosaraju_safety_wit_19_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_safety_wit_19 : kosaraju_safety_wit_19.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_1 : kosaraju_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_2_split_goal_1 : kosaraju_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_2_split_goal_2 : kosaraju_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_2_split_goal_3 : kosaraju_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_2_split_goal_spatial : kosaraju_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_2 : kosaraju_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_4_split_goal_1 : kosaraju_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_4_split_goal_2 : kosaraju_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_4_split_goal_3 : kosaraju_entail_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_4_split_goal_4 : kosaraju_entail_wit_4_split_goal_4.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_4_split_goal_5 : kosaraju_entail_wit_4_split_goal_5.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_4 : kosaraju_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_6 : kosaraju_entail_wit_6.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_7 : kosaraju_entail_wit_7.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_8_split_goal_1 : kosaraju_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_8_split_goal_2 : kosaraju_entail_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_8_split_goal_3 : kosaraju_entail_wit_8_split_goal_3.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_8_split_goal_4 : kosaraju_entail_wit_8_split_goal_4.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_8 : kosaraju_entail_wit_8.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_9 : kosaraju_entail_wit_9.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_10_1 : kosaraju_entail_wit_10_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_10_2 : kosaraju_entail_wit_10_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_11 : kosaraju_entail_wit_11.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_13_split_goal_1 : kosaraju_entail_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_13_split_goal_2 : kosaraju_entail_wit_13_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_13_split_goal_3 : kosaraju_entail_wit_13_split_goal_3.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_13_split_goal_spatial : kosaraju_entail_wit_13_split_goal_spatial.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_13 : kosaraju_entail_wit_13.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_14_split_goal_1 : kosaraju_entail_wit_14_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_14_split_goal_2 : kosaraju_entail_wit_14_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_14_split_goal_3 : kosaraju_entail_wit_14_split_goal_3.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_14 : kosaraju_entail_wit_14.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_15_split_goal_1 : kosaraju_entail_wit_15_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_15 : kosaraju_entail_wit_15.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_16_split_goal_1 : kosaraju_entail_wit_16_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_16_split_goal_2 : kosaraju_entail_wit_16_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_16 : kosaraju_entail_wit_16.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_17_split_goal_1 : kosaraju_entail_wit_17_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_17_split_goal_2 : kosaraju_entail_wit_17_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_17 : kosaraju_entail_wit_17.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_18_split_goal_1 : kosaraju_entail_wit_18_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_18 : kosaraju_entail_wit_18.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_19_1 : kosaraju_entail_wit_19_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_19_2 : kosaraju_entail_wit_19_2.
Proof. Admitted. 

Lemma proof_of_kosaraju_entail_wit_20_split_goal_1 : kosaraju_entail_wit_20_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_20_split_goal_spatial : kosaraju_entail_wit_20_split_goal_spatial.
Proof. Abort.

Lemma proof_of_kosaraju_entail_wit_20 : kosaraju_entail_wit_20.
Proof. Admitted. 

Lemma proof_of_kosaraju_return_wit_1 : kosaraju_return_wit_1.
Proof. Admitted. 

Lemma proof_of_kosaraju_partial_solve_wit_2_pure_split_goal_1 : kosaraju_partial_solve_wit_2_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_partial_solve_wit_2_pure : kosaraju_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_kosaraju_partial_solve_wit_22_pure_split_goal_1 : kosaraju_partial_solve_wit_22_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_kosaraju_partial_solve_wit_22_pure_split_goal_2 : kosaraju_partial_solve_wit_22_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_kosaraju_partial_solve_wit_22_pure_split_goal_3 : kosaraju_partial_solve_wit_22_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_kosaraju_partial_solve_wit_22_pure : kosaraju_partial_solve_wit_22_pure.
Proof. Admitted. 

Lemma proof_of_neg_vertex_return_wit_1_split_goal_1 : neg_vertex_return_wit_1_split_goal_1.
Proof. pre_process; entailer!; lia. Qed.

Lemma proof_of_neg_vertex_return_wit_1 : neg_vertex_return_wit_1.
Proof.
  right.
  intros a_pre retval PreH1 PreH2 PreH3 PreH4.
  pre_process; entailer!; lia.
Qed.

Lemma proof_of_main_safety_wit_16_split_goal_1 : main_safety_wit_16_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_16_split_goal_2 : main_safety_wit_16_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_16 : main_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_21_split_goal_1 : main_safety_wit_21_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_21_split_goal_2 : main_safety_wit_21_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_21 : main_safety_wit_21.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_22_split_goal_1 : main_safety_wit_22_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_22_split_goal_2 : main_safety_wit_22_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_22 : main_safety_wit_22.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_26_split_goal_1 : main_safety_wit_26_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_26_split_goal_2 : main_safety_wit_26_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_26 : main_safety_wit_26.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_27_split_goal_1 : main_safety_wit_27_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_27_split_goal_2 : main_safety_wit_27_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_27 : main_safety_wit_27.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_31_split_goal_1 : main_safety_wit_31_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_31_split_goal_2 : main_safety_wit_31_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_31 : main_safety_wit_31.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_32_split_goal_1 : main_safety_wit_32_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_32_split_goal_2 : main_safety_wit_32_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_32 : main_safety_wit_32.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_36_split_goal_1 : main_safety_wit_36_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_36_split_goal_2 : main_safety_wit_36_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_36 : main_safety_wit_36.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_37_split_goal_1 : main_safety_wit_37_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_37_split_goal_2 : main_safety_wit_37_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_37 : main_safety_wit_37.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_41_split_goal_1 : main_safety_wit_41_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_41_split_goal_2 : main_safety_wit_41_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_41 : main_safety_wit_41.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_42_split_goal_1 : main_safety_wit_42_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_42_split_goal_2 : main_safety_wit_42_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_42 : main_safety_wit_42.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_46_split_goal_1 : main_safety_wit_46_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_46_split_goal_2 : main_safety_wit_46_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_46 : main_safety_wit_46.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_47_split_goal_1 : main_safety_wit_47_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_47_split_goal_2 : main_safety_wit_47_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_47 : main_safety_wit_47.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_52_split_goal_1 : main_safety_wit_52_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_52_split_goal_2 : main_safety_wit_52_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_52 : main_safety_wit_52.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_58_split_goal_1 : main_safety_wit_58_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_58_split_goal_2 : main_safety_wit_58_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_58 : main_safety_wit_58.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_65_split_goal_1 : main_safety_wit_65_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_65_split_goal_2 : main_safety_wit_65_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_65 : main_safety_wit_65.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_66_split_goal_1 : main_safety_wit_66_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_66_split_goal_2 : main_safety_wit_66_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_66 : main_safety_wit_66.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_72_split_goal_1 : main_safety_wit_72_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_72_split_goal_2 : main_safety_wit_72_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_72 : main_safety_wit_72.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_73_split_goal_1 : main_safety_wit_73_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_73_split_goal_2 : main_safety_wit_73_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_73 : main_safety_wit_73.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_78_split_goal_1 : main_safety_wit_78_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_78_split_goal_2 : main_safety_wit_78_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_78 : main_safety_wit_78.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_85_split_goal_1 : main_safety_wit_85_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_85_split_goal_2 : main_safety_wit_85_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_85 : main_safety_wit_85.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_86_split_goal_1 : main_safety_wit_86_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_86_split_goal_2 : main_safety_wit_86_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_86 : main_safety_wit_86.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_91_split_goal_1 : main_safety_wit_91_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_91_split_goal_2 : main_safety_wit_91_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_91 : main_safety_wit_91.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_98_split_goal_1 : main_safety_wit_98_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_98_split_goal_2 : main_safety_wit_98_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_98 : main_safety_wit_98.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_99_split_goal_1 : main_safety_wit_99_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_99_split_goal_2 : main_safety_wit_99_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_99 : main_safety_wit_99.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_105_split_goal_1 : main_safety_wit_105_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_105_split_goal_2 : main_safety_wit_105_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_105 : main_safety_wit_105.
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

Lemma proof_of_main_safety_wit_123_split_goal_1 : main_safety_wit_123_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_123_split_goal_2 : main_safety_wit_123_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_123 : main_safety_wit_123.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_126_split_goal_1 : main_safety_wit_126_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_126_split_goal_2 : main_safety_wit_126_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_126 : main_safety_wit_126.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_129_split_goal_1 : main_safety_wit_129_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_129_split_goal_2 : main_safety_wit_129_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_129 : main_safety_wit_129.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_131_split_goal_1 : main_safety_wit_131_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_131_split_goal_2 : main_safety_wit_131_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_131 : main_safety_wit_131.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_132_split_goal_1 : main_safety_wit_132_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_132_split_goal_2 : main_safety_wit_132_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_132 : main_safety_wit_132.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_136_split_goal_1 : main_safety_wit_136_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_136_split_goal_2 : main_safety_wit_136_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_136 : main_safety_wit_136.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_137_split_goal_1 : main_safety_wit_137_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_137_split_goal_2 : main_safety_wit_137_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_137 : main_safety_wit_137.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_141_split_goal_1 : main_safety_wit_141_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_141_split_goal_2 : main_safety_wit_141_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_141 : main_safety_wit_141.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_142_split_goal_1 : main_safety_wit_142_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_142_split_goal_2 : main_safety_wit_142_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_142 : main_safety_wit_142.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_146_split_goal_1 : main_safety_wit_146_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_146_split_goal_2 : main_safety_wit_146_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_146 : main_safety_wit_146.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_147_split_goal_1 : main_safety_wit_147_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_147_split_goal_2 : main_safety_wit_147_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_147 : main_safety_wit_147.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_151_split_goal_1 : main_safety_wit_151_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_151_split_goal_2 : main_safety_wit_151_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_151 : main_safety_wit_151.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_152_split_goal_1 : main_safety_wit_152_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_152_split_goal_2 : main_safety_wit_152_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_152 : main_safety_wit_152.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_156_split_goal_1 : main_safety_wit_156_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_156_split_goal_2 : main_safety_wit_156_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_156 : main_safety_wit_156.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_157_split_goal_1 : main_safety_wit_157_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_157_split_goal_2 : main_safety_wit_157_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_157 : main_safety_wit_157.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_162_split_goal_1 : main_safety_wit_162_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_162_split_goal_2 : main_safety_wit_162_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_162 : main_safety_wit_162.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_168_split_goal_1 : main_safety_wit_168_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_168_split_goal_2 : main_safety_wit_168_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_168 : main_safety_wit_168.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_175_split_goal_1 : main_safety_wit_175_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_175_split_goal_2 : main_safety_wit_175_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_175 : main_safety_wit_175.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_176_split_goal_1 : main_safety_wit_176_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_176_split_goal_2 : main_safety_wit_176_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_176 : main_safety_wit_176.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_182_split_goal_1 : main_safety_wit_182_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_182_split_goal_2 : main_safety_wit_182_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_182 : main_safety_wit_182.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_183_split_goal_1 : main_safety_wit_183_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_183_split_goal_2 : main_safety_wit_183_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_183 : main_safety_wit_183.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_188_split_goal_1 : main_safety_wit_188_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_188_split_goal_2 : main_safety_wit_188_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_188 : main_safety_wit_188.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_195_split_goal_1 : main_safety_wit_195_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_195_split_goal_2 : main_safety_wit_195_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_195 : main_safety_wit_195.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_196_split_goal_1 : main_safety_wit_196_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_196_split_goal_2 : main_safety_wit_196_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_196 : main_safety_wit_196.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_201_split_goal_1 : main_safety_wit_201_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_201_split_goal_2 : main_safety_wit_201_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_201 : main_safety_wit_201.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_208_split_goal_1 : main_safety_wit_208_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_208_split_goal_2 : main_safety_wit_208_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_208 : main_safety_wit_208.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_209_split_goal_1 : main_safety_wit_209_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_209_split_goal_2 : main_safety_wit_209_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_209 : main_safety_wit_209.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_213_split_goal_1 : main_safety_wit_213_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_213_split_goal_2 : main_safety_wit_213_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_213 : main_safety_wit_213.
Proof. Admitted. 

Lemma proof_of_main_safety_wit_214_split_goal_1 : main_safety_wit_214_split_goal_1.
Proof. Abort.

Lemma proof_of_main_safety_wit_214_split_goal_2 : main_safety_wit_214_split_goal_2.
Proof. Abort.

Lemma proof_of_main_safety_wit_214 : main_safety_wit_214.
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

Lemma proof_of_main_entail_wit_2_split_goal_1 : main_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_2_split_goal_2 : main_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_2 : main_entail_wit_2.
Proof.
  left.
  pre_process.
  prop_apply (IntArray.full_Zlength radj_row).
  Intros_p Hradj_len.
  prop_apply (IntArray.full_Zlength fadj_row).
  Intros_p Hfadj_len.
  rewrite Zlength_replace_Znth in Hradj_len.
  rewrite Zlength_replace_Znth in Hfadj_len.
  Exists rcl_2 fcl_2 sdl_2 rcol_l_2 fcol_l_2
    (replace_Znth i 0 radj_l_2) (replace_Znth i 0 fadj_l_2).
  entailer!.
  - intros k [? ?].
    destruct (Z.eq_dec k i) as [-> | Hki].
    + rewrite Znth_replace_Znth_Same by lia; reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply PreH5; lia.
  - intros k [? ?].
    destruct (Z.eq_dec k i) as [-> | Hki].
    + rewrite Znth_replace_Znth_Same by lia; reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply PreH4; lia.
Qed.

Lemma proof_of_main_entail_wit_3_split_goal_1 : main_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_3_split_goal_2 : main_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_3_split_goal_3 : main_entail_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_main_entail_wit_3 : main_entail_wit_3.
Proof.
  left.
  pre_process.
  prop_apply (IntArray.full_Zlength sid).
  Intros_p Hsid_len.
  Exists rcl_2 fcl_2 rcol_l_2 fcol_l_2 sdl_2 radj_l_2 fadj_l_2.
  entailer!.
  - intros k [? ?].
    apply PreH5; lia.
  - intros k [? ?].
    apply PreH4; lia.
  - pose proof (Zlength_nonneg sdl_2); lia.
Qed.

Lemma proof_of_main_entail_wit_4_split_goal_1 : main_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_4 : main_entail_wit_4.
Proof.
  left.
  pre_process.
  prop_apply (IntArray.full_Zlength sid).
  Intros_p Hsid_len.
  rewrite Zlength_replace_Znth in Hsid_len.
  Exists rcl_2 fcl_2 rcol_l_2 fcol_l_2 (replace_Znth i 0 sdl_2)
    radj_l_2 fadj_l_2.
  entailer!.
  intros k [? ?].
  destruct (Z.eq_dec k i) as [-> | Hki].
  - rewrite Znth_replace_Znth_Same by lia; reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply PreH6; lia.
Qed.

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

Lemma proof_of_main_entail_wit_6_1_split_goal_15 : main_entail_wit_6_1_split_goal_15.
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

Lemma proof_of_main_entail_wit_6_2_split_goal_12 : main_entail_wit_6_2_split_goal_12.
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

Lemma proof_of_main_entail_wit_6_3_split_goal_12 : main_entail_wit_6_3_split_goal_12.
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

Lemma proof_of_main_entail_wit_6_4_split_goal_9 : main_entail_wit_6_4_split_goal_9.
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

Lemma proof_of_main_entail_wit_13_split_goal_16 : main_entail_wit_13_split_goal_16.
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

Lemma proof_of_main_entail_wit_14_1_split_goal_29 : main_entail_wit_14_1_split_goal_29.
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

Lemma proof_of_main_entail_wit_14_2_split_goal_26 : main_entail_wit_14_2_split_goal_26.
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

Lemma proof_of_main_entail_wit_14_3_split_goal_26 : main_entail_wit_14_3_split_goal_26.
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

Lemma proof_of_main_entail_wit_14_4_split_goal_23 : main_entail_wit_14_4_split_goal_23.
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
Proof.
  intros; pre_process; entailer!.
  unfold twosat_clause_encoding in PreH1.
  destruct PreH1 as [Hna [Hnb [Hva Hvb]]].
  unfold twosat_processed_prefix in PreH13.
  destruct PreH13 as [Hpi [Hpm [Hlit1 [Hlit2 Hprocessed]]]].
  unfold twosat_cursor_occupancy in *.
  destruct PreH17 as [Hi [Him [Hflen [Hrlen Hocc]]]].
  split; [lia|].
  split; [lia|].
  split.
  { rewrite Zlength_replace_Znth; rewrite Zlength_replace_Znth; exact Hflen. }
  split.
  { rewrite Zlength_replace_Znth; rewrite Zlength_replace_Znth; exact Hrlen. }
  intros u Hu.
  split.
  - specialize (Hocc u Hu).
    destruct Hocc as [Hf Hr].
    destruct (Z.eq_dec u nb) as [Hub|Hub].
    + subst u.
      rewrite Znth_replace_Znth_Same by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec nb na) as [Hba|Hba].
      * subst na.
        rewrite (PreH36 (eq_sym Hba)).
        rewrite (twosat_fdegree_succ_r13 i lit1_l lit2_l nb) by lia.
        rewrite <- PreH10, <- PreH11, <- Hba, <- Hnb.
        rewrite Z.eqb_refl. lia.
      * assert (Hba' : neg_vertex a <> nb) by (intros H; apply Hba; lia).
        rewrite (PreH37 ltac:(intros H; apply Hba; lia)).
        rewrite (twosat_fdegree_succ_r13 i lit1_l lit2_l nb) by lia.
        rewrite <- PreH10, <- PreH11, <- Hna, <- Hnb.
        rewrite Z.eqb_refl.
        destruct (Z.eqb na nb) eqn:Hn; simpl.
        { apply Z.eqb_eq in Hn; exfalso; apply Hba; lia. }
        { apply Z.eqb_neq in Hn; lia. }
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec u na) as [Hua|Hua].
      * subst u. rewrite Znth_replace_Znth_Same by lia.
        rewrite (twosat_fdegree_succ_r13 i lit1_l lit2_l na) by lia.
        rewrite <- PreH10, <- PreH11, <- Hna, <- Hnb.
        assert (Hba' : neg_vertex b <> na) by (intros H; apply Hub; rewrite <- Hnb in H; lia).
        rewrite Z.eqb_refl.
        destruct (Z.eqb nb na) eqn:Hn; simpl.
        { apply Z.eqb_eq in Hn; exfalso; apply Hub; lia. }
        { apply Z.eqb_neq in Hn; lia. }
      * rewrite Znth_replace_Znth_Diff by lia.
        rewrite (twosat_fdegree_succ_r13 i lit1_l lit2_l u) by lia.
        rewrite <- PreH10, <- PreH11, <- Hna, <- Hnb.
        destruct (Z.eqb na u) eqn:Hn;
        destruct (Z.eqb nb u) eqn:Hm; simpl.
        { apply Z.eqb_eq in Hn; exfalso; apply Hua; lia. }
        { apply Z.eqb_eq in Hn; exfalso; apply Hua; lia. }
        { apply Z.eqb_eq in Hm; exfalso; apply Hub; lia. }
        { apply Z.eqb_neq in Hn; apply Z.eqb_neq in Hm; lia. }
  - specialize (Hocc u Hu).
    destruct Hocc as [Hf Hr].
    destruct (Z.eq_dec u va) as [Huv|Huv].
    + subst u.
      rewrite Znth_replace_Znth_Same by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec va vb) as [Hab|Hab].
      *
        rewrite (PreH38 (eq_sym Hab)).
        rewrite (twosat_rdegree_succ_r13 i lit1_l lit2_l va) by lia.
        rewrite <- PreH10, <- PreH11, <- Hva, <- Hvb.
        rewrite <- Hab, Z.eqb_refl. lia.
      * rewrite (PreH39 ltac:(intros H; apply Hab; lia)).
        rewrite (twosat_rdegree_succ_r13 i lit1_l lit2_l va) by lia.
        rewrite <- PreH10, <- PreH11, <- Hva, <- Hvb.
        assert (Hfalse : Z.eqb vb va = false) by
          (apply Z.eqb_neq; intros H; apply Hab; lia).
        rewrite Z.eqb_refl, Hfalse. lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
      destruct (Z.eq_dec u vb) as [Hub|Hub].
      * subst u. rewrite Znth_replace_Znth_Same by lia.
        rewrite (twosat_rdegree_succ_r13 i lit1_l lit2_l vb) by lia.
        rewrite <- PreH10, <- PreH11, <- Hva, <- Hvb.
        assert (Hfalse : Z.eqb va vb = false) by
          (apply Z.eqb_neq; intros H; apply Huv; lia).
        rewrite Z.eqb_refl, Hfalse. lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        rewrite (twosat_rdegree_succ_r13 i lit1_l lit2_l u) by lia.
        rewrite <- PreH10, <- PreH11, <- Hva, <- Hvb.
        destruct (Z.eqb vb u) eqn:Hb;
        destruct (Z.eqb va u) eqn:Ha; simpl.
        { apply Z.eqb_eq in Hb; exfalso; apply Hub; lia. }
        { apply Z.eqb_eq in Hb; exfalso; apply Hub; lia. }
        { apply Z.eqb_eq in Ha; exfalso; apply Huv; lia. }
        { apply Z.eqb_neq in Hb; apply Z.eqb_neq in Ha; lia. }
Qed.

Lemma proof_of_main_entail_wit_16_split_goal_8 : main_entail_wit_16_split_goal_8.
Proof. Abort.

Lemma proof_of_main_entail_wit_16_split_goal_9 : main_entail_wit_16_split_goal_9.
Proof. Abort.

Lemma proof_of_main_entail_wit_16_split_goal_10 : main_entail_wit_16_split_goal_10.
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

Lemma proof_of_main_entail_wit_17_split_goal_3 : main_entail_wit_17_split_goal_3.
Proof. Abort.

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

Lemma proof_of_main_entail_wit_20 : main_entail_wit_20.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_21 : main_entail_wit_21.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_22_1 : main_entail_wit_22_1.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_22_2 : main_entail_wit_22_2.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_22_3 : main_entail_wit_22_3.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_22_4 : main_entail_wit_22_4.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_23_1_split_goal_1 : main_entail_wit_23_1_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_23_1_split_goal_2 : main_entail_wit_23_1_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_23_1 : main_entail_wit_23_1.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_23_2_split_goal_1 : main_entail_wit_23_2_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_23_2_split_goal_2 : main_entail_wit_23_2_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_23_2 : main_entail_wit_23_2.
Proof. Admitted. 

Lemma proof_of_main_entail_wit_23_3_split_goal_1 : main_entail_wit_23_3_split_goal_1.
Proof. Abort.

Lemma proof_of_main_entail_wit_23_3_split_goal_2 : main_entail_wit_23_3_split_goal_2.
Proof. Abort.

Lemma proof_of_main_entail_wit_23_3 : main_entail_wit_23_3.
Proof. Admitted. 

Lemma proof_of_main_return_wit_1_split_goal_1 : main_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_main_return_wit_1 : main_return_wit_1.
Proof. Admitted. 

Lemma proof_of_sort_by_fin_derive_high_level_spec_by_low_level_spec : sort_by_fin_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists fin_l_high_level_spec.
  Exists order_l_high_level_spec.
  split_pure_spatial.
  - cancel (IntArray.full fin_pre n_pre fin_l_high_level_spec).
    cancel (IntArray.full order_pre n_pre order_l_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros order_l__2.
    Exists order_l__2.
    split_pure_spatial.
    + cancel (IntArray.full fin_pre n_pre fin_l_high_level_spec).
      cancel (IntArray.full order_pre n_pre order_l__2).
    + split_pures; dump_pre_spatial; eassumption.
  - split_pures; dump_pre_spatial; eassumption.
Qed.

Lemma proof_of_transpose_derive_high_level_spec_by_low_level_spec : transpose_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists g_high_level_spec.
  Exists fadj_col_l_high_level_spec.
  Exists fadj_row_l_high_level_spec.
  Exists radj_col_l_high_level_spec.
  Exists radj_row_l_high_level_spec.
  Exists pos_l_high_level_spec.
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_high_level_spec) fadj_col_l_high_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_high_level_spec).
    cancel (IntArray.full radj_col_pre (m_of fadj_row_l_high_level_spec) radj_col_l_high_level_spec).
    cancel (IntArray.full radj_row_pre (n_pre + 1) radj_row_l_high_level_spec).
    cancel (IntArray.full pos_pre n_pre pos_l_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros pos_l__2 radj_col_l__2 radj_row_l__2.
    Exists pos_l__2.
    Exists radj_col_l__2.
    Exists radj_row_l__2.
    split_pure_spatial.
    + cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_high_level_spec) fadj_col_l_high_level_spec).
      cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_high_level_spec).
      cancel (IntArray.full radj_col_pre (m_of fadj_row_l_high_level_spec) radj_col_l__2).
      cancel (IntArray.full radj_row_pre (n_pre + 1) radj_row_l__2).
      cancel (IntArray.full pos_pre n_pre pos_l__2).
    + split_pures; dump_pre_spatial; eassumption.
  - split_pures; dump_pre_spatial; eassumption.
Qed.

Lemma proof_of_dfs2_derive_bind_spec_by_low_level_spec : dfs2_derive_bind_spec_by_low_level_spec.
Proof. intros; pre_process. apply safeExec_bind in H2 as (X_low_level_spec & Hsafe_first & Hsafe_cont). Exists g_bind_spec. Exists fadj_col_l_bind_spec. Exists fadj_row_l_bind_spec. Exists vis2_l_bind_spec. Exists sid_l_bind_spec. Exists root_v_bind_spec. Exists X_low_level_spec. split_pure_spatial. - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_bind_spec) fadj_col_l_bind_spec). cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_bind_spec). cancel (IntArray.full vis2_pre n_pre vis2_l_bind_spec). cancel (IntArray.full sid_pre n_pre sid_l_bind_spec). apply derivable1_wand_sepcon_adjoint. Intros vis2_l__2 sid_l__2. Exists vis2_l__2. Exists sid_l__2. split_pure_spatial. + cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_bind_spec) fadj_col_l_bind_spec). cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_bind_spec). cancel (IntArray.full vis2_pre n_pre vis2_l__2). cancel (IntArray.full sid_pre n_pre sid_l__2). + split_pures; dump_pre_spatial. exact H2. exact H9. unfold applyf. apply (Hsafe_cont (pre_dfs2 g_bind_spec fadj_col_l_bind_spec fadj_row_l_bind_spec vis2_l__2 sid_l__2 root_v_bind_spec) tt). exact H10. exact H11. exact H12. - split_pures; dump_pre_spatial. exact H. exact H0. exact H1. exact Hsafe_first. exact H3. exact H4. exact H5. exact H6. exact H7. exact H8. Qed.

Lemma proof_of_dfs2_derive_high_level_spec_by_low_level_spec : dfs2_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists g_high_level_spec.
  Exists fadj_col_l_high_level_spec.
  Exists fadj_row_l_high_level_spec.
  Exists vis2_l_high_level_spec.
  Exists sid_l_high_level_spec.
  Exists root_pre.
  Exists (result_state
            (pre_dfs2 g_high_level_spec fadj_col_l_high_level_spec
               fadj_row_l_high_level_spec vis2_l_high_level_spec
               sid_l_high_level_spec root_pre)
            (dfs_scc g_high_level_spec root_pre u_pre)).
  split_pure_spatial.
  - cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_high_level_spec) fadj_col_l_high_level_spec).
    cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_high_level_spec).
    cancel (IntArray.full vis2_pre n_pre vis2_l_high_level_spec).
    cancel (IntArray.full sid_pre n_pre sid_l_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros vis2_l__2 sid_l__2.
    Exists vis2_l__2.
    Exists sid_l__2.
    split_pure_spatial.
    + cancel (IntArray.full fadj_col_pre (m_of fadj_row_l_high_level_spec) fadj_col_l_high_level_spec).
      cancel (IntArray.full fadj_row_pre (n_pre + 1) fadj_row_l_high_level_spec).
      cancel (IntArray.full vis2_pre n_pre vis2_l__2).
      cancel (IntArray.full sid_pre n_pre sid_l__2).
    + unfold dfs2_high_level_post; entailer!.
  - split_pures; dump_pre_spatial.
    all: try eassumption.
    eapply safeExec_result_state.
    set (st0 := Kosaraju.MkSt 0%nat (fun _ => 0%nat) (fun _ => False)
                    (fun v => Znth v vis2_l_high_level_spec 0 <> 0)
                    (fun v => Z.to_nat (Znth v sid_l_high_level_spec 0)) 0%nat).
    exists st0.
    split.
    + unfold pre_dfs2, st0; simpl. split; intros; [tauto | reflexivity].
    + assert (Hgv : AdjGraphValid g_high_level_spec).
      { exact (proj1 H). }
      pose proof (@Kosaraju.DFS_scc_neighbor_visited_strong AdjGraph Z (Z * Z) KG
                    g_high_level_spec Hgv st0 root_pre u_pre) as Hhoare.
      destruct Hhoare as [_ Hnoerr].
      intro Herr. exact (Hnoerr st0 eq_refl Herr).
Qed. 

Lemma proof_of_dfs1_derive_bind_spec_by_low_level_spec : dfs1_derive_bind_spec_by_low_level_spec.
Proof. intros; pre_process. match goal with Hsafe : safeExec _ (bind _ _) _ |- _ => apply safeExec_bind in Hsafe as (X_low_level_spec & Hsafe_first & Hsafe_cont) end. Exists g_bind_spec. Exists radj_col_l_bind_spec. Exists radj_row_l_bind_spec. Exists vis1_l_bind_spec. Exists fin_l_bind_spec. Exists timer_v_bind_spec. Exists X_low_level_spec. split_pure_spatial. - cancel (IntArray.full radj_col_pre (m_of radj_row_l_bind_spec) radj_col_l_bind_spec). cancel (IntArray.full radj_row_pre (n_pre + 1) radj_row_l_bind_spec). cancel (IntArray.full vis1_pre n_pre vis1_l_bind_spec). cancel (IntArray.full fin_pre n_pre fin_l_bind_spec). cancel (IntArray.full timer_p_pre 1 (timer_v_bind_spec :: nil)). apply derivable1_wand_sepcon_adjoint. Intros timer_v__2 vis1_l__2 fin_l__2. Exists timer_v__2. Exists vis1_l__2. Exists fin_l__2. split_pure_spatial. + cancel (IntArray.full radj_col_pre (m_of radj_row_l_bind_spec) radj_col_l_bind_spec). cancel (IntArray.full radj_row_pre (n_pre + 1) radj_row_l_bind_spec). cancel (IntArray.full vis1_pre n_pre vis1_l__2). cancel (IntArray.full fin_pre n_pre fin_l__2). cancel (IntArray.full timer_p_pre 1 (timer_v__2 :: nil)). + split_pures; dump_pre_spatial. all: try eassumption. unfold applyf. apply (Hsafe_cont (pre_dfs1 g_bind_spec radj_col_l_bind_spec radj_row_l_bind_spec vis1_l__2 fin_l__2 timer_v__2) tt). eassumption. - split_pures; dump_pre_spatial. match goal with Hc : csr_wf1 _ _ _ _ _ |- csr_wf1 _ _ _ _ _ => exact Hc end. match goal with Hf : csr1_faithful _ _ _ |- csr1_faithful _ _ _ => exact Hf end. match goal with Ha : adj_verts _ = _ |- adj_verts _ = _ => exact Ha end. match goal with H : fin_values_in_int_range _ _ |- fin_values_in_int_range _ _ => exact H end. exact Hsafe_first. match goal with H : 0 <= u_pre |- _ => exact H end. match goal with H : u_pre < n_pre |- _ => exact H end. match goal with H : n_pre <= ?M |- _ => exact H end. match goal with H : Znth u_pre _ 0 = 0 |- _ => exact H end. match goal with H : 0 <= timer_v_bind_spec |- _ => exact H end. match goal with H : timer_v_bind_spec <= count_nonzero vis1_l_bind_spec |- _ => exact H end. Qed. 

Lemma proof_of_dfs1_derive_high_level_spec_by_low_level_spec : dfs1_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists g_high_level_spec.
  Exists radj_col_l_high_level_spec.
  Exists radj_row_l_high_level_spec.
  Exists vis1_l_high_level_spec.
  Exists fin_l_high_level_spec.
  Exists timer_v_high_level_spec.
  Exists (result_state
            (pre_dfs1 g_high_level_spec radj_col_l_high_level_spec
               radj_row_l_high_level_spec vis1_l_high_level_spec
               fin_l_high_level_spec timer_v_high_level_spec)
            (dfs_finish g_high_level_spec u_pre)).
  split_pure_spatial.
  - cancel (IntArray.full radj_col_pre (m_of radj_row_l_high_level_spec) radj_col_l_high_level_spec).
    cancel (IntArray.full radj_row_pre (n_pre + 1) radj_row_l_high_level_spec).
    cancel (IntArray.full vis1_pre n_pre vis1_l_high_level_spec).
    cancel (IntArray.full fin_pre n_pre fin_l_high_level_spec).
    cancel (IntArray.full timer_p_pre 1 (timer_v_high_level_spec :: nil)).
    apply derivable1_wand_sepcon_adjoint.
    Intros timer_v__2 vis1_l__2 fin_l__2.
    Exists vis1_l__2.
    Exists fin_l__2.
    Exists timer_v__2.
    split_pure_spatial.
    + cancel (IntArray.full radj_col_pre (m_of radj_row_l_high_level_spec) radj_col_l_high_level_spec).
      cancel (IntArray.full radj_row_pre (n_pre + 1) radj_row_l_high_level_spec).
      cancel (IntArray.full vis1_pre n_pre vis1_l__2).
      cancel (IntArray.full fin_pre n_pre fin_l__2).
      cancel (IntArray.full timer_p_pre 1 (timer_v__2 :: nil)).
    + unfold dfs1_high_level_post; entailer!; try eassumption; try lia.
      * destruct H11 as [sfin [Hpre_fin Hsafe_skip]].
        unfold safe, weakestpre in Hsafe_skip.
        destruct Hsafe_skip as [_ Hpost_skip].
        assert (Hnrm_skip : MonadErr.nrm (ret tt) sfin tt sfin).
        { apply ret_eq. split; reflexivity. }
        specialize (Hpost_skip tt sfin Hnrm_skip).
        destruct Hpost_skip as [s0 [Hpre0 Hnrm_finish]].
        assert (Hgv : AdjGraphValid g_high_level_spec).
        { exact (proj1 H). }
        assert (Hvlen : Zlength vis1_l_high_level_spec = adj_verts g_high_level_spec).
        { exact (proj1 (proj2 (proj2 H))). }
        assert (Hcount :
                  Kosaraju.count_pred (Kosaraju.visited1 s0)
                    (graph_basic.bijective_listV g_high_level_spec) =
                  Z.to_nat (count_nonzero vis1_l_high_level_spec)).
        { exact (pre_dfs1_count_pred_bijective_eq g_high_level_spec
                   radj_col_l_high_level_spec radj_row_l_high_level_spec
                   vis1_l_high_level_spec fin_l_high_level_spec
                   timer_v_high_level_spec s0 Hgv Hvlen Hpre0). }
        assert (Hcard :
                  (Kosaraju.count_pred (Kosaraju.visited1 s0)
                     (graph_basic.bijective_listV g_high_level_spec) >=
                   Kosaraju.timer s0)%nat).
        { rewrite Hcount.
          destruct Hpre0 as [_ [_ Htimer0]].
          rewrite Htimer0.
          apply Nat2Z.inj_le.
          repeat rewrite Nat2Z.id.
          rewrite Z2Nat.id by lia.
          rewrite Z2Nat.id by (apply count_nonzero_nonneg).
          lia. }
        pose proof (@Kosaraju.DFS_finish_neighbor_visited_strong AdjGraph Z (Z * Z) KG
                      g_high_level_spec Hgv s0 u_pre Hcard) as Hhoare.
        pose proof (proj1 Hhoare tt s0 sfin eq_refl Hnrm_finish) as Hpost.
        destruct Hpost as [Hvisu [_ _]].
        destruct Hpre_fin as [Hpv_fin _].
        pose proof (Hpv_fin u_pre) as Hfinu.
        specialize (Hfinu ltac:(rewrite H10; lia)).
        apply (proj1 Hfinu). exact Hvisu.
      * intros w Hw Hvisited_old.
        destruct H11 as [sfin [Hpre_fin Hsafe_skip]].
        unfold safe, weakestpre in Hsafe_skip.
        destruct Hsafe_skip as [_ Hpost_skip].
        assert (Hnrm_skip : MonadErr.nrm (ret tt) sfin tt sfin).
        { apply ret_eq. split; reflexivity. }
        specialize (Hpost_skip tt sfin Hnrm_skip).
        destruct Hpost_skip as [s0 [Hpre0 Hnrm_finish]].
        assert (Hgv : AdjGraphValid g_high_level_spec).
        { exact (proj1 H). }
        assert (Hvlen : Zlength vis1_l_high_level_spec = adj_verts g_high_level_spec).
        { exact (proj1 (proj2 (proj2 H))). }
        assert (Hcount :
                  Kosaraju.count_pred (Kosaraju.visited1 s0)
                    (graph_basic.bijective_listV g_high_level_spec) =
                  Z.to_nat (count_nonzero vis1_l_high_level_spec)).
        { exact (pre_dfs1_count_pred_bijective_eq g_high_level_spec
                   radj_col_l_high_level_spec radj_row_l_high_level_spec
                   vis1_l_high_level_spec fin_l_high_level_spec
                   timer_v_high_level_spec s0 Hgv Hvlen Hpre0). }
        assert (Hcard :
                  (Kosaraju.count_pred (Kosaraju.visited1 s0)
                     (graph_basic.bijective_listV g_high_level_spec) >=
                   Kosaraju.timer s0)%nat).
        { rewrite Hcount.
          destruct Hpre0 as [_ [_ Htimer0]].
          rewrite Htimer0.
          apply Nat2Z.inj_le.
          repeat rewrite Nat2Z.id.
          rewrite Z2Nat.id by lia.
          rewrite Z2Nat.id by (apply count_nonzero_nonneg).
          lia. }
        pose proof (@Kosaraju.DFS_finish_neighbor_visited_strong AdjGraph Z (Z * Z) KG
                      g_high_level_spec Hgv s0 u_pre Hcard) as Hhoare.
        pose proof (proj1 Hhoare tt s0 sfin eq_refl Hnrm_finish) as Hpost.
        destruct Hpost as [_ [Hmono _]].
        destruct Hpre_fin as [Hpv_fin _].
        destruct Hpre0 as [Hpv0 _].
        pose proof (Hpv_fin w) as Hfinw.
        specialize (Hfinw ltac:(rewrite H10; lia)).
        apply (proj1 Hfinw).
        apply Hmono.
        pose proof (Hpv0 w) as Hinitw.
        specialize (Hinitw ltac:(rewrite H1; exact Hw)).
        apply (proj2 Hinitw). exact Hvisited_old.
  - split_pures; dump_pre_spatial.
    all: try eassumption.
    eapply safeExec_result_state.
    set (st0 := Kosaraju.MkSt
                   (Z.to_nat timer_v_high_level_spec)
                   (fun v => Z.to_nat (Znth v fin_l_high_level_spec 0))
                   (fun v => Znth v vis1_l_high_level_spec 0 <> 0)
                   (fun _ => False)
                   (fun _ => 0%nat)
                   0%nat).
    exists st0.
    split.
    + unfold pre_dfs1, st0; simpl. split; [ intros; reflexivity | split; [ intros; reflexivity | reflexivity ] ].
    + assert (Hgv : AdjGraphValid g_high_level_spec).
      { match goal with H : csr_wf1 _ _ _ _ _ |- _ => exact (proj1 H) end. }
      assert (Hvlen : Zlength vis1_l_high_level_spec = adj_verts g_high_level_spec).
      { match goal with H : csr_wf1 _ _ _ _ _ |- _ => exact (proj1 (proj2 (proj2 H))) end. }
      assert (Hpre : pre_dfs1 g_high_level_spec radj_col_l_high_level_spec
                       radj_row_l_high_level_spec vis1_l_high_level_spec
                       fin_l_high_level_spec timer_v_high_level_spec st0).
      { unfold pre_dfs1, st0; simpl. split; [ intros; reflexivity | split; [ intros; reflexivity | reflexivity ] ]. }
      assert (Hcard :
                (Kosaraju.count_pred (Kosaraju.visited1 st0)
                   (graph_basic.bijective_listV g_high_level_spec) >=
                 Kosaraju.timer st0)%nat).
      { rewrite (pre_dfs1_count_pred_bijective_eq g_high_level_spec
                   radj_col_l_high_level_spec radj_row_l_high_level_spec
                   vis1_l_high_level_spec fin_l_high_level_spec
                   timer_v_high_level_spec st0 Hgv Hvlen Hpre).
        unfold st0; simpl.
        apply Nat2Z.inj_le.
        repeat rewrite Nat2Z.id.
        rewrite Z2Nat.id by lia.
        rewrite Z2Nat.id by (apply count_nonzero_nonneg).
        lia. }
      pose proof (@Kosaraju.DFS_finish_neighbor_visited_strong AdjGraph Z (Z * Z) KG
                    g_high_level_spec Hgv st0 u_pre Hcard) as Hhoare.
      destruct Hhoare as [_ Hnoerr].
      intro Herr. exact (Hnoerr st0 eq_refl Herr).
Qed. 
