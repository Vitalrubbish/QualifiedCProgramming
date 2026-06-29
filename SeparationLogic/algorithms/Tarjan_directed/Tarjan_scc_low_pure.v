Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From MaxMinLib Require Import MaxMin Interface.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn Tarjan_scc_low_defs.

Import SetsNotation.
Local Open Scope sets.

Section LOW_PURE.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  (* ================================================================ *)
  (* Min-value facts                                                 *)
  (* ================================================================ *)

  Lemma scc_low_witness (s: @SCCSt V) (w: V) (n: nat):
    scc_is_low_v_val g root s w n ->
    exists x, scc_low_tree g root s w x /\ dfn s x = n.
  Proof.
    unfold scc_is_low_v_val, min_value_of_subset.
    intros [a [[Ha_in Ha_min] Heq]].
    exists a. split; [exact Ha_in | exact Heq].
  Qed.

  Lemma scc_low_bound (s: @SCCSt V) (w: V) (n: nat) (x: V):
    scc_is_low_v_val g root s w n ->
    scc_low_tree g root s w x ->
    n <= dfn s x.
  Proof.
    unfold scc_is_low_v_val, min_value_of_subset.
    intros [a [[Ha_in Ha_min] Heq]] Hx_in.
    subst n. apply Ha_min. exact Hx_in.
  Qed.

  (* ================================================================ *)
  (* Reachability decomposition                                      *)
  (* ================================================================ *)

  Lemma dg_reachable_first_step (T: OriginalGraphType V E) (u z: V):
    dg_reachable T u z ->
    u = z \/ exists v, dg_step T u v /\ dg_reachable T v z.
  Proof.
    induction 1.
    - right. exists y. split; [exact H |].
      apply Coq.Relations.Relation_Operators.rt_refl.
    - left. reflexivity.
    - destruct IHclos_refl_trans1 as [Heq | [v [Hstep_uv Hreach_vy]]].
      + subst y. exact IHclos_refl_trans2.
      + right. exists v. split; [exact Hstep_uv |].
        eapply Coq.Relations.Relation_Operators.rt_trans.
        * exact Hreach_vy.
        * exact H1.
  Qed.

  (** [union_singleton_iff] reduces set-membership over a three-way
      union [ [u] ∪ P ∪ Q ] to a plain disjunction, without expanding
      [P] or [Q].  This avoids [cbv] and is much faster than [firstorder]. *)
  Lemma union_singleton_iff (w u : V) (P Q : V -> Prop) :
    (w ∈ [u] ∪ P ∪ Q) <-> (w = u \/ w ∈ P \/ w ∈ Q).
  Proof.
    cbv. split; intros; intuition.
  Qed.

  Lemma scc_low_tree_decompose (s: @SCCSt V) (u: V):
    u ∈ visited s ->
    scc_low_tree g root s u ==
    [u] ∪ scc_back_edge g root s u ∪
    (fun w => exists v,
      dg_step (state_to_dfs_tree g s root) u v /\
      scc_low_tree g root s v w).
  Proof.
    intros Hu.
    unfold scc_low_tree, scc_low_reachable.
    intros w. split; intros Hw.
    - (* -> direction *)
      destruct Hw as [z [Hreach Hz_case]].
      apply dg_reachable_first_step in Hreach as [Heq | [v [Hstep Hreach_v]]].
      + (* u = z *)
        subst z.
        apply union_singleton_iff.
        destruct Hz_case as [<- | Hback]; [left | right; left]; auto.
      + (* u -> v ->* z in tree *)
        apply union_singleton_iff. right. right.
        exists v. split; [exact Hstep | exists z; auto].
    - (* <- direction *)
      apply union_singleton_iff in Hw.
      destruct Hw as [Heq_w | [Hback | [v [Hstep [z [Hreach Hz_case]]]]]].
      + subst w. exists u; split; [apply Coq.Relations.Relation_Operators.rt_refl | auto].
      + exists u; split; [apply Coq.Relations.Relation_Operators.rt_refl | auto].
      + exists z; split.
        * eapply Coq.Relations.Relation_Operators.rt_trans.
          -- apply Coq.Relations.Relation_Operators.rt_step. exact Hstep.
          -- exact Hreach.
        * exact Hz_case.
  Qed.

  (* ================================================================ *)
  (* Low-valid to public low-link bridge                             *)
  (* ================================================================ *)

  Lemma scc_is_low_induction (s: @SCCSt V) (u: V)
    (IHu: forall v,
      dg_step (state_to_dfs_tree g s root) u v ->
      scc_is_low_v_val g root s v (low s v)):
    min_value_of_subset Nat.le
      (dg_step (state_to_dfs_tree g s root) u) (low s) ==
    min_value_of_subset Nat.le
      ((fun w => exists v,
        dg_step (state_to_dfs_tree g s root) u v /\
        scc_low_tree g root s v w))
      (dfn s).
  Proof.
    intros n. split; intros Hn.
    - (* S1 n -> S2 n *)
      eapply (@min_eq_forward' _ Nat.le NatLe_TotalOrder); [exact Hn | |].
      + intros v Hv.
        specialize (IHu v Hv).
        apply scc_low_witness in IHu as [w [Hw Heq]].
        exists w. split; [| rewrite Heq; apply Nat.le_refl].
        exists v. split; [exact Hv | exact Hw].
      + intros w [v [Hv Hw]].
        exists v. split; [exact Hv |].
        specialize (IHu v Hv).
        eapply scc_low_bound; [exact IHu | exact Hw].
    - (* S2 n -> S1 n *)
      eapply (@min_eq_forward' _ Nat.le NatLe_TotalOrder); [exact Hn | |].
      + intros w [v [Hv Hw]].
        exists v. split; [exact Hv |].
        specialize (IHu v Hv).
        eapply scc_low_bound; [exact IHu | exact Hw].
      + intros v Hv.
        specialize (IHu v Hv).
        apply scc_low_witness in IHu as [w [Hw Heq]].
        exists w. split; [| rewrite Heq; apply Nat.le_refl].
        exists v. split; [exact Hv | exact Hw].
  Qed.

  Lemma scc_is_low_induction_is_low (s: @SCCSt V) (u: V)
    (Hu: u ∈ visited s)
    (IHu: forall v,
      dg_step (state_to_dfs_tree g s root) u v ->
      scc_is_low_v_val g root s v (low s v)):
    scc_low_valid_v g root s u -> scc_is_low_v g root s u.
  Proof.
    intros Hvalid.
    unfold scc_low_valid_v in Hvalid.
    rewrite scc_is_low_induction in Hvalid; auto.
    apply min_union_iff in Hvalid.
    unfold scc_is_low_v, scc_is_low_v_val.
    rewrite scc_low_tree_decompose; auto.
    rewrite (Sets_union_comm [u] (scc_back_edge g root s u)).
    rewrite Sets_union_comm.
    exact Hvalid.
  Qed.

  Lemma scc_low_valid_implies_is_low (s: @SCCSt V):
    dfn_valid g s root ->
    dfn_inv s ->
    scc_low_valid g root s ->
    scc_is_low g root s.
  Proof.
    intros Hvalid Hinv Hlow.
    destruct Hinv as [Hdfn_lt [Hdfn_zero Hpos]].
    unfold scc_is_low.
    cut (forall n u, u ∈ visited s ->
           timer s - dfn s u = n -> scc_is_low_v g root s u).
    { intros H u Hu. apply H with (n := timer s - dfn s u); auto. }
    induction n as [n IH] using (well_founded_induction (Nat.lt_wf 0)).
    intros u Hu Hn.
    apply (scc_is_low_induction_is_low s u Hu).
    - intros v Hson_orig.
      pose proof Hson_orig as Hson_for_step.
      apply tree_step_char in Hson_for_step.
      destruct Hson_for_step as [_ [_ Hvis_v]].
      apply Hvalid in Hson_orig.
      pose proof (Hdfn_lt u Hu) as Hdfn_u_lt.
      pose proof (Hdfn_lt v Hvis_v) as Hdfn_v_lt.
      apply (IH (timer s - dfn s v)).
      + lia.
      + exact Hvis_v.
      + reflexivity.
    - apply Hlow. exact Hu.
  Qed.

  Lemma scc_low_valid_v_bound_self (s: @SCCSt V) (u: V):
    scc_low_valid_v g root s u ->
    low s u <= dfn s u.
  Proof.
    unfold scc_low_valid_v, min_value_of_subset, min_object_of_subset.
    intros [n [[_ Hbound] Hlow]].
    rewrite <- Hlow.
    pose proof (min_nonempty_exists
                  (fun x => dfn s x)
                  (scc_back_edge g root s u ∪ [u])) as Hmin.
    destruct Hmin as [m Hm].
    { exists u. sets_unfold. right. reflexivity. }
    specialize (Hbound m).
    assert (Hm_outer :
              (min_value_of_subset Nat.le
                 (scc_back_edge g root s u ∪ [u]) (dfn s)) m).
    { exact Hm. }
    specialize (Hbound (or_intror Hm_outer)).
    destruct Hm as [x [[Hx Hmin_x] Hm_eq]].
    rewrite <- Hm_eq in Hbound.
    eapply Nat.le_trans; [exact Hbound |].
    apply Hmin_x.
    right.
    reflexivity.
  Qed.

  (* ================================================================ *)
  (* Setoid support for local iteration invariants                   *)
  (* ================================================================ *)

  Lemma done_visited_proper:
    Proper (Sets.equiv ==> eq ==> iff) (@done_visited V).
  Proof.
    unfold Proper, respectful, done_visited.
    intros done1 done2 Hequiv s1 s2 Heq_s.
    subst s2. split; intros H w Hw.
    - apply H. destruct (Hequiv w) as [_ Hbw]. apply Hbw. exact Hw.
    - apply H. destruct (Hequiv w) as [Hfw _]. apply Hfw. exact Hw.
  Qed.

  Lemma low_src_proper (u: V) (s: @SCCSt V):
    Proper (Sets.equiv ==> iff) (fun done => low_src g u done s).
  Proof.
    unfold Proper, respectful, low_src.
    intros done1 done2 Hequiv.
    split; intros Hsrc.
    - destruct Hsrc as [Hlow | [(v & Hv & Hrest) | (w & Hw & Hrest)]].
      + left. exact Hlow.
      + right. left. exists v. split.
        * apply Hequiv. exact Hv.
        * exact Hrest.
      + right. right. exists w. split.
        * apply Hequiv. exact Hw.
        * exact Hrest.
    - destruct Hsrc as [Hlow | [(v & Hv & Hrest) | (w & Hw & Hrest)]].
      + left. exact Hlow.
      + right. left. exists v. split.
        * apply Hequiv. exact Hv.
        * exact Hrest.
      + right. right. exists w. split.
        * apply Hequiv. exact Hw.
        * exact Hrest.
  Qed.

  Lemma low_iteration_inv_proper (u: V):
    Proper (Sets.equiv ==> eq ==> iff) (low_iteration_inv g root u).
  Proof.
    unfold Proper, respectful.
    intros done1 done2 Hequiv s1 s2 Heq_s.
    subst s2.
    unfold low_iteration_inv.
    split; intros H; destruct H as [Hwf [Hvis [Hstack [Hdv [Hfront [Hsrc [Hchild [Hfa_child Hfa_not]]]]]]]].
    - (* done1 -> done2 *)
      destruct Hwf as [Hstack_in [Hdfn_inv [Hdfn_valid Hfa_visited]]].
      destruct Hdfn_inv as [Hdfn_lt [Hdfn0 Htimer_pos]].
      destruct Hfront as [Hlow_le Hfront'].
      repeat split; auto.
      + (* dfn0 -> *)
        apply Hdfn0.
      + (* dfn0 <- *)
        apply Hdfn0.
      + (* done_visited *)
        intros w Hw. apply Hdv. apply (proj2 (Hequiv w)). exact Hw.
      + (* low_frontier: fa direction *)
        intros Hfa_eq.
        specialize (Hfront' v (proj2 (Hequiv v) H) H1) as [Hfa_part _].
        apply Hfa_part. exact Hfa_eq.
      + (* low_frontier: stack direction *)
        intros Hinstack.
        specialize (Hfront' v (proj2 (Hequiv v) H) H1) as [_ Hstack_part].
        apply Hstack_part. exact Hinstack.
      + (* low_src *)
        destruct Hsrc as [Hlow | [(v1 & Hv1 & Hrest1) | (w1 & Hw1 & Hrest1)]].
        * left. exact Hlow.
        * right. left. exists v1. split; [apply (proj1 (Hequiv v1)); exact Hv1 | exact Hrest1].
        * right. right. exists w1. split; [apply (proj1 (Hequiv w1)); exact Hw1 | exact Hrest1].
      + (* children_low_valid *)
        intros v1 Hv1. apply Hchild. apply (proj2 (Hequiv v1)). exact Hv1.
      + (* fa_not_done_implies_eq_u *)
        intros v1 Hnv1. apply Hfa_not. intro Hv1. apply Hnv1. apply (proj1 (Hequiv v1)). exact Hv1.
    - (* done2 -> done1 *)
      destruct Hwf as [Hstack_in [Hdfn_inv [Hdfn_valid Hfa_visited]]].
      destruct Hdfn_inv as [Hdfn_lt [Hdfn0 Htimer_pos]].
      destruct Hfront as [Hlow_le Hfront'].
      repeat split; auto.
      + apply Hdfn0.
      + apply Hdfn0.
      + intros w Hw. apply Hdv. apply (proj1 (Hequiv w)). exact Hw.
      + intros Hfa_eq.
        specialize (Hfront' v (proj1 (Hequiv v) H) H1) as [Hfa_part _].
        apply Hfa_part. exact Hfa_eq.
      + intros Hinstack.
        specialize (Hfront' v (proj1 (Hequiv v) H) H1) as [_ Hstack_part].
        apply Hstack_part. exact Hinstack.
      + destruct Hsrc as [Hlow | [(v1 & Hv1 & Hrest1) | (w1 & Hw1 & Hrest1)]].
        * left. exact Hlow.
        * right. left. exists v1. split; [apply (proj2 (Hequiv v1)); exact Hv1 | exact Hrest1].
        * right. right. exists w1. split; [apply (proj2 (Hequiv w1)); exact Hw1 | exact Hrest1].
      + intros v1 Hv1. apply Hchild. apply (proj1 (Hequiv v1)). exact Hv1.
      + intros v1 Hnv1. apply Hfa_not. intro Hv1. apply Hnv1. apply (proj2 (Hequiv v1)). exact Hv1.
  Qed.

  Lemma low_frontier_and_src_imply_low_valid (u: V) (s: @SCCSt V):
    low_iteration_done g root u s ->
    scc_low_valid_v g root s u.
  Proof.
    intros [Hiter [_ _]].
    unfold low_iteration_inv in Hiter.
    destruct Hiter as
      [Hwf [Huvis [Hustack [Hdone_vis [Hfront [Hsrc [Hchild [Hfa_child Hfa_not]]]]]]]].
    unfold low_frontier in Hfront.
    destruct Hfront as [Hlow_dfn Hfront].
    unfold scc_low_valid_v, min_value_of_subset, min_object_of_subset.
    exists (low s u). split.
    - split.
      + unfold low_src in Hsrc.
        destruct Hsrc as [Hlow_eq | [(v & Hv_done & Hdg & Hfa & Hfa_ne & Hlow_eq) |
                                    (w & Hw_done & Hdg & Hstack_w & Hfa_ne & Hlow_eq)]].
        * right.
          exists u. split.
          -- split.
             ++ sets_unfold. right. reflexivity.
             ++ intros x Hx. sets_unfold in Hx.
                destruct Hx as [Hback | Heq_x].
                ** destruct Hback as [Hdg_x [Hstack_x _]].
                   rewrite <- Hlow_eq.
                   destruct (Hfront x Hdg_x Hdg_x) as [_ Hstack_part].
                   apply Hstack_part. exact Hstack_x.
                ** subst x. rewrite <- Hlow_eq. apply Nat.le_refl.
          -- symmetry. exact Hlow_eq.
        * left.
          assert (Hvis_v : v ∈ visited s) by (apply Hdone_vis; exact Hv_done).
          assert (Htree_v : dg_step (state_to_dfs_tree g s root) u v).
          { apply tree_step_char_backward; auto. }
          exists v. split.
          -- split.
             ++ exact Htree_v.
             ++ intros x Htree_x.
                apply tree_step_char in Htree_x as [Hfa_x [Hfa_ne_x _]].
                assert (Hdg_x : dg_step g u x).
                { apply Hfa_child. split; [exact Hfa_x | exact Hfa_ne_x]. }
                rewrite <- Hlow_eq.
                destruct (Hfront x Hdg_x Hdg_x) as [Hfa_part _].
                apply Hfa_part. exact Hfa_x.
          -- symmetry. exact Hlow_eq.
        * right.
          exists w. split.
          -- split.
             ++ sets_unfold. left.
                unfold scc_back_edge.
                split; [exact Hdg | split; [exact Hstack_w |]].
                intro Htree.
                apply tree_step_char in Htree as [Hfa_w [_ _]].
                apply Hfa_ne. exact Hfa_w.
             ++ intros x Hx. sets_unfold in Hx.
                destruct Hx as [Hback | Heq_x].
                ** destruct Hback as [Hdg_x [Hstack_x _]].
                   rewrite <- Hlow_eq.
                   destruct (Hfront x Hdg_x Hdg_x) as [_ Hstack_part].
                   apply Hstack_part. exact Hstack_x.
                ** subst x. rewrite <- Hlow_eq. exact Hlow_dfn.
          -- symmetry. exact Hlow_eq.
      + intros n Hn.
        destruct Hn as [Hmin_child | Hmin_back].
        * unfold min_value_of_subset, min_object_of_subset in Hmin_child.
          destruct Hmin_child as [x [[Htree_x _] Hn_eq]].
          subst n.
          apply tree_step_char in Htree_x as [Hfa_x [Hfa_ne_x _]].
          assert (Hdg_x : dg_step g u x).
          { apply Hfa_child. split; [exact Hfa_x | exact Hfa_ne_x]. }
          destruct (Hfront x Hdg_x Hdg_x) as [Hfa_part _].
          apply Hfa_part. exact Hfa_x.
        * unfold min_value_of_subset, min_object_of_subset in Hmin_back.
          destruct Hmin_back as [x [[Hx _] Hn_eq]].
          subst n. sets_unfold in Hx.
          destruct Hx as [Hback | Heq_x].
          -- destruct Hback as [Hdg_x [Hstack_x _]].
             destruct (Hfront x Hdg_x Hdg_x) as [_ Hstack_part].
             apply Hstack_part. exact Hstack_x.
          -- subst x. exact Hlow_dfn.
    - reflexivity.
  Qed.

End LOW_PURE.
