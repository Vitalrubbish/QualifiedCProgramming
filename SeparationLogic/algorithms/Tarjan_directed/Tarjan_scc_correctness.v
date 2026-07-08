Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Classical_Prop.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From MaxMinLib Require Import MaxMin.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn
  Tarjan_scc_is_low.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section SCC_OUTPUT_CORRECTNESS.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  Local Definition St : Type := @SCCSt V.

  Definition Visited (u: V) (s: St): Prop :=
    visited s u.

  Definition Active (u: V) (s: St): Prop :=
    In u (stack s).

  (* Output correctness needs graph validity of emitted SCC members.
     This is intentionally separated from the low-link invariant: low and
     closedness only need visited/active structure, while [is_SCC] needs
     original-graph validity. *)
  Definition VisitedValid (s: St): Prop :=
    forall v, Visited v s -> original_vvalid g v.

  (* Every SCC set already emitted by [pop_scc] is a mathematical SCC of
     the original directed graph. *)
  Definition SCCsSound (s: St): Prop :=
    forall C,
      In C (sccs s) ->
      is_SCC g C.

  (* Every visited vertex that has left the active DFS stack is covered by
     one of the emitted SCC sets. *)
  Definition SCCsCoverSettled (s: St): Prop :=
    forall v,
      Visited v s ->
      ~ Active v s ->
      exists C, In C (sccs s) /\ C v.

  (* Output-layer invariant carried by the Monad proof.  Disjointness is
     intentionally not included: after [SCCsSound], overlap of two emitted
     SCCs can be converted to extensional equality at the final partition
     bridge. *)
  Definition SCCsOutputInv (s: St): Prop :=
    SCCsSound s /\
    SCCsCoverSettled s.

  (* Final-bridge predicate: after [tarjan_scc_all], all valid vertices
     should have been visited.  This is already available from the basics
     layer as [tarjan_scc_all_visited_all]. *)
  Definition AllVerticesVisited (s: St): Prop :=
    forall v, original_vvalid g v -> Visited v s.

  (* State shape sufficient to turn [SCCsOutputInv] into
     [scc_partition g (sccs s)]. *)
  Definition SCCsPartitionReady (s: St): Prop :=
    AllVerticesVisited s /\
    stack s = nil /\
    SCCsOutputInv s.

  Lemma root_pop_branch_pre_loop_core_shape
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    LoopCoreShape g root u (edge_set g u) s.
  Proof.
    intros Hpre.
    destruct Hpre as [[Hloop _] _].
    destruct Hloop as [_ [Hshape _]].
    exact Hshape.
  Qed.

  Lemma root_pop_branch_pre_stack_rest_older
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    StackRestOlderThanRoot u s.
  Proof.
    intros Hpre.
    destruct Hpre as [[_ Hrest] _].
    exact Hrest.
  Qed.

  Lemma root_pop_branch_pre_active_root
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    Active u s.
  Proof.
    intros Hpre.
    destruct (root_pop_branch_pre_stack_rest_older u s Hpre)
      as [Hactive _].
    exact Hactive.
  Qed.

  Lemma root_pop_branch_pre_visited_root
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    Visited u s.
  Proof.
    intros Hpre.
    destruct (root_pop_branch_pre_loop_core_shape u s Hpre)
      as [_ [_ [Hu_visited _]]].
    exact Hu_visited.
  Qed.

  Lemma root_in_popped_segment
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    PoppedSegment u s u.
  Proof.
    intros Hpre.
    pose proof (root_pop_branch_pre_active_root u s Hpre) as Hactive.
    unfold PoppedSegment, Active in *.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    eapply stack_split_at_root_in_popped; eauto.
  Qed.

  Lemma popped_segment_nonempty_valid
        (u: V) (s: St):
    VisitedValid s ->
    RootPopBranchPre g root u s ->
    exists x, PoppedSegment u s x /\ original_vvalid g x.
  Proof.
    intros Hvalid Hpre.
    exists u.
    split.
    - apply root_in_popped_segment. exact Hpre.
    - apply Hvalid.
      apply root_pop_branch_pre_visited_root. exact Hpre.
  Qed.

  Lemma root_pop_branch_pre_wf_scc_state
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    wf_scc_state g root s.
  Proof.
    intros Hpre.
    destruct (root_pop_branch_pre_loop_core_shape u s Hpre)
      as [Hwf _].
    exact Hwf.
  Qed.

  Lemma root_pop_branch_pre_tree_edges_are_graph_edges
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    TreeEdgesAreGraphEdges g root s.
  Proof.
    intros Hpre.
    destruct (root_pop_branch_pre_loop_core_shape u s Hpre)
      as [_ [Htree _]].
    exact Htree.
  Qed.

  Lemma root_pop_branch_pre_stack_no_dup
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    StackNoDup s.
  Proof.
    intros Hpre.
    destruct Hpre as [[[Haux _] _] _].
    destruct Haux as [_ [_ [_ [_ Hnodup]]]].
    exact Hnodup.
  Qed.

  Lemma root_pop_branch_pre_closed
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    Closed g s.
  Proof.
    intros Hpre.
    destruct Hpre as [[Hloop _] _].
    destruct Hloop as [_ [_ [Hclosed _]]].
    exact Hclosed.
  Qed.

  Lemma popped_segment_member_active
        (u x: V) (s: St):
    RootPopBranchPre g root u s ->
    PoppedSegment u s x ->
    Active x s.
  Proof.
    intros _ Hpopped.
    unfold PoppedSegment, Active in *.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    exact (stack_split_at_in_original
             (stack s) u x popped rest Hsplit (or_introl Hpopped)).
  Qed.

  Lemma popped_segment_member_visited
        (u x: V) (s: St):
    RootPopBranchPre g root u s ->
    PoppedSegment u s x ->
    Visited x s.
  Proof.
    intros Hpre Hpopped.
    pose proof (popped_segment_member_active u x s Hpre Hpopped)
      as Hactive.
    destruct (root_pop_branch_pre_wf_scc_state u s Hpre)
      as [Hstack_in_visited _].
    apply Hstack_in_visited. exact Hactive.
  Qed.

  Lemma popped_segment_member_valid
        (u x: V) (s: St):
    VisitedValid s ->
    RootPopBranchPre g root u s ->
    PoppedSegment u s x ->
    original_vvalid g x.
  Proof.
    intros Hvalid Hpre Hpopped.
    apply Hvalid.
    eapply popped_segment_member_visited; eauto.
  Qed.

  Lemma popped_segment_self_reachable
        (u x: V) (s: St):
    VisitedValid s ->
    RootPopBranchPre g root u s ->
    PoppedSegment u s x ->
    dg_reachable g x x.
  Proof.
    intros Hvalid Hpre Hpopped.
    apply dg_reachable_refl.
    eapply popped_segment_member_valid; eauto.
  Qed.

  Lemma popped_segment_self_mutually_reachable
        (u x: V) (s: St):
    VisitedValid s ->
    RootPopBranchPre g root u s ->
    PoppedSegment u s x ->
    mutually_reachable g x x.
  Proof.
    intros Hvalid Hpre Hpopped.
    apply mutually_reachable_refl.
    eapply popped_segment_member_valid; eauto.
  Qed.

  Definition PoppedSegmentReachableFromRoot
             (u: V) (s: St): Prop :=
    forall x,
      PoppedSegment u s x ->
      dg_reachable g u x.

  Definition PoppedSegmentTreeReachableFromRoot
             (u: V) (s: St): Prop :=
    forall x,
      PoppedSegment u s x ->
      dg_reachable (state_to_dfs_tree g s root) u x.

  Definition PoppedSegmentInPartialTree
             (u: V) (s: St): Prop :=
    forall x,
      PoppedSegment u s x ->
      PartialTree g root u (edge_set g u) s x.

  Definition PoppedSegmentReachesRoot
             (u: V) (s: St): Prop :=
    forall x,
      PoppedSegment u s x ->
      dg_reachable g x u.

  Definition PoppedNonrootHasLowerPoppedTarget
             (u: V) (s: St): Prop :=
    forall x,
      PoppedSegment u s x ->
      x <> u ->
      exists y,
        PoppedSegment u s y /\
        dfn s y < dfn s x /\
        dg_reachable g x y.

  Definition PoppedSegmentPendingLow
             (u: V) (s: St): Prop :=
    forall x,
      PoppedSegment u s x ->
      x <> u ->
      scc_is_low_v g root s x /\ low s x <> dfn s x.

  Definition PoppedSegmentMaximal
             (u: V) (s: St): Prop :=
    forall x y,
      PoppedSegment u s x ->
      original_vvalid g y ->
      mutually_reachable g x y ->
      PoppedSegment u s y.

  Lemma popped_segment_maximal
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    RootPopCuts g u s ->
    PoppedSegmentMaximal u s.
  Proof.
    intros Hpre [Hpopped_closed Hno_active_reach].
    unfold PoppedSegmentMaximal.
    intros x y Hx _ [Hxy Hyx].
    pose proof (Hpopped_closed x y Hx Hxy) as Hvis_y.
    destruct (classic (Active y s)) as [Hactive_y | Hnot_active_y].
    - unfold Active in Hactive_y.
      unfold PoppedSegment.
      destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
      destruct (stack_split_at_in_cases
                  (stack s) u y popped rest Hsplit Hactive_y)
        as [Hy_popped | Hy_rest].
      + exact Hy_popped.
      + exfalso.
        eapply Hno_active_reach.
        * exact Hx.
        * exact Hxy.
        * unfold RestStack. rewrite Hsplit. exact Hy_rest.
    - pose proof (root_pop_branch_pre_closed u s Hpre) as Hclosed.
      pose proof (popped_segment_member_active u x s Hpre Hx) as Hactive_x.
      exfalso.
      eapply Hclosed; eauto.
  Qed.

  Lemma partial_tree_to_tree_reachable
        (u x: V) (s: St):
    LoopCoreShape g root u (edge_set g u) s ->
    PartialTree g root u (edge_set g u) s x ->
    dg_reachable (state_to_dfs_tree g s root) u x.
  Proof.
    intros Hshape Hpartial.
    destruct Hpartial as [Hx_eq_u | Hchild].
    - subst x. apply dg_reachable_refl'.
    - destruct Hchild as
        [child [Hdone_child [Hedge_child
          [Hfa_child [Hfane_child Hreach_child_x]]]]].
      destruct Hshape as [_ [_ [_ [_ [Hdone_vis _]]]]].
      assert (Hchild_vis: Visited child s).
      { apply Hdone_vis. exact Hdone_child. }
      assert (Htree_u_child:
                dg_step (state_to_dfs_tree g s root) u child).
      { eapply tree_step_char_backward; eauto. }
      eapply dg_reachable_trans.
      + apply dg_reachable_step. exact Htree_u_child.
      + exact Hreach_child_x.
  Qed.

  Lemma popped_segment_tree_reachable_from_partial_tree
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    PoppedSegmentInPartialTree u s ->
    PoppedSegmentTreeReachableFromRoot u s.
  Proof.
    intros Hpre Hpartial x Hpopped.
    eapply partial_tree_to_tree_reachable.
    - apply root_pop_branch_pre_loop_core_shape. exact Hpre.
    - apply Hpartial. exact Hpopped.
  Qed.

  Lemma popped_segment_in_partial_tree_from_tree_reachable
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    PoppedSegmentTreeReachableFromRoot u s ->
    PoppedSegmentInPartialTree u s.
  Proof.
    intros Hpre Htree_reach x Hpopped.
    pose proof (Htree_reach x Hpopped) as Hreach.
    pose proof (root_pop_branch_pre_tree_edges_are_graph_edges u s Hpre)
      as Htree_sound.
    destruct (tree_reachable_from_root_cases g root s u x
                Htree_sound Hreach)
      as [Hx_eq_u | [child [Hedge [Hfa [Hfane Hchild_reach]]]]].
    - subst x. apply partial_tree_root.
    - unfold PartialTree. right.
      exists child. repeat split; auto.
  Qed.

  Lemma popped_nonroot_has_lower_popped_target_from_pending_low
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    RootPopCuts g u s ->
    PoppedSegmentPendingLow u s ->
    PoppedNonrootHasLowerPoppedTarget u s.
  Proof.
    intros Hpre [_ Hno_active_reach] Hpending.
    unfold PoppedNonrootHasLowerPoppedTarget.
    intros x Hpopped Hx_ne_u.
    destruct (Hpending x Hpopped Hx_ne_u) as [Hx_low Hlow_ne].
    unfold scc_is_low_v, scc_is_low_v_val in Hx_low.
    unfold min_value_of_subset in Hx_low.
    destruct Hx_low as [target [[Htarget_low Htarget_min] Hlow_eq]].
    assert (Hx_self_target: scc_low_tree g root s x x).
    { unfold scc_low_tree, scc_low_reachable.
      exists x. split.
      - apply dg_reachable_refl'.
      - left. reflexivity. }
    pose proof (Htarget_min x Hx_self_target) as Htarget_le_x.
    assert (Htarget_lt_x: dfn s target < dfn s x).
    { rewrite Hlow_eq in Htarget_le_x.
      lia. }
    unfold scc_low_tree, scc_low_reachable in Htarget_low.
    destruct Htarget_low as [z [Htree_x_z [Hz_eq_target | Hback]]].
    - exfalso.
      subst target.
      pose proof (root_pop_branch_pre_wf_scc_state u s Hpre) as Hwf.
      pose proof (tree_reachable_dfn_monotone g root s x z Hwf Htree_x_z)
        as Hx_le_z.
      lia.
    - unfold scc_back_edge in Hback.
      destruct Hback as [Hedge_z_target [Hactive_target _]].
      pose proof (root_pop_branch_pre_tree_edges_are_graph_edges u s Hpre)
        as Htree_sound.
      assert (Hreach_x_z: dg_reachable g x z).
      { eapply tree_reachable_to_graph_reachable; eauto. }
      assert (Hreach_x_target: dg_reachable g x target).
      { eapply dg_reachable_trans.
        - exact Hreach_x_z.
        - apply dg_reachable_step. exact Hedge_z_target. }
      assert (Htarget_popped: PoppedSegment u s target).
      { unfold Active in Hactive_target.
        unfold PoppedSegment.
        destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
        destruct (stack_split_at_in_cases
                    (stack s) u target popped rest Hsplit
                    Hactive_target)
          as [Htarget_popped | Htarget_rest].
        - exact Htarget_popped.
        - exfalso.
          eapply Hno_active_reach.
          + exact Hpopped.
          + exact Hreach_x_target.
          + unfold RestStack. rewrite Hsplit. exact Htarget_rest. }
      exists target. repeat split; auto.
  Qed.

  Lemma popped_segment_reaches_root_from_lower_targets
        (u: V) (s: St):
    PoppedNonrootHasLowerPoppedTarget u s ->
    PoppedSegmentReachesRoot u s.
  Proof.
    intros Hlower x Hx.
    assert (Hmain:
              forall n y,
                dfn s y <= n ->
                PoppedSegment u s y ->
                dg_reachable g y u).
    { induction n as [| n IH].
      - intros y Hy_le_n Hy_popped.
        destruct (classic (y = u)) as [Hy_eq_u | Hy_ne_u].
        + subst y. apply dg_reachable_refl'.
        + destruct (Hlower y Hy_popped Hy_ne_u)
            as [target [_ [Htarget_lt _]]].
          lia.
      - intros y Hy_le_n Hy_popped.
        destruct (classic (y = u)) as [Hy_eq_u | Hy_ne_u].
        + subst y. apply dg_reachable_refl'.
        + destruct (Hlower y Hy_popped Hy_ne_u)
            as [target [Htarget_popped [Htarget_lt Hreach_target]]].
          eapply dg_reachable_trans.
          * exact Hreach_target.
          * apply IH.
            -- lia.
            -- exact Htarget_popped. }
    apply (Hmain (dfn s x)); [lia | exact Hx].
  Qed.

  Lemma popped_segment_members_mutually_reachable
        (u x y: V) (s: St):
    PoppedSegmentReachableFromRoot u s ->
    PoppedSegmentReachesRoot u s ->
    PoppedSegment u s x ->
    PoppedSegment u s y ->
    mutually_reachable g x y.
  Proof.
    intros Hfrom_root Hto_root Hx Hy.
    split.
    - eapply dg_reachable_trans.
      + apply Hto_root. exact Hx.
      + apply Hfrom_root. exact Hy.
    - eapply dg_reachable_trans.
      + apply Hto_root. exact Hy.
      + apply Hfrom_root. exact Hx.
  Qed.

  Lemma popped_segment_tree_reachable_lifts_to_graph
        (u: V) (s: St):
    RootPopBranchPre g root u s ->
    PoppedSegmentTreeReachableFromRoot u s ->
    PoppedSegmentReachableFromRoot u s.
  Proof.
    intros Hpre Htree_reach x Hpopped.
    eapply tree_reachable_to_graph_reachable.
    - exact (root_pop_branch_pre_tree_edges_are_graph_edges u s Hpre).
    - apply Htree_reach. exact Hpopped.
  Qed.

  Lemma popped_segment_is_scc_from_reachability_cuts
        (u: V) (s: St):
    VisitedValid s ->
    RootPopBranchPre g root u s ->
    PoppedSegmentReachableFromRoot u s ->
    PoppedSegmentReachesRoot u s ->
    PoppedSegmentMaximal u s ->
    is_SCC g (PoppedSegment u s).
  Proof.
    intros Hvalid Hpre Hfrom_root Hto_root Hmaximal.
    split.
    - eapply popped_segment_nonempty_valid; eauto.
    - split.
      + intros x y Hx Hy.
        eapply popped_segment_members_mutually_reachable; eauto.
      + intros x y Hx Hy_valid Hxy.
        eapply Hmaximal; eauto.
  Qed.

  Lemma pop_scc_preserves_sccs_sound_from_new_scc
        (u: V):
    Hoare
      (fun s: St =>
         SCCsSound s /\
         is_SCC g (PoppedSegment u s))
      (pop_scc u)
      (fun _ s => SCCsSound s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hsound Hnew_scc] Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold SCCsSound.
    intros C HC.
    unfold pop_scc_state in HC.
    destruct (stack_split_at (stack s1) u) as [popped rest] eqn:Hsplit.
    simpl in HC.
    destruct HC as [HC_head | HC_old].
    - subst C.
      unfold PoppedSegment in Hnew_scc.
      rewrite Hsplit in Hnew_scc.
      exact Hnew_scc.
    - apply Hsound. exact HC_old.
  Qed.

  Lemma pop_scc_preserves_cover_settled
        (u: V):
    Hoare
      (SCCsCoverSettled)
      (pop_scc u)
      (fun _ s => SCCsCoverSettled s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 Hcover Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold SCCsCoverSettled.
    intros v Hvis Hnot_active.
    unfold pop_scc_state in *.
    destruct (stack_split_at (stack s1) u) as [popped rest] eqn:Hsplit.
    simpl in *.
    destruct (classic (In v popped)) as [Hv_popped | Hv_not_popped].
    - exists (fun x => In x popped).
      split.
      + simpl. left. reflexivity.
      + exact Hv_popped.
    - destruct (Hcover v) as [C [HC_in HC_v]].
      + exact Hvis.
      + unfold Active.
        intros Hv_stack.
        destruct (stack_split_at_in_cases
                    (stack s1) u v popped rest Hsplit Hv_stack)
          as [Hv_popped | Hv_rest].
        * exact (Hv_not_popped Hv_popped).
        * apply Hnot_active. exact Hv_rest.
      + exists C. split.
        * simpl. right. exact HC_in.
        * exact HC_v.
  Qed.

  Lemma pop_scc_preserves_sccs_sound_from_reachability_cuts
        (u: V):
    Hoare
      (fun s: St =>
         SCCsSound s /\
         VisitedValid s /\
         RootPopBranchPre g root u s /\
         PoppedSegmentReachableFromRoot u s /\
         PoppedSegmentReachesRoot u s /\
         PoppedSegmentMaximal u s)
      (pop_scc u)
      (fun _ s => SCCsSound s).
  Proof.
    eapply Hoare_conseq_pre.
    2: apply pop_scc_preserves_sccs_sound_from_new_scc.
    intros s
      [Hsound [Hvalid [Hpre [Hfrom_root [Hto_root Hmaximal]]]]].
    split; [exact Hsound |].
    eapply popped_segment_is_scc_from_reachability_cuts; eauto.
  Qed.

  Lemma pop_scc_preserves_sccs_sound_from_tree_reachability_cuts
        (u: V):
    Hoare
      (fun s: St =>
         SCCsSound s /\
         VisitedValid s /\
         RootPopBranchPre g root u s /\
         PoppedSegmentTreeReachableFromRoot u s /\
         PoppedSegmentReachesRoot u s /\
         PoppedSegmentMaximal u s)
      (pop_scc u)
      (fun _ s => SCCsSound s).
  Proof.
    eapply Hoare_conseq_pre.
    2: apply pop_scc_preserves_sccs_sound_from_reachability_cuts.
    intros s
      [Hsound [Hvalid [Hpre [Htree_reach [Hto_root Hmaximal]]]]].
    split; [exact Hsound |].
    split; [exact Hvalid |].
    split; [exact Hpre |].
    split.
    - eapply popped_segment_tree_reachable_lifts_to_graph; eauto.
    - exact (conj Hto_root Hmaximal).
  Qed.

  Lemma popped_segment_is_scc_from_core_cuts
        (u: V) (s: St):
    VisitedValid s ->
    RootPopBranchPre g root u s ->
    RootPopCuts g u s ->
    PoppedSegmentInPartialTree u s ->
    PoppedNonrootHasLowerPoppedTarget u s ->
    is_SCC g (PoppedSegment u s).
  Proof.
    intros Hvalid Hpre Hcuts Hpartial Hlower.
    eapply popped_segment_is_scc_from_reachability_cuts; eauto.
    - eapply popped_segment_tree_reachable_lifts_to_graph.
      + exact Hpre.
      + eapply popped_segment_tree_reachable_from_partial_tree; eauto.
    - eapply popped_segment_reaches_root_from_lower_targets; eauto.
    - eapply popped_segment_maximal; eauto.
  Qed.

  Lemma pop_scc_preserves_sccs_sound_from_core_cuts
        (u: V):
    Hoare
      (fun s: St =>
         SCCsSound s /\
         VisitedValid s /\
         RootPopBranchPre g root u s /\
         RootPopCuts g u s /\
         PoppedSegmentInPartialTree u s /\
         PoppedNonrootHasLowerPoppedTarget u s)
      (pop_scc u)
      (fun _ s => SCCsSound s).
  Proof.
    eapply Hoare_conseq_pre.
    2: apply pop_scc_preserves_sccs_sound_from_new_scc.
    intros s
      [Hsound [Hvalid [Hpre [Hcuts [Hpartial Hlower]]]]].
    split; [exact Hsound |].
    eapply popped_segment_is_scc_from_core_cuts; eauto.
  Qed.

  Lemma popped_segment_is_scc_from_tree_and_pending_low
        (u: V) (s: St):
    VisitedValid s ->
    RootPopBranchPre g root u s ->
    RootPopCuts g u s ->
    PoppedSegmentTreeReachableFromRoot u s ->
    PoppedSegmentPendingLow u s ->
    is_SCC g (PoppedSegment u s).
  Proof.
    intros Hvalid Hpre Hcuts Htree_reach Hpending.
    eapply popped_segment_is_scc_from_core_cuts; eauto.
    - eapply popped_segment_in_partial_tree_from_tree_reachable; eauto.
    - eapply popped_nonroot_has_lower_popped_target_from_pending_low; eauto.
  Qed.

  Lemma pop_scc_preserves_sccs_sound_from_tree_and_pending_low
        (u: V):
    Hoare
      (fun s: St =>
         SCCsSound s /\
         VisitedValid s /\
         RootPopBranchPre g root u s /\
         RootPopCuts g u s /\
         PoppedSegmentTreeReachableFromRoot u s /\
         PoppedSegmentPendingLow u s)
      (pop_scc u)
      (fun _ s => SCCsSound s).
  Proof.
    eapply Hoare_conseq_pre.
    2: apply pop_scc_preserves_sccs_sound_from_new_scc.
    intros s
      [Hsound [Hvalid [Hpre [Hcuts [Htree_reach Hpending]]]]].
    split; [exact Hsound |].
    eapply popped_segment_is_scc_from_tree_and_pending_low; eauto.
  Qed.

End SCC_OUTPUT_CORRECTNESS.
