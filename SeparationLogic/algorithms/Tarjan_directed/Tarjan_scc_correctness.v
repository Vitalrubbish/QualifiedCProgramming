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
  Local Definition RecProgram : Type := V -> program St unit.

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

  Definition LoopPoppedSegmentInPartialTree
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall x,
      PoppedSegment u s x ->
      PartialTree g root u done s x.

  (* Output-layer producer field carried by the edge loop.  The first
     component is still partial in [done]; the pending-low component is
     stack-local and is independent of the processed-edge set. *)
  Definition LoopOutputReady
             (u: V) (done: V -> Prop) (s: St): Prop :=
    LoopPoppedSegmentInPartialTree u done s /\
    PoppedSegmentPendingLow u s.

  Definition RootOutputReady (u: V) (s: St): Prop :=
    PoppedSegmentTreeReachableFromRoot u s /\
    PoppedSegmentPendingLow u s.

  Definition RootActiveOutputReady (u: V) (s: St): Prop :=
    Active u s ->
      scc_is_low_v g root s u /\
      low s u <> dfn s u /\
      RootOutputReady u s.

  Definition RootOutputPost (u: V) (s: St): Prop :=
    RootFinal g root u s /\
    SCCsOutputInv s /\
    VisitedValid s /\
    RootActiveOutputReady u s.

  Definition VisitOutputContract (W: RecProgram): Prop :=
    forall u: V,
      Hoare
        (fun s: St =>
           EntryPre g root u s /\
           original_vvalid g u /\
           SCCsOutputInv s /\
           VisitedValid s)
        (W u)
        (fun _ s => RootOutputPost u s).

  Definition VisitChildOutputContract (W: RecProgram): Prop :=
    forall (parent child: V) (done: V -> Prop),
      Hoare
        (fun s: St =>
           ParentRecursivePre g root parent child done s /\
           LoopTraversalComplete g root parent done s /\
           LoopOutputReady parent done s /\
           SCCsOutputInv s /\
           VisitedValid s /\
           original_vvalid g child)
        (W child)
        (fun _ s =>
           exists s_before,
             LoopInv g root parent done s_before /\
             Edge g parent child /\
             ChildContributionContract g root parent child done s_before s /\
             LoopOutputReady parent (done_after done child) s /\
             SCCsOutputInv s /\
             VisitedValid s).

  (* Output-only analogue of the parent frame.  The low-link frame already
     preserves the program/low/traversal structure; this frame records the
     extra history needed to transport the parent output fields across a
     recursive child call. *)
  Definition ParentOutputFrameForChild
             (parent child: V) (done: V -> Prop)
             (s_before s: St): Prop :=
    (forall x,
      PoppedSegment parent s x ->
      (Active child s /\ PoppedSegment child s x) \/
      PoppedSegment parent s_before x) /\
    (forall x,
      PoppedSegment parent s_before x ->
      PartialTree g root parent done s_before x ->
      PartialTree g root parent (done_after done child) s x) /\
    (forall x,
      PoppedSegment parent s x ->
      PoppedSegment parent s_before x ->
      PartialTree g root parent done s_before x ->
      x <> parent ->
      scc_is_low_v g root s x /\ low s x <> dfn s x) /\
    (forall x,
      PoppedSegment parent s_before x ->
      x <> parent ->
      x <> child) /\
    (forall x,
      PoppedSegment parent s_before x ->
      PartialTree g root parent done s_before x ->
      x <> parent ->
      Active child s ->
      RestStack child s x).

  Definition NestedOutputFramePre
             (ancestor current loop_root next: V)
             (ancestor_done loop_done: V -> Prop)
             (s_before s: St): Prop :=
    NestedFramePre g root ancestor current loop_root next
      ancestor_done loop_done s_before s /\
    ParentOutputFrameForChild ancestor current ancestor_done s_before s /\
    LoopOutputReady ancestor ancestor_done s_before /\
    (forall x,
      PoppedSegment ancestor s_before x ->
      x <> ancestor ->
      x <> loop_root).

  Definition VisitOutputFrameContract (W: RecProgram): Prop :=
    forall (ancestor current loop_root next: V)
           (ancestor_done loop_done: V -> Prop)
           (s_before: St),
      Hoare
        (NestedOutputFramePre ancestor current loop_root next
           ancestor_done loop_done s_before)
        (W next)
        (fun _ s =>
           ParentOutputFrameForChild
             ancestor current ancestor_done s_before s).

  Lemma parent_frame_child_active
        (parent child: V) (done: V -> Prop)
        (s_before s: St):
    ParentFrameForChild g root parent child done s_before s ->
    Active child s.
  Proof.
    intros Hframe.
    unfold ParentFrameForChild in Hframe.
    destruct Hframe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hbelow _]]]]]]]]]]]].
    apply (rest_stack_root_active child parent s).
    apply Hbelow.
    apply partial_low_candidate_root.
  Qed.

  Lemma parent_frame_output_segment_cases
        (parent child: V) (done: V -> Prop)
        (s_before s: St):
    ParentFrameForChild g root parent child done s_before s ->
    forall x,
      PoppedSegment parent s x ->
      (Active child s /\ PoppedSegment child s x) \/
      PoppedSegment parent s_before x.
  Proof.
    intros Hframe x Hpopped_parent.
    pose proof (parent_frame_child_active parent child done s_before s Hframe)
      as Hchild_active.
    unfold ParentFrameForChild in Hframe.
    destruct Hframe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hstack_frame]]]]]]]]]]]].
    destruct Hstack_frame as [Hsegment_cases _].
    destruct (Hsegment_cases x Hpopped_parent)
      as [Hpopped_child | Hpopped_old].
    - left. exact (conj Hchild_active Hpopped_child).
    - right. exact Hpopped_old.
  Qed.

  Lemma parent_frame_child_rest_parent
        (parent child: V) (done: V -> Prop)
        (s_before s: St):
    ParentFrameForChild g root parent child done s_before s ->
    RestStack child s parent.
  Proof.
    intros Hframe.
    unfold ParentFrameForChild in Hframe.
    destruct Hframe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hbelow _]]]]]]]]]]]].
    apply Hbelow.
    apply partial_low_candidate_root.
  Qed.

  Lemma update_low_preserves_parent_output_frame_for_child
        (parent child u: V) (done: V -> Prop)
        (s_before: St) (n: nat):
    (forall x,
      PoppedSegment parent s_before x ->
      x <> parent ->
      x <> u) ->
    Hoare
      (ParentOutputFrameForChild parent child done s_before)
      (update_low u n)
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    intros Hu_not_old.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s.
      destruct H as
        [Hsegment [Hpartial [Hpending [Hchild_not_old Hrest_old]]]].
      split.
      + intros x Hpopped.
        unfold PoppedSegment in Hpopped |- *.
        simpl in Hpopped |- *.
        destruct (Hsegment x Hpopped) as [Hchild_case | Hold].
        * left. destruct Hchild_case as [Hactive Hpopped_child].
          split; [exact Hactive |].
          unfold PoppedSegment in Hpopped_child |- *.
          simpl in Hpopped_child |- *.
          exact Hpopped_child.
        * right. exact Hold.
      + split.
        * intros x Hpopped_old Htree_old.
          specialize (Hpartial x Hpopped_old Htree_old).
          unfold PartialTree in Hpartial |- *.
          simpl.
          exact Hpartial.
        * split.
          -- intros x Hpopped_after Hpopped_old Htree_old Hx_ne_parent.
             assert (Hpopped_before: PoppedSegment parent s0 x).
             { unfold PoppedSegment in *.
               simpl in Hpopped_after |- *.
               exact Hpopped_after. }
             destruct (Hpending x Hpopped_before Hpopped_old Htree_old Hx_ne_parent)
               as [Hlow Hlow_ne].
             assert (Hx_ne_u: x <> u).
             { exact (Hu_not_old x Hpopped_old Hx_ne_parent). }
             split.
             ++ unfold scc_is_low_v, scc_is_low_v_val in *.
                simpl.
                unfold equiv_decb.
                destruct (equiv_dec x u) as [Hx_eq_u | _].
                ** exfalso. exact (Hx_ne_u Hx_eq_u).
                ** exact Hlow.
             ++ simpl. unfold equiv_decb.
                destruct (equiv_dec x u) as [Hx_eq_u | _].
                ** exfalso. exact (Hx_ne_u Hx_eq_u).
                ** exact Hlow_ne.
          -- split.
             ++ exact Hchild_not_old.
             ++ intros x Hpopped_old Htree_old Hx_ne_parent Hactive_child.
                exact (Hrest_old x Hpopped_old Htree_old
                         Hx_ne_parent Hactive_child).
    - destruct H1 as [Heq _]. subst s.
      exact H.
  Qed.

  Lemma get_low_update_low_preserves_parent_output_frame_for_child
        (parent child u v: V) (done: V -> Prop)
        (s_before: St):
    (forall x,
      PoppedSegment parent s_before x ->
      x <> parent ->
      x <> u) ->
    Hoare
      (ParentOutputFrameForChild parent child done s_before)
      (lv <- get' (fun s => low s v);; update_low u lv)
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    intros Hu_not_old.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply update_low_preserves_parent_output_frame_for_child.
      exact Hu_not_old. }
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma get_dfn_update_low_preserves_parent_output_frame_for_child
        (parent child u v: V) (done: V -> Prop)
        (s_before: St):
    (forall x,
      PoppedSegment parent s_before x ->
      x <> parent ->
      x <> u) ->
    Hoare
      (ParentOutputFrameForChild parent child done s_before)
      (dv <- get' (fun s => dfn s v);; update_low u dv)
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    intros Hu_not_old.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply update_low_preserves_parent_output_frame_for_child.
      exact Hu_not_old. }
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma get_low_update_low_child_preserves_parent_output_frame_for_child
        (parent child v: V) (done: V -> Prop)
        (s_before: St):
    Hoare
      (ParentOutputFrameForChild parent child done s_before)
      (lv <- get' (fun s => low s v);; update_low child lv)
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    pose proof H as Houtput_frame.
    destruct Houtput_frame as [_ [_ [_ [Hchild_not_old _]]]].
    eapply Hoare_conseq_pre.
    2: {
      apply update_low_preserves_parent_output_frame_for_child.
      exact Hchild_not_old. }
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma get_dfn_update_low_child_preserves_parent_output_frame_for_child
        (parent child v: V) (done: V -> Prop)
        (s_before: St):
    Hoare
      (ParentOutputFrameForChild parent child done s_before)
      (dv <- get' (fun s => dfn s v);; update_low child dv)
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    pose proof H as Houtput_frame.
    destruct Houtput_frame as [_ [_ [_ [Hchild_not_old _]]]].
    eapply Hoare_conseq_pre.
    2: {
      apply update_low_preserves_parent_output_frame_for_child.
      exact Hchild_not_old. }
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma parent_output_frame_active_child_to_loop_output_ready
        (parent child: V) (done: V -> Prop) (s_before s: St):
    LoopOutputReady parent done s_before ->
    Edge g parent child ->
    ChildContributionContract g root parent child done s_before s ->
    ParentOutputFrameForChild parent child done s_before s ->
    RootActiveOutputReady child s ->
    Active child s ->
    LoopOutputReady parent (done_after done child) s.
  Proof.
    intros Hready_before Hedge_parent_child Hcontribution Houtput_frame
           Hchild_ready Hchild_active.
    destruct Hready_before as [Hpartial_before _].
    destruct Houtput_frame as
      [Hsegment_cases [Hpartial_old [Hpending_old _]]].
    destruct (Hchild_ready Hchild_active)
      as [Hchild_low [Hchild_low_ne [Hchild_tree Hchild_pending]]].
    destruct Hcontribution as [_ Hcontribution].
    destruct Hcontribution as [_ Hcontribution].
    destruct Hcontribution as [_ Hcontribution].
    destruct Hcontribution as [_ Hcontribution].
    destruct Hcontribution as [_ Hcontribution].
    destruct Hcontribution as [_ Hcontribution].
    destruct Hcontribution as [Hfa_child Hcontribution].
    destruct Hcontribution as [Hfane_child _].
    split.
    - intros x Hpopped_parent.
      destruct (Hsegment_cases x Hpopped_parent)
        as [[_ Hpopped_child] | Hpopped_old].
      + right. exists child. repeat split; auto.
        apply done_after_intro_new.
      + apply Hpartial_old.
        * exact Hpopped_old.
        * exact (Hpartial_before x Hpopped_old).
    - intros x Hpopped_parent Hx_ne_parent.
      destruct (Hsegment_cases x Hpopped_parent)
        as [[_ Hpopped_child] | Hpopped_old].
      + destruct (classic (x = child)) as [Hx_eq_child | Hx_ne_child].
        * subst x. exact (conj Hchild_low Hchild_low_ne).
        * exact (Hchild_pending x Hpopped_child Hx_ne_child).
      + exact (Hpending_old x Hpopped_parent Hpopped_old
                  (Hpartial_before x Hpopped_old) Hx_ne_parent).
  Qed.

  Lemma parent_output_frame_inactive_child_to_loop_output_ready
        (parent child: V) (done: V -> Prop) (s_before s: St):
    LoopOutputReady parent done s_before ->
    ParentOutputFrameForChild parent child done s_before s ->
    ~ Active child s ->
    LoopOutputReady parent (done_after done child) s.
  Proof.
    intros Hready_before Houtput_frame Hchild_inactive.
    destruct Hready_before as [Hpartial_before _].
    destruct Houtput_frame as
      [Hsegment_cases [Hpartial_old [Hpending_old _]]].
    split.
    - intros x Hpopped_parent.
      destruct (Hsegment_cases x Hpopped_parent)
        as [[Hchild_active _] | Hpopped_old].
      + exfalso. exact (Hchild_inactive Hchild_active).
      + apply Hpartial_old.
        * exact Hpopped_old.
        * exact (Hpartial_before x Hpopped_old).
    - intros x Hpopped_parent Hx_ne_parent.
      destruct (Hsegment_cases x Hpopped_parent)
        as [[Hchild_active _] | Hpopped_old].
      + exfalso. exact (Hchild_inactive Hchild_active).
      + exact (Hpending_old x Hpopped_parent Hpopped_old
                  (Hpartial_before x Hpopped_old) Hx_ne_parent).
  Qed.

  Lemma parent_output_frame_to_loop_output_ready
        (parent child: V) (done: V -> Prop) (s_before s: St):
    LoopOutputReady parent done s_before ->
    Edge g parent child ->
    ChildContributionContract g root parent child done s_before s ->
    ParentOutputFrameForChild parent child done s_before s ->
    RootOutputPost child s ->
    LoopOutputReady parent (done_after done child) s.
  Proof.
    intros Hready_before Hedge Hcontribution Houtput_frame Hchild_post.
    pose proof Hcontribution as Hcontribution_all.
    destruct Hchild_post as [_ [_ [_ Hchild_active_ready]]].
    destruct Hcontribution as [_ Hcontribution_tail].
    destruct Hcontribution_tail as [_ Hcontribution_tail].
    destruct Hcontribution_tail as [_ Hcontribution_tail].
    destruct Hcontribution_tail as [_ Hcontribution_tail].
    destruct Hcontribution_tail as [_ Hcontribution_tail].
    destruct Hcontribution_tail as [_ Hcontribution_tail].
    destruct Hcontribution_tail as [_ Hcontribution_tail].
    destruct Hcontribution_tail as [_ Hcontribution_tail].
    pose proof Hcontribution_tail as Hchild_low_contribution.
    destruct Hchild_low_contribution as
      [[Hchild_active _] | [Hchild_inactive _]].
    - eapply parent_output_frame_active_child_to_loop_output_ready.
      + exact Hready_before.
      + exact Hedge.
      + exact Hcontribution_all.
      + exact Houtput_frame.
      + exact Hchild_active_ready.
      + exact Hchild_active.
    - eapply parent_output_frame_inactive_child_to_loop_output_ready.
      + exact Hready_before.
      + exact Houtput_frame.
      + exact Hchild_inactive.
  Qed.

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

  Lemma partial_tree_done_mono
        (u x: V) (done1 done2: V -> Prop) (s: St):
    (forall a, done1 a -> done2 a) ->
    PartialTree g root u done1 s x ->
    PartialTree g root u done2 s x.
  Proof.
    intros Hdone Hpartial.
    destruct Hpartial as [Hx_eq_u | Hchild].
    - left. exact Hx_eq_u.
    - right.
      destruct Hchild as
        [child [Hdone_child [Hedge_child
          [Hfa_child [Hfane_child Hreach_child_x]]]]].
      exists child. repeat split; auto.
  Qed.

  Lemma loop_output_ready_done_mono
        (u: V) (done1 done2: V -> Prop) (s: St):
    (forall a, done1 a -> done2 a) ->
    LoopOutputReady u done1 s ->
    LoopOutputReady u done2 s.
  Proof.
    intros Hdone [Hpartial Hpending].
    split; [| exact Hpending].
    intros x Hpopped.
    eapply partial_tree_done_mono; eauto.
  Qed.

  Lemma loop_output_ready_done_after
        (u v: V) (done: V -> Prop) (s: St):
    LoopOutputReady u done s ->
    LoopOutputReady u (done_after done v) s.
  Proof.
    intros Hready.
    eapply loop_output_ready_done_mono.
    - intros a Hdone_a.
      apply done_after_intro_old. exact Hdone_a.
    - exact Hready.
  Qed.

  Lemma loop_output_ready_done_equiv
        (u: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    LoopOutputReady u done1 s ->
    LoopOutputReady u done2 s.
  Proof.
    intros Hdone Hready.
    eapply loop_output_ready_done_mono.
    - intros a Ha.
      apply Hdone. exact Ha.
    - exact Hready.
  Qed.

  Lemma loop_output_ready_to_root_output_ready
        (u: V) (s: St):
    LoopCoreShape g root u (edge_set g u) s ->
    LoopOutputReady u (edge_set g u) s ->
    RootOutputReady u s.
  Proof.
    intros Hshape [Hpartial Hpending].
    split; [| exact Hpending].
    intros x Hpopped.
    eapply partial_tree_to_tree_reachable; eauto.
  Qed.

  Lemma preloop_initializes_loop_output_ready_empty
        (u: V):
    Hoare
      (EntryPre g root u)
      (preloop u)
      (fun _ s => LoopOutputReady u ∅ s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s.
    unfold LoopOutputReady, LoopPoppedSegmentInPartialTree,
      PoppedSegmentPendingLow.
    split.
    - intros x Hpopped.
      unfold PoppedSegment in Hpopped.
      simpl in Hpopped. unfold equiv_decb in Hpopped.
      destruct (equiv_dec u u) as [_ | Hu_ne_u].
      + simpl in Hpopped.
        destruct Hpopped as [Hx_eq_u | Hnil].
        * subst x. apply partial_tree_root.
        * contradiction.
      + exfalso. apply Hu_ne_u. reflexivity.
    - intros x Hpopped Hx_ne_u.
      unfold PoppedSegment in Hpopped.
      simpl in Hpopped. unfold equiv_decb in Hpopped.
      destruct (equiv_dec u u) as [_ | Hu_ne_u].
      + simpl in Hpopped.
        destruct Hpopped as [Hx_eq_u | Hnil].
        * subst x. exfalso. apply Hx_ne_u. reflexivity.
        * contradiction.
      + exfalso. apply Hu_ne_u. reflexivity.
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

  Lemma pop_scc_preserves_output_inv_from_tree_and_pending_low
        (u: V):
    Hoare
      (fun s: St =>
         SCCsOutputInv s /\
         VisitedValid s /\
         RootPopBranchPre g root u s /\
         RootPopCuts g u s /\
         PoppedSegmentTreeReachableFromRoot u s /\
         PoppedSegmentPendingLow u s)
      (pop_scc u)
      (fun _ s => SCCsOutputInv s).
  Proof.
    unfold Hoare.
    intros s1 retv s2
      [[Hsound Hcover] [Hvalid [Hpre [Hcuts [Htree Hpending]]]]]
      Hexec.
    split.
    - pose proof (pop_scc_preserves_sccs_sound_from_tree_and_pending_low u)
        as Hsound_hoare.
      unfold Hoare in Hsound_hoare.
      eapply Hsound_hoare; eauto.
      exact (conj Hsound
              (conj Hvalid
                (conj Hpre
                  (conj Hcuts
                    (conj Htree Hpending))))).
    - pose proof (pop_scc_preserves_cover_settled u) as Hcover_hoare.
      unfold Hoare in Hcover_hoare.
      eapply Hcover_hoare; eauto.
  Qed.

  Lemma pop_scc_preserves_visited_valid
        (u: V):
    Hoare
      (VisitedValid)
      (pop_scc u)
      (fun _ s => VisitedValid s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 Hvalid Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold VisitedValid in *.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s1) u) as [popped rest] eqn:Hsplit.
    simpl.
    unfold Visited in *.
    intros v Hv.
    apply Hvalid.
    exact Hv.
  Qed.

  Lemma set_fa_preserves_sccs_output_inv
        (v p: V):
    Hoare
      (SCCsOutputInv)
      (set_fa v p)
      (fun _ s => SCCsOutputInv s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. exact H.
  Qed.

  Lemma update_low_preserves_sccs_output_inv
        (u: V) (n: nat):
    Hoare
      (SCCsOutputInv)
      (update_low u n)
      (fun _ s => SCCsOutputInv s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma get_low_update_low_preserves_sccs_output_inv
        (u v: V):
    Hoare
      (SCCsOutputInv)
      (lv <- get' (fun s => low s v);; update_low u lv)
      (fun _ s => SCCsOutputInv s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_sccs_output_inv.
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma get_dfn_update_low_preserves_sccs_output_inv
        (u v: V):
    Hoare
      (SCCsOutputInv)
      (dv <- get' (fun s => dfn s v);; update_low u dv)
      (fun _ s => SCCsOutputInv s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_sccs_output_inv.
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma set_fa_preserves_visited_valid
        (v p: V):
    Hoare
      (VisitedValid)
      (set_fa v p)
      (fun _ s => VisitedValid s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. exact H.
  Qed.

  Lemma update_low_preserves_visited_valid
        (u: V) (n: nat):
    Hoare
      (VisitedValid)
      (update_low u n)
      (fun _ s => VisitedValid s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma get_low_update_low_preserves_visited_valid
        (u v: V):
    Hoare
      (VisitedValid)
      (lv <- get' (fun s => low s v);; update_low u lv)
      (fun _ s => VisitedValid s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_visited_valid.
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma get_dfn_update_low_preserves_visited_valid
        (u v: V):
    Hoare
      (VisitedValid)
      (dv <- get' (fun s => dfn s v);; update_low u dv)
      (fun _ s => VisitedValid s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_visited_valid.
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma set_fa_pending_scc_low_tree_iff
        (s: St) (v p x target: V):
    ~ Visited v s ->
    (scc_low_tree g root (set_fa_state s v p) x target <->
     scc_low_tree g root s x target).
  Proof.
    intros Hnotvis.
    unfold scc_low_tree, scc_low_reachable, scc_back_edge.
    split.
    - intros [z [Hreach Hcase]].
      exists z. split.
      + apply (proj1 (set_fa_pending_tree_reachable_iff
                        g root s v p x z Hnotvis)).
        exact Hreach.
      + destruct Hcase as [Hz_eq | Hback].
        * left. exact Hz_eq.
        * destruct Hback as [Hedge [Hactive Hnot_tree]].
          right. repeat split; auto.
          intros Htree.
          apply Hnot_tree.
          apply (proj2 (set_fa_pending_tree_step_iff
                          g root s v p z target Hnotvis)).
          exact Htree.
    - intros [z [Hreach Hcase]].
      exists z. split.
      + apply (proj2 (set_fa_pending_tree_reachable_iff
                        g root s v p x z Hnotvis)).
        exact Hreach.
      + destruct Hcase as [Hz_eq | Hback].
        * left. exact Hz_eq.
        * destruct Hback as [Hedge [Hactive Hnot_tree]].
          right. repeat split; auto.
          intros Htree.
          apply Hnot_tree.
          apply (proj1 (set_fa_pending_tree_step_iff
                          g root s v p z target Hnotvis)).
          exact Htree.
  Qed.

  Lemma set_fa_pending_preserves_scc_is_low_v
        (s: St) (v p x: V):
    ~ Visited v s ->
    scc_is_low_v g root s x ->
    scc_is_low_v g root (set_fa_state s v p) x.
  Proof.
    intros Hnotvis Hlow.
    unfold scc_is_low_v, scc_is_low_v_val in *.
    unfold min_value_of_subset in *.
    destruct Hlow as [witness [[Hwitness Hmin] Hlow_eq]].
    exists witness. split.
    - unfold min_object_of_subset.
      split.
      + apply (proj2 (set_fa_pending_scc_low_tree_iff
                        s v p x witness Hnotvis)).
        assumption.
      + intros target Htarget.
        apply Hmin.
        apply (proj1 (set_fa_pending_scc_low_tree_iff
                        s v p x target Hnotvis)).
        exact Htarget.
    - simpl. exact Hlow_eq.
  Qed.

  Lemma tree_reachable_preserves_visited
        (s: St) (x y: V):
    wf_scc_state g root s ->
    Visited x s ->
    dg_reachable (state_to_dfs_tree g s root) x y ->
    Visited y s.
  Proof.
    intros Hwf Hx Hreach.
    induction Hreach as [a b Hstep | a | a b c _ IH_ab _ IH_bc].
    - apply tree_step_char in Hstep as [_ [_ Hb_vis]].
      exact Hb_vis.
    - exact Hx.
    - apply IH_bc. apply IH_ab. exact Hx.
  Qed.

  Lemma partial_tree_visited_from_shape
        (u x: V) (done: V -> Prop) (s: St):
    LoopCoreShape g root u done s ->
    PartialTree g root u done s x ->
    Visited x s.
  Proof.
    intros Hshape Hpartial.
    destruct Hshape as [Hwf [_ [Hu_vis [_ [Hdone_vis _]]]]].
    destruct Hpartial as [Hx_u | Hchild].
    - subst x. exact Hu_vis.
    - destruct Hchild as
        [child [Hdone_child [_ [_ [_ Hreach_child_x]]]]].
      assert (Hchild_vis: Visited child s).
      { apply Hdone_vis. exact Hdone_child. }
      eapply tree_reachable_preserves_visited; eauto.
  Qed.

  Lemma scc_low_tree_target_visited
        (s: St) (x target: V):
    wf_scc_state g root s ->
    Visited x s ->
    scc_low_tree g root s x target ->
    Visited target s.
  Proof.
    intros Hwf Hx Htarget.
    unfold scc_low_tree, scc_low_reachable, scc_back_edge in Htarget.
    destruct Htarget as [z [Hreach [Hz_eq | [_ [Hactive _]]]]].
    - subst target.
      eapply tree_reachable_preserves_visited; eauto.
    - destruct Hwf as [Hstack_vis _].
      apply Hstack_vis. exact Hactive.
  Qed.

  Lemma preloop_preserves_partial_tree
        (u center x: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    (s_before, retv, s_after) ∈ preloop u ->
    PartialTree g root center done s_before x ->
    PartialTree g root center done s_after x.
  Proof.
    intros Hexec Hpartial.
    unfold PartialTree in Hpartial |- *.
    destruct Hpartial as [Hx_center | Hchild].
    - left. exact Hx_center.
    - right.
      destruct Hchild as
        [child [Hdone [Hedge [Hfa [Hfane Hreach]]]]].
      exists child. repeat split; auto.
      + pose proof (preloop_preserves_any_fa
                      u child (fa s_before child)) as Hhoare.
        unfold Hoare in Hhoare.
        rewrite (Hhoare s_before retv s_after eq_refl Hexec).
        exact Hfa.
      + pose proof (preloop_preserves_any_fa
                      u child (fa s_before child)) as Hhoare.
        unfold Hoare in Hhoare.
        rewrite (Hhoare s_before retv s_after eq_refl Hexec).
        exact Hfane.
      + eapply preloop_tree_reachable_pre_lift; eauto.

  Qed.

  Lemma preloop_scc_low_tree_pre_lift_not_child
        (parent child x target: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre g root parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    target <> child ->
    scc_low_tree g root s_before x target ->
    scc_low_tree g root s_after x target.
  Proof.
    intros Hpre Hexec Htarget_ne_child Htarget.
    unfold scc_low_tree, scc_low_reachable, scc_back_edge in Htarget |- *.
    destruct Htarget as [z [Hreach [Hz_eq | Hback]]].
    - exists z. split.
      + eapply preloop_tree_reachable_pre_lift; eauto.
      + left. exact Hz_eq.
    - destruct Hback as [Hedge [Hactive Hnot_tree]].
      exists z. split.
      + eapply preloop_tree_reachable_pre_lift; eauto.
      + right. repeat split; auto.
        * eapply preloop_preserves_active; eauto.
        * intros Htree_after.
          destruct (preloop_tree_edge_post_cases
                      g root parent child z target done
                      s_before s_after retv Hpre Hexec Htree_after)
            as [Htree_before | [_ Htarget_eq_child]].
          -- exact (Hnot_tree Htree_before).
          -- exact (Htarget_ne_child Htarget_eq_child).
  Qed.

  Lemma preloop_old_partial_no_reach_child
        (parent child x: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre g root parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    PartialTree g root parent done s_before x ->
    x <> parent ->
    ~ dg_reachable (state_to_dfs_tree g s_after root) x child.
  Proof.
    intros Hpre Hexec Hpartial Hx_ne_parent Hreach_x_child.
    unfold PartialTree in Hpartial.
    destruct Hpartial as [Hx_parent | Hsubtree].
    - exact (Hx_ne_parent Hx_parent).
    - destruct Hsubtree as
        [old_child [Hdone_old [Hedge_old
          [Hfa_old [Hfane_old Hreach_old_x]]]]].
      assert (Hfa_old_after: fa s_after old_child = parent).
      { pose proof (preloop_preserves_any_fa
                      child old_child (fa s_before old_child))
          as Hhoare.
        unfold Hoare in Hhoare.
        rewrite (Hhoare s_before retv s_after eq_refl Hexec).
        exact Hfa_old. }
      assert (Hfane_old_after: fa s_after old_child <> old_child).
      { pose proof (preloop_preserves_any_fa
                      child old_child (fa s_before old_child))
          as Hhoare.
        unfold Hoare in Hhoare.
        rewrite (Hhoare s_before retv s_after eq_refl Hexec).
        exact Hfane_old. }
      assert (Hreach_old_x_after:
                dg_reachable (state_to_dfs_tree g s_after root)
                             old_child x).
      { eapply preloop_tree_reachable_pre_lift; eauto. }
      eapply preloop_old_processed_child_not_reach_child; eauto.
      eapply dg_reachable_trans; eauto.
  Qed.

  Lemma preloop_scc_low_tree_post_cases
        (parent child x target: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre g root parent child done s_before ->
    PartialTree g root parent done s_before x ->
    x <> parent ->
    (s_before, retv, s_after) ∈ preloop child ->
    scc_low_tree g root s_after x target ->
    scc_low_tree g root s_before x target \/ target = child.
  Proof.
    intros Hpre Hpartial Hx_ne_parent Hexec Htarget.
    unfold scc_low_tree, scc_low_reachable, scc_back_edge in Htarget.
    destruct Htarget as [z [Hreach [Hz_eq | Hback]]].
    - subst z.
      destruct (classic (target = child)) as [Htarget_eq_child | Htarget_ne_child].
      + right. exact Htarget_eq_child.
      + left. unfold scc_low_tree, scc_low_reachable.
        exists target. split.
        * eapply preloop_reachable_backward_not_child; eauto.
        * left. reflexivity.
    - destruct Hback as [Hedge [Hactive Hnot_tree]].
      destruct (preloop_active_post_cases
                  child target s_before s_after retv Hexec Hactive)
        as [Hactive_before | Htarget_eq_child].
      + assert (Hz_ne_child: z <> child).
        { intros Hz_eq_child. subst z.
          eapply preloop_old_partial_no_reach_child; eauto. }
        left. unfold scc_low_tree, scc_low_reachable, scc_back_edge.
        exists z. split.
        * eapply preloop_reachable_backward_not_child; eauto.
        * right. repeat split; auto.
          intros Htree_before. apply Hnot_tree.
          eapply preloop_tree_edge_pre_lift; eauto.
      + right. exact Htarget_eq_child.
  Qed.

  Lemma preloop_preserves_pending_low_for_old_partial
        (parent child x: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre g root parent child done s_before ->
    LoopOutputReady parent done s_before ->
    PoppedSegment parent s_before x ->
    PartialTree g root parent done s_before x ->
    x <> parent ->
    (s_before, retv, s_after) ∈ preloop child ->
    scc_is_low_v g root s_after x /\ low s_after x <> dfn s_after x.
  Proof.
    intros Hpre Hready Hpopped Hpartial Hx_ne_parent Hexec.
    pose proof Hpre as Hpre_all.
    destruct Hpre as [Hloop_parent [_ [Hentry_child _]]].
    destruct Hentry_child as [[_ Hchild_notvis] _].
    destruct Hloop_parent as [_ [Hshape_parent _]].
    destruct Hshape_parent as [Hwf_before _].
    pose proof Hwf_before as Hwf_before_full.
    destruct Hwf_before as [Hstack_vis_before [Hdfn_inv_before _]].
    assert (Hx_active_before: Active x s_before).
    { eapply popped_segment_in_stack; eauto. }
    assert (Hx_vis_before: Visited x s_before).
    { apply Hstack_vis_before. exact Hx_active_before. }
    assert (Hx_ne_child: x <> child).
    { intros Hx_eq_child. apply Hchild_notvis.
      rewrite <- Hx_eq_child. exact Hx_vis_before. }
    assert (Hchild_ne_x: child <> x).
    { intros Hchild_eq_x. apply Hx_ne_child. symmetry. exact Hchild_eq_x. }
    destruct Hready as [_ Hpending_before].
    destruct (Hpending_before x Hpopped Hx_ne_parent)
      as [Hlow_before Hlow_ne_before].
    assert (Hlow_pres: low s_after x = low s_before x).
    { pose proof (preloop_keep_low
                    child x (low s_before x)) as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s_before retv s_after
                        (conj Hchild_ne_x
                          (conj Hx_vis_before eq_refl)) Hexec)
        as [_ [_ Hlow_eq]].
      exact Hlow_eq. }
    assert (Hdfn_x_pres: dfn s_after x = dfn s_before x).
    { pose proof (preloop_keep_dfn
                    child x (dfn s_before x)) as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s_before retv s_after
                        (conj Hchild_ne_x
                          (conj Hx_vis_before eq_refl)) Hexec)
        as [_ [_ Hdfn_eq]].
      exact Hdfn_eq. }
    unfold scc_is_low_v, scc_is_low_v_val in Hlow_before |- *.
    unfold min_value_of_subset in Hlow_before |- *.
    destruct Hlow_before as [witness [[Hwitness_old Hmin_old] Hlow_eq_old]].
    assert (Hwitness_vis_before: Visited witness s_before).
    { eapply scc_low_tree_target_visited.
      - exact Hwf_before_full.
      - exact Hx_vis_before.
      - exact Hwitness_old. }
    assert (Hwitness_ne_child: witness <> child).
    { intros Hwitness_eq_child. apply Hchild_notvis.
      rewrite <- Hwitness_eq_child. exact Hwitness_vis_before. }
    assert (Hchild_ne_witness: child <> witness).
    { intros Hchild_eq_witness. apply Hwitness_ne_child.
      symmetry. exact Hchild_eq_witness. }
    assert (Hdfn_witness_pres:
              dfn s_after witness = dfn s_before witness).
    { pose proof (preloop_keep_dfn
                    child witness (dfn s_before witness)) as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s_before retv s_after
                        (conj Hchild_ne_witness
                          (conj Hwitness_vis_before eq_refl)) Hexec)
        as [_ [_ Hdfn_eq]].
      exact Hdfn_eq. }
    split.
    - exists witness. split.
      + unfold min_object_of_subset. split.
        * eapply preloop_scc_low_tree_pre_lift_not_child; eauto.
        * intros target Htarget_after.
          destruct (preloop_scc_low_tree_post_cases
                      parent child x target done
                      s_before s_after retv Hpre_all Hpartial
                      Hx_ne_parent Hexec Htarget_after)
            as [Htarget_old | Htarget_eq_child].
          -- assert (Htarget_vis_before: Visited target s_before).
             { eapply scc_low_tree_target_visited.
               - exact Hwf_before_full.
               - exact Hx_vis_before.
               - exact Htarget_old. }
             assert (Htarget_ne_child: target <> child).
             { intros Htarget_eq_child. apply Hchild_notvis.
               rewrite <- Htarget_eq_child. exact Htarget_vis_before. }
             assert (Hchild_ne_target: child <> target).
             { intros Hchild_eq_target. apply Htarget_ne_child.
               symmetry. exact Hchild_eq_target. }
             assert (Hdfn_target_pres:
                       dfn s_after target = dfn s_before target).
             { pose proof (preloop_keep_dfn
                             child target (dfn s_before target))
                 as Hhoare.
               unfold Hoare in Hhoare.
               destruct (Hhoare s_before retv s_after
                                 (conj Hchild_ne_target
                                   (conj Htarget_vis_before eq_refl)) Hexec)
                 as [_ [_ Hdfn_eq]].
               exact Hdfn_eq. }
             rewrite Hdfn_witness_pres, Hdfn_target_pres.
             apply Hmin_old. exact Htarget_old.
          -- subst target.
             assert (Hx_self_target: scc_low_tree g root s_before x x).
             { unfold scc_low_tree, scc_low_reachable.
               exists x. split.
               - apply dg_reachable_refl'.
               - left. reflexivity. }
	             pose proof (Hmin_old x Hx_self_target) as Hw_le_x.
	             assert (Hw_lt_x: dfn s_before witness < dfn s_before x).
	             { assert (Hw_ne_x:
	                         dfn s_before witness <> dfn s_before x).
	               { intros Hw_eq_x. apply Hlow_ne_before.
	                 rewrite <- Hlow_eq_old. exact Hw_eq_x. }
	               lia. }
             assert (Hx_lt_child: dfn s_after x < dfn s_after child).
             { pose proof (preloop_after_visited_dfn_lt
                             x child) as Hhoare.
               unfold Hoare in Hhoare.
               exact (Hhoare s_before retv s_after
                             (conj Hx_vis_before
                               (conj Hchild_notvis Hdfn_inv_before))
                             Hexec). }
             rewrite Hdfn_witness_pres.
             rewrite <- Hdfn_x_pres in Hw_lt_x.
             lia.
      + rewrite Hlow_pres, Hdfn_witness_pres.
        exact Hlow_eq_old.
    - rewrite Hlow_pres, Hdfn_x_pres.
      exact Hlow_ne_before.
  Qed.

  Lemma nested_output_frame_old_member_visited_mid
        (ancestor current loop_root next x: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid: St):
    NestedOutputFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    PoppedSegment ancestor s_before x ->
    Visited x s_mid.
  Proof.
    intros Hpre Hpopped_old.
    unfold NestedOutputFramePre in Hpre.
    destruct Hpre as [Hnested [Houtput [Hready _]]].
    destruct Hnested as [_ [Hparent_frame _]].
    destruct Hparent_frame as [_ [Hshape _]].
    destruct Hready as [Hpartial_before _].
    destruct Houtput as [_ [Hpartial_old _]].
    eapply partial_tree_visited_from_shape.
    - exact Hshape.
    - apply Hpartial_old.
      + exact Hpopped_old.
      + apply Hpartial_before. exact Hpopped_old.
  Qed.

  Lemma nested_output_frame_next_not_old
        (ancestor current loop_root next x: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid: St):
    NestedOutputFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    PoppedSegment ancestor s_before x ->
    x <> next.
  Proof.
    intros Hpre Hpopped_old Hx_next.
    pose proof
      (nested_output_frame_old_member_visited_mid
         ancestor current loop_root next x ancestor_done loop_done
         s_before s_mid Hpre Hpopped_old) as Hx_vis.
    unfold NestedOutputFramePre in Hpre.
    destruct Hpre as [Hnested _].
    destruct Hnested as [_ [_ [_ [_ [_ [Hentry _]]]]]].
    destruct Hentry as [[_ Hnext_notvis] _].
    subst x. exact (Hnext_notvis Hx_vis).
  Qed.

  Lemma rest_stack_dfn_lt_root_from_wf_order
        (u x: V) (s: St):
    wf_scc_state g root s ->
    OrderFacts s ->
    Active u s ->
    RestStack u s x ->
    dfn s x < dfn s u.
  Proof.
    intros Hwf Horder Hu_active Hrest.
    destruct Hwf as [Hstack_vis _].
    destruct Horder as [Hstack_order [Hdfn_inj Hnodup]].
    destruct (rest_stack_below_root u x s Hu_active Hrest)
      as [l1 [l2 [Hstk Hx_in_l2]]].
    assert (Hx_active: Active x s).
    { unfold Active. rewrite Hstk.
      rewrite List.in_app_iff. right. simpl. right. exact Hx_in_l2. }
    assert (Habove:
              exists l1' l2',
                stack s = l1' ++ u :: l2' /\ In x l2').
    { exists l1, l2. exact (conj Hstk Hx_in_l2). }
    assert (Hu_ne_x: u <> x).
    { intros Hu_eq_x.
      exact (rest_stack_member_ne_root u x s Hnodup Hu_active
                Hrest (eq_sym Hu_eq_x)). }
    eapply stack_dfn_order_strict; eauto.
  Qed.

  Lemma nested_output_frame_old_not_in_current_subtree
        (ancestor current loop_root next x: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid: St):
    NestedOutputFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    PoppedSegment ancestor s_before x ->
    PartialTree g root ancestor ancestor_done s_before x ->
    x <> ancestor ->
    ~ dg_reachable (state_to_dfs_tree g s_mid root) current x.
  Proof.
    intros Hpre Hpopped_old Htree_old Hx_ne_ancestor Hreach_current_x.
    unfold NestedOutputFramePre in Hpre.
    destruct Hpre as [Hnested [Houtput _]].
    destruct Hnested as [_ [Hparent_frame _]].
    pose proof (parent_frame_child_active
                  ancestor current ancestor_done s_before s_mid
                  Hparent_frame) as Hcurrent_active.
    destruct Hparent_frame as [_ [Hshape [Haux _]]].
    destruct Hshape as [Hwf _].
    destruct Haux as [_ [_ Horder]].
    destruct Houtput as [_ [_ [_ [_ Hrest_old]]]].
    assert (Hrest_current_x: RestStack current s_mid x).
    { exact (Hrest_old x Hpopped_old Htree_old
                      Hx_ne_ancestor Hcurrent_active). }
    pose proof
      (rest_stack_dfn_lt_root_from_wf_order
         current x s_mid Hwf Horder Hcurrent_active Hrest_current_x)
      as Hx_lt_current.
    pose proof (tree_reachable_dfn_monotone
                  g root s_mid current x Hwf Hreach_current_x)
      as Hcurrent_le_x.
    lia.
  Qed.

  Lemma preloop_nested_scc_low_tree_pre_lift_not_next
        (ancestor current loop_root next x target: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedFramePre g root ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    (s_mid, retv, s_after) ∈ preloop next ->
    target <> next ->
    scc_low_tree g root s_mid x target ->
    scc_low_tree g root s_after x target.
  Proof.
    intros Hnested Hexec Htarget_ne_next Htarget.
    pose proof (nested_frame_pre_parent_recursive_pre
                  g root ancestor current loop_root next
                  ancestor_done loop_done s_before s_mid Hnested)
      as Hrecursive_pre.
    unfold scc_low_tree, scc_low_reachable, scc_back_edge in Htarget |- *.
    destruct Htarget as [z [Hreach [Hz_eq | Hback]]].
    - exists z. split.
      + eapply preloop_tree_reachable_pre_lift; eauto.
      + left. exact Hz_eq.
    - destruct Hback as [Hedge [Hactive Hnot_tree]].
      exists z. split.
      + eapply preloop_tree_reachable_pre_lift; eauto.
      + right. repeat split; auto.
        * eapply preloop_preserves_active; eauto.
        * intros Htree_after.
          destruct (preloop_tree_edge_post_cases
                      g root loop_root next z target loop_done
                      s_mid s_after retv Hrecursive_pre Hexec Htree_after)
            as [Htree_before | [_ Htarget_eq_next]].
          -- exact (Hnot_tree Htree_before).
          -- exact (Htarget_ne_next Htarget_eq_next).
  Qed.

  Lemma preloop_nested_old_partial_no_reach_next
        (ancestor current loop_root next x: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedOutputFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    PoppedSegment ancestor s_before x ->
    PartialTree g root ancestor ancestor_done s_before x ->
    x <> ancestor ->
    (s_mid, retv, s_after) ∈ preloop next ->
    ~ dg_reachable (state_to_dfs_tree g s_after root) x next.
  Proof.
    intros Hpre Hpopped_old Htree_old Hx_ne_ancestor Hexec Hreach_x_next.
    pose proof Hpre as Hpre_all.
    unfold NestedOutputFramePre in Hpre.
    destruct Hpre as [Hnested [Houtput _]].
    destruct Houtput as [_ [Hpartial_old _]].
    specialize (Hpartial_old x Hpopped_old Htree_old).
    destruct Hpartial_old as [Hx_ancestor | Hchild].
    - exact (Hx_ne_ancestor Hx_ancestor).
    - destruct Hchild as
        [old_child [Hdone_after [Hedge_old
          [Hfa_old_mid [Hfane_old_mid Hreach_old_x_mid]]]]].
      destruct (done_after_elim ancestor_done current old_child Hdone_after)
        as [Hdone_old | Hold_eq_current].
      + assert (Hfa_old_pres:
                  fa s_after old_child = fa s_mid old_child).
        { pose proof (preloop_preserves_any_fa
                        next old_child (fa s_mid old_child)) as Hhoare.
          unfold Hoare in Hhoare.
          exact (Hhoare s_mid retv s_after eq_refl Hexec). }
        assert (Hfa_old_after: fa s_after old_child = ancestor).
        { rewrite Hfa_old_pres. exact Hfa_old_mid. }
        assert (Hfane_old_after: fa s_after old_child <> old_child).
        { intros Hfa_eq_old.
          apply Hfane_old_mid.
          rewrite <- Hfa_old_pres. exact Hfa_eq_old. }
        assert (Hreach_old_x_after:
                  dg_reachable (state_to_dfs_tree g s_after root)
                               old_child x).
        { eapply preloop_tree_reachable_pre_lift; eauto. }
        assert (Hreach_old_next:
                  dg_reachable (state_to_dfs_tree g s_after root)
                               old_child next).
        { eapply dg_reachable_trans; eauto. }
        eapply preloop_nested_done_child_not_reach_next; eauto.
      + subst old_child.
        assert (Hreach_current_x_mid:
                  dg_reachable (state_to_dfs_tree g s_mid root) current x).
        { exact Hreach_old_x_mid. }
        eapply nested_output_frame_old_not_in_current_subtree; eauto.
  Qed.

  Lemma preloop_nested_scc_low_tree_post_cases
        (ancestor current loop_root next x target: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedOutputFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    PoppedSegment ancestor s_before x ->
    PartialTree g root ancestor ancestor_done s_before x ->
    x <> ancestor ->
    (s_mid, retv, s_after) ∈ preloop next ->
    scc_low_tree g root s_after x target ->
    scc_low_tree g root s_mid x target \/ target = next.
  Proof.
    intros Hpre Hpopped_old Htree_old Hx_ne_ancestor Hexec Htarget.
    unfold NestedOutputFramePre in Hpre.
    destruct Hpre as [Hnested Hpre_tail].
    pose proof Hnested as Hnested_all.
    pose proof (nested_frame_pre_parent_recursive_pre
                  g root ancestor current loop_root next
                  ancestor_done loop_done s_before s_mid Hnested_all)
      as Hrecursive_pre.
    destruct Hnested as [_ [_ [_ [_ [_ [Hentry _]]]]]].
    destruct Hentry as [[_ Hnext_notvis] _].
    unfold scc_low_tree, scc_low_reachable, scc_back_edge in Htarget.
    destruct Htarget as [z [Hreach [Hz_eq | Hback]]].
    - subst z.
      destruct (classic (target = next)) as [Htarget_eq_next | Htarget_ne_next].
      + right. exact Htarget_eq_next.
      + left. unfold scc_low_tree, scc_low_reachable.
        exists target. split.
        * eapply preloop_reachable_backward_not_child; eauto.
        * left. reflexivity.
    - destruct Hback as [Hedge [Hactive Hnot_tree]].
      assert (Hz_ne_next: z <> next).
      { intros Hz_eq_next. subst z.
        eapply preloop_nested_old_partial_no_reach_next.
        - unfold NestedOutputFramePre. exact (conj Hnested_all Hpre_tail).
        - exact Hpopped_old.
        - exact Htree_old.
        - exact Hx_ne_ancestor.
        - exact Hexec.
        - exact Hreach. }
      destruct (preloop_active_post_cases
                  next target s_mid s_after retv Hexec Hactive)
        as [Hactive_before | Htarget_eq_next].
      + left. unfold scc_low_tree, scc_low_reachable, scc_back_edge.
        exists z. split.
        * eapply preloop_reachable_backward_not_child; eauto.
        * right. repeat split; auto.
          intros Htree_before. apply Hnot_tree.
          eapply preloop_tree_edge_pre_lift; eauto.
      + right. exact Htarget_eq_next.
  Qed.

  Lemma preloop_preserves_nested_pending_low_for_old_partial
        (ancestor current loop_root next x: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedOutputFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    PoppedSegment ancestor s_after x ->
    PoppedSegment ancestor s_before x ->
    PartialTree g root ancestor ancestor_done s_before x ->
    x <> ancestor ->
    (s_mid, retv, s_after) ∈ preloop next ->
    scc_is_low_v g root s_after x /\ low s_after x <> dfn s_after x.
  Proof.
    intros Hpre Hpopped_after Hpopped_old Htree_old Hx_ne_ancestor Hexec.
    pose proof Hpre as Hpre_all.
    unfold NestedOutputFramePre in Hpre.
    destruct Hpre as [Hnested [Houtput _]].
    pose proof Hnested as Hnested_all.
    destruct Hnested as [_ [Hparent_frame [_ [_ [_ [Hentry _]]]]]].
    destruct Hentry as [[_ Hnext_notvis] _].
    destruct Hparent_frame as [_ [Hshape_mid _]].
    destruct Hshape_mid as [Hwf_mid_full [_ [Hancestor_vis_mid _]]].
    pose proof Hwf_mid_full as Hwf_mid_parts.
    destruct Hwf_mid_parts as [Hstack_vis_mid [Hdfn_inv_mid _]].
    assert (Hx_vis_mid: Visited x s_mid).
    { eapply nested_output_frame_old_member_visited_mid; eauto. }
    assert (Hx_ne_next: x <> next).
    { eapply nested_output_frame_next_not_old; eauto. }
    assert (Hnext_ne_x: next <> x).
    { intros Hnext_eq_x. apply Hx_ne_next. symmetry. exact Hnext_eq_x. }
    assert (Hnext_ne_ancestor: next <> ancestor).
    { intros Hnext_eq_ancestor. apply Hnext_notvis.
      rewrite Hnext_eq_ancestor.
      exact Hancestor_vis_mid. }
    assert (Hpopped_mid: PoppedSegment ancestor s_mid x).
    { destruct (preloop_popped_segment_post_cases
                  next ancestor x s_mid s_after retv
                  Hnext_ne_ancestor Hexec Hpopped_after)
        as [Hx_eq_next | Hpopped_mid].
      - exfalso. exact (Hx_ne_next Hx_eq_next).
      - exact Hpopped_mid. }
    destruct Houtput as [_ [_ [Hpending_mid _]]].
    destruct (Hpending_mid x Hpopped_mid Hpopped_old
                Htree_old Hx_ne_ancestor) as [Hlow_mid Hlow_ne_mid].
    assert (Hlow_pres: low s_after x = low s_mid x).
    { pose proof (preloop_keep_low next x (low s_mid x)) as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s_mid retv s_after
                        (conj Hnext_ne_x
                          (conj Hx_vis_mid eq_refl)) Hexec)
        as [_ [_ Hlow_eq]].
      exact Hlow_eq. }
    assert (Hdfn_x_pres: dfn s_after x = dfn s_mid x).
    { pose proof (preloop_keep_dfn next x (dfn s_mid x)) as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s_mid retv s_after
                        (conj Hnext_ne_x
                          (conj Hx_vis_mid eq_refl)) Hexec)
        as [_ [_ Hdfn_eq]].
      exact Hdfn_eq. }
    unfold scc_is_low_v, scc_is_low_v_val in Hlow_mid |- *.
    unfold min_value_of_subset in Hlow_mid |- *.
    destruct Hlow_mid as [witness [[Hwitness_mid Hmin_mid] Hlow_eq_mid]].
    assert (Hwitness_vis_mid: Visited witness s_mid).
    { eapply scc_low_tree_target_visited.
      - exact Hwf_mid_full.
      - exact Hx_vis_mid.
      - exact Hwitness_mid. }
    assert (Hwitness_ne_next: witness <> next).
    { intros Hwitness_eq_next. apply Hnext_notvis.
      rewrite <- Hwitness_eq_next. exact Hwitness_vis_mid. }
    assert (Hnext_ne_witness: next <> witness).
    { intros Hnext_eq_witness. apply Hwitness_ne_next.
      symmetry. exact Hnext_eq_witness. }
    assert (Hdfn_witness_pres:
              dfn s_after witness = dfn s_mid witness).
    { pose proof (preloop_keep_dfn
                    next witness (dfn s_mid witness)) as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s_mid retv s_after
                        (conj Hnext_ne_witness
                          (conj Hwitness_vis_mid eq_refl)) Hexec)
        as [_ [_ Hdfn_eq]].
      exact Hdfn_eq. }
    split.
    - exists witness. split.
      + unfold min_object_of_subset. split.
        * eapply preloop_nested_scc_low_tree_pre_lift_not_next; eauto.
        * intros target Htarget_after.
          destruct (preloop_nested_scc_low_tree_post_cases
                      ancestor current loop_root next x target
                      ancestor_done loop_done s_before s_mid s_after retv
                      Hpre_all Hpopped_old Htree_old Hx_ne_ancestor
                      Hexec Htarget_after)
            as [Htarget_mid | Htarget_eq_next].
          -- assert (Htarget_vis_mid: Visited target s_mid).
             { eapply scc_low_tree_target_visited.
               - exact Hwf_mid_full.
               - exact Hx_vis_mid.
               - exact Htarget_mid. }
             assert (Htarget_ne_next: target <> next).
             { intros Htarget_eq_next. apply Hnext_notvis.
               rewrite <- Htarget_eq_next. exact Htarget_vis_mid. }
             assert (Hnext_ne_target: next <> target).
             { intros Hnext_eq_target. apply Htarget_ne_next.
               symmetry. exact Hnext_eq_target. }
             assert (Hdfn_target_pres:
                       dfn s_after target = dfn s_mid target).
             { pose proof (preloop_keep_dfn
                             next target (dfn s_mid target)) as Hhoare.
               unfold Hoare in Hhoare.
               destruct (Hhoare s_mid retv s_after
                                 (conj Hnext_ne_target
                                   (conj Htarget_vis_mid eq_refl)) Hexec)
                 as [_ [_ Hdfn_eq]].
               exact Hdfn_eq. }
             rewrite Hdfn_witness_pres, Hdfn_target_pres.
             apply Hmin_mid. exact Htarget_mid.
          -- subst target.
             assert (Hx_self_target: scc_low_tree g root s_mid x x).
             { unfold scc_low_tree, scc_low_reachable.
               exists x. split.
               - apply dg_reachable_refl'.
               - left. reflexivity. }
             pose proof (Hmin_mid x Hx_self_target) as Hw_le_x.
             assert (Hw_lt_x: dfn s_mid witness < dfn s_mid x).
             { assert (Hw_ne_x:
                         dfn s_mid witness <> dfn s_mid x).
               { intros Hw_eq_x. apply Hlow_ne_mid.
                 rewrite <- Hlow_eq_mid. exact Hw_eq_x. }
               lia. }
             assert (Hx_lt_next: dfn s_after x < dfn s_after next).
             { pose proof (preloop_after_visited_dfn_lt
                             x next) as Hhoare.
               unfold Hoare in Hhoare.
               exact (Hhoare s_mid retv s_after
                             (conj Hx_vis_mid
                               (conj Hnext_notvis Hdfn_inv_mid))
                             Hexec). }
             rewrite Hdfn_witness_pres.
             rewrite <- Hdfn_x_pres in Hw_lt_x.
             lia.
      + rewrite Hlow_pres, Hdfn_witness_pres.
        exact Hlow_eq_mid.
    - rewrite Hlow_pres, Hdfn_x_pres.
      exact Hlow_ne_mid.
  Qed.

  Lemma preloop_establishes_parent_output_frame_for_child_exact
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         s = s_before /\
         ParentRecursivePre g root parent child done s /\
         LoopOutputReady parent done s)
      (preloop child)
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    unfold Hoare.
    intros s0 retv s_after [Hs0 [Hpre Hready]] Hexec.
    subst s0.
    pose proof Hpre as Hpre_all.
    assert (Hparent_frame:
              ParentFrameForChild g root parent child done s_before s_after).
    { pose proof (preloop_establishes_parent_frame_for_child_exact
                    g root parent child done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s_before retv s_after
                        (conj eq_refl Hpre_all) Hexec)
        as [_ [_ Hframe]].
      exact Hframe. }
    split.
    - intros x Hpopped.
      eapply parent_frame_output_segment_cases; eauto.
    - split.
      + intros x Hpopped_old Htree_old.
        eapply partial_tree_done_mono.
        * intros a Hdone_a.
          apply done_after_intro_old. exact Hdone_a.
        * eapply preloop_preserves_partial_tree; eauto.
      + split.
        * intros x Hpopped_after Hpopped_old Htree_old Hx_ne_parent.
          eapply preloop_preserves_pending_low_for_old_partial; eauto.
        * split.
          -- intros x Hpopped_old Hx_ne_parent Hx_eq_child.
             pose proof Hpre_all as Hpre_for_vis.
             destruct Hpre_for_vis as [Hloop_parent [_ [Hentry_child _]]].
             destruct Hentry_child as [[_ Hchild_notvis] _].
             destruct Hloop_parent as [_ [Hshape_parent _]].
             destruct Hshape_parent as [Hwf_before _].
             destruct Hwf_before as [Hstack_vis_before _].
             assert (Hx_active_before: Active x s_before).
             { eapply popped_segment_in_stack; eauto. }
             assert (Hx_vis_before: Visited x s_before).
             { apply Hstack_vis_before. exact Hx_active_before. }
             apply Hchild_notvis.
             rewrite <- Hx_eq_child. exact Hx_vis_before.
          -- intros x Hpopped_old _ _ _.
             assert (Hx_active_before: Active x s_before).
             { eapply popped_segment_in_stack; eauto. }
             pose proof (preloop_old_stack_element_rest child x) as Hhoare.
             unfold Hoare in Hhoare.
             exact (Hhoare s_before retv s_after
                           Hx_active_before Hexec).
  Qed.

  Lemma preloop_preserves_nested_parent_output_frame
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St):
    Hoare
      (NestedOutputFramePre ancestor current loop_root next
         ancestor_done loop_done s_before)
      (preloop next)
      (fun _ s =>
         LoopInv g root next ∅ s /\
         LoopTraversalComplete g root next ∅ s /\
         ParentFrameForChild
           g root ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint
           g root ancestor current next ancestor_done s /\
         RestStack next s current /\
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s /\
         LoopOutputReady ancestor ancestor_done s_before /\
         (forall x,
           PoppedSegment ancestor s_before x ->
           x <> ancestor ->
           x <> next)).
  Proof.
    unfold Hoare.
    intros s_mid retv s_after Hpre Hexec.
    pose proof Hpre as Hpre_all.
    unfold NestedOutputFramePre in Hpre.
    destruct Hpre as [Hnested [Houtput_frame [Hready Hloop_not_old]]].
    pose proof Hnested as Hnested_for_ctx.
    pose proof Hnested as Hnested_for_current.
    assert (Hctx:
              LoopInv g root next ∅ s_after /\
              LoopTraversalComplete g root next ∅ s_after /\
              ParentFrameForChild
                g root ancestor current ancestor_done s_before s_after /\
              NestedFrameDisjoint
                g root ancestor current next ancestor_done s_after /\
              RestStack next s_after current).
    { pose proof (preloop_preserves_nested_parent_context_with_rest
                    g root ancestor current loop_root next
                    ancestor_done loop_done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_mid retv s_after Hnested_for_ctx Hexec). }
    destruct Hctx as
      [Hloop_next [Htraversal_next
        [Hparent_frame_after [Hdisjoint_after Hrest_next_current]]]].
    destruct Hnested_for_current as [_ [Hparent_frame_mid [_ [_ [_ [Hentry _]]]]]].
    destruct Hentry as [[_ Hnext_notvis] _].
    assert (Hcurrent_active_mid: Active current s_mid).
    { eapply parent_frame_child_active; eauto. }
    assert (Hcurrent_vis_mid: Visited current s_mid).
    { destruct Hparent_frame_mid as [_ [Hshape_mid _]].
      destruct Hshape_mid as [Hwf_mid _].
      destruct Hwf_mid as [Hstack_vis_mid _].
      apply Hstack_vis_mid. exact Hcurrent_active_mid. }
    assert (Hnext_ne_current: next <> current).
    { intros Hnext_eq_current. apply Hnext_notvis.
      rewrite Hnext_eq_current. exact Hcurrent_vis_mid. }
    destruct Houtput_frame as
      [Hsegment_mid [Hpartial_mid
        [Hpending_mid [Hcurrent_not_old Hrest_old]]]].
    assert (Houtput_after:
              ParentOutputFrameForChild
                ancestor current ancestor_done s_before s_after).
    { split.
      - intros x Hpopped_after.
        eapply parent_frame_output_segment_cases; eauto.
      - split.
        + intros x Hpopped_old Htree_old.
          eapply preloop_preserves_partial_tree; eauto.
        + split.
          * intros x Hpopped_after Hpopped_old Htree_old Hx_ne_ancestor.
            eapply preloop_preserves_nested_pending_low_for_old_partial;
              eauto.
          * split.
            -- exact Hcurrent_not_old.
            -- intros x Hpopped_old Htree_old Hx_ne_ancestor _.
               assert (Hrest_mid: RestStack current s_mid x).
               { exact (Hrest_old x Hpopped_old Htree_old
                          Hx_ne_ancestor Hcurrent_active_mid). }
               pose proof (preloop_preserves_rest_stack
                             next current x Hnext_ne_current) as Hhoare.
               unfold Hoare in Hhoare.
               exact (Hhoare s_mid retv s_after Hrest_mid Hexec). }
    assert (Hnext_not_old:
              forall x,
                PoppedSegment ancestor s_before x ->
                x <> ancestor ->
                x <> next).
    { intros x Hpopped_old _.
      eapply nested_output_frame_next_not_old; eauto. }
    exact (conj Hloop_next
            (conj Htraversal_next
              (conj Hparent_frame_after
                (conj Hdisjoint_after
                  (conj Hrest_next_current
                    (conj Houtput_after
                      (conj Hready Hnext_not_old))))))).
  Qed.

  Lemma set_fa_pending_preserves_parent_output_frame_for_child
        (parent child a p: V) (done: V -> Prop)
        (s_before: St):
    Hoare
      (fun s: St =>
         ~ Visited a s /\
         (forall z, done_after done child z -> Visited z s) /\
         ParentOutputFrameForChild parent child done s_before s)
      (set_fa a p)
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s.
    change
      (ParentOutputFrameForChild parent child done s_before
         (set_fa_state s0 a p)).
    destruct H as
      [Hnotvis [Hdone_vis [Hsegment [Hpartial
        [Hpending [Hchild_not_old Hrest_old]]]]]].
    split.
    - intros x Hpopped.
      assert (Hpopped_old: PoppedSegment parent s0 x).
      { unfold PoppedSegment in *.
        simpl in Hpopped |- *.
        exact Hpopped. }
      destruct (Hsegment x Hpopped_old) as [[Hactive_child Hpopped_child] | Hold].
      + left. split.
        * unfold Active in *. simpl. exact Hactive_child.
        * unfold PoppedSegment in *.
          simpl in Hpopped_child |- *.
          exact Hpopped_child.
      + right. exact Hold.
    - split.
      + intros x Hpopped_old Htree_old.
        specialize (Hpartial x Hpopped_old Htree_old).
        unfold PartialTree in Hpartial |- *.
        destruct Hpartial as [Hx_parent | Hchild_tree].
        * left. exact Hx_parent.
        * right.
          destruct Hchild_tree as
            [old_child [Hdone_child [Hedge_child
              [Hfa_child [Hfane_child Hreach_child_x]]]]].
          assert (Hold_child_ne_a: old_child <> a).
          { intros Heq. apply Hnotvis. rewrite <- Heq.
            apply Hdone_vis. exact Hdone_child. }
          exists old_child. repeat split; auto.
          -- rewrite set_fa_state_keep_other_fa; auto.
          -- rewrite set_fa_state_keep_other_fa; auto.
          -- apply (proj2 (set_fa_pending_tree_reachable_iff
                            g root s0 a p old_child x Hnotvis)).
             exact Hreach_child_x.
      + split.
        * intros x Hpopped_after Hpopped_old Htree_old Hx_ne_parent.
          assert (Hpopped_before: PoppedSegment parent s0 x).
          { unfold PoppedSegment in *.
            simpl in Hpopped_after |- *.
            exact Hpopped_after. }
          destruct (Hpending x Hpopped_before Hpopped_old Htree_old Hx_ne_parent)
            as [Hlow Hlow_ne].
          split.
          -- eapply set_fa_pending_preserves_scc_is_low_v; eauto.
          -- simpl. exact Hlow_ne.
        * split.
          -- exact Hchild_not_old.
          -- intros x Hpopped_old Htree_old Hx_ne_parent Hactive_child.
             unfold RestStack.
             simpl.
             exact (Hrest_old x Hpopped_old Htree_old
                      Hx_ne_parent Hactive_child).
  Qed.

  Lemma set_fa_pending_prepares_nested_output_frame_pre
        (parent child a: V) (done current_done: V -> Prop)
        (s_before: St):
    Hoare
      (fun s: St =>
         LoopInv g root child current_done s /\
         ParentFrameForChild g root parent child done s_before s /\
         ParentOutputFrameForChild parent child done s_before s /\
         LoopOutputReady parent done s_before /\
         Edge g child a /\
         ~ current_done a /\
         ~ Visited a s)
      (set_fa a child)
      (fun _ s =>
         NestedOutputFramePre parent child child a
           done current_done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2
      [Hloop [Hparent_frame [Houtput_frame
        [Hready_before [Hedge [Hnot_done Hnotvis]]]]]] Hexec.
    assert (Hnested:
              NestedFramePre g root parent child child a
                done current_done s_before s2).
    { pose proof (set_fa_pending_prepares_nested_frame_pre
                    g root parent child a done current_done s_before)
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hloop
                      (conj Hparent_frame
                        (conj Hedge
                          (conj Hnot_done Hnotvis))))
                    Hexec). }
    assert (Hdone_vis:
              forall z, done_after done child z -> Visited z s1).
    { unfold ParentFrameForChild in Hparent_frame.
      destruct Hparent_frame as [_ [Hshape _]].
      destruct Hshape as [_ [_ [_ [_ [Hdone_vis _]]]]].
      exact Hdone_vis. }
    assert (Houtput_frame_after:
              ParentOutputFrameForChild parent child done s_before s2).
    { pose proof (set_fa_pending_preserves_parent_output_frame_for_child
                    parent child a child done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hnotvis (conj Hdone_vis Houtput_frame))
                    Hexec). }
    unfold NestedOutputFramePre.
    pose proof Houtput_frame as Houtput_frame_before.
    destruct Houtput_frame_before as [_ [_ [_ [Hchild_not_old _]]]].
    exact (conj Hnested
            (conj Houtput_frame_after
              (conj Hready_before Hchild_not_old))).
  Qed.

  Lemma set_fa_pending_prepares_external_nested_output_frame_pre
        (ancestor current loop_root a: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St):
    Hoare
      (fun s: St =>
         LoopInv g root loop_root loop_done s /\
         ParentFrameForChild
           g root ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint
           g root ancestor current loop_root ancestor_done s /\
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s /\
         LoopOutputReady ancestor ancestor_done s_before /\
         (forall x,
           PoppedSegment ancestor s_before x ->
           x <> ancestor ->
           x <> loop_root) /\
         Edge g loop_root a /\
         ~ loop_done a /\
         ~ Visited a s)
      (set_fa a loop_root)
      (fun _ s =>
         NestedOutputFramePre ancestor current loop_root a
           ancestor_done loop_done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2
      [Hloop [Hparent_frame [Hdisjoint [Houtput_frame
        [Hready_before [Hloop_not_old
          [Hedge [Hnot_done Hnotvis]]]]]]]] Hexec.
    assert (Hnested:
              NestedFramePre g root ancestor current loop_root a
                ancestor_done loop_done s_before s2).
    { pose proof (set_fa_pending_prepares_external_nested_frame_pre
                    g root ancestor current loop_root a
                    ancestor_done loop_done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hloop
                      (conj Hparent_frame
                        (conj Hdisjoint
                          (conj Hedge
                            (conj Hnot_done Hnotvis)))))
                    Hexec). }
    assert (Hdone_vis:
              forall z,
                done_after ancestor_done current z -> Visited z s1).
    { unfold ParentFrameForChild in Hparent_frame.
      destruct Hparent_frame as [_ [Hshape _]].
      destruct Hshape as [_ [_ [_ [_ [Hdone_vis _]]]]].
      exact Hdone_vis. }
    assert (Houtput_frame_after:
              ParentOutputFrameForChild
                ancestor current ancestor_done s_before s2).
    { pose proof (set_fa_pending_preserves_parent_output_frame_for_child
                    ancestor current a loop_root ancestor_done s_before)
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hnotvis (conj Hdone_vis Houtput_frame))
                    Hexec). }
    unfold NestedOutputFramePre.
    exact (conj Hnested
            (conj Houtput_frame_after
              (conj Hready_before Hloop_not_old))).
  Qed.

  Lemma process_edge_preserves_parent_output_frame_for_child
        (parent child a: V) (done current_done: V -> Prop)
        (s_before: St) (W: RecProgram):
    VisitOutputFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv g root child current_done s /\
         ParentFrameForChild g root parent child done s_before s /\
         ParentOutputFrameForChild parent child done s_before s /\
         LoopOutputReady parent done s_before /\
         Edge g child a /\
         ~ current_done a)
      (process_edge child W a)
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    intros Houtput_contract.
    unfold process_edge, if_else.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: {
        eapply Hoare_bind with
          (Q := fun (_: unit) s =>
                  NestedOutputFramePre parent child child a
                    done current_done s_before s).
        - apply set_fa_pending_prepares_nested_output_frame_pre.
        - simpl. intros _.
          eapply Hoare_bind with
            (Q := fun (_: unit) s =>
                    ParentOutputFrameForChild
                      parent child done s_before s).
          + apply (Houtput_contract parent child child a
                     done current_done s_before).
          + simpl. intros _.
            apply get_low_update_low_child_preserves_parent_output_frame_for_child. }
      intros s1 [Hnotvis Hs1]. subst s1.
      destruct H as
        [Hloop [Hparent_frame [Houtput_frame
          [Hready_before [Hedge Hnot_done]]]]].
      exact (conj Hloop
              (conj Hparent_frame
                (conj Houtput_frame
                  (conj Hready_before
                    (conj Hedge
                      (conj Hnot_done Hnotvis)))))).
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_ Hs1]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: apply get_dfn_update_low_child_preserves_parent_output_frame_for_child.
        intros s1 [_ Hs1]. subst s1.
        destruct H as [_ [_ [Houtput_frame _]]].
        exact Houtput_frame.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        simpl. intros _ s [Heq _]. subst s.
        destruct H as [_ [_ [Houtput_frame _]]].
        exact Houtput_frame.
  Qed.

  Lemma process_edge_preserves_nested_parent_output_frame
        (ancestor current loop_root a: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St) (W: RecProgram):
    VisitOutputFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv g root loop_root loop_done s /\
         ParentFrameForChild
           g root ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint
           g root ancestor current loop_root ancestor_done s /\
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s /\
         LoopOutputReady ancestor ancestor_done s_before /\
         (forall x,
           PoppedSegment ancestor s_before x ->
           x <> ancestor ->
           x <> loop_root) /\
         Edge g loop_root a /\
         ~ loop_done a)
      (process_edge loop_root W a)
      (fun _ s =>
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s).
  Proof.
    intros Houtput_contract.
    unfold process_edge, if_else.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: {
        eapply Hoare_bind with
          (Q := fun (_: unit) s =>
                  NestedOutputFramePre ancestor current loop_root a
                    ancestor_done loop_done s_before s).
        - apply set_fa_pending_prepares_external_nested_output_frame_pre.
        - simpl. intros _.
          eapply Hoare_bind with
            (Q := fun (_: unit) s =>
                    ParentOutputFrameForChild
                      ancestor current ancestor_done s_before s).
          + apply (Houtput_contract ancestor current loop_root a
                     ancestor_done loop_done s_before).
          + simpl. intros _.
            apply get_low_update_low_preserves_parent_output_frame_for_child.
            intros x Hpopped_old Hx_ne_ancestor.
            destruct H as [_ [_ [_ [_ [_ [Hloop_not_old _]]]]]].
            exact (Hloop_not_old x Hpopped_old Hx_ne_ancestor). }
      intros s1 [Hnotvis Hs1]. subst s1.
      destruct H as
        [Hloop [Hparent_frame [Hdisjoint [Houtput_frame
          [Hready_before [Hloop_not_old [Hedge Hnot_done]]]]]]].
      exact (conj Hloop
              (conj Hparent_frame
                (conj Hdisjoint
                  (conj Houtput_frame
                    (conj Hready_before
                      (conj Hloop_not_old
                        (conj Hedge
                          (conj Hnot_done Hnotvis)))))))).
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_ Hs1]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: {
          apply get_dfn_update_low_preserves_parent_output_frame_for_child.
          intros x Hpopped_old Hx_ne_ancestor.
          destruct H as [_ [_ [_ [_ [_ [Hloop_not_old _]]]]]].
          exact (Hloop_not_old x Hpopped_old Hx_ne_ancestor). }
        intros s1 [_ Hs1]. subst s1.
        destruct H as [_ [_ [_ [Houtput_frame _]]]].
        exact Houtput_frame.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        simpl. intros _ s [Heq _]. subst s.
        destruct H as [_ [_ [_ [Houtput_frame _]]]].
        exact Houtput_frame.
  Qed.

  Lemma edge_loop_preserves_parent_output_frame_for_child
        (parent child: V) (done: V -> Prop) (s_before: St)
        (W: RecProgram):
    VisitChildContract g root W ->
    VisitFrameContract g root W ->
    VisitOutputFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv g root child ∅ s /\
         ParentFrameForChild g root parent child done s_before s /\
         ParentOutputFrameForChild parent child done s_before s /\
         LoopOutputReady parent done s_before)
      (forset (edge_set g child) (process_edge child W))
      (fun _ s =>
         LoopInv g root child (edge_set g child) s /\
         ParentFrameForChild g root parent child done s_before s /\
         ParentOutputFrameForChild parent child done s_before s /\
         LoopOutputReady parent done s_before).
  Proof.
    intros Hchild Hframe_contract Houtput_contract.
    apply Hoare_forset with
      (P := fun current_done s =>
              LoopInv g root child current_done s /\
              ParentFrameForChild g root parent child done s_before s /\
              ParentOutputFrameForChild parent child done s_before s /\
              LoopOutputReady parent done s_before)
      (universe := edge_set g child).
    - intros done1 done2 Hdone s1 s2 Heq. subst s2.
      split; intros [Hloop [Hparent_frame [Houtput_frame Hready]]].
      + split.
        * eapply loop_inv_done_equiv; eauto.
        * exact (conj Hparent_frame (conj Houtput_frame Hready)).
      + split.
        * eapply loop_inv_done_equiv.
          -- symmetry. exact Hdone.
          -- exact Hloop.
        * exact (conj Hparent_frame (conj Houtput_frame Hready)).
    - intros current_done a _ Hedge Hnot_done.
      apply Hoare_conj with
        (Q1 := fun _ s =>
                 LoopInv g root child (done_after current_done a) s).
      + eapply Hoare_conseq_pre.
        2: {
          eapply process_edge_preserves_loop_inv.
          eapply Hoare_conseq_pre.
          2: apply Hchild.
          intros s [Hloop [Hedge' [Hentry [Hfa Hfane]]]].
          unfold ParentRecursivePre.
          exact (conj Hloop
                  (conj Hedge'
                    (conj Hentry
                      (conj Hfa Hfane)))). }
        intros s [Hloop _].
        exact (conj Hloop (conj Hedge Hnot_done)).
      + apply Hoare_conj with
          (Q1 := fun _ s =>
                   ParentFrameForChild
                     g root parent child done s_before s).
        * eapply Hoare_conseq_pre.
          2: {
            apply (process_edge_preserves_parent_frame_for_child
                     g root parent child a done current_done
                     s_before W Hframe_contract). }
          intros s [Hloop [Hparent_frame _]].
          exact (conj Hloop
                  (conj Hparent_frame
                    (conj Hedge Hnot_done))).
        * apply Hoare_conj with
            (Q1 := fun _ s =>
                     ParentOutputFrameForChild
                       parent child done s_before s).
          -- eapply Hoare_conseq_pre.
             2: {
               apply (process_edge_preserves_parent_output_frame_for_child
                        parent child a done current_done s_before W
                        Houtput_contract). }
             intros s [Hloop [Hparent_frame [Houtput_frame Hready]]].
             exact (conj Hloop
                     (conj Hparent_frame
                       (conj Houtput_frame
                         (conj Hready
                           (conj Hedge Hnot_done))))).
          -- eapply Hoare_conseq_post.
             2: {
               unfold Hoare.
               intros s1 retv s2 [_ [_ [_ Hready]]] Hexec.
               exact Hready. }
             simpl. intros _ _ Hready.
             exact Hready.
  Qed.

  Lemma edge_loop_preserves_nested_parent_output_frame
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (s_before: St)
        (W: RecProgram):
    VisitChildContract g root W ->
    VisitFrameContract g root W ->
    VisitOutputFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv g root loop_root ∅ s /\
         ParentFrameForChild
           g root ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint
           g root ancestor current loop_root ancestor_done s /\
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s /\
         LoopOutputReady ancestor ancestor_done s_before /\
         (forall x,
           PoppedSegment ancestor s_before x ->
           x <> ancestor ->
           x <> loop_root))
      (forset (edge_set g loop_root) (process_edge loop_root W))
      (fun _ s =>
         LoopInv g root loop_root (edge_set g loop_root) s /\
         ParentFrameForChild
           g root ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint
           g root ancestor current loop_root ancestor_done s /\
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s /\
         LoopOutputReady ancestor ancestor_done s_before /\
         (forall x,
           PoppedSegment ancestor s_before x ->
           x <> ancestor ->
           x <> loop_root)).
  Proof.
    intros Hchild Hframe_contract Houtput_contract.
    apply Hoare_forset with
      (P := fun loop_done s =>
              LoopInv g root loop_root loop_done s /\
              ParentFrameForChild
                g root ancestor current ancestor_done s_before s /\
              NestedFrameDisjoint
                g root ancestor current loop_root ancestor_done s /\
              ParentOutputFrameForChild
                ancestor current ancestor_done s_before s /\
              LoopOutputReady ancestor ancestor_done s_before /\
              (forall x,
                PoppedSegment ancestor s_before x ->
                x <> ancestor ->
                x <> loop_root))
      (universe := edge_set g loop_root).
    - intros done1 done2 Hdone s1 s2 Heq. subst s2.
      split; intros
        [Hloop [Hparent_frame [Hdisjoint [Houtput_frame
          [Hready Hloop_not_old]]]]].
      + split.
        * eapply loop_inv_done_equiv; eauto.
        * exact (conj Hparent_frame
                  (conj Hdisjoint
                    (conj Houtput_frame
                      (conj Hready Hloop_not_old)))).
      + split.
        * eapply loop_inv_done_equiv.
          -- symmetry. exact Hdone.
          -- exact Hloop.
        * exact (conj Hparent_frame
                  (conj Hdisjoint
                    (conj Houtput_frame
                      (conj Hready Hloop_not_old)))).
    - intros loop_done a _ Hedge Hnot_done.
      apply Hoare_conj with
        (Q1 := fun _ s =>
                 LoopInv g root loop_root
                   (done_after loop_done a) s).
      + eapply Hoare_conseq_pre.
        2: {
          eapply process_edge_preserves_loop_inv.
          eapply Hoare_conseq_pre.
          2: apply Hchild.
          intros s [Hloop [Hedge' [Hentry [Hfa Hfane]]]].
          unfold ParentRecursivePre.
          exact (conj Hloop
                  (conj Hedge'
                    (conj Hentry
                      (conj Hfa Hfane)))). }
        intros s [Hloop _].
        exact (conj Hloop (conj Hedge Hnot_done)).
      + apply Hoare_conj with
          (Q1 := fun _ s =>
                   ParentFrameForChild
                     g root ancestor current ancestor_done s_before s).
        * eapply Hoare_conseq_post.
          2: {
            eapply Hoare_conseq_pre.
            2: {
              apply (process_edge_preserves_nested_parent_frame
                       g root ancestor current loop_root a
                       ancestor_done loop_done s_before W Hframe_contract). }
            intros s [Hloop [Hparent_frame [Hdisjoint _]]].
            exact (conj Hloop
                    (conj Hparent_frame
                      (conj Hdisjoint
                        (conj Hedge Hnot_done)))). }
          intros _ s [Hparent_frame _].
          exact Hparent_frame.
        * apply Hoare_conj with
            (Q1 := fun _ s =>
                     NestedFrameDisjoint
                       g root ancestor current loop_root ancestor_done s).
          -- eapply Hoare_conseq_post.
             2: {
               eapply Hoare_conseq_pre.
               2: {
                 apply (process_edge_preserves_nested_parent_frame
                          g root ancestor current loop_root a
                          ancestor_done loop_done s_before W Hframe_contract). }
               intros s [Hloop [Hparent_frame [Hdisjoint _]]].
               exact (conj Hloop
                       (conj Hparent_frame
                         (conj Hdisjoint
                           (conj Hedge Hnot_done)))). }
             intros _ s [_ Hdisjoint].
             exact Hdisjoint.
          -- apply Hoare_conj with
              (Q1 := fun _ s =>
                       ParentOutputFrameForChild
                         ancestor current ancestor_done s_before s).
             ++ eapply Hoare_conseq_pre.
                2: {
                  apply (process_edge_preserves_nested_parent_output_frame
                           ancestor current loop_root a ancestor_done loop_done
                           s_before W Houtput_contract). }
                intros s
                  [Hloop [Hparent_frame [Hdisjoint [Houtput_frame
                    [Hready Hloop_not_old]]]]].
                exact (conj Hloop
                        (conj Hparent_frame
                          (conj Hdisjoint
                            (conj Houtput_frame
                              (conj Hready
                                (conj Hloop_not_old
                                  (conj Hedge Hnot_done))))))).
             ++ apply Hoare_conj with
                 (Q1 := fun _ _ =>
                          LoopOutputReady ancestor ancestor_done s_before).
                ** eapply Hoare_conseq_post.
                   2: {
                     unfold Hoare.
                     intros s1 retv s2
                       [_ [_ [_ [_ [Hready _]]]]] Hexec.
                     exact Hready. }
                   simpl. intros _ _ Hready.
                   exact Hready.
                ** eapply Hoare_conseq_post.
                   2: {
                     unfold Hoare.
                     intros s1 retv s2
                       [_ [_ [_ [_ [_ Hloop_not_old]]]]] Hexec.
                     exact Hloop_not_old. }
                   simpl. intros _ _ Hloop_not_old.
	                   exact Hloop_not_old.
  Qed.

  Lemma edge_loop_preserves_nested_output_maybe_pop_context
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (s_before: St)
        (W: RecProgram):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitFrameContract g root W ->
    VisitOutputFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv g root loop_root ∅ s /\
         LoopTraversalComplete g root loop_root ∅ s /\
         ParentFrameForChild
           g root ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint
           g root ancestor current loop_root ancestor_done s /\
         RestStack loop_root s current /\
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s /\
         LoopOutputReady ancestor ancestor_done s_before /\
         (forall x,
           PoppedSegment ancestor s_before x ->
           x <> ancestor ->
           x <> loop_root))
      (forset (edge_set g loop_root) (process_edge loop_root W))
      (fun _ s =>
         RootPreMaybePop g root loop_root s /\
         ParentFrameForChild
           g root ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint
           g root ancestor current loop_root ancestor_done s /\
         RestStack loop_root s current /\
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s).
  Proof.
    intros Hchild Hchild_traversal Hframe_contract Houtput_contract.
    unfold Hoare.
    intros s1 retv s2 Hpre Hexec.
    destruct Hpre as
      [Hloop [Htraversal [Hparent_frame [Hdisjoint
        [Hrest [Houtput_frame [Hready Hloop_not_old]]]]]]].
    assert (Hctx:
              LoopInv g root loop_root (edge_set g loop_root) s2 /\
              RootTraversalComplete g root loop_root s2 /\
              ParentFrameForChild
                g root ancestor current ancestor_done s_before s2 /\
              NestedFrameDisjoint
                g root ancestor current loop_root ancestor_done s2 /\
              RestStack loop_root s2 current).
    { pose proof (edge_loop_preserves_nested_parent_context_with_rest
                    g root ancestor current loop_root ancestor_done
                    s_before W Hchild Hchild_traversal Hframe_contract)
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hloop
                      (conj Htraversal
                        (conj Hparent_frame
                          (conj Hdisjoint Hrest))))
                    Hexec). }
    assert (Houtput:
              LoopInv g root loop_root (edge_set g loop_root) s2 /\
              ParentFrameForChild
                g root ancestor current ancestor_done s_before s2 /\
              NestedFrameDisjoint
                g root ancestor current loop_root ancestor_done s2 /\
              ParentOutputFrameForChild
                ancestor current ancestor_done s_before s2 /\
              LoopOutputReady ancestor ancestor_done s_before /\
              (forall x,
                PoppedSegment ancestor s_before x ->
                x <> ancestor ->
                x <> loop_root)).
    { pose proof (edge_loop_preserves_nested_parent_output_frame
                    ancestor current loop_root ancestor_done s_before W
                    Hchild Hframe_contract Houtput_contract) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hloop
                      (conj Hparent_frame
                        (conj Hdisjoint
                          (conj Houtput_frame
                            (conj Hready Hloop_not_old)))))
                    Hexec). }
    destruct Hctx as
      [Hloop_after [Hroot_traversal
        [Hparent_after [Hdisjoint_after Hrest_after]]]].
    destruct Houtput as
      [_ [_ [_ [Houtput_after _]]]].
    split.
    - unfold RootPreMaybePop.
      exact (conj (conj Hloop_after
                    (loop_inv_derives_stack_rest_older_than_root
                       g root loop_root s2 Hloop_after))
                  Hroot_traversal).
    - exact (conj Hparent_after
              (conj Hdisjoint_after
                (conj Hrest_after Houtput_after))).
  Qed.

  Lemma set_fa_pending_preserves_loop_output_ready
        (u v p: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         ~ Visited v s /\
         LoopCoreShape g root u done s /\
         LoopOutputReady u done s)
      (set_fa v p)
      (fun _ s => LoopOutputReady u done s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s.
    change (LoopOutputReady u done (set_fa_state s0 v p)).
    destruct H as [Hnotvis [Hshape [Hpartial Hpending]]].
    destruct Hshape as [_ [_ [_ [_ [Hdone_vis _]]]]].
    split.
    - intros x Hpopped.
      assert (Hpopped_old: PoppedSegment u s0 x).
      { unfold PoppedSegment in *.
        simpl in Hpopped |- *.
        exact Hpopped. }
      destruct (Hpartial x Hpopped_old) as [Hx_eq_u | Hchild].
      + left. exact Hx_eq_u.
      + right.
        destruct Hchild as
          [child [Hdone_child [Hedge_child
            [Hfa_child [Hfane_child Hreach_child_x]]]]].
        assert (Hchild_ne_v: v <> child).
        { intros Hv_eq_child.
          apply Hnotvis. rewrite Hv_eq_child.
          apply Hdone_vis. exact Hdone_child. }
        exists child. repeat split; auto.
        * rewrite set_fa_state_keep_other_fa; auto.
        * rewrite set_fa_state_keep_other_fa; auto.
        * apply (proj2 (set_fa_pending_tree_reachable_iff
                          g root s0 v p child x Hnotvis)).
          exact Hreach_child_x.
    - intros x Hpopped Hx_ne_u.
      assert (Hpopped_old: PoppedSegment u s0 x).
      { unfold PoppedSegment in *.
        simpl in Hpopped |- *.
        exact Hpopped. }
      destruct (Hpending x Hpopped_old Hx_ne_u) as [Hlow Hlow_ne].
      split.
      + eapply set_fa_pending_preserves_scc_is_low_v; eauto.
      + simpl. exact Hlow_ne.
  Qed.

  Lemma update_low_preserves_loop_output_ready
        (u: V) (done: V -> Prop) (n: nat):
    Hoare
      (LoopOutputReady u done)
      (update_low u n)
      (fun _ s => LoopOutputReady u done s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s.
      destruct H as [Hpartial Hpending].
      split.
      + intros x Hpopped.
        apply Hpartial.
        unfold PoppedSegment in *.
        simpl in Hpopped |- *.
        exact Hpopped.
      + intros x Hpopped Hx_ne_u.
        assert (Hpopped_old: PoppedSegment u s0 x).
        { unfold PoppedSegment in *.
          simpl in Hpopped |- *.
          exact Hpopped. }
        destruct (Hpending x Hpopped_old Hx_ne_u) as [Hlow Hlow_ne].
        split.
        * unfold scc_is_low_v, scc_is_low_v_val in *.
          simpl.
          unfold equiv_decb.
          destruct (equiv_dec x u) as [Hx_eq_u | _].
          -- exfalso. apply Hx_ne_u. exact Hx_eq_u.
          -- exact Hlow.
        * simpl. unfold equiv_decb.
          destruct (equiv_dec x u) as [Hx_eq_u | _].
          -- exfalso. apply Hx_ne_u. exact Hx_eq_u.
          -- exact Hlow_ne.
    - destruct H1 as [Heq _]. subst s.
      exact H.
  Qed.

  Lemma get_low_update_low_preserves_loop_output_ready
        (u v: V) (done: V -> Prop):
    Hoare
      (LoopOutputReady u done)
      (lv <- get' (fun s => low s v);; update_low u lv)
      (fun _ s => LoopOutputReady u done s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_loop_output_ready.
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma get_dfn_update_low_preserves_loop_output_ready
        (u v: V) (done: V -> Prop):
    Hoare
      (LoopOutputReady u done)
      (dv <- get' (fun s => dfn s v);; update_low u dv)
      (fun _ s => LoopOutputReady u done s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_loop_output_ready.
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma get_low_update_low_preserves_output_triple
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         LoopOutputReady u done s /\
         SCCsOutputInv s /\
         VisitedValid s)
      (lv <- get' (fun s => low s v);; update_low u lv)
      (fun _ s =>
         LoopOutputReady u done s /\
         SCCsOutputInv s /\
         VisitedValid s).
  Proof.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopOutputReady u done s).
    - eapply Hoare_conseq_pre.
      2: apply get_low_update_low_preserves_loop_output_ready.
      intros s [Hready _]. exact Hready.
    - apply Hoare_conj with
        (Q1 := fun _ s => SCCsOutputInv s).
      + eapply Hoare_conseq_pre.
        2: apply get_low_update_low_preserves_sccs_output_inv.
        intros s [_ [Hout _]]. exact Hout.
      + eapply Hoare_conseq_pre.
        2: apply get_low_update_low_preserves_visited_valid.
        intros s [_ [_ Hvalid]]. exact Hvalid.
  Qed.

  Lemma get_dfn_update_low_preserves_output_triple
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         LoopOutputReady u done s /\
         SCCsOutputInv s /\
         VisitedValid s)
      (dv <- get' (fun s => dfn s v);; update_low u dv)
      (fun _ s =>
         LoopOutputReady u done s /\
         SCCsOutputInv s /\
         VisitedValid s).
  Proof.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopOutputReady u done s).
    - eapply Hoare_conseq_pre.
      2: apply get_dfn_update_low_preserves_loop_output_ready.
      intros s [Hready _]. exact Hready.
    - apply Hoare_conj with
        (Q1 := fun _ s => SCCsOutputInv s).
      + eapply Hoare_conseq_pre.
        2: apply get_dfn_update_low_preserves_sccs_output_inv.
        intros s [_ [Hout _]]. exact Hout.
      + eapply Hoare_conseq_pre.
        2: apply get_dfn_update_low_preserves_visited_valid.
        intros s [_ [_ Hvalid]]. exact Hvalid.
  Qed.

  Lemma set_fa_pending_prepares_child_output_pre
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         LoopInv g root u done s /\
         LoopTraversalComplete g root u done s /\
         LoopOutputReady u done s /\
         SCCsOutputInv s /\
         VisitedValid s /\
         Edge g u v /\
         ~ Visited v s)
      (set_fa v u)
      (fun _ s =>
         ParentRecursivePre g root u v done s /\
         LoopTraversalComplete g root u done s /\
         LoopOutputReady u done s /\
         SCCsOutputInv s /\
         VisitedValid s /\
         original_vvalid g v).
  Proof.
    unfold Hoare.
    intros s1 retv s2
      [Hloop [Htraversal [Hready [Hout [Hvalid [Hedge Hnotvis]]]]]]
      Hexec.
    assert (Hrecursive: ParentRecursivePre g root u v done s2).
    { pose proof (set_fa_pending_prepares_parent_recursive_pre
                    g root u v done) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hloop (conj Hedge Hnotvis)) Hexec). }
    assert (Hshape: LoopCoreShape g root u done s1).
    { destruct Hloop as [_ [Hshape _]]. exact Hshape. }
    assert (Hready_after: LoopOutputReady u done s2).
    { pose proof (set_fa_pending_preserves_loop_output_ready
                    u v u done) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hnotvis (conj Hshape Hready)) Hexec). }
    assert (Htraversal_after: LoopTraversalComplete g root u done s2).
    { pose proof (set_fa_pending_preserves_loop_traversal_complete_cmd
                    g root u done v u) as Hhoare.
      unfold Hoare in Hhoare.
      destruct Hshape as [_ [_ [_ [_ [Hdone_vis _]]]]].
      exact (Hhoare s1 retv s2
                    (conj Hnotvis (conj Hdone_vis Htraversal)) Hexec). }
    assert (Hout_after: SCCsOutputInv s2).
    { pose proof (set_fa_preserves_sccs_output_inv v u) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hout Hexec). }
    assert (Hvalid_after: VisitedValid s2).
    { pose proof (set_fa_preserves_visited_valid v u) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hvalid Hexec). }
    assert (Hv_valid: original_vvalid g v).
    { destruct (dg_step_vvalid g OriginalGraph_gvalid0 u v Hedge) as [_ Hv].
      exact Hv. }
    exact (conj Hrecursive
            (conj Htraversal_after
            (conj Hready_after
              (conj Hout_after
                (conj Hvalid_after Hv_valid))))).
  Qed.

  Lemma process_edge_preserves_output_ready
        (u v: V) (done: V -> Prop) (W: RecProgram):
    VisitChildOutputContract W ->
    Hoare
      (fun s: St =>
         LoopInv g root u done s /\
         LoopTraversalComplete g root u done s /\
         LoopOutputReady u done s /\
         SCCsOutputInv s /\
         VisitedValid s /\
         Edge g u v /\
         ~ done v)
      (process_edge u W v)
      (fun _ s =>
         LoopOutputReady u (done_after done v) s /\
         SCCsOutputInv s /\
         VisitedValid s).
  Proof.
    intros Hchild_output.
    unfold process_edge, if_else.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_bind with
        (Q := fun (_: unit) s =>
                ParentRecursivePre g root u v done s /\
                LoopTraversalComplete g root u done s /\
                LoopOutputReady u done s /\
                SCCsOutputInv s /\
                VisitedValid s /\
                original_vvalid g v).
      + eapply Hoare_conseq_pre.
        2: apply set_fa_pending_prepares_child_output_pre.
        intros s1 [Hnotvis Hs1]. subst s1.
        destruct H as
          [Hloop [Htraversal [Hready [Hout [Hvalid [Hedge _]]]]]].
        exact (conj Hloop
                (conj Htraversal
                (conj Hready
                  (conj Hout
                    (conj Hvalid
                      (conj Hedge Hnotvis)))))).
      + simpl. intros _.
        eapply Hoare_bind with
          (Q := fun (_: unit) s =>
                  LoopOutputReady u (done_after done v) s /\
                  SCCsOutputInv s /\
                  VisitedValid s).
        * eapply Hoare_conseq_post.
          2: { apply Hchild_output. }
          intros _ s
            [s_before
              [Hloop_before [Hedge
                [Hcontrib [Hready [Hout Hvalid]]]]]].
          exact (conj Hready (conj Hout Hvalid)).
        * simpl. intros _.
          apply get_low_update_low_preserves_output_triple.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hvisited_by_classic Hs1]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: apply get_dfn_update_low_preserves_output_triple.
        intros s1 [_ Hs1]. subst s1.
        destruct H as [_ [_ [Hready [Hout [Hvalid _]]]]].
        exact (conj (loop_output_ready_done_after u v done s0 Hready)
                (conj Hout Hvalid)).
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        simpl. intros _ s [Heq _]. subst s.
        destruct H as [_ [_ [Hready [Hout [Hvalid _]]]]].
        exact (conj (loop_output_ready_done_after u v done s0 Hready)
                (conj Hout Hvalid)).
  Qed.

  Lemma edge_loop_preserves_output_ready
        (u: V) (W: RecProgram):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitChildOutputContract W ->
    Hoare
      (fun s: St =>
         LoopInv g root u ∅ s /\
         LoopTraversalComplete g root u ∅ s /\
         LoopOutputReady u ∅ s /\
         SCCsOutputInv s /\
         VisitedValid s)
      (forset (edge_set g u) (process_edge u W))
      (fun _ s =>
         LoopInv g root u (edge_set g u) s /\
         LoopTraversalComplete g root u (edge_set g u) s /\
         LoopOutputReady u (edge_set g u) s /\
         SCCsOutputInv s /\
         VisitedValid s).
  Proof.
    intros Hchild Hchild_traversal Hchild_output.
    apply Hoare_forset with
      (P := fun done s =>
              LoopInv g root u done s /\
              LoopTraversalComplete g root u done s /\
              LoopOutputReady u done s /\
              SCCsOutputInv s /\
              VisitedValid s)
      (universe := edge_set g u).
    - intros done1 done2 Hdone s1 s2 Heq. subst s2.
      split; intros [Hloop [Htraversal [Hready [Hout Hvalid]]]].
      + split.
        * eapply loop_inv_done_equiv; eauto.
        * split.
          -- eapply loop_traversal_complete_done_equiv; eauto.
          -- split.
             ++ eapply loop_output_ready_done_equiv; eauto.
             ++ exact (conj Hout Hvalid).
      + split.
        * eapply loop_inv_done_equiv.
          -- symmetry. exact Hdone.
          -- exact Hloop.
        * split.
          -- eapply loop_traversal_complete_done_equiv.
             ++ symmetry. exact Hdone.
             ++ exact Htraversal.
          -- split.
             ++ eapply loop_output_ready_done_equiv.
                ** symmetry. exact Hdone.
                ** exact Hready.
             ++ exact (conj Hout Hvalid).
    - intros done a _ Hedge Hnot_done.
      apply Hoare_conj with
        (Q1 := fun _ s => LoopInv g root u (done_after done a) s).
      + eapply Hoare_conseq_pre.
        2: {
          eapply process_edge_preserves_loop_inv.
          eapply Hoare_conseq_pre.
          2: apply Hchild.
          intros s [Hloop [Hedge' [Hentry [Hfa Hfane]]]].
          unfold ParentRecursivePre.
          exact (conj Hloop
                  (conj Hedge'
                    (conj Hentry
                      (conj Hfa Hfane)))). }
        intros s [Hloop _].
        exact (conj Hloop (conj Hedge Hnot_done)).
      + apply Hoare_conj with
          (Q1 := fun _ s =>
                   LoopTraversalComplete g root u
                     (done_after done a) s).
        * eapply Hoare_conseq_pre.
          2: {
            eapply process_edge_preserves_loop_traversal_complete.
            exact Hchild_traversal. }
          intros s [Hloop [Htraversal _]].
          exact (conj Hloop
                  (conj Htraversal
                    (conj Hedge Hnot_done))).
        * eapply Hoare_conseq_pre.
          2: {
            eapply process_edge_preserves_output_ready.
            exact Hchild_output. }
          intros s [Hloop [Htraversal [Hready [Hout Hvalid]]]].
          exact (conj Hloop
                  (conj Htraversal
                    (conj Hready
                      (conj Hout
                        (conj Hvalid
                          (conj Hedge Hnot_done)))))).
  Qed.

  Lemma edge_loop_produces_root_output_ready
        (u: V) (W: RecProgram):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitChildOutputContract W ->
    Hoare
      (fun s: St =>
         LoopInv g root u ∅ s /\
         LoopTraversalComplete g root u ∅ s /\
         LoopOutputReady u ∅ s /\
         SCCsOutputInv s /\
         VisitedValid s)
      (forset (edge_set g u) (process_edge u W))
      (fun _ s =>
         LoopInv g root u (edge_set g u) s /\
         RootOutputReady u s /\
         SCCsOutputInv s /\
         VisitedValid s).
  Proof.
    intros Hchild Hchild_traversal Hchild_output.
    eapply Hoare_conseq_post.
    2: { apply edge_loop_preserves_output_ready; auto. }
    intros _ s [Hloop [_ [Hready [Hout Hvalid]]]].
    split; [exact Hloop |].
    split.
    - destruct Hloop as [_ [Hshape _]].
      eapply loop_output_ready_to_root_output_ready; eauto.
    - exact (conj Hout Hvalid).
  Qed.

  Lemma preloop_preserves_output_context
        (u: V):
    Hoare
      (fun s: St =>
         SCCsOutputInv s /\ VisitedValid s /\ original_vvalid g u)
      (preloop u)
      (fun _ s => SCCsOutputInv s /\ VisitedValid s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s.
    destruct H as [[Hsound Hcover] [Hvalid Hu_valid]].
    split.
    - split.
      + unfold SCCsSound in *. simpl. exact Hsound.
      + unfold SCCsCoverSettled in *.
        intros v Hvis Hnot_active.
        simpl in Hvis. sets_unfold in Hvis.
        destruct Hvis as [Hvis_old | Hv_eq_u].
        * apply Hcover.
          -- exact Hvis_old.
          -- unfold Active in *.
             intros Hv_stack.
             apply Hnot_active. simpl. right. exact Hv_stack.
        * subst v. exfalso.
          apply Hnot_active. unfold Active. simpl. left. reflexivity.
    - unfold VisitedValid in *.
      intros v Hvis.
      simpl in Hvis. sets_unfold in Hvis.
      destruct Hvis as [Hvis_old | Hv_eq_u].
      + apply Hvalid. exact Hvis_old.
      + subst v. exact Hu_valid.
  Qed.

  Lemma root_pre_maybe_pop_active_nodup
        (u: V) (s: St):
    RootPreMaybePop g root u s ->
    Active u s /\ StackNoDup s.
  Proof.
    intros [[Hloop _] _].
    destruct Hloop as [Haux _].
    destruct Haux as [_ [Hactive [_ [_ Hnodup]]]].
    exact (conj Hactive Hnodup).
  Qed.

  Lemma root_final_scc_is_low_v
        (u: V) (s: St):
    RootFinal g root u s ->
    scc_is_low_v g root s u.
  Proof.
    intros [_ [_ [_ Hlow]]].
    exact Hlow.
  Qed.

  Lemma pop_scc_state_scc_low_tree_lift_pre
        (root0 x target: V) (s: St):
    scc_low_tree g root (pop_scc_state s root0) x target ->
    scc_low_tree g root s x target.
  Proof.
    unfold scc_low_tree, scc_low_reachable, scc_back_edge.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s) root0) as [popped rest] eqn:Hsplit.
    simpl.
    intros [z [Hreach [Hz_eq | Hback]]].
    - exists z. split; [exact Hreach | left; exact Hz_eq].
    - destruct Hback as [Hedge [Hactive Hnot_tree]].
      exists z. split; [exact Hreach |].
      right. repeat split; auto.
      unfold Active.
      apply (stack_split_at_in_original
               (stack s) root0 target popped rest Hsplit).
      right. exact Hactive.
  Qed.

  Lemma pop_scc_state_preserves_scc_is_low_v_for_rest_low
        (root0 x: V) (s: St):
    RootPreMaybePop g root root0 s ->
    RestStack root0 s x ->
    scc_is_low_v g root s x ->
    low s x <> dfn s x ->
    scc_is_low_v g root (pop_scc_state s root0) x.
  Proof.
    intros Hroot Hx_rest Hx_low Hlow_ne.
    destruct Hroot as [[Hloop Hrest_older] _].
    destruct Hloop as [Haux [Hcore _]].
    destruct Haux as [_ [Hroot_active Horder]].
    destruct Hcore as [Hwf _].
    destruct Hrest_older as [_ Hrest_older].
    unfold scc_is_low_v, scc_is_low_v_val in *.
    unfold min_value_of_subset in *.
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
    assert (Htarget_active: Active target s).
    { unfold scc_low_tree, scc_low_reachable in Htarget_low.
      destruct Htarget_low as [z [Htree_x_z [Hz_eq_target | Hback]]].
      - subst target.
        pose proof (tree_reachable_dfn_monotone
                      g root s x z Hwf Htree_x_z) as Hx_le_z.
        exfalso. lia.
      - unfold scc_back_edge in Hback.
        destruct Hback as [_ [Hactive_target _]].
        exact Hactive_target. }
    assert (Htarget_rest: RestStack root0 s target).
    { assert (Htarget_lt_root: dfn s target < dfn s root0).
      { pose proof (Hrest_older x Hx_rest) as Hx_lt_root.
        lia. }
      eapply active_dfn_lt_root_rest_stack.
      - exact Horder.
      - exact Hroot_active.
      - exact Htarget_active.
      - exact Htarget_lt_root. }
    unfold pop_scc_state.
    destruct (stack_split_at (stack s) root0) as [popped rest] eqn:Hsplit.
    simpl.
    exists target. split.
    - unfold min_object_of_subset.
      split.
      + unfold scc_low_tree, scc_low_reachable in Htarget_low |- *.
        destruct Htarget_low as [z [Htree_x_z [Hz_eq_target | Hback]]].
        * exfalso.
          subst target.
          pose proof (tree_reachable_dfn_monotone
                        g root s x z Hwf Htree_x_z) as Hx_le_z.
          lia.
        * unfold scc_back_edge in Hback.
          destruct Hback as [Hedge [Hactive_target Hnot_tree]].
          exists z. split; [exact Htree_x_z |].
          right. unfold scc_back_edge.
          split; [exact Hedge |].
          split.
          -- unfold RestStack in Htarget_rest.
             rewrite Hsplit in Htarget_rest.
             exact Htarget_rest.
          -- intros Htree_post. exact (Hnot_tree Htree_post).
      + intros target' Htarget'_post.
        apply Htarget_min.
        apply pop_scc_state_scc_low_tree_lift_pre with (root0 := root0).
        unfold pop_scc_state.
        rewrite Hsplit.
        simpl.
        exact Htarget'_post.
    - exact Hlow_eq.
  Qed.

  Lemma pop_scc_state_preserves_partial_tree
        (center u x: V) (done: V -> Prop) (s: St):
    PartialTree g root center done s x ->
    PartialTree g root center done (pop_scc_state s u) x.
  Proof.
    intros Htree.
    unfold PartialTree in Htree |- *.
    destruct Htree as [Hx_center | Hchild].
    - left. exact Hx_center.
    - right.
      destruct Hchild as
        [child [Hdone [Hedge [Hfa [Hfane Hreach]]]]].
      exists child.
      repeat split; auto.
      + unfold pop_scc_state.
        destruct (stack_split_at (stack s) u) as [popped rest].
        simpl. exact Hfa.
      + unfold pop_scc_state.
        destruct (stack_split_at (stack s) u) as [popped rest].
        simpl. exact Hfane.
      + unfold pop_scc_state.
        destruct (stack_split_at (stack s) u) as [popped rest].
        simpl. exact Hreach.
  Qed.

  Lemma pop_scc_preserves_parent_output_frame_for_child
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         RootPreMaybePop g root child s /\
         ParentFrameForChild g root parent child done s_before s /\
         ParentOutputFrameForChild parent child done s_before s)
      (pop_scc child)
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hroot [Hparent_frame Houtput_frame]] Hexec.
    pose proof Hroot as Hroot_all.
    destruct Hroot as [[Hloop_child _] _].
    destruct Hloop_child as [Haux_child _].
    destruct Haux_child as [_ [Hchild_active [_ [_ Hnodup_child]]]].
    unfold ParentFrameForChild in Hparent_frame.
    destruct Hparent_frame as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hparent_frame_tail].
    destruct Hparent_frame_tail as [_ Hbelow_child].
    destruct Hbelow_child as [Hbelow_child _].
    assert (Hchild_rest_parent: RestStack child s1 parent).
    { apply Hbelow_child. apply partial_low_candidate_root. }
    destruct Houtput_frame as
      [Hsegment [Hpartial [Hpending [Hchild_not_old Hrest_old]]]].
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    split.
    - intros x Hpopped_after.
      assert (Hpopped_before: PoppedSegment parent s1 x).
      { eapply popped_segment_after_pop_lift_original; eauto. }
      destruct (Hsegment x Hpopped_before)
        as [[_ Hpopped_child] | Hpopped_old].
      + assert (Hrest_child_x: RestStack child s1 x).
        { exact (popped_segment_after_pop_in_root_rest
                   child parent x s1 Hpopped_after). }
        exfalso.
        unfold PoppedSegment, RestStack in *.
        destruct (stack_split_at (stack s1) child)
          as [popped rest] eqn:Hsplit.
        eapply stack_split_at_popped_rest_disjoint; eauto.
      + right. exact Hpopped_old.
    - split.
      + intros x Hpopped_old Htree_old.
        apply pop_scc_state_preserves_partial_tree.
        apply Hpartial.
        * exact Hpopped_old.
        * exact Htree_old.
      + split.
        * intros x Hpopped_after Hpopped_old Htree_old Hx_ne_parent.
          assert (Hpopped_before: PoppedSegment parent s1 x).
          { eapply popped_segment_after_pop_lift_original; eauto. }
          destruct (Hpending x Hpopped_before Hpopped_old Htree_old Hx_ne_parent)
            as [Hlow Hlow_ne].
          assert (Hrest_child_x: RestStack child s1 x).
          { exact (popped_segment_after_pop_in_root_rest
                     child parent x s1 Hpopped_after). }
          split.
          -- eapply pop_scc_state_preserves_scc_is_low_v_for_rest_low; eauto.
          -- unfold pop_scc_state.
             destruct (stack_split_at (stack s1) child) as [popped rest].
             simpl. exact Hlow_ne.
        * split.
          -- exact Hchild_not_old.
          -- intros x _ _ _ Hchild_active_after.
             exfalso.
             unfold Active in Hchild_active_after.
             unfold pop_scc_state in Hchild_active_after.
             destruct (stack_split_at (stack s1) child)
               as [popped rest] eqn:Hsplit.
             simpl in Hchild_active_after.
             assert (Hchild_popped: In child popped).
             { eapply stack_split_at_root_in_popped; eauto. }
             eapply stack_split_at_popped_rest_disjoint; eauto.
  Qed.

  Lemma pop_scc_preserves_nested_parent_output_frame
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         RootPreMaybePop g root loop_root s /\
         ParentFrameForChild
           g root ancestor current ancestor_done s_before s /\
         RestStack loop_root s current /\
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s)
      (pop_scc loop_root)
      (fun _ s =>
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2
      [Hroot [Hparent_frame [Hroot_current Houtput_frame]]] Hexec.
    pose proof Hroot as Hroot_all.
    destruct (root_pre_maybe_pop_active_nodup
                loop_root s1 Hroot) as [_ Hnodup_root].
    assert (Hcurrent_rest_ancestor: RestStack current s1 ancestor).
    { eapply parent_frame_child_rest_parent; eauto. }
    assert (Hroot_rest_ancestor: RestStack loop_root s1 ancestor).
    { eapply rest_stack_trans; eauto. }
    destruct Houtput_frame as
      [Hsegment [Hpartial [Hpending [Hcurrent_not_old Hrest_old]]]].
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    split.
    - intros x Hpopped_after.
      assert (Hpopped_before: PoppedSegment ancestor s1 x).
      { eapply popped_segment_after_pop_lift_original; eauto. }
      assert (Hroot_rest_x: RestStack loop_root s1 x).
      { exact (popped_segment_after_pop_in_root_rest
                 loop_root ancestor x s1 Hpopped_after). }
      destruct (Hsegment x Hpopped_before)
        as [[_ Hpopped_current_before] | Hpopped_old].
      + left. split.
        * unfold pop_scc_state.
          unfold RestStack in Hroot_current.
          destruct (stack_split_at (stack s1) loop_root)
            as [popped rest] eqn:Hsplit.
          simpl. exact Hroot_current.
        * eapply popped_segment_after_pop_preserves_of_rest; eauto.
      + right. exact Hpopped_old.
    - split.
      + intros x Hpopped_old Htree_old.
        apply pop_scc_state_preserves_partial_tree.
        apply Hpartial.
        * exact Hpopped_old.
        * exact Htree_old.
      + split.
        * intros x Hpopped_after Hpopped_old Htree_old Hx_ne_ancestor.
          assert (Hpopped_before: PoppedSegment ancestor s1 x).
          { eapply popped_segment_after_pop_lift_original; eauto. }
          destruct (Hpending x Hpopped_before Hpopped_old Htree_old Hx_ne_ancestor)
            as [Hlow Hlow_ne].
          assert (Hroot_rest_x: RestStack loop_root s1 x).
          { exact (popped_segment_after_pop_in_root_rest
                     loop_root ancestor x s1 Hpopped_after). }
          split.
          -- eapply pop_scc_state_preserves_scc_is_low_v_for_rest_low; eauto.
          -- unfold pop_scc_state.
             destruct (stack_split_at (stack s1) loop_root) as [popped rest].
             simpl. exact Hlow_ne.
        * split.
          -- exact Hcurrent_not_old.
          -- intros x Hpopped_old Htree_old Hx_ne_ancestor _.
             assert (Hcurrent_active_before: Active current s1).
             { eapply rest_stack_root_active; eauto. }
             assert (Hrest_current_x: RestStack current s1 x).
             { exact (Hrest_old x Hpopped_old Htree_old
                        Hx_ne_ancestor Hcurrent_active_before). }
             eapply rest_stack_after_pop_preserves_nested; eauto.
  Qed.

  Lemma maybe_pop_preserves_parent_output_frame_for_child
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         RootPreMaybePop g root child s /\
         ParentFrameForChild g root parent child done s_before s /\
         ParentOutputFrameForChild parent child done s_before s)
      (If (fun s => low s child = dfn s child) (pop_scc child))
      (fun _ s =>
         ParentOutputFrameForChild parent child done s_before s).
  Proof.
    unfold If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: apply pop_scc_preserves_parent_output_frame_for_child.
      intros s1 [_ Hs1]. subst s1.
      exact H.
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume_s. }
      simpl. intros _ s [Heq _]. subst s.
      destruct H as [_ [_ Houtput_frame]].
      exact Houtput_frame.
  Qed.

  Lemma maybe_pop_preserves_nested_parent_output_frame
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         RootPreMaybePop g root loop_root s /\
         ParentFrameForChild
           g root ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint
           g root ancestor current loop_root ancestor_done s /\
         RestStack loop_root s current /\
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s)
      (If (fun s => low s loop_root = dfn s loop_root)
          (pop_scc loop_root))
      (fun _ s =>
         ParentOutputFrameForChild
           ancestor current ancestor_done s_before s).
  Proof.
    unfold If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: apply pop_scc_preserves_nested_parent_output_frame.
      intros s1 [_ Hs1]. subst s1.
      destruct H as [Hroot [Hparent_frame [_ [Hrest Houtput_frame]]]].
      exact (conj Hroot
              (conj Hparent_frame
                (conj Hrest Houtput_frame))).
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume_s. }
      simpl. intros _ s [Heq _]. subst s.
      destruct H as [_ [_ [_ [_ Houtput_frame]]]].
      exact Houtput_frame.
  Qed.

  Lemma maybe_pop_preserves_output_inv_from_tree_and_pending_low
        (u: V):
    Hoare
      (fun s: St =>
         SCCsOutputInv s /\
         VisitedValid s /\
         RootPreMaybePop g root u s /\
         PoppedSegmentTreeReachableFromRoot u s /\
         PoppedSegmentPendingLow u s)
      (If (fun s => low s u = dfn s u) (pop_scc u))
      (fun _ s => SCCsOutputInv s).
  Proof.
    unfold If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: apply pop_scc_preserves_output_inv_from_tree_and_pending_low.
      intros s1 [Hcond Hs1]. subst s1.
      destruct H as [Hout [Hvalid [Hroot [Htree Hpending]]]].
      destruct Hroot as [Hpre Htraversal].
      assert (Hcuts: RootPopCuts g u s0).
      { exact (root_pre_maybe_pop_low_eq_derives_pop_cuts
                 g root u s0 (conj Hpre Htraversal) Hcond). }
      exact (conj Hout
              (conj Hvalid
                (conj (conj Hpre Hcond)
                  (conj Hcuts
                    (conj Htree Hpending))))).
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume_s. }
      simpl. intros _ s [Heq _]. subst s.
      destruct H as [Hout _].
      exact Hout.
  Qed.

  Lemma maybe_pop_produces_root_output_post_from_ready
        (u: V):
    Hoare
      (fun s: St =>
         SCCsOutputInv s /\
         VisitedValid s /\
         RootPreMaybePop g root u s /\
         RootOutputReady u s)
      (If (fun s => low s u = dfn s u) (pop_scc u))
      (fun _ s => RootOutputPost u s).
  Proof.
    unfold If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold Hoare.
      intros s1 retv s2 [Hcond Hs1] Hexec. subst s1.
      destruct H as [Hout [Hvalid [Hroot [Htree Hpending]]]].
      destruct Hroot as [Hpre Htraversal].
      assert (Hcuts: RootPopCuts g u s0).
      { exact (root_pre_maybe_pop_low_eq_derives_pop_cuts
                 g root u s0 (conj Hpre Htraversal) Hcond). }
      assert (Hfinal: RootFinal g root u s2).
      { pose proof (maybe_pop_pop_produces_root_final_from_pop_cuts
                      g root u) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s0 retv s2
                      (conj (conj Hpre Hcond) Hcuts) Hexec). }
      assert (Hout_after: SCCsOutputInv s2).
      { pose proof (pop_scc_preserves_output_inv_from_tree_and_pending_low
                      u) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s0 retv s2
                      (conj Hout
                        (conj Hvalid
                          (conj (conj Hpre Hcond)
                            (conj Hcuts
                              (conj Htree Hpending)))))
                      Hexec). }
      assert (Hvalid_after: VisitedValid s2).
      { pose proof (pop_scc_preserves_visited_valid u) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s0 retv s2 Hvalid Hexec). }
      assert (Hnot_active_after: ~ Active u s2).
      { pose proof (pop_scc_removes_root u) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s0 retv s2
                      (root_pre_maybe_pop_active_nodup
                         u s0 (conj Hpre Htraversal))
                      Hexec). }
      unfold RootOutputPost.
      split; [exact Hfinal |].
      split; [exact Hout_after |].
      split; [exact Hvalid_after |].
      unfold RootActiveOutputReady.
      intros Hactive_after.
      exfalso. exact (Hnot_active_after Hactive_after).
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume_s. }
      simpl. intros _ s [Heq Hnot_cond]. subst s.
      destruct H as [Hout [Hvalid [Hroot Hready]]].
      destruct Hroot as [Hpre Htraversal].
      assert (Hfinal: RootFinal g root u s0).
      { apply maybe_pop_skip_produces_root_final.
        unfold RootSkipBranchPre.
        exact (conj Hpre Hnot_cond). }
      unfold RootOutputPost.
      split; [exact Hfinal |].
      split; [exact Hout |].
      split; [exact Hvalid |].
      unfold RootActiveOutputReady.
      intros _.
      split.
      + eapply root_final_scc_is_low_v; eauto.
      + split; [exact Hnot_cond | exact Hready].
  Qed.

  Lemma preloop_initializes_output_edge_loop_pre
        (u: V):
    Hoare
      (fun s: St =>
         EntryPre g root u s /\
         original_vvalid g u /\
         SCCsOutputInv s /\
         VisitedValid s)
      (preloop u)
      (fun _ s =>
         LoopInv g root u ∅ s /\
         LoopTraversalComplete g root u ∅ s /\
         LoopOutputReady u ∅ s /\
         SCCsOutputInv s /\
         VisitedValid s).
  Proof.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopInv g root u ∅ s).
    - eapply Hoare_conseq_post.
      2: {
        eapply Hoare_conseq_pre.
        2: apply (preloop_initializes_edge_loop_pre g root u).
        intros s [Hentry _]. exact Hentry. }
      intros _ s [Hloop _]. exact Hloop.
    - apply Hoare_conj with
        (Q1 := fun _ s => LoopTraversalComplete g root u ∅ s).
      + eapply Hoare_conseq_pre.
        2: apply preloop_initializes_loop_traversal_complete_empty.
        intros s [Hentry _]. exact Hentry.
      + apply Hoare_conj with
          (Q1 := fun _ s => LoopOutputReady u ∅ s).
        * eapply Hoare_conseq_pre.
          2: apply preloop_initializes_loop_output_ready_empty.
          intros s [Hentry _]. exact Hentry.
        * eapply Hoare_conseq_pre.
          2: apply preloop_preserves_output_context.
          intros s [_ [Hu_valid [Hout Hvalid]]].
          exact (conj Hout (conj Hvalid Hu_valid)).
  Qed.

  Lemma edge_loop_produces_root_output_pre
        (u: V) (W: RecProgram):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitChildOutputContract W ->
    Hoare
      (fun s: St =>
         LoopInv g root u ∅ s /\
         LoopTraversalComplete g root u ∅ s /\
         LoopOutputReady u ∅ s /\
         SCCsOutputInv s /\
         VisitedValid s)
      (forset (edge_set g u) (process_edge u W))
      (fun _ s =>
         RootPreMaybePop g root u s /\
         RootOutputReady u s /\
         SCCsOutputInv s /\
         VisitedValid s).
  Proof.
    intros Hchild Hchild_traversal Hchild_output.
    apply Hoare_conj with
      (Q1 := fun _ s => RootPreMaybePop g root u s).
    - eapply Hoare_conseq_pre.
      2: {
        apply edge_loop_preserves_root_pre_maybe_pop_from_traversal_contract;
          auto. }
      intros s [Hloop [Htraversal _]].
      exact (conj Hloop Htraversal).
    - eapply Hoare_conseq_post.
      2: {
        eapply Hoare_conseq_pre.
        2: { apply edge_loop_produces_root_output_ready; auto. }
        intros s [Hloop [Htraversal [Hready [Hout Hvalid]]]].
        exact (conj Hloop
                (conj Htraversal
                  (conj Hready (conj Hout Hvalid)))). }
      intros _ s [Hloop [Hready [Hout Hvalid]]].
      exact (conj Hready (conj Hout Hvalid)).
  Qed.

  Theorem tarjan_scc_f_produces_root_output_post
        (W: RecProgram) (u: V):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitChildOutputContract W ->
    Hoare
      (fun s: St =>
         EntryPre g root u s /\
         original_vvalid g u /\
         SCCsOutputInv s /\
         VisitedValid s)
      (tarjan_scc_f g W u)
      (fun _ s => RootOutputPost u s).
  Proof.
    intros Hchild Hchild_traversal Hchild_output.
    unfold tarjan_scc_f.
    eapply Hoare_bind.
    { apply preloop_initializes_output_edge_loop_pre. }
    simpl. intros _.
    eapply Hoare_bind.
    { apply edge_loop_produces_root_output_pre; auto. }
    simpl. intros _.
    eapply Hoare_conseq_pre.
    2: apply maybe_pop_produces_root_output_post_from_ready.
    intros s [Hroot [Hready [Hout Hvalid]]].
    exact (conj Hout (conj Hvalid (conj Hroot Hready))).
  Qed.

  Lemma preloop_establishes_child_output_context_for_parent
        (parent child: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         ParentRecursivePre g root parent child done s /\
         LoopOutputReady parent done s /\
         SCCsOutputInv s /\
         VisitedValid s /\
         original_vvalid g child)
      (preloop child)
      (fun _ s =>
         exists s_before,
           LoopInv g root child ∅ s /\
           LoopTraversalComplete g root child ∅ s /\
           LoopOutputReady child ∅ s /\
           LoopInv g root parent done s_before /\
           Edge g parent child /\
           ParentFrameForChild g root parent child done s_before s /\
           ParentOutputFrameForChild parent child done s_before s /\
           LoopOutputReady parent done s_before /\
           SCCsOutputInv s /\
           VisitedValid s).
  Proof.
    unfold Hoare.
    intros s0 retv s1
      [Hrecursive [Hready_parent [Hout [Hvalid Hchild_valid]]]] Hexec.
    pose proof Hrecursive as Hrecursive_all.
    destruct Hrecursive as [_ [Hedge [Hentry _]]].
    assert (Hframe_pack:
              LoopInv g root child ∅ s1 /\
              LoopInv g root parent done s0 /\
              ParentFrameForChild g root parent child done s0 s1).
    { pose proof (preloop_establishes_parent_frame_for_child_exact
                    g root parent child done s0) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s0 retv s1
                    (conj eq_refl Hrecursive_all) Hexec). }
    destruct Hframe_pack as
      [Hloop_child [Hloop_parent Hparent_frame]].
    assert (Htraversal_child: LoopTraversalComplete g root child ∅ s1).
    { pose proof (preloop_initializes_loop_traversal_complete_empty
                    g root child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s0 retv s1 Hentry Hexec). }
    assert (Hready_child: LoopOutputReady child ∅ s1).
    { pose proof (preloop_initializes_loop_output_ready_empty child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s0 retv s1 Hentry Hexec). }
    assert (Houtput_frame:
              ParentOutputFrameForChild parent child done s0 s1).
    { pose proof (preloop_establishes_parent_output_frame_for_child_exact
                    parent child done s0) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s0 retv s1
                    (conj eq_refl (conj Hrecursive_all Hready_parent))
                    Hexec). }
    assert (Hout_valid_after: SCCsOutputInv s1 /\ VisitedValid s1).
    { pose proof (preloop_preserves_output_context child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s0 retv s1
                    (conj Hout (conj Hvalid Hchild_valid)) Hexec). }
    destruct Hout_valid_after as [Hout_after Hvalid_after].
    exists s0.
    exact (conj Hloop_child
            (conj Htraversal_child
              (conj Hready_child
                (conj Hloop_parent
                  (conj Hedge
                    (conj Hparent_frame
                      (conj Houtput_frame
                        (conj Hready_parent
                          (conj Hout_after Hvalid_after))))))))).
  Qed.

  Lemma edge_loop_produces_child_output_context_for_parent
        (parent child: V) (done: V -> Prop) (W: RecProgram):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitFrameContract g root W ->
    VisitOutputFrameContract W ->
    VisitChildOutputContract W ->
    Hoare
      (fun s: St =>
         exists s_before,
           LoopInv g root child ∅ s /\
           LoopTraversalComplete g root child ∅ s /\
           LoopOutputReady child ∅ s /\
           LoopInv g root parent done s_before /\
           Edge g parent child /\
           ParentFrameForChild g root parent child done s_before s /\
           ParentOutputFrameForChild parent child done s_before s /\
           LoopOutputReady parent done s_before /\
           SCCsOutputInv s /\
           VisitedValid s)
      (forset (edge_set g child) (process_edge child W))
      (fun _ s =>
         exists s_before,
           RootPreMaybePop g root child s /\
           RootOutputReady child s /\
           LoopInv g root parent done s_before /\
           Edge g parent child /\
           ParentFrameForChild g root parent child done s_before s /\
           ParentOutputFrameForChild parent child done s_before s /\
           LoopOutputReady parent done s_before /\
           SCCsOutputInv s /\
           VisitedValid s).
  Proof.
    intros Hchild Hchild_traversal Hframe_contract
           Houtput_frame_contract Hchild_output.
    unfold Hoare.
    intros s1 retv s2 Hpre Hexec.
    destruct Hpre as [s_before Hpre].
    destruct Hpre as [Hloop_child Hpre].
    destruct Hpre as [Htraversal_child Hpre].
    destruct Hpre as [Hready_child Hpre].
    destruct Hpre as [Hloop_parent Hpre].
    destruct Hpre as [Hedge Hpre].
    destruct Hpre as [Hparent_frame Hpre].
    destruct Hpre as [Houtput_frame Hpre].
    destruct Hpre as [Hready_parent [Hout Hvalid]].
    assert (Hroot_output:
              RootPreMaybePop g root child s2 /\
              RootOutputReady child s2 /\
              SCCsOutputInv s2 /\
              VisitedValid s2).
    { pose proof (edge_loop_produces_root_output_pre
                    child W Hchild Hchild_traversal Hchild_output)
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hloop_child
                      (conj Htraversal_child
                        (conj Hready_child (conj Hout Hvalid))))
                    Hexec). }
    assert (Hparent_frame_after:
              ParentFrameForChild g root parent child done s_before s2).
    { pose proof (edge_loop_preserves_parent_frame_for_child
                    g root parent child done s_before W
                    Hchild Hframe_contract) as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s1 retv s2
                      (conj Hloop_child Hparent_frame) Hexec)
        as [_ Hframe_after].
      exact Hframe_after. }
    assert (Houtput_frame_after:
              ParentOutputFrameForChild parent child done s_before s2).
    { pose proof (edge_loop_preserves_parent_output_frame_for_child
                    parent child done s_before W
                    Hchild Hframe_contract Houtput_frame_contract)
        as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s1 retv s2
                      (conj Hloop_child
                        (conj Hparent_frame
                          (conj Houtput_frame Hready_parent))) Hexec)
        as [_ [_ [Houtput_after _]]].
      exact Houtput_after. }
    destruct Hroot_output as [Hroot [Hroot_ready [Hout_after Hvalid_after]]].
    exists s_before.
    exact (conj Hroot
            (conj Hroot_ready
              (conj Hloop_parent
                (conj Hedge
                  (conj Hparent_frame_after
                    (conj Houtput_frame_after
                      (conj Hready_parent
                        (conj Hout_after Hvalid_after)))))))).
  Qed.

  Lemma maybe_pop_produces_child_output_contract_from_context
        (parent child: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         exists s_before,
           RootPreMaybePop g root child s /\
           RootOutputReady child s /\
           LoopInv g root parent done s_before /\
           Edge g parent child /\
           ParentFrameForChild g root parent child done s_before s /\
           ParentOutputFrameForChild parent child done s_before s /\
           LoopOutputReady parent done s_before /\
           SCCsOutputInv s /\
           VisitedValid s)
      (If (fun s => low s child = dfn s child) (pop_scc child))
      (fun _ s =>
         exists s_before,
           LoopInv g root parent done s_before /\
           Edge g parent child /\
           ChildContributionContract g root parent child done s_before s /\
           LoopOutputReady parent (done_after done child) s /\
           SCCsOutputInv s /\
           VisitedValid s).
  Proof.
    unfold Hoare.
    intros s2 retv s3 Hpre Hexec.
    destruct Hpre as [s_before Hpre].
    destruct Hpre as [Hroot Hpre].
    destruct Hpre as [Hroot_ready Hpre].
    destruct Hpre as [Hloop_parent Hpre].
    destruct Hpre as [Hedge Hpre].
    destruct Hpre as [Hparent_frame Hpre].
    destruct Hpre as [Houtput_frame Hpre].
    destruct Hpre as [Hready_parent [Hout Hvalid]].
    assert (Hroot_post: RootOutputPost child s3).
    { pose proof (maybe_pop_produces_root_output_post_from_ready child)
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s2 retv s3
                    (conj Hout
                      (conj Hvalid
                        (conj Hroot Hroot_ready))) Hexec). }
    assert (Hchild_contribution:
              ChildContributionContract g root parent child done s_before s3).
    { pose proof (maybe_pop_produces_child_contribution
                    g root parent child done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s2 retv s3
                    (conj Hroot Hparent_frame) Hexec). }
    assert (Houtput_frame_after:
              ParentOutputFrameForChild parent child done s_before s3).
    { pose proof (maybe_pop_preserves_parent_output_frame_for_child
                    parent child done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s2 retv s3
                    (conj Hroot
                      (conj Hparent_frame Houtput_frame)) Hexec). }
    assert (Hready_parent_after:
              LoopOutputReady parent (done_after done child) s3).
    { eapply parent_output_frame_to_loop_output_ready; eauto. }
    unfold RootOutputPost in Hroot_post.
    destruct Hroot_post as [_ [Hout_after [Hvalid_after _]]].
    exists s_before.
    exact (conj Hloop_parent
            (conj Hedge
              (conj Hchild_contribution
                (conj Hready_parent_after
                  (conj Hout_after Hvalid_after))))).
  Qed.

  Theorem tarjan_scc_f_produces_child_output_contract
        (W: RecProgram) (parent child: V) (done: V -> Prop):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitFrameContract g root W ->
    VisitOutputFrameContract W ->
    VisitChildOutputContract W ->
    Hoare
      (fun s: St =>
         ParentRecursivePre g root parent child done s /\
         LoopTraversalComplete g root parent done s /\
         LoopOutputReady parent done s /\
         SCCsOutputInv s /\
         VisitedValid s /\
         original_vvalid g child)
      (tarjan_scc_f g W child)
      (fun _ s =>
         exists s_before,
           LoopInv g root parent done s_before /\
           Edge g parent child /\
           ChildContributionContract g root parent child done s_before s /\
           LoopOutputReady parent (done_after done child) s /\
           SCCsOutputInv s /\
           VisitedValid s).
  Proof.
    intros Hchild Hchild_traversal Hframe_contract
           Houtput_frame_contract Hchild_output.
    unfold tarjan_scc_f.
    eapply Hoare_bind.
    { eapply Hoare_conseq_pre.
      2: apply preloop_establishes_child_output_context_for_parent.
      intros s [Hrecursive [_ [Hready [Hout [Hvalid Hchild_valid]]]]].
      exact (conj Hrecursive
              (conj Hready
                (conj Hout
                  (conj Hvalid Hchild_valid)))). }
    simpl. intros _.
    eapply Hoare_bind.
    { apply edge_loop_produces_child_output_context_for_parent; auto. }
    simpl. intros _.
    apply maybe_pop_produces_child_output_contract_from_context.
  Qed.

  Theorem tarjan_scc_f_preserves_child_output_contract
        (W: RecProgram):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitFrameContract g root W ->
    VisitOutputFrameContract W ->
    VisitChildOutputContract W ->
    VisitChildOutputContract (tarjan_scc_f g W).
  Proof.
    intros Hchild Hchild_traversal Hframe_contract
           Houtput_frame_contract Hchild_output.
    intros parent child done.
    apply tarjan_scc_f_produces_child_output_contract; auto.
  Qed.

  Theorem tarjan_scc_f_preserves_output_frame_contract
        (W: RecProgram):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitFrameContract g root W ->
    VisitOutputFrameContract W ->
    VisitOutputFrameContract (tarjan_scc_f g W).
  Proof.
    intros Hchild Hchild_traversal Hframe_contract Houtput_frame_contract.
    intros ancestor current loop_root next ancestor_done loop_done s_before.
    unfold tarjan_scc_f.
    eapply Hoare_bind.
    { apply preloop_preserves_nested_parent_output_frame. }
    simpl. intros _.
    eapply Hoare_bind.
    { eapply Hoare_conseq_pre.
      2: {
        apply (edge_loop_preserves_nested_output_maybe_pop_context
                 ancestor current next ancestor_done s_before W);
          auto. }
      intros s
        [Hloop [Htraversal [Hparent_frame [Hdisjoint
          [Hrest [Houtput_frame [Hready Hnext_not_old]]]]]]].
      exact (conj Hloop
              (conj Htraversal
                (conj Hparent_frame
                  (conj Hdisjoint
                    (conj Hrest
                      (conj Houtput_frame
                        (conj Hready Hnext_not_old))))))). }
    simpl. intros _.
    apply maybe_pop_preserves_nested_parent_output_frame.
  Qed.

  Theorem tarjan_scc_f_preserves_root_child_output_contracts
        (W: RecProgram):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitFrameContract g root W ->
    VisitOutputFrameContract W ->
    VisitChildOutputContract W ->
    VisitOutputContract W ->
    VisitOutputContract (tarjan_scc_f g W) /\
    VisitChildOutputContract (tarjan_scc_f g W).
  Proof.
    intros Hchild Hchild_traversal Hframe_contract
           Houtput_frame_contract Hchild_output Hroot_output.
    split.
    - intros u.
      apply tarjan_scc_f_produces_root_output_post; auto.
    - apply tarjan_scc_f_preserves_child_output_contract; auto.
  Qed.

  Theorem tarjan_scc_f_preserves_output_contracts
        (W: RecProgram):
    VisitChildContract g root W ->
    VisitChildTraversalContract g root W ->
    VisitFrameContract g root W ->
    VisitOutputFrameContract W ->
    VisitChildOutputContract W ->
    VisitOutputContract W ->
    VisitOutputContract (tarjan_scc_f g W) /\
    VisitChildOutputContract (tarjan_scc_f g W) /\
    VisitOutputFrameContract (tarjan_scc_f g W).
  Proof.
    intros Hchild Hchild_traversal Hframe_contract
           Houtput_frame_contract Hchild_output Hroot_output.
    split.
    - intros u.
      apply tarjan_scc_f_produces_root_output_post; auto.
    - split.
      + apply tarjan_scc_f_preserves_child_output_contract; auto.
      + apply tarjan_scc_f_preserves_output_frame_contract; auto.
  Qed.

End SCC_OUTPUT_CORRECTNESS.
