Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From MaxMinLib Require Import MaxMin Interface.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section IS_LOW.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  Local Definition St : Type := @SCCSt V.
  Local Definition RecProgram : Type := V -> program St unit.

  Definition Edge (u v: V): Prop :=
    dg_step g u v.

  Definition Visited (u: V) (s: St): Prop :=
    u ∈ visited s.

  Definition Active (u: V) (s: St): Prop :=
    In u (stack s).

  Definition edge_set (u: V): V -> Prop :=
    Edge u.

  Definition done_after (done: V -> Prop) (a: V): V -> Prop :=
    done ∪ [a].

  Definition tree_edge (s: St) (x y: V): Prop :=
    dg_step (state_to_dfs_tree g s root) x y.

  (* Public low-link specification.  This is the mathematical target:
     a low target is a DFS-subtree vertex itself, or one active vertex
     reached by one non-tree edge from that subtree. *)
  Definition scc_back_edge (s: St) (x y: V): Prop :=
    Edge x y /\ Active y s /\ ~ tree_edge s x y.

  Definition scc_low_reachable (s: St) (x y: V): Prop :=
    exists z,
      dg_reachable (state_to_dfs_tree g s root) x z /\
      (z = y \/ scc_back_edge s z y).

  Definition scc_low_tree (s: St) (x: V): V -> Prop :=
    fun y => scc_low_reachable s x y.

  Definition scc_is_low_v_val (s: St) (u: V) (n: nat): Prop :=
    min_value_of_subset Nat.le (scc_low_tree s u) (dfn s) n.

  Definition scc_is_low_v (s: St) (u: V): Prop :=
    scc_is_low_v_val s u (low s u).

  Definition scc_is_low (s: St): Prop :=
    forall v, Visited v s -> scc_is_low_v s v.

  (* Main closedness invariant from chain.md.  This is the only
     closedness fact used by the low-link loop: once a vertex is no
     longer active, it cannot reach the current active stack. *)
  Definition Closed (s: St): Prop :=
    forall v b,
      Visited v s ->
      ~ Active v s ->
      dg_reachable g v b ->
      Active b s ->
      False.

  (* Auxiliary global closure: settled vertices cannot reach unvisited
     vertices.  This is not the low-link closedness invariant; it is
     carried separately so the pop branch can restore the same property
     after adding a newly popped segment to the settled region. *)
  Definition NoUnvisitedReach (s: St): Prop :=
    settled_closed g s.

  Definition TreeEdgesAreGraphEdges (s: St): Prop :=
    forall x y, tree_edge s x y -> Edge x y.

  Definition StackNoDup (s: St): Prop :=
    NoDup (stack s).

  Definition OrderFacts (s: St): Prop :=
    stack_dfn_order s /\ dfn_injective s /\ StackNoDup s.

  Definition PoppedSegment (u: V) (s: St) (x: V): Prop :=
    match stack_split_at (stack s) u with
    | (popped, _) => In x popped
    end.

  Definition RestStack (u: V) (s: St) (x: V): Prop :=
    match stack_split_at (stack s) u with
    | (_, rest) => In x rest
    end.

  Definition StackRestOlderThanRoot (u: V) (s: St): Prop :=
    Active u s /\
    forall b, RestStack u s b -> dfn s b < dfn s u.

  (* Pop-local goals produced from full low correctness and
     [low[u] = dfn[u]].  These are not loop invariants; they are proof
     cuts used only to restore [NoUnvisitedReach] and [Closed] after
     [pop_scc u]. *)
  Definition PoppedSegmentClosed (u: V) (s: St): Prop :=
    forall x y,
      PoppedSegment u s x ->
      dg_reachable g x y ->
      Visited y s.

  Definition PoppedSegmentNoActiveReach (u: V) (s: St): Prop :=
    forall x b,
      PoppedSegment u s x ->
      dg_reachable g x b ->
      RestStack u s b ->
      False.

  Definition EntryPre (u: V) (s: St): Prop :=
    wf_scc_state_pre g root u s /\
    NoUnvisitedReach s /\
    Closed s /\
    TreeEdgesAreGraphEdges s /\
    OrderFacts s /\
    (fa s u <> u -> Edge (fa s u) u).

  (* Loop-progress meaning of [done]: every already materialized DFS-tree
     child of [u] must come from a processed outgoing edge.  The [Visited]
     guard is intentional: [set_fa child u] may create a pending parent
     pointer before [child] is visited, and that transient state must not
     violate the parent loop invariant. *)
  Definition ProcessedTreeChild
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall child,
      Visited child s ->
      fa s child = u ->
      fa s child <> child ->
      done child.

  Definition LoopCoreShape (u: V) (done: V -> Prop) (s: St): Prop :=
    wf_scc_state g root s /\
    TreeEdgesAreGraphEdges s /\
    Visited u s /\
    (forall a, done a -> Edge u a) /\
    (forall a, done a -> Visited a s) /\
    ProcessedTreeChild u done s.

  (* Auxiliary facts needed to resume the concrete program frame and to
     run the pop proof.  They are deliberately outside [LoopCoreShape]:
     low correctness and closedness do not mathematically depend on them
     during the neighbour loop. *)
  Definition LoopAuxFacts (u: V) (s: St): Prop :=
    NoUnvisitedReach s /\
    Active u s /\
    OrderFacts s.

  (* A partial DFS tree rooted at [u], containing [u] and complete
     subtrees of already processed tree children. *)
  Definition PartialTree (u: V) (done: V -> Prop) (s: St) (x: V): Prop :=
    x = u \/
    exists child,
      done child /\
      Edge u child /\
      fa s child = u /\
      fa s child <> child /\
      dg_reachable (state_to_dfs_tree g s root) child x.

  (* This is exactly chain.md's [Targets(PartialTree(u, i))]:
     active stack endpoints contributed by already processed outgoing
     edges.  The direct edge case must mention [done]; otherwise the
     empty loop invariant would already have to account for every
     unprocessed back edge out of [u]. *)
  Definition PartialActiveTarget
             (u: V) (done: V -> Prop) (s: St) (b: V): Prop :=
    (exists a,
      done a /\
      b = a /\
      Edge u a /\
      Active a s /\
      ~ tree_edge s u a) \/
    (exists child x,
      done child /\
      Edge u child /\
      fa s child = u /\
      fa s child <> child /\
      dg_reachable (state_to_dfs_tree g s root) child x /\
      Edge x b /\
      Active b s /\
      ~ tree_edge s x b).

  (* This is chain.md's [{u} ∪ Targets(PartialTree(u, i))], the set
     whose dfn image is minimized by [low[u]]. *)
  Definition PartialLowCandidate
             (u: V) (done: V -> Prop) (s: St) (b: V): Prop :=
    b = u \/ PartialActiveTarget u done s b.

  Definition LowComplete (u: V) (done: V -> Prop) (s: St): Prop :=
    forall b, PartialLowCandidate u done s b -> low s u <= dfn s b.

  Definition LowSound (u: V) (done: V -> Prop) (s: St): Prop :=
    exists b, PartialLowCandidate u done s b /\ low s u = dfn s b.

  Definition LowCorrect (u: V) (done: V -> Prop) (s: St): Prop :=
    LowSound u done s /\ LowComplete u done s.

  (* The chain.md joint invariant: low correctness plus exactly one
     main closedness predicate. *)
  Definition LoopCoreInv (u: V) (done: V -> Prop) (s: St): Prop :=
    LoopCoreShape u done s /\
    Closed s /\
    LowCorrect u done s.

  (* Full loop invariant used by the verification script.  The first
     component is auxiliary program-frame context; it is intentionally
     outside [LoopCoreInv]. *)
  Definition LoopInv (u: V) (done: V -> Prop) (s: St): Prop :=
    LoopAuxFacts u s /\ LoopCoreInv u done s.

  Definition RootLowCorrect (u: V) (s: St): Prop :=
    LowCorrect u (edge_set u) s.

  (* State immediately after the edge loop and before [maybe_pop].
     This is where chain.md's full low correctness is still stated over
     the pre-pop stack. *)
  Definition RootPrePop (u: V) (s: St): Prop :=
    LoopInv u (edge_set u) s /\
    StackRestOlderThanRoot u s.

  Definition RootPopBranchPre (u: V) (s: St): Prop :=
    RootPrePop u s /\ low s u = dfn s u.

  Definition RootSkipBranchPre (u: V) (s: St): Prop :=
    RootPrePop u s /\ low s u <> dfn s u.

  (* Public postcondition after [maybe_pop].  It deliberately does not
     contain [RootLowCorrect], because pop changes [stack] and therefore
     the active-target semantics used by [RootLowCorrect]. *)
  Definition RootAfterMaybePop (u: V) (s: St): Prop :=
    wf_scc_state g root s /\
    NoUnvisitedReach s /\
    Closed s /\
    scc_is_low_v s u.

  Definition RootFinal (u: V) (s: St): Prop :=
    RootAfterMaybePop u s.

  Definition ChildNoActiveTarget (v: V) (s: St): Prop :=
    forall x b,
      dg_reachable (state_to_dfs_tree g s root) v x ->
      Edge x b ->
      Active b s ->
      ~ tree_edge s x b ->
      False.

  Definition ChildLowContribution (u v: V) (s: St): Prop :=
    (Active v s /\ LoopCoreShape v (edge_set v) s /\ RootLowCorrect v s) \/
    (~ Active v s /\ low s v = dfn s v /\
     dfn s u < dfn s v /\ ChildNoActiveTarget v s).

  Definition ParentLowFrame
             (u: V) (done: V -> Prop) (s_before s_after: St): Prop :=
    low s_after u = low s_before u /\
    (forall b,
      PartialLowCandidate u done s_before b ->
      PartialLowCandidate u done s_after b /\
      dfn s_after b = dfn s_before b) /\
    (forall b,
      PartialLowCandidate u done s_after b ->
      PartialLowCandidate u done s_before b /\
      dfn s_after b = dfn s_before b).

  Definition ChildContributionContract
             (u v: V) (done: V -> Prop) (s_before s_after: St): Prop :=
    ParentLowFrame u done s_before s_after /\
    LoopCoreShape u (done_after done v) s_after /\
    LoopAuxFacts u s_after /\
    Closed s_after /\
    TreeEdgesAreGraphEdges s_after /\
    Visited v s_after /\
    fa s_after v = u /\
    fa s_after v <> v /\
    ChildLowContribution u v s_after.

  Lemma done_after_intro_old (done: V -> Prop) (a b: V):
    done b -> done_after done a b.
  Proof.
    unfold done_after. sets_unfold. auto.
  Qed.

  Lemma done_after_intro_new (done: V -> Prop) (a: V):
    done_after done a a.
  Proof.
    unfold done_after. sets_unfold. auto.
  Qed.

  Lemma done_after_elim (done: V -> Prop) (a b: V):
    done_after done a b -> done b \/ b = a.
  Proof.
    unfold done_after. sets_unfold.
    intros [Hdone | Heq].
    - left. exact Hdone.
    - right. symmetry. exact Heq.
  Qed.

  Lemma partial_tree_done_mono (u a x: V) (done: V -> Prop) (s: St):
    PartialTree u done s x ->
    PartialTree u (done_after done a) s x.
  Proof.
    intros Hpt. unfold PartialTree in *.
    destruct Hpt as [-> | [child [Hdone [Hedge [Hfa [Hfane Hreach]]]]]].
    - left. reflexivity.
    - right. exists child. repeat split; auto.
      apply done_after_intro_old. exact Hdone.
  Qed.

  Lemma partial_active_target_done_mono
        (u a b: V) (done: V -> Prop) (s: St):
    PartialActiveTarget u done s b ->
    PartialActiveTarget u (done_after done a) s b.
  Proof.
    intros Ht. unfold PartialActiveTarget in *.
    destruct Ht as [Hdirect | Hchild].
    - destruct Hdirect as [w [Hdone [Hb [Hedge [Hactive Hntr]]]]].
      left. exists w. repeat split; auto.
      apply done_after_intro_old. exact Hdone.
    - destruct Hchild as
        [child [x [Hdone [Hedge [Hfa [Hfane [Hreach [Hxb [Hactive Hntr]]]]]]]]].
      right. exists child, x. repeat split; auto.
      apply done_after_intro_old. exact Hdone.
  Qed.

  Lemma partial_low_candidate_done_mono
        (u a b: V) (done: V -> Prop) (s: St):
    PartialLowCandidate u done s b ->
    PartialLowCandidate u (done_after done a) s b.
  Proof.
    intros Ht. unfold PartialLowCandidate in *.
    destruct Ht as [Hb | Hactive].
    - left. exact Hb.
    - right. apply partial_active_target_done_mono. exact Hactive.
  Qed.

  Lemma partial_tree_root (u: V) (done: V -> Prop) (s: St):
    PartialTree u done s u.
  Proof.
    unfold PartialTree. left. reflexivity.
  Qed.

  Lemma partial_low_candidate_root (u: V) (done: V -> Prop) (s: St):
    PartialLowCandidate u done s u.
  Proof.
    unfold PartialLowCandidate. left. reflexivity.
  Qed.

  Lemma partial_active_target_direct
        (u a: V) (done: V -> Prop) (s: St):
    Edge u a ->
    Active a s ->
    ~ tree_edge s u a ->
    PartialActiveTarget u (done_after done a) s a.
  Proof.
    intros Hedge Hactive Hntr.
    left. exists a. repeat split; auto.
    apply done_after_intro_new.
  Qed.

  Lemma partial_low_candidate_direct_active
        (u a: V) (done: V -> Prop) (s: St):
    Edge u a ->
    Active a s ->
    ~ tree_edge s u a ->
    PartialLowCandidate u (done_after done a) s a.
  Proof.
    intros Hedge Hactive Hntr.
    right. apply partial_active_target_direct; auto.
  Qed.

  Lemma low_correct_empty (u: V) (s: St):
    low s u = dfn s u ->
    LowCorrect u ∅ s.
  Proof.
    intros Hlow. split.
    - exists u. split.
      + apply partial_low_candidate_root.
      + exact Hlow.
    - unfold LowComplete. intros b Ht.
      unfold PartialLowCandidate in Ht.
      destruct Ht as [-> | Hactive].
      + rewrite Hlow. lia.
      + unfold PartialActiveTarget in Hactive.
        destruct Hactive as [[a [Hdone _]] | [child [x [Hdone _]]]];
          sets_unfold in Hdone; tauto.
  Qed.

  Lemma low_complete_done_mono
        (u a: V) (done: V -> Prop) (s: St):
    LowComplete u (done_after done a) s ->
    LowComplete u done s.
  Proof.
    unfold LowComplete. intros H b Ht.
    apply H. apply partial_low_candidate_done_mono. exact Ht.
  Qed.

  Lemma processed_tree_child_done_equiv
        (u: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    ProcessedTreeChild u done1 s ->
    ProcessedTreeChild u done2 s.
  Proof.
    intros Hdone Hprocessed child Hchild_vis Hfa Hfane.
    sets_unfold in Hdone.
    apply Hdone.
    exact (Hprocessed child Hchild_vis Hfa Hfane).
  Qed.

  Lemma loop_core_shape_done_equiv
        (u: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    LoopCoreShape u done1 s ->
    LoopCoreShape u done2 s.
  Proof.
    intros Hdone [Hwf [Htree [Huvis [Hdone_edge [Hdone_vis Hprocessed]]]]].
    sets_unfold in Hdone.
    split; [exact Hwf |].
    split; [exact Htree |].
    split; [exact Huvis |].
    split.
    - intros a Ha. apply Hdone_edge. apply Hdone. exact Ha.
    - split.
      + intros a Ha. apply Hdone_vis. apply Hdone. exact Ha.
      + unfold ProcessedTreeChild in *.
        intros child Hchild_vis Hfa Hfane.
        apply Hdone.
        exact (Hprocessed child Hchild_vis Hfa Hfane).
  Qed.

  Lemma partial_active_target_done_equiv
        (u b: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    PartialActiveTarget u done1 s b ->
    PartialActiveTarget u done2 s b.
  Proof.
    intros Hdone Htarget.
    sets_unfold in Hdone.
    unfold PartialActiveTarget in Htarget |- *.
    destruct Htarget as [Hdirect | Hchild].
    - destruct Hdirect as [a [Hdone_a [Hb [Hedge [Hactive Hnot_tree]]]]].
      left. exists a. repeat split; auto.
      apply Hdone. exact Hdone_a.
    - destruct Hchild as
        [child [x [Hdone_child [Hedge [Hfa [Hfane [Hreach [Hxb [Hactive Hnot_tree]]]]]]]]].
      right. exists child, x. repeat split; auto.
      apply Hdone. exact Hdone_child.
  Qed.

  Lemma partial_low_candidate_done_equiv
        (u b: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    PartialLowCandidate u done1 s b ->
    PartialLowCandidate u done2 s b.
  Proof.
    intros Hdone Hcandidate.
    unfold PartialLowCandidate in Hcandidate |- *.
    destruct Hcandidate as [Hb | Htarget].
    - left. exact Hb.
    - right.
      eapply partial_active_target_done_equiv; eauto.
  Qed.

  Lemma low_correct_done_equiv
        (u: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    LowCorrect u done1 s ->
    LowCorrect u done2 s.
  Proof.
    intros Hdone [Hsound Hcomplete]. split.
    - destruct Hsound as [witness [Hcandidate Hlow]].
      exists witness. split.
      + eapply partial_low_candidate_done_equiv; eauto.
      + exact Hlow.
    - intros target Hcandidate.
      apply Hcomplete.
      eapply partial_low_candidate_done_equiv.
      + symmetry. exact Hdone.
      + exact Hcandidate.
  Qed.

  Lemma loop_core_inv_done_equiv
        (u: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    LoopCoreInv u done1 s ->
    LoopCoreInv u done2 s.
  Proof.
    intros Hdone [Hshape [Hclosed Hlow]].
    split.
    - eapply loop_core_shape_done_equiv; eauto.
    - split; [exact Hclosed |].
      eapply low_correct_done_equiv; eauto.
  Qed.

  Lemma loop_inv_done_equiv
        (u: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    LoopInv u done1 s ->
    LoopInv u done2 s.
  Proof.
    intros Hdone [Haux Hcore].
    split; [exact Haux |].
    eapply loop_core_inv_done_equiv; eauto.
  Qed.

  (** Preloop **)

  Lemma preloop_low_eq_dfn (u: V):
    Hoare (fun _ : St => True)
          (preloop u)
          (fun _ s => low s u = dfn s u).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    unfold equiv_decb.
    destruct (equiv_dec u u) as [_ | Hneq];
      [reflexivity | exfalso; apply Hneq; reflexivity].
  Qed.

  Lemma preloop_preserves_stack_nodup (u: V):
    Hoare (fun s: St =>
             StackNoDup s /\ stack_in_visited s /\ ~ Visited u s)
          (preloop u)
          (fun _ s => StackNoDup s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [Hnodup [Hstack_vis Hunvis]].
    constructor.
    - intros Hin. apply Hunvis. apply Hstack_vis. exact Hin.
    - exact Hnodup.
  Qed.

  Lemma preloop_preserves_tree_edges_are_graph_edges (u: V):
    Hoare
      (fun s: St =>
         wf_scc_state_pre g root u s /\
         TreeEdgesAreGraphEdges s /\
         (fa s u <> u -> Edge (fa s u) u))
      (preloop u)
      (fun _ s => TreeEdgesAreGraphEdges s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [[Hwf Hunvis] [Htree_sound Hincoming]].
    unfold TreeEdgesAreGraphEdges, tree_edge, Edge in *.
    intros x y Hstep.
    unfold dg_step in Hstep.
    destruct Hstep as [e [Htree [Hfst Hsnd]]].
    simpl in Hfst, Hsnd.
    unfold state_to_dfs_tree in Htree. simpl in Htree.
    destruct Htree as [z [Hzvis [Hfane [Hfst_fa Hsnd_z]]]].
    sets_unfold in Hzvis.
    destruct Hzvis as [Hzvis_old | Hz_eq_u].
    - apply Htree_sound.
      unfold dg_step.
      exists e. split; [| split; [exact Hfst | exact Hsnd]].
      unfold state_to_dfs_tree. simpl.
      exists z. repeat split; auto.
    - subst z.
      assert (Hx: x = fa s0 u).
      { rewrite <- Hfst. exact Hfst_fa. }
      assert (Hy: y = u).
      { rewrite <- Hsnd. exact Hsnd_z. }
      rewrite Hx, Hy. apply Hincoming. exact Hfane.
  Qed.

  Lemma preloop_empty_done_edges (u: V):
    Hoare (fun _ : St => True)
          (preloop u)
          (fun _ _ => forall a, ∅ a -> Edge u a).
  Proof.
    eapply Hoare_conseq_post.
    2: apply preloop_low_eq_dfn.
    intros _ s _ w Hempty. sets_unfold in Hempty. tauto.
  Qed.

  Lemma preloop_empty_done_visited (u: V):
    Hoare (fun _ : St => True)
          (preloop u)
          (fun _ s => forall a, ∅ a -> Visited a s).
  Proof.
    eapply Hoare_conseq_post.
    2: apply preloop_low_eq_dfn.
    intros _ s _ w Hempty. sets_unfold in Hempty. tauto.
  Qed.

  Lemma preloop_processed_tree_child_empty (u: V):
    Hoare (fun s: St => wf_scc_state_pre g root u s)
          (preloop u)
          (fun _ s => ProcessedTreeChild u ∅ s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [[_ [_ [_ Hfa_visited]]] Hunvis].
    unfold ProcessedTreeChild, Visited.
    intros child Hchild_vis Hfa Hfane.
    sets_unfold in Hchild_vis.
    destruct Hchild_vis as [Hchild_vis_old | Hchild_eq_u].
    - exfalso. apply Hunvis.
      rewrite <- Hfa. apply Hfa_visited. exact Hfane.
    - subst child. exfalso. apply Hfane. exact Hfa.
  Qed.

  Lemma preloop_preserves_closed (u: V):
    Hoare
      (fun s: St =>
         wf_scc_state_pre g root u s /\
         NoUnvisitedReach s /\
         Closed s)
      (preloop u)
      (fun _ s => Closed s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [[Hwf Hunvis] [Hsettled Hclosed]].
    unfold Closed, Visited, Active in *.
    intros v target Hvis_post Hvinact_post Hreach Htarget_active_post.
    simpl in Hvis_post, Hvinact_post, Htarget_active_post.
    sets_unfold in Hvis_post.
    destruct Hvis_post as [Hvis_old | Hv_eq_u].
    - assert (Hvinact_old: ~ In v (stack s0)).
      { intros Hvstk. apply Hvinact_post. right. exact Hvstk. }
      destruct Htarget_active_post as [Htarget_eq_u | Htarget_active_old].
      + subst target. apply Hunvis.
        unfold NoUnvisitedReach, settled_closed in Hsettled.
        exact (Hsettled v u Hvis_old Hvinact_old Hreach).
      + exact (Hclosed v target Hvis_old Hvinact_old Hreach Htarget_active_old).
    - subst v. apply Hvinact_post. left. reflexivity.
  Qed.

  Lemma preloop_produces_low_correct_empty (u: V):
    Hoare (fun _ : St => True)
          (preloop u)
          (fun _ s => LowCorrect u ∅ s).
  Proof.
    eapply Hoare_conseq_post.
    2: apply preloop_low_eq_dfn.
    intros ret s Hlow. apply low_correct_empty. exact Hlow.
  Qed.

  Lemma preloop_produces_loop_core_shape (u: V):
    Hoare (EntryPre u)
          (preloop u)
          (fun _ s => LoopCoreShape u ∅ s).
  Proof.
    unfold LoopCoreShape.
    apply Hoare_conj with
      (Q1 := fun _ s => wf_scc_state g root s).
    { eapply Hoare_conseq_pre.
      2: apply preloop_preserves_wf_scc_state.
      intros s [Hwf _]. exact Hwf. }
    apply Hoare_conj with
      (Q1 := fun _ s => TreeEdgesAreGraphEdges s).
    { eapply Hoare_conseq_pre.
      2: apply preloop_preserves_tree_edges_are_graph_edges.
      intros s [Hwf [_ [_ [Htree [_ Hincoming]]]]].
      exact (conj Hwf (conj Htree Hincoming)). }
    apply Hoare_conj with
      (Q1 := fun _ s => Visited u s).
    { eapply Hoare_conseq_pre.
      2: apply preloop_self_visited.
      intros s _. exact I. }
    apply Hoare_conj with
      (Q1 := fun _ s => forall a, ∅ a -> Edge u a).
    { eapply Hoare_conseq_pre.
      2: apply preloop_empty_done_edges.
      intros s _. exact I. }
    apply Hoare_conj with
      (Q1 := fun _ s => forall a, ∅ a -> Visited a s).
    { eapply Hoare_conseq_pre.
      2: apply preloop_empty_done_visited.
      intros s _. exact I. }
    { eapply Hoare_conseq_pre.
      2: apply preloop_processed_tree_child_empty.
      intros s [Hwf _]. exact Hwf. }
  Qed.

  Lemma preloop_produces_loop_aux_facts (u: V):
    Hoare (EntryPre u)
          (preloop u)
          (fun _ s => LoopAuxFacts u s).
  Proof.
    unfold LoopAuxFacts, OrderFacts.
    apply Hoare_conj with
      (Q1 := fun _ s => NoUnvisitedReach s).
    { eapply Hoare_conseq_pre.
      2: apply preloop_keep_settled_closed.
      intros s [_ [Hsettled _]]. exact Hsettled. }
    apply Hoare_conj with
      (Q1 := fun _ s => Active u s).
    { eapply Hoare_conseq_pre.
      2: apply preloop_in_stack.
      intros s _. exact I. }
    apply Hoare_conj with
      (Q1 := fun _ s => stack_dfn_order s).
    { eapply Hoare_conseq_pre.
      2: apply preloop_preserves_stack_dfn_order.
      intros s [Hwf [_ [_ [_ [Horder _]]]]].
      destruct Hwf as [[Hsiv [Hinv _]] Hunvis].
      destruct Horder as [Hstack_order _].
      exact (conj Hstack_order (conj Hinv (conj Hsiv Hunvis))). }
    apply Hoare_conj with
      (Q1 := fun _ s => dfn_injective s).
    { eapply Hoare_conseq_pre.
      2: apply preloop_preserves_dfn_injective.
      intros s [Hwf [_ [_ [_ [Horder _]]]]].
      destruct Hwf as [[_ [Hinv _]] Hunvis].
      destruct Horder as [_ [Hinj _]].
      exact (conj Hinj (conj Hinv Hunvis)). }
    { eapply Hoare_conseq_pre.
      2: apply preloop_preserves_stack_nodup.
      intros s [Hwf [_ [_ [_ [Horder _]]]]].
      destruct Hwf as [[Hsiv _] Hunvis].
      destruct Horder as [_ [_ Hnodup]].
      exact (conj Hnodup (conj Hsiv Hunvis)). }
  Qed.

  Theorem preloop_initializes_loop_inv (u: V):
    Hoare (EntryPre u)
          (preloop u)
          (fun _ s => LoopInv u ∅ s).
  Proof.
    unfold LoopInv, LoopCoreInv.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopAuxFacts u s).
    { apply preloop_produces_loop_aux_facts. }
    apply Hoare_conj with
      (Q1 := fun _ s => LoopCoreShape u ∅ s).
    { apply preloop_produces_loop_core_shape. }
    apply Hoare_conj with
      (Q1 := fun _ s => Closed s).
    { eapply Hoare_conseq_pre.
      2: apply preloop_preserves_closed.
      intros s [Hwf [Hsettled [Hclosed _]]].
      exact (conj Hwf (conj Hsettled Hclosed)). }
    { eapply Hoare_conseq_pre.
      2: apply preloop_produces_low_correct_empty.
      intros s _. exact I. }
  Qed.

  (* edge loop *)

  (* 1. state preservation lemmas *)

  Lemma update_low_value (u: V) (n old: nat):
    Hoare (fun s: St => low s u = old)
          (update_low u n)
          (fun _ s => low s u = Nat.min old n).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl.
      unfold equiv_decb.
      destruct (equiv_dec u u) as [_ | Hneq].
      + rewrite Nat.min_r; lia.
      + exfalso. apply Hneq. reflexivity.
    - destruct H as [Heq Hnot_lt]. subst s.
      rewrite Nat.min_l; lia.
  Qed.

  Lemma update_low_preserves_closed (u: V) (n: nat):
    Hoare (Closed)
          (update_low u n)
          (fun _ s => Closed s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma update_low_preserves_tree_edges_are_graph_edges (u: V) (n: nat):
    Hoare (TreeEdgesAreGraphEdges)
          (update_low u n)
          (fun _ s => TreeEdgesAreGraphEdges s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma update_low_preserves_processed_tree_child
        (center: V) (done: V -> Prop) (u: V) (n: nat):
    Hoare (ProcessedTreeChild center done)
          (update_low u n)
          (fun _ s => ProcessedTreeChild center done s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma update_low_preserves_stack_nodup (u: V) (n: nat):
    Hoare (StackNoDup)
          (update_low u n)
          (fun _ s => StackNoDup s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma set_fa_preserves_stack_nodup (v p: V):
    Hoare (StackNoDup)
          (set_fa v p)
          (fun _ s => StackNoDup s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl. exact H.
  Qed.

  Lemma get_low_update_low_preserves_stack_nodup (u v: V):
    Hoare (StackNoDup)
          (lv <- get' (fun s => low s v);; update_low u lv)
          (fun _ s => StackNoDup s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_stack_nodup.
    intros s1 Hs1. destruct Hs1. subst s1. exact H.
  Qed.

  Lemma get_dfn_update_low_preserves_stack_nodup (u v: V):
    Hoare (StackNoDup)
          (dv <- get' (fun s => dfn s v);; update_low u dv)
          (fun _ s => StackNoDup s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_stack_nodup.
    intros s1 Hs1. destruct Hs1. subst s1. exact H.
  Qed.

  Lemma update_low_preserves_loop_core_shape
        (center: V) (done: V -> Prop) (u: V) (n: nat):
    Hoare
      (fun s: St => LoopCoreShape center done s /\ u ∈ visited s)
      (update_low u n)
      (fun _ s => LoopCoreShape center done s).
  Proof.
    unfold LoopCoreShape.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl.
      destruct H as [[Hwf [Htree [Hvis [Hedge [Hvis_done Hprocessed]]]]] _].
      split; [exact Hwf |].
      split.
      { unfold TreeEdgesAreGraphEdges, tree_edge, Edge in *.
        simpl. exact Htree. }
      split; [exact Hvis |].
      split; [exact Hedge |].
      split; [exact Hvis_done |].
      unfold ProcessedTreeChild, Visited in *.
      simpl. exact Hprocessed.
    - destruct H1 as [Heq _]. subst s.
      exact (proj1 H).
  Qed.

  Lemma update_low_preserves_loop_aux_facts (center u: V) (n: nat):
    Hoare (LoopAuxFacts center)
          (update_low u n)
          (fun _ s => LoopAuxFacts center s).
  Proof.
    unfold LoopAuxFacts, OrderFacts.
    apply Hoare_conj with
      (Q1 := fun _ s => NoUnvisitedReach s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_keep_settled_closed.
      intros s [Hsettled _]. exact Hsettled. }
    apply Hoare_conj with
      (Q1 := fun _ s => Active center s).
    { eapply Hoare_conseq_pre.
      2: apply (update_low_keep_in_stack u center n).
      intros s [_ [Hactive _]]. exact Hactive. }
    apply Hoare_conj with
      (Q1 := fun _ s => stack_dfn_order s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_keep_stack_dfn_order.
      intros s [_ [_ [Hstack_order _]]]. exact Hstack_order. }
    apply Hoare_conj with
      (Q1 := fun _ s => dfn_injective s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_keep_dfn_injective.
      intros s [_ [_ [_ [Hinj _]]]]. exact Hinj. }
    { eapply Hoare_conseq_pre.
      2: apply update_low_preserves_stack_nodup.
      intros s [_ [_ [_ [_ Hnodup]]]]. exact Hnodup. }
  Qed.

  Lemma update_low_preserves_loop_inv_shape
        (center: V) (done: V -> Prop) (u: V) (n: nat):
    Hoare
      (fun s: St => LoopInv center done s /\ u ∈ visited s)
      (update_low u n)
      (fun _ s =>
         LoopAuxFacts center s /\
         LoopCoreShape center done s /\
         Closed s).
  Proof.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopAuxFacts center s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_preserves_loop_aux_facts.
      intros s [[Haux _] _]. exact Haux. }
    apply Hoare_conj with
      (Q1 := fun _ s => LoopCoreShape center done s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_preserves_loop_core_shape.
      intros s [[_ [Hshape _]] Huvis]. exact (conj Hshape Huvis). }
    { eapply Hoare_conseq_pre.
      2: apply update_low_preserves_closed.
      intros s [[_ [_ [Hclosed _]]] _]. exact Hclosed. }
  Qed.

  Lemma set_fa_state_keep_other_fa (s: St) (v p w: V):
    w <> v ->
    fa (set_fa_state s v p) w = fa s w.
  Proof.
    intros Hneq.
    unfold set_fa_state. simpl.
    unfold equiv_decb.
    destruct (equiv_dec w v) as [Heq | _].
    - exfalso. apply Hneq. exact Heq.
    - reflexivity.
  Qed.

  Lemma set_fa_pending_tree_step_iff (s: St) (v p x y: V):
    ~ Visited v s ->
    (tree_edge (set_fa_state s v p) x y <-> tree_edge s x y).
  Proof.
    intros Hnotvis. split.
    - unfold tree_edge, dg_step.
      intros [e [Htree [Hfst Hsnd]]].
      exists e. split; [| split; [exact Hfst | exact Hsnd]].
      unfold state_to_dfs_tree in Htree |- *. simpl in Htree |- *.
      destruct Htree as [child [Hchild_vis [Hfane [Hfst_fa Hsnd_child]]]].
      assert (Hchild_ne: child <> v).
      { intros Heq. apply Hnotvis. rewrite <- Heq. exact Hchild_vis. }
      exists child. split; [exact Hchild_vis | split].
      + unfold equiv_decb in Hfane.
        destruct (equiv_dec child v) as [Heq | _].
        * exfalso. apply Hchild_ne. exact Heq.
        * exact Hfane.
      + split.
        * unfold equiv_decb in Hfst_fa.
          destruct (equiv_dec child v) as [Heq | _].
          -- exfalso. apply Hchild_ne. exact Heq.
          -- exact Hfst_fa.
        * exact Hsnd_child.
    - unfold tree_edge, dg_step.
      intros [e [Htree [Hfst Hsnd]]].
      exists e. split; [| split; [exact Hfst | exact Hsnd]].
      unfold state_to_dfs_tree in Htree |- *. simpl in Htree |- *.
      destruct Htree as [child [Hchild_vis [Hfane [Hfst_fa Hsnd_child]]]].
      assert (Hchild_ne: child <> v).
      { intros Heq. apply Hnotvis. rewrite <- Heq. exact Hchild_vis. }
      exists child. split; [exact Hchild_vis | split].
      + unfold set_fa_state. simpl. unfold equiv_decb.
        destruct (equiv_dec child v) as [Heq | _].
        * exfalso. apply Hchild_ne. exact Heq.
        * exact Hfane.
      + split.
        * unfold set_fa_state. simpl. unfold equiv_decb.
          destruct (equiv_dec child v) as [Heq | _].
          -- exfalso. apply Hchild_ne. exact Heq.
          -- exact Hfst_fa.
        * exact Hsnd_child.
  Qed.

  Lemma set_fa_pending_tree_reachable_iff (s: St) (v p x y: V):
    ~ Visited v s ->
    (dg_reachable (state_to_dfs_tree g (set_fa_state s v p) root) x y <->
     dg_reachable (state_to_dfs_tree g s root) x y).
  Proof.
    intros Hnotvis. split; intro Hreach.
    - eapply dg_reachable_lift.
      + intros a b Hstep.
        apply (proj1 (set_fa_pending_tree_step_iff s v p a b Hnotvis)).
        exact Hstep.
      + exact Hreach.
    - eapply dg_reachable_lift.
      + intros a b Hstep.
        apply (proj2 (set_fa_pending_tree_step_iff s v p a b Hnotvis)).
        exact Hstep.
      + exact Hreach.
  Qed.

  Lemma set_fa_pending_preserves_tree_edges_are_graph_edges
        (s: St) (v p: V):
    ~ Visited v s ->
    TreeEdgesAreGraphEdges s ->
    TreeEdgesAreGraphEdges (set_fa_state s v p).
  Proof.
    intros Hnotvis Htree_sound x y Htree.
    apply Htree_sound.
    apply (proj1 (set_fa_pending_tree_step_iff s v p x y Hnotvis)).
    exact Htree.
  Qed.

  Lemma set_fa_pending_preserves_wf_scc_state (s: St) (u v: V):
    wf_scc_state g root s ->
    Visited u s ->
    ~ Visited v s ->
    wf_scc_state g root (set_fa_state s v u).
  Proof.
    intros [Hstack_vis [Hdfn_inv [Hdfn_valid Hfa_vis]]] Huvis Hnotvis.
    unfold wf_scc_state. split; [| split; [| split]].
    - unfold stack_in_visited in *. simpl. exact Hstack_vis.
    - unfold dfn_inv in *. simpl. exact Hdfn_inv.
    - unfold dfn_valid in *. simpl.
      intros x y Hstep.
      apply Hdfn_valid.
      apply (proj1 (set_fa_pending_tree_step_iff s v u x y Hnotvis)).
      exact Hstep.
    - unfold fa_visited in *. simpl.
      intros w Hfane.
      unfold equiv_decb in Hfane |- *.
      destruct (equiv_dec w v) as [Hw_eq_v | Hw_ne_v].
      + exact Huvis.
      + apply Hfa_vis. exact Hfane.
  Qed.

  Lemma set_fa_pending_preserves_processed_tree_child
        (center: V) (done: V -> Prop) (s: St) (v p: V):
    ~ Visited v s ->
    ProcessedTreeChild center done s ->
    ProcessedTreeChild center done (set_fa_state s v p).
  Proof.
    intros Hnotvis Hprocessed child Hchild_vis Hfa Hfane.
    simpl in Hchild_vis.
    assert (Hchild_ne: child <> v).
    { intros Heq. apply Hnotvis. rewrite <- Heq. exact Hchild_vis. }
    apply (Hprocessed child Hchild_vis).
    - rewrite set_fa_state_keep_other_fa in Hfa; auto.
    - rewrite set_fa_state_keep_other_fa in Hfane; auto.
  Qed.

  Lemma set_fa_pending_preserves_loop_core_shape
        (center: V) (done: V -> Prop) (s: St) (v p: V):
    Visited p s ->
    ~ Visited v s ->
    LoopCoreShape center done s ->
    LoopCoreShape center done (set_fa_state s v p).
  Proof.
    intros Hpvis Hnotvis [Hwf [Htree_sound [Hcenter_vis [Hdone_edge [Hdone_vis Hprocessed]]]]].
    assert (Hwf_post: wf_scc_state g root (set_fa_state s v p)).
    { apply set_fa_pending_preserves_wf_scc_state; auto. }
    assert (Htree_post: TreeEdgesAreGraphEdges (set_fa_state s v p)).
    { apply set_fa_pending_preserves_tree_edges_are_graph_edges; auto. }
    assert (Hcenter_vis_post: Visited center (set_fa_state s v p)).
    { simpl. exact Hcenter_vis. }
    assert (Hdone_vis_post:
              forall a, done a -> Visited a (set_fa_state s v p)).
    { intros a Hdone. simpl. apply Hdone_vis. exact Hdone. }
    assert (Hprocessed_post:
              ProcessedTreeChild center done (set_fa_state s v p)).
    { apply set_fa_pending_preserves_processed_tree_child; auto. }
    exact (conj Hwf_post
            (conj Htree_post
              (conj Hcenter_vis_post
                (conj Hdone_edge
                  (conj Hdone_vis_post Hprocessed_post))))).
  Qed.

  Lemma set_fa_pending_partial_active_target_iff
        (center: V) (done: V -> Prop) (s: St) (v p b: V):
    ~ Visited v s ->
    (forall a, done a -> Visited a s) ->
    (PartialActiveTarget center done (set_fa_state s v p) b <->
     PartialActiveTarget center done s b).
  Proof.
    intros Hnotvis Hdone_vis. split; intro Htarget.
    - unfold PartialActiveTarget in Htarget |- *.
      destruct Htarget as [Hdirect | Hchild].
      + destruct Hdirect as [a [Hdone [Hb [Hedge [Hactive Hnot_tree]]]]].
        left. exists a.
        split; [exact Hdone | split; [exact Hb | split; [exact Hedge | split]]].
        * simpl in Hactive. exact Hactive.
        * intros Htree.
          apply Hnot_tree.
          apply (proj2 (set_fa_pending_tree_step_iff s v p center a Hnotvis)).
          exact Htree.
      + destruct Hchild as
          [child [x [Hdone [Hedge [Hfa [Hfane [Hreach [Hxb [Hactive Hnot_tree]]]]]]]]].
        assert (Hchild_ne: child <> v).
        { intros Heq. apply Hnotvis. rewrite <- Heq. apply Hdone_vis. exact Hdone. }
        right. exists child, x.
        split; [exact Hdone | split; [exact Hedge | split]].
        * rewrite set_fa_state_keep_other_fa in Hfa; auto.
        * split.
          -- rewrite set_fa_state_keep_other_fa in Hfane; auto.
          -- split.
             ++ apply (proj1 (set_fa_pending_tree_reachable_iff s v p child x Hnotvis)).
                exact Hreach.
             ++ split; [exact Hxb | split].
                ** simpl in Hactive. exact Hactive.
                ** intros Htree.
                   apply Hnot_tree.
                   apply (proj2 (set_fa_pending_tree_step_iff s v p x b Hnotvis)).
                   exact Htree.
    - unfold PartialActiveTarget in Htarget |- *.
      destruct Htarget as [Hdirect | Hchild].
      + destruct Hdirect as [a [Hdone [Hb [Hedge [Hactive Hnot_tree]]]]].
        left. exists a.
        split; [exact Hdone | split; [exact Hb | split; [exact Hedge | split]]].
        * simpl. exact Hactive.
        * intros Htree.
          apply Hnot_tree.
          apply (proj1 (set_fa_pending_tree_step_iff s v p center a Hnotvis)).
          exact Htree.
      + destruct Hchild as
          [child [x [Hdone [Hedge [Hfa [Hfane [Hreach [Hxb [Hactive Hnot_tree]]]]]]]]].
        assert (Hchild_ne: child <> v).
        { intros Heq. apply Hnotvis. rewrite <- Heq. apply Hdone_vis. exact Hdone. }
        right. exists child, x.
        split; [exact Hdone | split; [exact Hedge | split]].
        * rewrite set_fa_state_keep_other_fa; auto.
        * split.
          -- rewrite set_fa_state_keep_other_fa; auto.
          -- split.
             ++ apply (proj2 (set_fa_pending_tree_reachable_iff s v p child x Hnotvis)).
                exact Hreach.
             ++ split; [exact Hxb | split].
                ** simpl. exact Hactive.
                ** intros Htree.
                   apply Hnot_tree.
                   apply (proj1 (set_fa_pending_tree_step_iff s v p x b Hnotvis)).
                   exact Htree.
  Qed.

  Lemma set_fa_pending_partial_low_candidate_iff
        (center: V) (done: V -> Prop) (s: St) (v p b: V):
    ~ Visited v s ->
    (forall a, done a -> Visited a s) ->
    (PartialLowCandidate center done (set_fa_state s v p) b <->
     PartialLowCandidate center done s b).
  Proof.
    intros Hnotvis Hdone_vis.
    unfold PartialLowCandidate. split; intros [Hb | Htarget].
    - left. exact Hb.
    - right.
      apply (proj1 (set_fa_pending_partial_active_target_iff
                      center done s v p b Hnotvis Hdone_vis)).
      exact Htarget.
    - left. exact Hb.
    - right.
      apply (proj2 (set_fa_pending_partial_active_target_iff
                      center done s v p b Hnotvis Hdone_vis)).
      exact Htarget.
  Qed.

  Lemma set_fa_pending_preserves_low_correct
        (center: V) (done: V -> Prop) (s: St) (v p: V):
    ~ Visited v s ->
    (forall a, done a -> Visited a s) ->
    LowCorrect center done s ->
    LowCorrect center done (set_fa_state s v p).
  Proof.
    intros Hnotvis Hdone_vis [Hsound Hcomplete]. split.
    - destruct Hsound as [b [Hcandidate Hlow]].
      exists b. split.
      + apply (proj2 (set_fa_pending_partial_low_candidate_iff
                        center done s v p b Hnotvis Hdone_vis)).
        exact Hcandidate.
      + simpl. exact Hlow.
    - intros b Hcandidate.
      simpl.
      apply Hcomplete.
      apply (proj1 (set_fa_pending_partial_low_candidate_iff
                      center done s v p b Hnotvis Hdone_vis)).
      exact Hcandidate.
  Qed.

  Lemma set_fa_pending_preserves_closed (s: St) (v p: V):
    Closed s ->
    Closed (set_fa_state s v p).
  Proof.
    unfold Closed, Visited, Active.
    simpl. auto.
  Qed.

  Lemma set_fa_pending_preserves_loop_core_inv
        (center: V) (done: V -> Prop) (s: St) (v p: V):
    Visited p s ->
    ~ Visited v s ->
    LoopCoreInv center done s ->
    LoopCoreInv center done (set_fa_state s v p).
  Proof.
    intros Hpvis Hnotvis [Hshape [Hclosed Hlow]].
    destruct Hshape as [Hwf [Htree_sound [Hcenter_vis [Hdone_edge [Hdone_vis Hprocessed]]]]].
    assert (Hshape_post: LoopCoreShape center done (set_fa_state s v p)).
    { apply set_fa_pending_preserves_loop_core_shape; auto.
      exact (conj Hwf
              (conj Htree_sound
                (conj Hcenter_vis
                  (conj Hdone_edge
                    (conj Hdone_vis Hprocessed))))). }
    assert (Hclosed_post: Closed (set_fa_state s v p)).
    { apply set_fa_pending_preserves_closed. exact Hclosed. }
    assert (Hlow_post: LowCorrect center done (set_fa_state s v p)).
    { apply set_fa_pending_preserves_low_correct; auto. }
    exact (conj Hshape_post (conj Hclosed_post Hlow_post)).
  Qed.

  Lemma set_fa_pending_preserves_parent_core
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         LoopCoreInv u done s /\
         Edge u v /\
         Active u s /\
         ~ Visited v s)
      (set_fa v u)
      (fun _ s => LoopCoreInv u done s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. change (LoopCoreInv u done (set_fa_state s0 v u)).
    destruct H as [Hcore [_ [_ Hnotvis]]].
    destruct Hcore as [Hshape [Hclosed Hlow]].
    destruct Hshape as [Hwf [Htree_sound [Huvis [Hdone_edge [Hdone_vis Hprocessed]]]]].
    apply set_fa_pending_preserves_loop_core_inv; auto.
    exact (conj
             (conj Hwf
               (conj Htree_sound
                 (conj Huvis
                   (conj Hdone_edge
                     (conj Hdone_vis Hprocessed)))))
             (conj Hclosed Hlow)).
  Qed.

  Lemma set_fa_pending_preserves_loop_aux_facts
        (u v: V):
    Hoare
      (LoopAuxFacts u)
      (set_fa v u)
      (fun _ s => LoopAuxFacts u s).
  Proof.
    unfold LoopAuxFacts, OrderFacts.
    apply Hoare_conj with
      (Q1 := fun _ s => NoUnvisitedReach s).
    { eapply Hoare_conseq_pre.
      2: apply set_fa_keep_settled_closed.
      intros s [Hsettled _]. exact Hsettled. }
    apply Hoare_conj with
      (Q1 := fun _ s => Active u s).
    { eapply Hoare_conseq_pre.
      2: apply (set_fa_keep_in_stack v u u).
      intros s [_ [Hactive _]]. exact Hactive. }
    apply Hoare_conj with
      (Q1 := fun _ s => stack_dfn_order s).
    { eapply Hoare_conseq_pre.
      2: apply set_fa_keep_stack_dfn_order.
      intros s [_ [_ [Hstack_order _]]]. exact Hstack_order. }
    apply Hoare_conj with
      (Q1 := fun _ s => dfn_injective s).
    { eapply Hoare_conseq_pre.
      2: apply set_fa_keep_dfn_injective.
      intros s [_ [_ [_ [Hinj _]]]]. exact Hinj. }
    { unfold set_fa. intro_state. hoare_auto_s.
      subst s. simpl.
      destruct H as [_ [_ [_ [_ Hnodup]]]]. exact Hnodup. }
  Qed.

  Lemma set_fa_pending_preserves_parent_loop
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         ~ Visited v s)
      (set_fa v u)
      (fun _ s => LoopInv u done s).
  Proof.
    unfold LoopInv.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopAuxFacts u s).
    { eapply Hoare_conseq_pre.
      2: apply set_fa_pending_preserves_loop_aux_facts.
      intros s [[Haux _] _]. exact Haux. }
    { eapply Hoare_conseq_pre.
      2: apply set_fa_pending_preserves_parent_core.
      intros s [[Haux Hcore] [Hedge Hnotvis]].
      destruct Haux as [_ [Hactive _]].
      exact (conj Hcore (conj Hedge (conj Hactive Hnotvis))). }
  Qed.

  Lemma set_fa_pending_prepares_child_entry
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         ~ Visited v s)
      (set_fa v u)
      (fun _ s =>
         LoopInv u done s /\
         EntryPre v s /\
         fa s v = u /\
         fa s v <> v).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. change
      (LoopInv u done (set_fa_state s0 v u) /\
       EntryPre v (set_fa_state s0 v u) /\
       fa (set_fa_state s0 v u) v = u /\
       fa (set_fa_state s0 v u) v <> v).
    destruct H as [Hinv [Hedge Hnotvis]].
    destruct Hinv as [Haux Hcore].
    destruct Hcore as [Hshape [Hclosed Hlow]].
    destruct Hshape as
      [Hwf [Htree_sound [Huvis [Hdone_edge [Hdone_vis Hprocessed]]]]].
    destruct Haux as [Hsettled [Hactive Horder]].
    assert (Hloop_post: LoopInv u done (set_fa_state s0 v u)).
    { unfold LoopInv. split.
      - unfold LoopAuxFacts, OrderFacts in *.
        simpl. exact (conj Hsettled (conj Hactive Horder)).
      - apply set_fa_pending_preserves_loop_core_inv; auto.
        exact (conj
                 (conj Hwf
                   (conj Htree_sound
                     (conj Huvis
                       (conj Hdone_edge
                         (conj Hdone_vis Hprocessed)))))
                 (conj Hclosed Hlow)). }
    assert (Hfa_new: fa (set_fa_state s0 v u) v = u).
    { unfold set_fa_state. simpl. unfold equiv_decb.
      destruct (equiv_dec v v) as [_ | Hneq].
      - reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    assert (Hu_ne_v: u <> v).
    { intros Hu_eq_v. apply Hnotvis. rewrite <- Hu_eq_v. exact Huvis. }
    assert (Hfa_ne: fa (set_fa_state s0 v u) v <> v).
    { rewrite Hfa_new. exact Hu_ne_v. }
    assert (Hentry: EntryPre v (set_fa_state s0 v u)).
    { assert (Hwf_pre: wf_scc_state_pre g root v (set_fa_state s0 v u)).
      { exact (conj
                 (set_fa_pending_preserves_wf_scc_state s0 u v Hwf Huvis Hnotvis)
                 Hnotvis). }
      assert (Hclosed_post: Closed (set_fa_state s0 v u)).
      { apply set_fa_pending_preserves_closed. exact Hclosed. }
      assert (Htree_post: TreeEdgesAreGraphEdges (set_fa_state s0 v u)).
      { apply set_fa_pending_preserves_tree_edges_are_graph_edges; auto. }
      assert (Hincoming:
                fa (set_fa_state s0 v u) v <> v ->
                Edge (fa (set_fa_state s0 v u) v) v).
      { intros _. rewrite Hfa_new. exact Hedge. }
      exact (conj Hwf_pre
              (conj Hsettled
                (conj Hclosed_post
                  (conj Htree_post
                    (conj Horder Hincoming))))). }
    exact (conj Hloop_post (conj Hentry (conj Hfa_new Hfa_ne))).
  Qed.

  Lemma current_active_edge_not_tree
        (u v: V) (done: V -> Prop) (s: St):
    LoopInv u done s ->
    Edge u v ->
    ~ done v ->
    Visited v s ->
    Active v s ->
    ~ tree_edge s u v.
  Proof.
    intros Hinv _ Hnot_done _ _ Htree.
    destruct Hinv as [_ [Hshape _]].
    destruct Hshape as [_ [_ [_ [_ [_ Hprocessed]]]]].
    unfold tree_edge, dg_step in Htree.
    destruct Htree as [e [Htree_edge [Hfst Hsnd]]].
    simpl in Hfst, Hsnd.
    unfold state_to_dfs_tree in Htree_edge. simpl in Htree_edge.
    destruct Htree_edge as [child [Hchild_vis [Hfane [Hfst_fa Hsnd_child]]]].
    assert (Hfa_child: fa s child = u).
    { rewrite <- Hfst_fa. exact Hfst. }
    apply Hnot_done.
    rewrite <- Hsnd.
    rewrite Hsnd_child.
    exact (Hprocessed child Hchild_vis Hfa_child Hfane).
  Qed.

  Lemma loop_core_shape_done_after_active
        (u v: V) (done: V -> Prop) (s: St):
    LoopCoreShape u done s ->
    Edge u v ->
    Visited v s ->
    LoopCoreShape u (done_after done v) s.
  Proof.
    intros [Hwf [Htree [Huvis [Hdone_edge [Hdone_vis Hprocessed]]]]]
           Hedge Hvis.
    assert (Hdone_edge_after:
              forall a, done_after done v a -> Edge u a).
    { intros a Hdone_after.
      destruct (done_after_elim done v a Hdone_after) as [Hdone | Ha_eq_v].
      + apply Hdone_edge. exact Hdone.
      + subst a. exact Hedge. }
    assert (Hdone_vis_after:
              forall a, done_after done v a -> Visited a s).
    { intros a Hdone_after.
      destruct (done_after_elim done v a Hdone_after) as [Hdone | Ha_eq_v].
      + apply Hdone_vis. exact Hdone.
      + subst a. exact Hvis. }
    assert (Hprocessed_after: ProcessedTreeChild u (done_after done v) s).
    { unfold ProcessedTreeChild in *.
      intros child Hchild_vis Hfa Hfane.
      apply done_after_intro_old.
      exact (Hprocessed child Hchild_vis Hfa Hfane). }
    exact (conj Hwf
            (conj Htree
              (conj Huvis
                (conj Hdone_edge_after
                  (conj Hdone_vis_after Hprocessed_after))))).
  Qed.

  Lemma partial_low_candidate_active_done_after_cases
        (u v b: V) (done: V -> Prop) (s: St):
    LoopCoreShape u done s ->
    ~ done v ->
    Visited v s ->
    PartialLowCandidate u (done_after done v) s b ->
    PartialLowCandidate u done s b \/ b = v.
  Proof.
    intros Hshape Hnot_done Hvis Hcandidate.
    destruct Hshape as [_ [_ [_ [_ [_ Hprocessed]]]]].
    unfold PartialLowCandidate in Hcandidate |- *.
    destruct Hcandidate as [Hb_root | Htarget].
    - left. left. exact Hb_root.
    - unfold PartialActiveTarget in Htarget.
      destruct Htarget as [Hdirect | Hchild].
      + destruct Hdirect as [a [Hdone_after [Hb [Hedge [Hactive Hnot_tree]]]]].
        destruct (done_after_elim done v a Hdone_after) as [Hdone | Ha_eq_v].
        * left. right. left.
          exists a. repeat split; auto.
        * right. rewrite Hb. exact Ha_eq_v.
      + destruct Hchild as
          [child [x [Hdone_after [Hedge [Hfa [Hfane [Hreach [Hxb [Hactive Hnot_tree]]]]]]]]].
        destruct (done_after_elim done v child Hdone_after) as [Hdone | Hchild_eq_v].
        * left. right. right.
          exists child, x. repeat split; auto.
        * exfalso. apply Hnot_done.
          rewrite Hchild_eq_v in Hfa, Hfane.
          exact (Hprocessed v Hvis Hfa Hfane).
  Qed.

  Lemma update_low_active_direct_preserves_loop_core_shape
        (u v: V) (done: V -> Prop) (n: nat):
    Hoare
      (fun s: St => LoopCoreShape u done s /\ Edge u v /\ Visited v s)
      (update_low u n)
      (fun _ s => LoopCoreShape u (done_after done v) s).
  Proof.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s => LoopCoreShape u done s)
        (Q2 := fun _ s => Edge u v /\ Visited v s).
      - eapply Hoare_conseq_pre.
        2: apply update_low_preserves_loop_core_shape.
        intros s [Hshape _].
        assert (Huvis: u ∈ visited s).
        { destruct Hshape as [_ [_ [Huvis _]]]. exact Huvis. }
        exact (conj Hshape Huvis).
      - apply Hoare_conj with
          (Q1 := fun _ _ => Edge u v)
          (Q2 := fun _ s => Visited v s).
        + unfold update_low. unfold_op. intro_state. hoare_auto_s;
            try (destruct H as [_ [Hedge _]]; exact Hedge);
            try (destruct H1 as [_ _];
                 destruct H as [_ [Hedge _]]; exact Hedge).
        + eapply Hoare_conseq_pre.
          2: apply (update_low_keep_visited u v n).
          intros s [_ [_ Hvis]]. exact Hvis. }
    intros _ s [Hshape [Hedge Hvis]].
    apply loop_core_shape_done_after_active; auto.
  Qed.

  Lemma update_low_active_direct_preserves_low_correct
        (u v: V) (done: V -> Prop) (n: nat):
    Hoare
      (fun s: St =>
         LoopCoreShape u done s /\
         LowCorrect u done s /\
         Edge u v /\
         ~ done v /\
         Visited v s /\
         Active v s /\
         ~ tree_edge s u v /\
         n = dfn s v)
      (update_low u n)
      (fun _ s => LowCorrect u (done_after done v) s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl.
      destruct H as [Hshape [[Hsound Hcomplete]
        [Hedge [Hnot_done [Hvis [Hactive [Hnot_tree Hn]]]]]]].
      split.
      + exists v. split.
        * apply partial_low_candidate_direct_active; auto.
        * simpl. unfold equiv_decb.
          destruct (equiv_dec u u) as [_ | Hneq].
          -- exact Hn.
          -- exfalso. apply Hneq. reflexivity.
      + intros target Hcandidate.
        pose proof (partial_low_candidate_active_done_after_cases
                      u v target done s0 Hshape Hnot_done Hvis Hcandidate)
          as [Hold_candidate | Hb_eq_v].
        * specialize (Hcomplete target Hold_candidate).
          simpl. unfold equiv_decb.
          destruct (equiv_dec u u) as [_ | Hneq].
          -- lia.
          -- exfalso. apply Hneq. reflexivity.
        * subst target.
          simpl. unfold equiv_decb.
          destruct (equiv_dec u u) as [_ | Hneq].
          -- lia.
          -- exfalso. apply Hneq. reflexivity.
    - destruct H1 as [Heq Hnot_lt]. subst s.
      destruct H as [Hshape [[Hsound Hcomplete]
        [Hedge [Hnot_done [Hvis [Hactive [Hnot_tree Hn]]]]]]].
      split.
      + destruct Hsound as [witness [Hcandidate Hlow]].
        exists witness. split.
        * apply partial_low_candidate_done_mono. exact Hcandidate.
        * exact Hlow.
      + intros target Hcandidate.
        pose proof (partial_low_candidate_active_done_after_cases
                      u v target done s0 Hshape Hnot_done Hvis Hcandidate)
          as [Hold_candidate | Hb_eq_v].
        * apply Hcomplete. exact Hold_candidate.
        * subst target. rewrite Hn in Hnot_lt. lia.
  Qed.

  Lemma update_low_active_direct_preserves_loop_inv
        (u v: V) (done: V -> Prop) (n: nat):
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         ~ done v /\
         Visited v s /\
         Active v s /\
         ~ tree_edge s u v /\
         n = dfn s v)
      (update_low u n)
      (fun _ s => LoopInv u (done_after done v) s).
  Proof.
    unfold LoopInv, LoopCoreInv.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopAuxFacts u s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_preserves_loop_aux_facts.
      intros s [[Haux _] _]. exact Haux. }
    apply Hoare_conj with
      (Q1 := fun _ s => LoopCoreShape u (done_after done v) s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_active_direct_preserves_loop_core_shape.
      intros s [[_ [Hshape _]] [Hedge [_ [Hvis _]]]].
      exact (conj Hshape (conj Hedge Hvis)). }
    apply Hoare_conj with
      (Q1 := fun _ s => Closed s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_preserves_closed.
      intros s [[_ [_ [Hclosed _]]] _]. exact Hclosed. }
    { eapply Hoare_conseq_pre.
      2: apply update_low_active_direct_preserves_low_correct.
      intros s [[_ [Hshape [_ Hlow]]] [Hedge [Hnot_done [Hvis [Hactive [Hnot_tree Hn]]]]]].
      exact (conj Hshape
              (conj Hlow
                (conj Hedge
                  (conj Hnot_done
                    (conj Hvis
                      (conj Hactive
                        (conj Hnot_tree Hn))))))). }
  Qed.

  Lemma visited_active_branch_preserves_loop_inv
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         ~ done v /\
         Visited v s /\
         Active v s)
      (dv <- get' (fun s => dfn s v);; update_low u dv)
      (fun _ s => LoopInv u (done_after done v) s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: apply update_low_active_direct_preserves_loop_inv.
    intros s1 [Hs1 Hdv]. subst s1.
    destruct H as [Hinv [Hedge [Hnot_done [Hvis Hactive]]]].
    assert (Hnot_tree: ~ tree_edge s0 u v).
    { eapply current_active_edge_not_tree; eauto. }
    exact (conj Hinv
            (conj Hedge
              (conj Hnot_done
                (conj Hvis
                  (conj Hactive
                    (conj Hnot_tree Hdv)))))).
  Qed.

  Lemma tree_reachable_to_graph_reachable (s: St) (x y: V):
    TreeEdgesAreGraphEdges s ->
    dg_reachable (state_to_dfs_tree g s root) x y ->
    dg_reachable g x y.
  Proof.
    intros Htree_sound Hreach.
    eapply dg_reachable_lift.
    - intros a b Hstep.
      apply Htree_sound. exact Hstep.
    - exact Hreach.
  Qed.

  Lemma inactive_done_no_new_target
        (u v b: V) (done: V -> Prop) (s: St):
    Closed s ->
    TreeEdgesAreGraphEdges s ->
    Visited v s ->
    ~ Active v s ->
    Edge u v ->
    PartialLowCandidate u (done_after done v) s b ->
    PartialLowCandidate u done s b.
  Proof.
    intros Hclosed Htree_sound Hvis Hnot_active _ Hcandidate.
    unfold PartialLowCandidate in Hcandidate |- *.
    destruct Hcandidate as [Hb_root | Htarget].
    - left. exact Hb_root.
    - unfold PartialActiveTarget in Htarget |- *.
      destruct Htarget as [Hdirect | Hchild].
      + destruct Hdirect as [a [Hdone_after [Hb [Hedge [Hactive Hnot_tree]]]]].
        destruct (done_after_elim done v a Hdone_after) as [Hdone | Ha_eq_v].
        * right. left. exists a. repeat split; auto.
        * exfalso. apply Hnot_active.
          rewrite Ha_eq_v in Hactive. exact Hactive.
      + destruct Hchild as
          [child [x [Hdone_after [Hedge [Hfa [Hfane [Hreach [Hxb [Hactive Hnot_tree]]]]]]]]].
        destruct (done_after_elim done v child Hdone_after) as [Hdone | Hchild_eq_v].
        * right. right. exists child, x. repeat split; auto.
        * exfalso.
          rewrite Hchild_eq_v in Hreach.
          assert (Htree_graph: dg_reachable g v x).
          { eapply tree_reachable_to_graph_reachable; eauto. }
          assert (Hreach_target: dg_reachable g v b).
          { eapply dg_reachable_step_reachable; eauto. }
          exact (Hclosed v b Hvis Hnot_active Hreach_target Hactive).
  Qed.

  Lemma low_correct_add_inactive_done
        (u v: V) (done: V -> Prop) (s: St):
    Closed s ->
    TreeEdgesAreGraphEdges s ->
    Visited v s ->
    ~ Active v s ->
    Edge u v ->
    LowCorrect u done s ->
    LowCorrect u (done_after done v) s.
  Proof.
    intros Hclosed Htree_sound Hvis Hnot_active Hedge [Hsound Hcomplete].
    split.
    - destruct Hsound as [witness [Hcandidate Hlow]].
      exists witness. split.
      + apply partial_low_candidate_done_mono. exact Hcandidate.
      + exact Hlow.
    - intros target Hcandidate.
      apply Hcomplete.
      eapply inactive_done_no_new_target; eauto.
  Qed.

  Lemma visited_inactive_branch_preserves_loop_inv
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         ~ done v /\
         Visited v s /\
         ~ Active v s)
      (ret tt)
      (fun _ s => LoopInv u (done_after done v) s).
  Proof.
    unfold Hoare, ret. simpl. sets_unfold.
    unfold StateRelMonad.ret.
    intros s1 retv s2 Hpre [Hret Hstate].
    subst retv s2.
    destruct Hpre as [Hinv [Hedge [_ [Hvis Hnot_active]]]].
    destruct Hinv as [Haux [Hshape [Hclosed Hlow]]].
    destruct Hshape as [Hwf [Htree_sound [Huvis [Hdone_edge [Hdone_vis Hprocessed]]]]].
    assert (Hshape_old: LoopCoreShape u done s1).
    { exact (conj Hwf
              (conj Htree_sound
                (conj Huvis
                  (conj Hdone_edge
                    (conj Hdone_vis Hprocessed))))). }
    unfold LoopInv, LoopCoreInv.
    split.
    - exact Haux.
    - split.
      + apply loop_core_shape_done_after_active; auto.
      + split.
        * exact Hclosed.
        * apply low_correct_add_inactive_done; auto.
  Qed.

  Lemma tree_reachable_from_root_cases (s: St) (v x: V):
    TreeEdgesAreGraphEdges s ->
    dg_reachable (state_to_dfs_tree g s root) v x ->
    x = v \/
    exists child,
      Edge v child /\
      fa s child = v /\
      fa s child <> child /\
      dg_reachable (state_to_dfs_tree g s root) child x.
  Proof.
    intros Htree_sound Hreach.
    unfold dg_reachable in Hreach.
    induction Hreach as [a b Hstep | a | a b c Hreach_ab IH_ab Hreach_bc IH_bc].
    - right. exists b.
      pose proof Hstep as Hstep_tree.
      apply tree_step_char in Hstep_tree as [Hfa [Hfane _]].
      split.
      + apply Htree_sound. exact Hstep.
      + split; [exact Hfa | split; [exact Hfane |]].
        unfold dg_reachable.
        apply Coq.Relations.Relation_Operators.rt_refl.
    - left. reflexivity.
    - destruct IH_ab as [Hb_eq | [child [Hedge [Hfa [Hfane Hreach_child_b]]]]].
      + subst b. exact IH_bc.
      + right. exists child. repeat split; auto.
        eapply dg_reachable_trans; eauto.
  Qed.

  Lemma tree_escape_to_child_candidate
        (v x b: V) (s: St):
    TreeEdgesAreGraphEdges s ->
    dg_reachable (state_to_dfs_tree g s root) v x ->
    Edge x b ->
    Active b s ->
    ~ tree_edge s x b ->
    PartialLowCandidate v (edge_set v) s b.
  Proof.
    intros Htree_sound Hreach Hedge Hactive Hnot_tree.
    destruct (tree_reachable_from_root_cases s v x Htree_sound Hreach)
      as [Hx_eq_v | [child [Hchild_edge [Hfa [Hfane Hreach_child_x]]]]].
    - subst x. right. left.
      exists b. repeat split; auto.
    - right. right.
      exists child, x. repeat split; auto.
  Qed.

  Lemma child_candidate_lifts_to_parent
        (u v b: V) (done: V -> Prop) (s: St):
    LoopCoreShape v (edge_set v) s ->
    Edge u v ->
    fa s v = u ->
    fa s v <> v ->
    PartialLowCandidate v (edge_set v) s b ->
    b = v \/ PartialActiveTarget u (done_after done v) s b.
  Proof.
    intros Hshape Hedge_uv Hfa_v Hfane_v Hcandidate.
    destruct Hcandidate as [Hb_eq_v | Htarget].
    - left. exact Hb_eq_v.
    - right.
      destruct Hshape as [_ [_ [_ [_ [Hdone_vis _]]]]].
      unfold PartialActiveTarget in Htarget |- *.
      destruct Htarget as [Hdirect | Hchild].
      + destruct Hdirect as [a [Hdone [Hb [Hedge [Hactive Hnot_tree]]]]].
        right. exists v, v.
        repeat split; auto.
        * apply done_after_intro_new.
        * unfold dg_reachable.
          apply Coq.Relations.Relation_Operators.rt_refl.
        * rewrite Hb. exact Hedge.
        * rewrite Hb. exact Hactive.
        * rewrite Hb. exact Hnot_tree.
      + destruct Hchild as
          [child [x [Hdone [Hedge [Hfa [Hfane [Hreach [Hxb [Hactive Hnot_tree]]]]]]]]].
        assert (Hchild_vis: Visited child s).
        { apply Hdone_vis. exact Hdone. }
        assert (Htree_v_child: tree_edge s v child).
        { unfold tree_edge.
          eapply tree_step_char_backward; eauto. }
        assert (Hreach_v_x:
                  dg_reachable (state_to_dfs_tree g s root) v x).
        { eapply dg_step_reachable_reachable; eauto. }
        right. exists v, x.
        repeat split; auto.
        apply done_after_intro_new.
  Qed.

  Lemma parent_candidate_done_after_child_cases
        (u v b: V) (done: V -> Prop) (s: St):
    TreeEdgesAreGraphEdges s ->
    Edge u v ->
    Visited v s ->
    fa s v = u ->
    fa s v <> v ->
    PartialLowCandidate u (done_after done v) s b ->
    PartialLowCandidate u done s b \/
    exists x,
      dg_reachable (state_to_dfs_tree g s root) v x /\
      Edge x b /\
      Active b s /\
      ~ tree_edge s x b.
  Proof.
    intros _ Hedge_uv Hvis_v Hfa_v Hfane_v Hcandidate.
    assert (Htree_uv: tree_edge s u v).
    { unfold tree_edge.
      eapply tree_step_char_backward; eauto. }
    unfold PartialLowCandidate in Hcandidate |- *.
    destruct Hcandidate as [Hb_root | Htarget].
    - left. left. exact Hb_root.
    - unfold PartialActiveTarget in Htarget |- *.
      destruct Htarget as [Hdirect | Hchild].
      + destruct Hdirect as [a [Hdone_after [Hb [Hedge [Hactive Hnot_tree]]]]].
        destruct (done_after_elim done v a Hdone_after) as [Hdone | Ha_eq_v].
        * left. right. left.
          exists a. repeat split; auto.
        * subst a. subst b.
          exfalso. apply Hnot_tree. exact Htree_uv.
      + destruct Hchild as
          [child [x [Hdone_after [Hedge [Hfa [Hfane [Hreach [Hxb [Hactive Hnot_tree]]]]]]]]].
        destruct (done_after_elim done v child Hdone_after) as [Hdone | Hchild_eq_v].
        * left. right. right.
          exists child, x. repeat split; auto.
        * subst child. right.
          exists x. repeat split; auto.
  Qed.

  Lemma low_correct_add_child_contribution_value
        (u v: V) (done: V -> Prop) (s_before s: St) (n: nat):
    LoopInv u done s_before ->
    Edge u v ->
    ParentLowFrame u done s_before s ->
    TreeEdgesAreGraphEdges s ->
    Visited v s ->
    fa s v = u ->
    fa s v <> v ->
    ChildLowContribution u v s ->
    n = Nat.min (low s_before u) (low s v) ->
    (exists witness,
       PartialLowCandidate u (done_after done v) s witness /\
       n = dfn s witness) /\
    (forall target,
       PartialLowCandidate u (done_after done v) s target ->
       n <= dfn s target).
  Proof.
    intros Hinv Hedge_uv Hframe Htree_sound Hvis_v Hfa_v Hfane_v
           Hchild_contrib Hn.
    destruct Hinv as [_ [_ [_ [Hsound_old Hcomplete_old]]]].
    destruct Hframe as [_ [Hframe_fwd Hframe_bwd]].
    assert (Hroot_before: PartialLowCandidate u done s_before u).
    { apply partial_low_candidate_root. }
    pose proof (Hcomplete_old u Hroot_before) as Hlow_before_le_dfn_before_u.
    destruct (Hframe_fwd u Hroot_before) as [_ Hdfn_u_eq].
    assert (Hlow_before_le_dfn_u: low s_before u <= dfn s u) by lia.
    split.
    - destruct (Nat.le_gt_cases (low s_before u) (low s v))
        as [Hold_le | Hchild_lt].
      + destruct Hsound_old as [witness [Hcandidate_before Hlow_before_eq]].
        destruct (Hframe_fwd witness Hcandidate_before) as
          [Hcandidate_after Hdfn_w_eq].
        exists witness. split.
        * apply partial_low_candidate_done_mono. exact Hcandidate_after.
        * subst n. rewrite Nat.min_l by exact Hold_le. lia.
      + destruct Hchild_contrib as
          [[Hv_active [Hchild_shape [Hchild_sound _]]] |
           [Hv_inactive [Hlow_v_eq [Hdfn_lt Hno_target]]]].
        * destruct Hchild_sound as [witness [Hcandidate_child Hlow_v_witness]].
          destruct (child_candidate_lifts_to_parent
                      u v witness done s Hchild_shape Hedge_uv Hfa_v
                      Hfane_v Hcandidate_child)
            as [Hwitness_eq_v | Hparent_target].
          -- subst witness.
             destruct Hchild_shape as [Hwf_child _].
             destruct Hwf_child as [_ [_ [Hdfn_valid _]]].
             assert (Hdfn_parent_child: dfn s u < dfn s v).
             { eapply fa_parent_dfn_lt; eauto. }
             lia.
          -- exists witness. split.
             ++ right. exact Hparent_target.
             ++ subst n. rewrite Nat.min_r by lia. lia.
        * lia.
    - intros target Hcandidate_after.
      subst n.
      destruct (parent_candidate_done_after_child_cases
                  u v target done s Htree_sound Hedge_uv Hvis_v
                  Hfa_v Hfane_v Hcandidate_after)
        as [Hcandidate_old_after |
            [x [Hreach_v_x [Hedge_x_target [Hactive_target Hnot_tree]]]]].
      + destruct (Hframe_bwd target Hcandidate_old_after) as
          [Hcandidate_before Hdfn_target_eq].
        pose proof (Hcomplete_old target Hcandidate_before) as Hcomplete_target.
        pose proof (Nat.le_min_l (low s_before u) (low s v)) as Hmin_le_old.
        lia.
      + destruct Hchild_contrib as
          [[Hv_active [Hchild_shape [_ Hchild_complete]]] |
           [Hv_inactive [Hlow_v_eq [Hdfn_lt Hno_target]]]].
        * assert (Hcandidate_child:
                    PartialLowCandidate v (edge_set v) s target).
          { eapply tree_escape_to_child_candidate; eauto. }
          pose proof (Hchild_complete target Hcandidate_child)
            as Hchild_complete_target.
          pose proof (Nat.le_min_r (low s_before u) (low s v)) as Hmin_le_child.
          lia.
        * exfalso.
          exact (Hno_target x target Hreach_v_x Hedge_x_target
                            Hactive_target Hnot_tree).
  Qed.

  Lemma update_low_child_contribution_preserves_low_correct
        (u v: V) (done: V -> Prop) (s_before: St) (n: nat):
    Hoare
      (fun s: St =>
         LoopInv u done s_before /\
         Edge u v /\
         ChildContributionContract u v done s_before s /\
         n = low s v)
      (update_low u n)
      (fun _ s => LowCorrect u (done_after done v) s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl.
      destruct H as [Hinv [Hedge_uv [Hcontract Hn_low_v]]].
      destruct Hcontract as
        [Hframe [Hshape [Haux [Hclosed [Htree [Hvis [Hfa [Hfane Hchild]]]]]]]].
      destruct Hframe as [Hlow_u_frame Hframe_rest].
      assert (Hframe_all:
                ParentLowFrame u done s_before s0).
      { exact (conj Hlow_u_frame Hframe_rest). }
      assert (Hn_min:
                n = Nat.min (low s_before u) (low s0 v)).
      { rewrite <- Hlow_u_frame.
        rewrite <- Hn_low_v.
        rewrite Nat.min_r by lia.
        reflexivity. }
      destruct (low_correct_add_child_contribution_value
                  u v done s_before s0 n Hinv Hedge_uv Hframe_all
                  Htree Hvis Hfa Hfane Hchild Hn_min)
        as [Hsound_value Hcomplete_value].
      split.
      + destruct Hsound_value as [witness [Hcandidate Hlow_witness]].
        exists witness. split.
        * change (PartialLowCandidate u (done_after done v) s0 witness).
          exact Hcandidate.
        * simpl. unfold equiv_decb.
          destruct (equiv_dec u u) as [_ | Hneq].
          -- exact Hlow_witness.
          -- exfalso. apply Hneq. reflexivity.
      + intros target Hcandidate.
        simpl. unfold equiv_decb.
        destruct (equiv_dec u u) as [_ | Hneq].
        * apply Hcomplete_value.
          change (PartialLowCandidate u (done_after done v) s0 target)
            in Hcandidate.
          exact Hcandidate.
        * exfalso. apply Hneq. reflexivity.
    - destruct H1 as [Heq Hnot_lt]. subst s.
      destruct H as [Hinv [Hedge_uv [Hcontract Hn_low_v]]].
      destruct Hcontract as
        [Hframe [Hshape [Haux [Hclosed [Htree [Hvis [Hfa [Hfane Hchild]]]]]]]].
      destruct Hframe as [Hlow_u_frame Hframe_rest].
      assert (Hframe_all:
                ParentLowFrame u done s_before s0).
      { exact (conj Hlow_u_frame Hframe_rest). }
      assert (Hn_min:
                low s0 u = Nat.min (low s_before u) (low s0 v)).
      { rewrite <- Hlow_u_frame.
        rewrite <- Hn_low_v.
        rewrite Nat.min_l by lia.
        reflexivity. }
      destruct (low_correct_add_child_contribution_value
                  u v done s_before s0 (low s0 u) Hinv Hedge_uv Hframe_all
                  Htree Hvis Hfa Hfane Hchild Hn_min)
        as [Hsound_value Hcomplete_value].
      exact (conj Hsound_value Hcomplete_value).
  Qed.

  Lemma update_low_child_contribution_preserves_loop_core_shape
        (u v: V) (done: V -> Prop) (s_before: St) (n: nat):
    Hoare
      (fun s: St =>
         ChildContributionContract u v done s_before s)
      (update_low u n)
      (fun _ s => LoopCoreShape u (done_after done v) s).
  Proof.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_loop_core_shape.
    intros s Hcontract.
    destruct Hcontract as [_ [Hshape _]].
    pose proof Hshape as Hshape_copy.
    destruct Hshape_copy as [_ [_ [Huvis _]]].
    exact (conj Hshape Huvis).
  Qed.

  Lemma update_low_child_contribution_preserves_loop_inv
        (u v: V) (done: V -> Prop) (s_before: St) (n: nat):
    Hoare
      (fun s: St =>
         LoopInv u done s_before /\
         Edge u v /\
         ChildContributionContract u v done s_before s /\
         n = low s v)
      (update_low u n)
      (fun _ s => LoopInv u (done_after done v) s).
  Proof.
    unfold LoopInv, LoopCoreInv.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopAuxFacts u s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_preserves_loop_aux_facts.
      intros s [_ [_ [Hcontract _]]].
      destruct Hcontract as [_ [_ [Haux _]]].
      exact Haux. }
    apply Hoare_conj with
      (Q1 := fun _ s => LoopCoreShape u (done_after done v) s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_child_contribution_preserves_loop_core_shape.
      intros s [_ [Hedge [Hcontract _]]].
      exact Hcontract. }
    apply Hoare_conj with
      (Q1 := fun _ s => Closed s).
    { eapply Hoare_conseq_pre.
      2: apply update_low_preserves_closed.
      intros s [_ [_ [Hcontract _]]].
      destruct Hcontract as [_ [_ [_ [Hclosed _]]]].
      exact Hclosed. }
    { eapply Hoare_conseq_pre.
      2: apply update_low_child_contribution_preserves_low_correct.
      intros s [Hinv [Hedge [Hcontract Hn]]].
      exact (conj Hinv (conj Hedge (conj Hcontract Hn))). }
  Qed.

  Lemma get_low_update_low_child_contribution_preserves_loop_inv
        (u v: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         LoopInv u done s_before /\
         Edge u v /\
         ChildContributionContract u v done s_before s)
      (lv <- get' (fun s => low s v);; update_low u lv)
      (fun _ s => LoopInv u (done_after done v) s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: apply update_low_child_contribution_preserves_loop_inv.
    intros s1 [Hs1 Hlv]. subst s1.
    destruct H as [Hinv [Hedge Hcontract]].
    exact (conj Hinv (conj Hedge (conj Hcontract Hlv))).
  Qed.

  Lemma get_low_update_low_child_contribution_preserves_loop_inv_exists
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         exists s_before,
           LoopInv u done s_before /\
           Edge u v /\
           ChildContributionContract u v done s_before s)
      (lv <- get' (fun s => low s v);; update_low u lv)
      (fun _ s => LoopInv u (done_after done v) s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [s_before Hpre] Hexec.
    pose proof
      (get_low_update_low_child_contribution_preserves_loop_inv
         u v done s_before) as Hhoare.
    unfold Hoare in Hhoare.
    exact (Hhoare s1 retv s2 Hpre Hexec).
  Qed.

  Lemma unvisited_tree_child_branch_preserves_loop_inv
        (u v: V) (done: V -> Prop) (W: RecProgram):
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         EntryPre v s /\
         fa s v = u /\
         fa s v <> v)
      (W v)
      (fun _ s =>
         exists s_before,
           LoopInv u done s_before /\
           Edge u v /\
           ChildContributionContract u v done s_before s) ->
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         ~ Visited v s)
      (set_fa v u;;
       W v;;
       lv <- get' (fun s => low s v);;
       update_low u lv)
      (fun _ s => LoopInv u (done_after done v) s).
  Proof.
    intros HW.
    eapply Hoare_bind.
    { apply set_fa_pending_prepares_child_entry. }
    simpl. intros _.
    eapply Hoare_bind.
    { eapply Hoare_conseq_pre.
      2: exact HW.
      intros s [Hloop [Hentry [Hfa Hfane]]].
      assert (Hedge: Edge u v).
      { destruct Hentry as [_ [_ [_ [_ [_ Hincoming]]]]].
        rewrite <- Hfa. apply Hincoming. exact Hfane. }
      exact (conj Hloop
              (conj Hedge
                (conj Hentry
                  (conj Hfa Hfane)))). }
    simpl. intros _.
    apply get_low_update_low_child_contribution_preserves_loop_inv_exists.
  Qed.

  Lemma process_edge_preserves_loop_inv
        (u v: V) (done: V -> Prop) (W: RecProgram):
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         EntryPre v s /\
         fa s v = u /\
         fa s v <> v)
      (W v)
      (fun _ s =>
         exists s_before,
           LoopInv u done s_before /\
           Edge u v /\
           ChildContributionContract u v done s_before s) ->
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         ~ done v)
      (process_edge u W v)
      (fun _ s => LoopInv u (done_after done v) s).
  Proof.
    intros HW.
    unfold process_edge, if_else.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: apply (unvisited_tree_child_branch_preserves_loop_inv
                  u v done W HW).
      intros s1 [Hnotvis Hs1]. subst s1.
      destruct H as [Hinv [Hedge _]].
      exact (conj Hinv (conj Hedge Hnotvis)).
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hvisited_by_classic Hs1]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: apply visited_active_branch_preserves_loop_inv.
        intros s1 [Hactive Hs1]. subst s1.
        destruct H as [Hinv [Hedge Hnotdone]].
        assert (Hvis: Visited v s0).
        { unfold Visited. apply NNPP. exact Hvisited_by_classic. }
        assert (Hactive': Active v s0).
        { unfold Active. exact Hactive. }
        exact (conj Hinv
                (conj Hedge
                  (conj Hnotdone
                    (conj Hvis Hactive')))).
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        simpl. intros _ s [Heq Hnotactive]. subst s.
        destruct H as [Hinv [Hedge _]].
        assert (Hvis: Visited v s0).
        { unfold Visited. apply NNPP. exact Hvisited_by_classic. }
        assert (Hnotactive': ~ Active v s0).
        { unfold Active. exact Hnotactive. }
        destruct Hinv as [Haux [Hshape [Hclosed Hlow]]].
        pose proof Hshape as Hshape_old.
        destruct Hshape as
          [Hwf [Htree_sound [Huvis [Hdone_edge [Hdone_vis Hprocessed]]]]].
        unfold LoopInv, LoopCoreInv.
        split; [exact Haux |].
        split.
        * apply loop_core_shape_done_after_active; auto.
        * split; [exact Hclosed |].
          apply low_correct_add_inactive_done; auto.
  Qed.

  Lemma process_edge_preserves_stack_nodup
        (u v: V) (W: RecProgram):
    (forall x, Hoare StackNoDup (W x) (fun _ s => StackNoDup s)) ->
    Hoare StackNoDup
          (process_edge u W v)
          (fun _ s => StackNoDup s).
  Proof.
    intros HW.
    unfold process_edge, if_else.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := StackNoDup).
      intros s1 [_ Hs1]. subst s1. exact H.
      hoare_bind (set_fa_preserves_stack_nodup v u). simpl. clear a.
      eapply Hoare_bind.
      { apply HW. }
      simpl. intros _.
      apply get_low_update_low_preserves_stack_nodup.
    - intro_state. hoare_auto_s.
      + eapply Hoare_conseq_pre.
        2: apply (update_low_preserves_stack_nodup u (dfn s0 v)).
        intros s1 Hs1. subst s1. exact H.
      + destruct H3 as [Heq _]. subst s. subst s1. exact H.
  Qed.

  Lemma process_edge_preserves_loop_aux_facts
        (u v: V) (W: RecProgram):
    (forall x,
       Hoare NoUnvisitedReach (W x) (fun _ s => NoUnvisitedReach s)) ->
    (forall x,
       Hoare (Active u) (W x) (fun _ s => Active u s)) ->
    (forall x,
       Hoare stack_dfn_order (W x) (fun _ s => stack_dfn_order s)) ->
    (forall x,
       Hoare dfn_injective (W x) (fun _ s => dfn_injective s)) ->
    (forall x,
       Hoare StackNoDup (W x) (fun _ s => StackNoDup s)) ->
    Hoare (LoopAuxFacts u)
          (process_edge u W v)
          (fun _ s => LoopAuxFacts u s).
  Proof.
    intros HWsettled HWactive HWorder HWinj HWnodup.
    unfold LoopAuxFacts, OrderFacts.
    apply Hoare_conj with
      (Q1 := fun _ s => NoUnvisitedReach s).
    { eapply Hoare_conseq_pre.
      2: { apply process_edge_keep_settled_closed.
           intros x. apply HWsettled. }
      intros s [Hsettled _]. exact Hsettled. }
    apply Hoare_conj with
      (Q1 := fun _ s => Active u s).
    { eapply Hoare_conseq_pre.
      2: { apply process_edge_keep_in_stack.
           intros x. apply HWactive. }
      intros s [_ [Hactive _]]. exact Hactive. }
    apply Hoare_conj with
      (Q1 := fun _ s => stack_dfn_order s).
    { eapply Hoare_conseq_pre.
      2: { apply process_edge_preserves_stack_dfn_order.
           intros x. apply HWorder. }
      intros s [_ [_ [Hstack_order _]]]. exact Hstack_order. }
    apply Hoare_conj with
      (Q1 := fun _ s => dfn_injective s).
    { eapply Hoare_conseq_pre.
      2: { apply process_edge_keep_dfn_injective.
           intros x. apply HWinj. }
      intros s [_ [_ [_ [Hinj _]]]]. exact Hinj. }
    { eapply Hoare_conseq_pre.
      2: { apply process_edge_preserves_stack_nodup.
           intros x. apply HWnodup. }
      intros s [_ [_ [_ [_ Hnodup]]]]. exact Hnodup. }
  Qed.

  Lemma forset_process_edge_preserves_loop_aux_facts
        (u: V) (W: RecProgram):
    (forall x,
       Hoare NoUnvisitedReach (W x) (fun _ s => NoUnvisitedReach s)) ->
    (forall x,
       Hoare (Active u) (W x) (fun _ s => Active u s)) ->
    (forall x,
       Hoare stack_dfn_order (W x) (fun _ s => stack_dfn_order s)) ->
    (forall x,
       Hoare dfn_injective (W x) (fun _ s => dfn_injective s)) ->
    (forall x,
       Hoare StackNoDup (W x) (fun _ s => StackNoDup s)) ->
    Hoare (LoopAuxFacts u)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => LoopAuxFacts u s).
  Proof.
    intros HWsettled HWactive HWorder HWinj HWnodup.
    unfold forset. hoare_fix_nolv_auto (V -> Prop).
    simpl; intros W0 IH0 todo.
    unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
    eapply Hoare_bind with (R := fun (_: unit) s => LoopAuxFacts u s).
    { apply Hoare_conseq_pre with (P2 := LoopAuxFacts u).
      { intros s1 Hs1. subst s1. exact H. }
      apply process_edge_preserves_loop_aux_facts; auto. }
    simpl. intros _. apply IH0.
  Qed.

  Lemma edge_loop_preserves_loop_inv
        (u: V) (W: RecProgram):
    (forall done v,
       done ⊆ edge_set u ->
       Edge u v ->
       ~ done v ->
       Hoare
         (fun s: St =>
            LoopInv u done s /\
            Edge u v /\
            EntryPre v s /\
            fa s v = u /\
            fa s v <> v)
         (W v)
         (fun _ s =>
            exists s_before,
              LoopInv u done s_before /\
              Edge u v /\
              ChildContributionContract u v done s_before s)) ->
    Hoare
      (fun s: St => LoopInv u ∅ s)
      (forset (edge_set u) (process_edge u W))
      (fun _ s => LoopInv u (edge_set u) s).
  Proof.
    intros HW.
    apply Hoare_forset with
      (P := fun done s => LoopInv u done s)
      (universe := edge_set u).
    - intros done1 done2 Hdone s1 s2 Heq. subst s2.
      split; intro Hinv.
      + eapply loop_inv_done_equiv; eauto.
      + eapply loop_inv_done_equiv.
        * symmetry. exact Hdone.
        * exact Hinv.
    - intros done a Hdone_sub Hedge Hnot_done.
      eapply Hoare_conseq_pre.
      2: {
        eapply process_edge_preserves_loop_inv.
        apply HW; auto. }
      intros s Hinv.
      exact (conj Hinv (conj Hedge Hnot_done)).
  Qed.

  (* maybe pop *)
  
End IS_LOW.
