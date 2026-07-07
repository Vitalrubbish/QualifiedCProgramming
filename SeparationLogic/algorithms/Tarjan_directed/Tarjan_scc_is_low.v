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

  Definition LoopCoreShape (u: V) (done: V -> Prop) (s: St): Prop :=
    wf_scc_state g root s /\
    TreeEdgesAreGraphEdges s /\
    Visited u s /\
    (forall a, done a -> Edge u a) /\
    (forall a, done a -> Visited a s).

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

  Lemma PartialTree_done_mono (u a x: V) (done: V -> Prop) (s: St):
    PartialTree u done s x ->
    PartialTree u (done_after done a) s x.
  Proof.
    intros Hpt. unfold PartialTree in *.
    destruct Hpt as [-> | [child [Hdone [Hedge [Hfa [Hfane Hreach]]]]]].
    - left. reflexivity.
    - right. exists child. repeat split; auto.
      apply done_after_intro_old. exact Hdone.
  Qed.

  Lemma PartialActiveTarget_done_mono
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

  Lemma PartialLowCandidate_done_mono
        (u a b: V) (done: V -> Prop) (s: St):
    PartialLowCandidate u done s b ->
    PartialLowCandidate u (done_after done a) s b.
  Proof.
    intros Ht. unfold PartialLowCandidate in *.
    destruct Ht as [Hb | Hactive].
    - left. exact Hb.
    - right. apply PartialActiveTarget_done_mono. exact Hactive.
  Qed.

  Lemma PartialTree_root (u: V) (done: V -> Prop) (s: St):
    PartialTree u done s u.
  Proof.
    unfold PartialTree. left. reflexivity.
  Qed.

  Lemma PartialLowCandidate_root (u: V) (done: V -> Prop) (s: St):
    PartialLowCandidate u done s u.
  Proof.
    unfold PartialLowCandidate. left. reflexivity.
  Qed.

  Lemma PartialActiveTarget_direct
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

  Lemma PartialLowCandidate_direct_active
        (u a: V) (done: V -> Prop) (s: St):
    Edge u a ->
    Active a s ->
    ~ tree_edge s u a ->
    PartialLowCandidate u (done_after done a) s a.
  Proof.
    intros Hedge Hactive Hntr.
    right. apply PartialActiveTarget_direct; auto.
  Qed.

  Lemma LowCorrect_empty (u: V) (s: St):
    low s u = dfn s u ->
    LowCorrect u ∅ s.
  Proof.
    intros Hlow. split.
    - exists u. split.
      + apply PartialLowCandidate_root.
      + exact Hlow.
    - unfold LowComplete. intros b Ht.
      unfold PartialLowCandidate in Ht.
      destruct Ht as [-> | Hactive].
      + rewrite Hlow. lia.
      + unfold PartialActiveTarget in Hactive.
        destruct Hactive as [[a [Hdone _]] | [child [x [Hdone _]]]];
          sets_unfold in Hdone; tauto.
  Qed.

  Lemma LowComplete_done_mono
        (u a: V) (done: V -> Prop) (s: St):
    LowComplete u (done_after done a) s ->
    LowComplete u done s.
  Proof.
    unfold LowComplete. intros H b Ht.
    apply H. apply PartialLowCandidate_done_mono. exact Ht.
  Qed.

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

  Lemma PreloopPreservesClosed (u: V):
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

  Lemma PreloopProducesLowCorrectEmpty (u: V):
    Hoare (fun _ : St => True)
          (preloop u)
          (fun _ s => LowCorrect u ∅ s).
  Proof.
    eapply Hoare_conseq_post.
    2: apply preloop_low_eq_dfn.
    intros ret s Hlow. apply LowCorrect_empty. exact Hlow.
  Qed.

  Lemma PreloopProducesLoopCoreShape (u: V):
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
    { eapply Hoare_conseq_pre.
      2: apply preloop_empty_done_visited.
      intros s _. exact I. }
  Qed.

  Lemma PreloopProducesLoopAuxFacts (u: V):
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

  Theorem PreloopInitializesLoopInv (u: V):
    Hoare (EntryPre u)
          (preloop u)
          (fun _ s => LoopInv u ∅ s).
  Proof.
    unfold LoopInv, LoopCoreInv.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopAuxFacts u s).
    { apply PreloopProducesLoopAuxFacts. }
    apply Hoare_conj with
      (Q1 := fun _ s => LoopCoreShape u ∅ s).
    { apply PreloopProducesLoopCoreShape. }
    apply Hoare_conj with
      (Q1 := fun _ s => Closed s).
    { eapply Hoare_conseq_pre.
      2: apply PreloopPreservesClosed.
      intros s [Hwf [Hsettled [Hclosed _]]].
      exact (conj Hwf (conj Hsettled Hclosed)). }
    { eapply Hoare_conseq_pre.
      2: apply PreloopProducesLowCorrectEmpty.
      intros s _. exact I. }
  Qed.

End IS_LOW.
