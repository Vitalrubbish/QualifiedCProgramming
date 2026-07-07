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
End IS_LOW.
