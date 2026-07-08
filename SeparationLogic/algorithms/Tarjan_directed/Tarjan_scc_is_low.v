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

  Definition PoppedSegmentNoUnvisitedStep (u: V) (s: St): Prop :=
    forall x y,
      PoppedSegment u s x ->
      Edge x y ->
      ~ Visited y s ->
      False.

  Definition RootPopCuts (u: V) (s: St): Prop :=
    PoppedSegmentClosed u s /\
    PoppedSegmentNoActiveReach u s.

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

  Definition PoppedSegmentRestTargetCut (u: V) (s: St): Prop :=
    forall x b,
      PoppedSegment u s x ->
      Edge x b ->
      RestStack u s b ->
      exists target,
        PartialLowCandidate u (edge_set u) s target /\
        dfn s target <= dfn s b.

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

  Definition RootPopBranchWithCuts (u: V) (s: St): Prop :=
    RootPopBranchPre u s /\ RootPopCuts u s.

  (* Edge-loop completion facts consumed by the pop bridge.  They are
     deliberately weaker than [PoppedSegmentClosed]: before the pop
     branch, the current segment may reach unvisited vertices through
     older stack frames.  The first field only rules out direct unvisited
     exits from the completed current segment; the second field connects
     every path from the current segment to the older stack with a
     full-loop low candidate, so [low[u] = dfn[u]] can rule that path
     out. *)
  Definition RootTraversalComplete (u: V) (s: St): Prop :=
    PoppedSegmentNoUnvisitedStep u s /\
    PoppedSegmentRestTargetCut u s.

  Definition LoopNoUnvisitedStep
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall x y,
      PoppedSegment u s x ->
      Edge x y ->
      ~ Visited y s ->
      x = u /\ ~ done y.

  Definition LoopRestTargetCut
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall x b,
      PoppedSegment u s x ->
      Edge x b ->
      RestStack u s b ->
      (x = u /\ ~ done b) \/
      exists target,
        PartialLowCandidate u done s target /\
        dfn s target <= dfn s b.

  Definition LoopTraversalComplete
             (u: V) (done: V -> Prop) (s: St): Prop :=
    LoopNoUnvisitedStep u done s /\
    LoopRestTargetCut u done s.

  Definition RootPreMaybePop (u: V) (s: St): Prop :=
    RootPrePop u s /\
    RootTraversalComplete u s.

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
    (Active v s /\
     LoopCoreShape v (edge_set v) s /\
     RootLowCorrect v s /\
     RootTraversalComplete v s) \/
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
      low s_before u <= dfn s_after b).

  (* Parent-side stack frame for a recursive tree child: all old low
     candidates of [parent] lie below [child], so popping [child]'s
     segment cannot remove the witnesses already used by [parent]. *)
  Definition ParentOldCandidatesBelowChild
             (parent child: V) (done: V -> Prop)
             (s_before s: St): Prop :=
    forall b,
      PartialLowCandidate parent done s_before b ->
      RestStack child s b.

  (* Stack preservation component of the tree-child frame.  It is a
     proof-only cut for traversal completeness: the child segment accounts
     for newly explored stack entries, while the old parent segment/rest
     can still be read in [s_before]. *)
  Definition ParentTraversalStackFrame
             (parent child: V) (s_before s: St): Prop :=
    (forall x,
      PoppedSegment parent s x ->
      PoppedSegment child s x \/ PoppedSegment parent s_before x) /\
    (forall b,
      RestStack parent s b ->
      RestStack parent s_before b) /\
    (forall y,
      Visited y s_before ->
      Visited y s) /\
    (forall b,
      RestStack parent s b ->
      dfn s b = dfn s_before b).

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

  Definition ParentRecursivePre
             (parent child: V) (done: V -> Prop) (s: St): Prop :=
    LoopInv parent done s /\
    Edge parent child /\
    EntryPre child s /\
    fa s child = parent /\
    fa s child <> child.

  Definition ParentFrameForChild
             (parent child: V) (done: V -> Prop)
             (s_before s: St): Prop :=
    ParentLowFrame parent done s_before s /\
    LoopCoreShape parent (done_after done child) s /\
    LoopAuxFacts parent s /\
    Closed s /\
    TreeEdgesAreGraphEdges s /\
    Edge parent child /\
    Visited child s /\
    fa s child = parent /\
    fa s child <> child /\
    dfn s parent < dfn s child /\
    ~ done child /\
    ParentOldCandidatesBelowChild parent child done s_before s /\
    ParentTraversalStackFrame parent child s_before s.

  Definition ChildReturnPreMaybePop
             (parent child: V) (done: V -> Prop)
             (s_before s: St): Prop :=
    RootPreMaybePop child s /\
    ParentFrameForChild parent child done s_before s.

  Definition NestedFrameDisjoint
             (ancestor current loop_root: V)
             (ancestor_done: V -> Prop) (s: St): Prop :=
    dg_reachable (state_to_dfs_tree g s root) current loop_root /\
    forall old_child,
      ancestor_done old_child ->
      fa s old_child = ancestor ->
      fa s old_child <> old_child ->
      ~ dg_reachable (state_to_dfs_tree g s root) old_child loop_root.

  Definition NestedFramePre
             (ancestor current loop_root next: V)
             (ancestor_done loop_done: V -> Prop)
             (s_before s: St): Prop :=
    LoopInv loop_root loop_done s /\
    ParentFrameForChild ancestor current ancestor_done s_before s /\
    NestedFrameDisjoint ancestor current loop_root ancestor_done s /\
    Edge loop_root next /\
    ~ loop_done next /\
    EntryPre next s /\
    fa s next = loop_root /\
    fa s next <> next.

  Definition VisitMainContract (W: RecProgram): Prop :=
    forall u: V,
      Hoare
        (EntryPre u)
        (W u)
        (fun _ s => RootFinal u s).

  Definition VisitChildContract (W: RecProgram): Prop :=
    forall (parent child: V) (done: V -> Prop),
      Hoare
        (ParentRecursivePre parent child done)
        (W child)
        (fun _ s =>
           exists s_before,
             LoopInv parent done s_before /\
             Edge parent child /\
             ChildContributionContract parent child done s_before s).

  Definition VisitChildTraversalContract (W: RecProgram): Prop :=
    forall (parent child: V) (done: V -> Prop),
      Hoare
        (fun s: St =>
           ParentRecursivePre parent child done s /\
           LoopTraversalComplete parent done s)
        (W child)
        (fun _ s =>
           exists s_before,
             LoopInv parent done s_before /\
             Edge parent child /\
             ChildContributionContract parent child done s_before s /\
             LoopTraversalComplete parent (done_after done child) s).

  Definition VisitFrameContract (W: RecProgram): Prop :=
    forall (ancestor current loop_root next: V)
           (ancestor_done loop_done: V -> Prop)
           (s_before: St),
      Hoare
        (NestedFramePre ancestor current loop_root next
           ancestor_done loop_done s_before)
        (W next)
        (fun _ s =>
           ParentFrameForChild ancestor current ancestor_done s_before s /\
           NestedFrameDisjoint ancestor current loop_root ancestor_done s).

  Definition VisitContract (W: RecProgram): Prop :=
    VisitMainContract W /\
    VisitChildContract W /\
    VisitChildTraversalContract W /\
    VisitFrameContract W.

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

  Lemma partial_low_candidate_active
        (u b: V) (done: V -> Prop) (s: St):
    Active u s ->
    PartialLowCandidate u done s b ->
    Active b s.
  Proof.
    intros Hu_active Hcandidate.
    unfold PartialLowCandidate in Hcandidate.
    destruct Hcandidate as [Hb_eq_u | Htarget].
    - subst b. exact Hu_active.
    - unfold PartialActiveTarget in Htarget.
      destruct Htarget as [Hdirect | Hsubtree].
      + destruct Hdirect as
          [a [_ [Hb_eq_a [_ [Ha_active _]]]]].
        subst b. exact Ha_active.
      + destruct Hsubtree as
          [child [x [_ [_ [_ [_ [_ [_ [Hb_active _]]]]]]]]].
        exact Hb_active.
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

  Lemma loop_no_unvisited_step_done_equiv
        (u: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    LoopNoUnvisitedStep u done1 s ->
    LoopNoUnvisitedStep u done2 s.
  Proof.
    intros Hdone Hno x y Hpopped Hedge Hnotvis.
    pose proof Hdone as Hdone_pointwise.
    sets_unfold in Hdone_pointwise.
    destruct (Hno x y Hpopped Hedge Hnotvis) as [Hx Hnot_done1].
    split; [exact Hx |].
    intros Hdone2.
    apply Hnot_done1.
    apply Hdone_pointwise.
    exact Hdone2.
  Qed.

  Lemma loop_rest_target_cut_done_equiv
        (u: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    LoopRestTargetCut u done1 s ->
    LoopRestTargetCut u done2 s.
  Proof.
    intros Hdone Hcut x b Hpopped Hedge Hrest.
    pose proof Hdone as Hdone_pointwise.
    sets_unfold in Hdone_pointwise.
    destruct (Hcut x b Hpopped Hedge Hrest) as
      [[Hx Hnot_done1] | [target [Hcandidate Hdfn]]].
    - left. split; [exact Hx |].
      intros Hdone2.
      apply Hnot_done1.
      apply Hdone_pointwise.
      exact Hdone2.
    - right. exists target. split; [| exact Hdfn].
      eapply partial_low_candidate_done_equiv; eauto.
  Qed.

  Lemma loop_traversal_complete_done_equiv
        (u: V) (done1 done2: V -> Prop) (s: St):
    done1 == done2 ->
    LoopTraversalComplete u done1 s ->
    LoopTraversalComplete u done2 s.
  Proof.
    intros Hdone [Hno Hcut].
    split.
    - eapply loop_no_unvisited_step_done_equiv; eauto.
    - eapply loop_rest_target_cut_done_equiv; eauto.
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

  Lemma preloop_preserves_any_fa (u x p: V):
    Hoare (fun s: St => fa s x = p)
          (preloop u)
          (fun _ s => fa s x = p).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl. reflexivity.
  Qed.

  Lemma tree_reachable_dfn_monotone (s: St) (x y: V):
    wf_scc_state g root s ->
    dg_reachable (state_to_dfs_tree g s root) x y ->
    dfn s x <= dfn s y.
  Proof.
    intros [_ [_ [Hdfn_valid _]]] Hreach.
    unfold dg_reachable in Hreach.
    induction Hreach as [a b Hstep | a | a b c _ IH_ab _ IH_bc].
    - specialize (Hdfn_valid a b Hstep). lia.
    - lia.
    - lia.
  Qed.

  Lemma preloop_tree_edge_post_cases
        (parent child x y: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    tree_edge s_after x y ->
    tree_edge s_before x y \/ (x = parent /\ y = child).
  Proof.
    intros Hpre Hexec Htree_post.
    pose proof Htree_post as Htree_arg.
    clear Htree_post.
    assert (Hhoare:
              Hoare
                (fun s: St =>
                   s = s_before /\
                   ParentRecursivePre parent child done s_before)
                (preloop child)
                (fun _ s =>
                   forall x y,
                     tree_edge s x y ->
                     tree_edge s_before x y \/
                     (x = parent /\ y = child))).
    { unfold preloop. unfold_op. intro_state. hoare_auto_s.
      subst s. simpl.
      destruct H as [Hs0 Hpre0]. subst s0.
      destruct Hpre0 as [_ [Hedge [Hentry [Hfa _]]]].
      destruct Hentry as [[_ Hchild_notvis] _].
      match goal with
      | Hstep : tree_edge _ _ _ |- _ =>
          unfold tree_edge, dg_step in Hstep |- *;
          destruct Hstep as [e [Htree_step [Hfst Hsnd]]]
      end.
      unfold state_to_dfs_tree in Htree_step. simpl in Htree_step.
      destruct Htree_step as
        [z [Hzvis [Hzfane [Hfst_fa Hsnd_z]]]].
      sets_unfold in Hzvis.
      destruct Hzvis as [Hzvis_old | Hz_eq_child].
      - left.
        exists e. split; [| split; [exact Hfst | exact Hsnd]].
        unfold state_to_dfs_tree. simpl.
        exists z. split; [exact Hzvis_old | split].
        + unfold equiv_decb in Hzfane.
          destruct (equiv_dec z child) as [Hz_eq_child | _].
          * exfalso. apply Hchild_notvis.
            rewrite <- Hz_eq_child. exact Hzvis_old.
          * exact Hzfane.
        + split.
          * unfold equiv_decb in Hfst_fa.
            destruct (equiv_dec z child) as [Hz_eq_child | _].
            -- exfalso. apply Hchild_notvis.
               rewrite <- Hz_eq_child. exact Hzvis_old.
            -- exact Hfst_fa.
          * exact Hsnd_z.
      - subst z. right.
        match goal with
        | |- ?src = parent /\ ?dst = child =>
            assert (Hx: src = fa s_before child);
            [ rewrite <- Hfst; exact Hfst_fa |];
            assert (Hy: dst = child);
            [ rewrite <- Hsnd; exact Hsnd_z |];
            rewrite Hx, Hy, Hfa; auto
        end. }
    exact (Hhoare s_before retv s_after (conj eq_refl Hpre)
                  Hexec x y Htree_arg).
  Qed.

  Lemma preloop_child_no_tree_out
        (parent child target: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    ~ tree_edge s_after child target.
  Proof.
    intros Hpre Hexec Htree.
    destruct Hpre as [Hloop [_ [Hentry _]]].
    destruct Hentry as [[_ Hchild_notvis] _].
    destruct Hloop as [_ [Hshape _]].
    destruct Hshape as [Hwf _].
    destruct Hwf as [_ [_ [_ Hfa_visited]]].
    unfold tree_edge, dg_step in Htree.
    destruct Htree as [e [Htree_step [Hfst _]]].
    unfold state_to_dfs_tree in Htree_step, Hfst. simpl in Htree_step, Hfst.
    destruct Htree_step as [z [_ [Hzfane [Hfst_fa _]]]].
    assert (Hfa_pres: fa s_after z = fa s_before z).
    { pose proof (preloop_preserves_any_fa
                    child z (fa s_before z)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after eq_refl Hexec). }
    assert (Hchild_eq_fa_before: child = fa s_before z).
    { rewrite <- Hfst. rewrite <- Hfa_pres. exact Hfst_fa. }
    assert (Hzfane_before: fa s_before z <> z).
    { intro Hz_eq. apply Hzfane. rewrite Hfa_pres. exact Hz_eq. }
    assert (Hchild_vis: Visited child s_before).
    { rewrite Hchild_eq_fa_before.
      apply Hfa_visited. exact Hzfane_before. }
    exact (Hchild_notvis Hchild_vis).
  Qed.

  Lemma preloop_reachable_backward_not_child
        (parent child start target: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    target <> child ->
    dg_reachable (state_to_dfs_tree g s_after root) start target ->
    dg_reachable (state_to_dfs_tree g s_before root) start target.
  Proof.
    intros Hpre Hexec Htarget_ne Hreach.
    eapply dg_reachable_reverse_lift.
    - intros u v Hstep Hv_ne_child.
      destruct (preloop_tree_edge_post_cases
                  parent child u v done s_before s_after retv
                  Hpre Hexec Hstep)
        as [Hstep_old | [_ Hv_eq_child]].
      + exact Hstep_old.
      + exfalso. apply Hv_ne_child. exact Hv_eq_child.
    - intros v Hstep.
      eapply preloop_child_no_tree_out; eauto.
    - exact Hreach.
    - exact Htarget_ne.
  Qed.

  Lemma preloop_preserves_active
        (u w: V) (s_before s_after: St) (retv: unit):
    (s_before, retv, s_after) ∈ preloop u ->
    Active w s_before ->
    Active w s_after.
  Proof.
    intros Hexec Hactive.
    unfold Active in *.
    pose proof (preloop_keep_in_stack u w) as Hhoare.
    unfold Hoare in Hhoare.
    exact (Hhoare s_before retv s_after Hactive Hexec).
  Qed.

  Lemma preloop_active_post_cases
        (u w: V) (s_before s_after: St) (retv: unit):
    (s_before, retv, s_after) ∈ preloop u ->
    Active w s_after ->
    Active w s_before \/ w = u.
  Proof.
    intros Hexec Hactive_post.
    pose proof Hactive_post as Hactive_arg.
    clear Hactive_post.
    assert (Hhoare:
              Hoare
                (fun s: St => s = s_before)
                (preloop u)
                (fun _ s =>
                   Active w s -> Active w s_before \/ w = u)).
    { unfold preloop. unfold_op. intro_state. hoare_auto_s.
      subst s. unfold Active in *. simpl in *.
      match goal with
      | Hactive : u = w \/ In w (stack s_before) |- _ =>
          destruct Hactive as [Hw_eq_u | Hactive_old]
      end.
      - right. symmetry. exact Hw_eq_u.
      - left. exact Hactive_old. }
    exact (Hhoare s_before retv s_after eq_refl Hexec Hactive_arg).
  Qed.

  Lemma preloop_old_stack_element_rest
        (u w: V):
    Hoare
      (fun s: St => Active w s)
      (preloop u)
      (fun _ s => RestStack u s w).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. unfold Active, RestStack in *. simpl.
    unfold equiv_decb.
    destruct (equiv_dec u u) as [_ | Hu_neq].
    - exact H.
    - exfalso. apply Hu_neq. reflexivity.
  Qed.

  Lemma stack_split_at_rest_root_in
        (stk: list V) (u x: V) (popped rest: list V):
    stack_split_at stk u = (popped, rest) ->
    In x rest ->
    In u stk.
  Proof.
    revert u x popped rest.
    induction stk as [| a stk IH]; intros u x popped rest Hsplit Hrest.
    - simpl in Hsplit. inversion Hsplit. subst rest. exact Hrest.
    - simpl in Hsplit.
      destruct (equiv_decb a u) eqn:Ha_u.
      + inversion Hsplit. subst popped rest. simpl.
        left.
        unfold equiv_decb in Ha_u.
        destruct (equiv_dec a u) as [Ha_eq_u | Ha_ne_u].
        * exact Ha_eq_u.
        * inversion Ha_u.
      + destruct (stack_split_at stk u) as [popped' rest'] eqn:Hinner.
        inversion Hsplit. subst popped rest. simpl.
        right. eapply IH; eauto.
  Qed.

  Lemma stack_split_at_rest_in_original_early
        (stk: list V) (u x: V) (popped rest: list V):
    stack_split_at stk u = (popped, rest) ->
    In x rest ->
    In x stk.
  Proof.
    revert u x popped rest.
    induction stk as [| a stk IH]; intros u x popped rest Hsplit Hrest.
    - simpl in Hsplit. inversion Hsplit. subst rest. exact Hrest.
    - simpl in Hsplit.
      destruct (equiv_decb a u) eqn:Ha_u.
      + inversion Hsplit. subst popped rest. simpl.
        right. exact Hrest.
      + destruct (stack_split_at stk u) as [popped' rest'] eqn:Hinner.
        inversion Hsplit. subst popped rest. simpl.
        right. eapply IH; eauto.
  Qed.

  Lemma rest_stack_root_active
        (u x: V) (s: St):
    RestStack u s x ->
    Active u s.
  Proof.
    unfold RestStack, Active.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    intros Hrest.
    eapply stack_split_at_rest_root_in; eauto.
  Qed.

  Lemma preloop_preserves_rest_stack
        (u center w: V):
    u <> center ->
    Hoare
      (fun s: St => RestStack center s w)
      (preloop u)
      (fun _ s => RestStack center s w).
  Proof.
    intros Hu_ne_root.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. unfold RestStack in *. simpl.
    unfold equiv_decb.
    destruct (equiv_dec u center) as [Hu_eq_center | _].
    - exfalso. apply Hu_ne_root. exact Hu_eq_center.
    - destruct (stack_split_at (stack s0) center) as [popped rest].
      exact H.
  Qed.

  Lemma preloop_rest_stack_post_pre
        (u center w: V) (s_before s_after: St) (retv: unit):
    u <> center ->
    (s_before, retv, s_after) ∈ preloop u ->
    RestStack center s_after w ->
    RestStack center s_before w.
  Proof.
    intros Hu_ne_center Hexec Hrest.
    assert (Hhoare:
              Hoare
                (fun s: St => s = s_before /\ u <> center)
                (preloop u)
                (fun _ s =>
                   RestStack center s w -> RestStack center s_before w)).
    { unfold preloop. unfold_op. intro_state. hoare_auto_s.
      all: subst s; destruct H as [Hs0 Hu_ne_center0]; subst s0;
        unfold RestStack in *; simpl in *; unfold equiv_decb in *;
        destruct (equiv_dec u center) as [Hu_eq_center | _];
        [ exfalso; exact (Hu_ne_center0 Hu_eq_center)
        | destruct (stack_split_at (stack s_before) center)
            as [popped rest]; assumption ]. }
    exact (Hhoare s_before retv s_after
                  (conj eq_refl Hu_ne_center) Hexec Hrest).
  Qed.

  Lemma preloop_popped_segment_pre_lift
        (u center x: V) (s_before s_after: St) (retv: unit):
    u <> center ->
    (s_before, retv, s_after) ∈ preloop u ->
    PoppedSegment center s_before x ->
    PoppedSegment center s_after x.
  Proof.
    intros Hu_ne_center Hexec Hpopped.
    assert (Hhoare:
              Hoare
                (fun s: St =>
                   s = s_before /\ u <> center /\
                   PoppedSegment center s_before x)
                (preloop u)
                (fun _ s => PoppedSegment center s x)).
    { unfold preloop. unfold_op. intro_state. hoare_auto_s.
      subst s. destruct H as [Hs0 [Hu_ne_center0 Hpopped0]].
      subst s0.
      unfold PoppedSegment in Hpopped0 |- *.
      simpl. unfold equiv_decb.
      destruct (equiv_dec u center) as [Hu_eq_center | _].
      - exfalso. exact (Hu_ne_center0 Hu_eq_center).
      - destruct (stack_split_at (stack s_before) center)
          as [popped rest].
        simpl. right. exact Hpopped0. }
    exact (Hhoare s_before retv s_after
                  (conj eq_refl (conj Hu_ne_center Hpopped)) Hexec).
  Qed.

  Lemma preloop_popped_segment_post_cases
        (u center x: V) (s_before s_after: St) (retv: unit):
    u <> center ->
    (s_before, retv, s_after) ∈ preloop u ->
    PoppedSegment center s_after x ->
    x = u \/ PoppedSegment center s_before x.
  Proof.
    intros Hu_ne_center Hexec Hpopped.
    assert (Hhoare:
              Hoare
                (fun s: St => s = s_before /\ u <> center)
                (preloop u)
                (fun _ s =>
                   PoppedSegment center s x ->
                   x = u \/ PoppedSegment center s_before x)).
    { unfold preloop. unfold_op. intro_state. hoare_auto_s.
      subst s. destruct H as [Hs0 Hu_ne_center0]. subst s0.
      unfold PoppedSegment in *. simpl in *. unfold equiv_decb in *.
      destruct (equiv_dec u center) as [Hu_eq_center | _].
      - exfalso. exact (Hu_ne_center0 Hu_eq_center).
      - destruct (stack_split_at (stack s_before) center)
          as [popped rest].
        simpl in *.
        match goal with
        | Hpop : u = x \/ _ |- _ =>
            destruct Hpop as [Hu_eq_x | Hpopped_old];
            [left; symmetry; exact Hu_eq_x | right; exact Hpopped_old]
        end. }
    exact (Hhoare s_before retv s_after
                  (conj eq_refl Hu_ne_center) Hexec Hpopped).
  Qed.

  Lemma preloop_new_in_popped_segment
        (u center: V) (s_before s_after: St) (retv: unit):
    u <> center ->
    (s_before, retv, s_after) ∈ preloop u ->
    PoppedSegment center s_after u.
  Proof.
    intros Hu_ne_center Hexec.
    assert (Hhoare:
              Hoare
                (fun s: St => s = s_before /\ u <> center)
                (preloop u)
                (fun _ s => PoppedSegment center s u)).
    { unfold preloop. unfold_op. intro_state. hoare_auto_s.
      subst s. destruct H as [Hs0 Hu_ne_center0]. subst s0.
      unfold PoppedSegment. simpl. unfold equiv_decb.
      destruct (equiv_dec u center) as [Hu_eq_center | _].
      - exfalso. exact (Hu_ne_center0 Hu_eq_center).
      - destruct (stack_split_at (stack s_before) center)
          as [popped rest].
        simpl. left. reflexivity. }
    exact (Hhoare s_before retv s_after
                  (conj eq_refl Hu_ne_center) Hexec).
  Qed.

  Lemma preloop_parent_old_candidates_below_child
        (parent child: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    ParentOldCandidatesBelowChild parent child done s_before s_after.
  Proof.
    intros Hpre Hexec b Hcandidate.
    destruct Hpre as [Hloop _].
    destruct Hloop as [Haux _].
    destruct Haux as [_ [Hparent_active _]].
    assert (Hb_active: Active b s_before).
    { eapply partial_low_candidate_active; eauto. }
    pose proof (preloop_old_stack_element_rest child b) as Hhoare.
    unfold Hoare in Hhoare.
    exact (Hhoare s_before retv s_after Hb_active Hexec).
  Qed.

  Lemma preloop_parent_traversal_stack_frame
        (par child: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre par child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    ParentTraversalStackFrame par child s_before s_after.
  Proof.
    intros Hpre Hexec.
    destruct Hpre as [_ [_ [Hentry [Hfa_child Hfane_child]]]].
    destruct Hentry as [[Hwf_pre Hchild_notvis] _].
    destruct Hwf_pre as [Hstack_vis _].
    assert (Hchild_ne_parent: child <> par).
    { intros Hchild_eq_parent. apply Hfane_child.
      rewrite Hfa_child. symmetry. exact Hchild_eq_parent. }
    assert (Hhoare:
              Hoare
                (fun s: St =>
                   s = s_before /\ child <> par /\
                   ~ Visited child s_before /\
                   stack_in_visited s_before)
                (preloop child)
                (fun _ s =>
                   ParentTraversalStackFrame par child s_before s)).
    { unfold preloop. unfold_op. intro_state. hoare_auto_s.
      subst s.
      destruct H as
        [Hs0 [Hchild_ne_parent0 [Hchild_notvis0 Hstack_vis0]]].
      subst s0.
      unfold ParentTraversalStackFrame.
      split.
      - intros x Hpopped.
        unfold PoppedSegment in Hpopped |- *.
        simpl in Hpopped |- *.
        unfold equiv_decb in Hpopped |- *.
        destruct (equiv_dec child (fa s_before child))
          as [Hchild_eq_parent | _].
        + exfalso. exact (Hchild_ne_parent0 Hchild_eq_parent).
        + destruct (stack_split_at (stack s_before) (fa s_before child))
            as [popped rest] eqn:Hsplit.
          simpl in Hpopped.
          destruct Hpopped as [Hx_child | Hx_old].
          * left.
            destruct (equiv_dec child child) as [_ | Hneq].
            -- simpl. left. exact Hx_child.
            -- exfalso. apply Hneq. reflexivity.
          * right. exact Hx_old.
      - split.
        + intros z Hrest.
          unfold RestStack in Hrest |- *.
          simpl in Hrest.
          unfold equiv_decb in Hrest.
          destruct (equiv_dec child (fa s_before child))
            as [Hchild_eq_parent | _].
          * exfalso. exact (Hchild_ne_parent0 Hchild_eq_parent).
          * destruct (stack_split_at (stack s_before) (fa s_before child))
              as [popped rest] eqn:Hsplit.
            exact Hrest.
        + split.
          * intros y Hvis.
          unfold Visited in *. simpl.
          sets_unfold. left. exact Hvis.
          * intros z Hrest.
          assert (Hz_rest_before: RestStack (fa s_before child) s_before z).
          { unfold RestStack in Hrest |- *.
            simpl in Hrest.
            unfold equiv_decb in Hrest.
            destruct (equiv_dec child (fa s_before child))
              as [Hchild_eq_parent | _].
            - exfalso. exact (Hchild_ne_parent0 Hchild_eq_parent).
            - destruct (stack_split_at (stack s_before) (fa s_before child))
                as [popped rest] eqn:Hsplit.
              exact Hrest. }
          assert (Hz_vis_before: Visited z s_before).
          { apply Hstack_vis0.
            unfold Active, RestStack in *.
            destruct (stack_split_at (stack s_before) (fa s_before child))
              as [popped rest] eqn:Hsplit.
            eapply stack_split_at_rest_in_original_early; eauto. }
          assert (Hz_ne_child: z <> child).
          { intros Hz_eq_child. subst z.
            exact (Hchild_notvis0 Hz_vis_before). }
          simpl. unfold equiv_decb.
          destruct (equiv_dec z child) as [Hz_eq_child | _];
            [exfalso; exact (Hz_ne_child Hz_eq_child) | reflexivity]. }
    exact (Hhoare s_before retv s_after
                  (conj eq_refl
                    (conj Hchild_ne_parent
                      (conj Hchild_notvis Hstack_vis))) Hexec).
  Qed.

  Lemma preloop_preserves_parent_traversal_stack_frame_nested
        (ancestor current next: V)
        (s_before s_mid s_after: St) (retv: unit):
    next <> ancestor ->
    next <> current ->
    ~ Visited next s_mid ->
    stack_in_visited s_mid ->
    (s_mid, retv, s_after) ∈ preloop next ->
    ParentTraversalStackFrame ancestor current s_before s_mid ->
    ParentTraversalStackFrame ancestor current s_before s_after.
  Proof.
    intros Hnext_ne_ancestor Hnext_ne_current Hnext_notvis
           Hstack_vis Hexec Hframe.
    destruct Hframe as [Hpopped_frame [Hrest_frame [Hvis_frame Hdfn_frame]]].
    split.
    - intros x Hpopped_after.
      destruct (preloop_popped_segment_post_cases
                  next ancestor x s_mid s_after retv
                  Hnext_ne_ancestor Hexec Hpopped_after)
        as [Hx_next | Hpopped_mid].
      + subst x. left.
        eapply preloop_new_in_popped_segment; eauto.
      + destruct (Hpopped_frame x Hpopped_mid)
          as [Hpopped_current_mid | Hpopped_old].
        * left.
          eapply preloop_popped_segment_pre_lift; eauto.
        * right. exact Hpopped_old.
    - split.
      + intros b Hrest_after.
        apply Hrest_frame.
        eapply preloop_rest_stack_post_pre; eauto.
      + split.
        * intros y Hvis_before.
          pose proof (Hvis_frame y Hvis_before) as Hvis_mid.
          pose proof (preloop_keep_visited next y) as Hhoare.
          unfold Hoare in Hhoare.
          exact (Hhoare s_mid retv s_after Hvis_mid Hexec).
        * intros b Hrest_after.
          assert (Hrest_mid: RestStack ancestor s_mid b).
          { eapply preloop_rest_stack_post_pre; eauto. }
          assert (Hb_vis_mid: Visited b s_mid).
          { apply Hstack_vis.
            unfold Active, RestStack in *.
            destruct (stack_split_at (stack s_mid) ancestor)
              as [popped rest] eqn:Hsplit.
            eapply stack_split_at_rest_in_original_early; eauto. }
          assert (Hb_ne_next: next <> b).
          { intros Hnext_eq_b. subst b.
            exact (Hnext_notvis Hb_vis_mid). }
          pose proof (preloop_keep_dfn next b (dfn s_mid b)) as Hhoare.
          unfold Hoare in Hhoare.
          destruct (Hhoare s_mid retv s_after
                            (conj Hb_ne_next
                              (conj Hb_vis_mid eq_refl)) Hexec)
            as [_ [_ Hdfn_after]].
          rewrite Hdfn_after.
          exact (Hdfn_frame b Hrest_mid).
  Qed.

  Lemma preloop_visited_post_cases
        (u w: V) (s_before s_after: St) (retv: unit):
    (s_before, retv, s_after) ∈ preloop u ->
    Visited w s_after ->
    Visited w s_before \/ w = u.
  Proof.
    intros Hexec Hvis_post.
    assert (Hhoare:
              Hoare
                (fun s: St => s = s_before)
                (preloop u)
                (fun _ s =>
                   Visited w s -> Visited w s_before \/ w = u)).
    { unfold preloop. unfold_op. intro_state. hoare_auto_s.
      subst s. unfold Visited in *. simpl in *.
      match goal with
      | Hvis : w ∈ visited s_before ∪ [u] |- _ =>
          sets_unfold in Hvis;
          destruct Hvis as [Hvis_old | Hw_new]
      end.
      - left. exact Hvis_old.
      - right. symmetry. exact Hw_new. }
    exact (Hhoare s_before retv s_after eq_refl Hexec Hvis_post).
  Qed.

  Lemma preloop_preserves_dfn_of_visited
        (u w: V) (s_before s_after: St) (retv: unit):
    (s_before, retv, s_after) ∈ preloop u ->
    u <> w ->
    Visited w s_before ->
    dfn s_after w = dfn s_before w.
  Proof.
    intros Hexec Hneq Hvis.
    pose proof (preloop_keep_dfn u w (dfn s_before w)) as Hhoare.
    unfold Hoare in Hhoare.
    destruct (Hhoare s_before retv s_after
                      (conj Hneq (conj Hvis eq_refl)) Hexec)
      as [_ [_ Hdfn]].
    exact Hdfn.
  Qed.

  Lemma preloop_tree_edge_pre_lift
        (u x y: V) (s_before s_after: St) (retv: unit):
    (s_before, retv, s_after) ∈ preloop u ->
    tree_edge s_before x y ->
    tree_edge s_after x y.
  Proof.
    intros Hexec Htree.
    unfold tree_edge, dg_step in Htree |- *.
    destruct Htree as [e [Htree_step [Hfst Hsnd]]].
    unfold state_to_dfs_tree in Htree_step, Hfst, Hsnd |- *.
    simpl in Htree_step, Hfst, Hsnd |- *.
    destruct Htree_step as [z [Hzvis [Hzfane [Hfst_fa Hsnd_z]]]].
    assert (Hzvis_after: Visited z s_after).
    { pose proof (preloop_keep_visited u z) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after Hzvis Hexec). }
    assert (Hfa_pres: fa s_after z = fa s_before z).
    { pose proof (preloop_preserves_any_fa
                    u z (fa s_before z)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after eq_refl Hexec). }
    exists e. split; [| split; [exact Hfst | exact Hsnd]].
    exists z. split; [exact Hzvis_after | split].
    - intros Hfa_eq_z. apply Hzfane.
      rewrite <- Hfa_pres. exact Hfa_eq_z.
    - split.
      + rewrite Hfa_pres. exact Hfst_fa.
      + exact Hsnd_z.
  Qed.

  Lemma preloop_tree_reachable_pre_lift
        (u x y: V) (s_before s_after: St) (retv: unit):
    (s_before, retv, s_after) ∈ preloop u ->
    dg_reachable (state_to_dfs_tree g s_before root) x y ->
    dg_reachable (state_to_dfs_tree g s_after root) x y.
  Proof.
    intros Hexec Hreach.
    eapply dg_reachable_lift.
    - intros a b Hstep.
      eapply preloop_tree_edge_pre_lift; eauto.
    - exact Hreach.
  Qed.

  Lemma preloop_old_processed_child_not_reach_child
        (parent child old_child: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    done old_child ->
    fa s_after old_child = parent ->
    fa s_after old_child <> old_child ->
    ~ dg_reachable (state_to_dfs_tree g s_after root) old_child child.
  Proof.
    intros Hpre Hexec Hdone_old Hfa_old_after Hfane_old_after Hreach.
    pose proof Hpre as Hpre_all.
    destruct Hpre as
      [Hloop [_ [Hentry [Hfa_child Hfane_child]]]].
    destruct Hentry as [[_ Hchild_notvis] _].
    destruct Hloop as [_ [Hshape _]].
    destruct Hshape as
      [Hwf [Htree_sound [Hparent_vis [Hdone_edge [Hdone_vis _]]]]].
    assert (Hold_vis: Visited old_child s_before).
    { apply Hdone_vis. exact Hdone_old. }
    assert (Hold_ne_child: old_child <> child).
    { intros Hold_eq_child. apply Hchild_notvis.
      rewrite <- Hold_eq_child. exact Hold_vis. }
    destruct (dg_reachable_vertex_path
                (state_to_dfs_tree g s_after root)
                old_child child Hreach)
      as [path Hpath].
    assert (Hchild_not_ne: ~ (child = child -> False)).
    { intros Hneq. apply Hneq. reflexivity. }
    destruct (dg_vertex_path_last_exit_from_pred
                (state_to_dfs_tree g s_after root)
                (fun z => z = child -> False)
                old_child child path
                Hold_ne_child Hchild_not_ne Hpath)
      as [a [b [suffix
        [Ha_ne_child [Hb_not_ne_child
          [Hstep_ab [Hreach_old_a_post [_ _]]]]]]]].
    assert (Hb_eq_child: b = child).
    { apply NNPP. exact Hb_not_ne_child. }
    subst b.
    destruct (preloop_tree_edge_post_cases
                parent child a child done s_before s_after retv
                Hpre_all Hexec Hstep_ab)
      as [Hstep_old | [Ha_eq_parent _]].
    - apply tree_step_char in Hstep_old as [_ [_ Hchild_vis_pre]].
      exact (Hchild_notvis Hchild_vis_pre).
    - subst a.
      assert (Hparent_ne_child: parent <> child).
      { intros Hparent_eq_child. apply Hfane_child.
        rewrite Hfa_child. exact Hparent_eq_child. }
      assert (Hreach_old_parent_pre:
                dg_reachable (state_to_dfs_tree g s_before root)
                             old_child parent).
      { eapply preloop_reachable_backward_not_child; eauto. }
      assert (Hfa_old_pres:
                fa s_after old_child = fa s_before old_child).
      { pose proof (preloop_preserves_any_fa
                      child old_child (fa s_before old_child)) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s_before retv s_after eq_refl Hexec). }
      assert (Hfa_old_before: fa s_before old_child = parent).
      { rewrite <- Hfa_old_pres. exact Hfa_old_after. }
      assert (Hfane_old_before: fa s_before old_child <> old_child).
      { intros Hfa_eq_old.
        apply Hfane_old_after.
        rewrite Hfa_old_pres. exact Hfa_eq_old. }
      assert (Hparent_lt_old:
                dfn s_before parent < dfn s_before old_child).
      { destruct Hwf as [_ [_ [Hdfn_valid _]]].
        eapply fa_parent_dfn_lt.
        - exact Hfa_old_before.
        - exact Hfane_old_before.
        - apply Hdone_edge. exact Hdone_old.
        - apply Hdone_vis. exact Hdone_old.
        - exact Hdfn_valid. }
      pose proof (tree_reachable_dfn_monotone
                    s_before old_child parent Hwf Hreach_old_parent_pre)
        as Hold_le_parent.
      lia.
  Qed.

  Lemma preloop_old_processed_child_reach_backward
        (parent child old_child x: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    done old_child ->
    fa s_after old_child = parent ->
    fa s_after old_child <> old_child ->
    dg_reachable (state_to_dfs_tree g s_after root) old_child x ->
    dg_reachable (state_to_dfs_tree g s_before root) old_child x.
  Proof.
    intros Hpre Hexec Hdone_old Hfa_old_after Hfane_old_after Hreach.
    destruct (classic (x = child)) as [Hx_eq_child | Hx_ne_child].
    - subst x. exfalso.
      eapply preloop_old_processed_child_not_reach_child; eauto.
    - eapply preloop_reachable_backward_not_child; eauto.
  Qed.

  Lemma preloop_parent_old_candidate_forward
        (parent child b: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    PartialLowCandidate parent done s_before b ->
    PartialLowCandidate parent done s_after b /\
    dfn s_after b = dfn s_before b.
  Proof.
    intros Hpre Hexec Hcandidate.
    pose proof Hpre as Hpre_all.
    destruct Hpre as
      [Hloop [_ [Hentry [Hfa_child Hfane_child]]]].
    destruct Hentry as [[_ Hchild_notvis] _].
    destruct Hloop as [_ [Hshape _]].
    destruct Hshape as
      [Hwf [_ [Hparent_vis [Hdone_edge [Hdone_vis _]]]]].
    destruct Hwf as [Hstack_vis [Hdfn_inv [Hdfn_valid Hfa_visited]]].
    assert (Hchild_ne_parent: child <> parent).
    { intros Hchild_eq_parent. apply Hfane_child.
      rewrite Hfa_child. symmetry. exact Hchild_eq_parent. }
    unfold PartialLowCandidate in Hcandidate |- *.
    destruct Hcandidate as [Hb_parent | Htarget].
    - subst b. split.
      + left. reflexivity.
      + eapply preloop_preserves_dfn_of_visited; eauto.
    - unfold PartialActiveTarget in Htarget |- *.
      destruct Htarget as [Hdirect | Hsubtree].
      + destruct Hdirect as
          [a [Hdone_a [Hb_eq_a [Hedge_pa [Hactive_a Hnot_tree]]]]].
        subst b.
        assert (Ha_vis: Visited a s_before).
        { apply Hdone_vis. exact Hdone_a. }
        assert (Hchild_ne_a: child <> a).
        { intros Hchild_eq_a. apply Hchild_notvis.
          rewrite Hchild_eq_a. exact Ha_vis. }
        split.
        * right. left. exists a.
          repeat split; auto.
          -- eapply preloop_preserves_active; eauto.
          -- intros Htree_post.
             destruct (preloop_tree_edge_post_cases
                         parent child parent a done
                         s_before s_after retv
                         Hpre_all
                         Hexec Htree_post)
               as [Htree_old | [_ Ha_eq_child]].
             ++ exact (Hnot_tree Htree_old).
             ++ subst a. exact (Hchild_notvis Ha_vis).
        * eapply preloop_preserves_dfn_of_visited; eauto.
      + destruct Hsubtree as
          [old_child [x
            [Hdone_old [Hedge_old [Hfa_old [Hfane_old
              [Hreach_old_x [Hedge_x_b [Hactive_b Hnot_tree]]]]]]]]].
        assert (Hold_vis: Visited old_child s_before).
        { apply Hdone_vis. exact Hdone_old. }
        assert (Hchild_ne_old: child <> old_child).
        { intros Hchild_eq_old. apply Hchild_notvis.
          rewrite Hchild_eq_old. exact Hold_vis. }
        assert (Hb_vis: Visited b s_before).
        { apply Hstack_vis. exact Hactive_b. }
        assert (Hchild_ne_b: child <> b).
        { intros Hchild_eq_b. apply Hchild_notvis.
          rewrite Hchild_eq_b. exact Hb_vis. }
        assert (Hfa_old_pres:
                  fa s_after old_child = fa s_before old_child).
        { pose proof (preloop_preserves_any_fa
                        child old_child (fa s_before old_child))
            as Hhoare.
          unfold Hoare in Hhoare.
          exact (Hhoare s_before retv s_after eq_refl Hexec). }
        assert (Hfa_old_after: fa s_after old_child = parent).
        { rewrite Hfa_old_pres. exact Hfa_old. }
        assert (Hfane_old_after: fa s_after old_child <> old_child).
        { intros Hfa_eq_old.
          apply Hfane_old.
          rewrite <- Hfa_old_pres. exact Hfa_eq_old. }
        assert (Hreach_after:
                  dg_reachable (state_to_dfs_tree g s_after root)
                               old_child x).
        { eapply preloop_tree_reachable_pre_lift; eauto. }
        split.
        * right. right. exists old_child, x.
          repeat split; auto.
          -- eapply preloop_preserves_active; eauto.
          -- intros Htree_post.
             destruct (preloop_tree_edge_post_cases
                         parent child x b done
                         s_before s_after retv
                         Hpre_all
                         Hexec Htree_post)
               as [Htree_old | [_ Hb_eq_child]].
             ++ exact (Hnot_tree Htree_old).
             ++ subst b. exact (Hchild_notvis Hb_vis).
        * eapply preloop_preserves_dfn_of_visited; eauto.
  Qed.

  Lemma preloop_parent_post_candidate_cases
        (parent child b: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    PartialLowCandidate parent done s_after b ->
    PartialLowCandidate parent done s_before b \/ b = child.
  Proof.
    intros Hpre Hexec Hcandidate.
    pose proof Hpre as Hpre_all.
    destruct Hpre as [Hloop [_ [Hentry _]]].
    destruct Hentry as [[_ Hchild_notvis] _].
    destruct Hloop as [_ [Hshape _]].
    destruct Hshape as
      [Hwf [_ [_ [_ [Hdone_vis _]]]]].
    destruct Hwf as [Hstack_vis _].
    unfold PartialLowCandidate in Hcandidate |- *.
    destruct Hcandidate as [Hb_parent | Htarget].
    - left. left. exact Hb_parent.
    - unfold PartialActiveTarget in Htarget |- *.
      destruct Htarget as [Hdirect | Hsubtree].
      + destruct Hdirect as
          [a [Hdone_a [Hb_eq_a [Hedge_pa [Hactive_a_after Hnot_tree_after]]]]].
        subst b.
        destruct (preloop_active_post_cases
                    child a s_before s_after retv Hexec Hactive_a_after)
          as [Hactive_a_before | Ha_eq_child].
        * left. right. left. exists a.
          repeat split; auto.
          intros Htree_before.
          apply Hnot_tree_after.
          eapply preloop_tree_edge_pre_lift; eauto.
        * right. exact Ha_eq_child.
      + destruct Hsubtree as
          [old_child [x
            [Hdone_old [Hedge_old [Hfa_old_after [Hfane_old_after
              [Hreach_after [Hedge_x_b [Hactive_b_after Hnot_tree_after]]]]]]]]].
        destruct (preloop_active_post_cases
                    child b s_before s_after retv Hexec Hactive_b_after)
          as [Hactive_b_before | Hb_eq_child].
        * assert (Hreach_before:
                    dg_reachable (state_to_dfs_tree g s_before root)
                                 old_child x).
          { eapply preloop_old_processed_child_reach_backward; eauto. }
          assert (Hfa_old_pres:
                    fa s_after old_child = fa s_before old_child).
          { pose proof (preloop_preserves_any_fa
                          child old_child (fa s_before old_child))
              as Hhoare.
            unfold Hoare in Hhoare.
            exact (Hhoare s_before retv s_after eq_refl Hexec). }
          assert (Hfa_old_before: fa s_before old_child = parent).
          { rewrite <- Hfa_old_pres. exact Hfa_old_after. }
          assert (Hfane_old_before: fa s_before old_child <> old_child).
          { intros Hfa_eq_old.
            apply Hfane_old_after.
            rewrite Hfa_old_pres. exact Hfa_eq_old. }
          left. right. right.
          exists old_child, x.
          repeat split; auto.
          intros Htree_before.
          apply Hnot_tree_after.
          eapply preloop_tree_edge_pre_lift; eauto.
        * right. exact Hb_eq_child.
  Qed.

  Lemma preloop_parent_old_candidates_low_bound
        (parent child b: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    PartialLowCandidate parent done s_after b ->
    low s_before parent <= dfn s_after b.
  Proof.
    intros Hpre Hexec Hcandidate_after.
    pose proof Hpre as Hpre_all.
    destruct Hpre as
      [Hloop [_ [Hentry [Hfa_child Hfane_child]]]].
    destruct Hentry as [[_ Hchild_notvis] _].
    destruct Hloop as [_ [Hshape [_ Hlow_correct]]].
    destruct Hshape as [Hwf [_ [Hparent_vis _]]].
    destruct Hwf as [_ [Hdfn_inv _]].
    destruct Hlow_correct as [_ Hcomplete].
    destruct (preloop_parent_post_candidate_cases
                parent child b done s_before s_after retv
                Hpre_all Hexec Hcandidate_after)
      as [Hcandidate_before | Hb_eq_child].
    - destruct (preloop_parent_old_candidate_forward
                  parent child b done s_before s_after retv
                  Hpre_all Hexec Hcandidate_before)
        as [_ Hdfn_eq].
      pose proof (Hcomplete b Hcandidate_before) as Hbound.
      lia.
    - subst b.
      assert (Hroot_candidate:
                PartialLowCandidate parent done s_before parent).
      { apply partial_low_candidate_root. }
      pose proof (Hcomplete parent Hroot_candidate)
        as Hlow_le_parent_before.
      assert (Hchild_ne_parent: child <> parent).
      { intros Hchild_eq_parent. apply Hfane_child.
        rewrite Hfa_child. symmetry. exact Hchild_eq_parent. }
      assert (Hdfn_parent_eq:
                dfn s_after parent = dfn s_before parent).
      { eapply preloop_preserves_dfn_of_visited; eauto. }
      assert (Hparent_lt_child:
                dfn s_after parent < dfn s_after child).
      { pose proof (preloop_after_visited_dfn_lt parent child) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s_before retv s_after
                      (conj Hparent_vis
                        (conj Hchild_notvis Hdfn_inv))
                      Hexec). }
      lia.
  Qed.

  Lemma preloop_preserves_parent_low_frame
        (parent child: V) (done: V -> Prop):
    Hoare
      (ParentRecursivePre parent child done)
      (preloop child)
      (fun _ s =>
         exists s_before,
           ParentLowFrame parent done s_before s).
  Proof.
    unfold Hoare.
    intros s_before retv s_after Hpre Hexec.
    exists s_before.
    pose proof Hpre as Hpre_all.
    destruct Hpre as
      [Hloop [_ [_ [Hfa_child Hfane_child]]]].
    destruct Hloop as [_ [Hshape _]].
    destruct Hshape as [_ [_ [Hparent_vis _]]].
    assert (Hchild_ne_parent: child <> parent).
    { intros Hchild_eq_parent. apply Hfane_child.
      rewrite Hfa_child. symmetry. exact Hchild_eq_parent. }
    assert (Hlow_eq: low s_after parent = low s_before parent).
    { pose proof (preloop_keep_low child parent (low s_before parent))
        as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s_before retv s_after
                       (conj Hchild_ne_parent
                         (conj Hparent_vis eq_refl))
                       Hexec)
        as [_ [_ Hlow]].
      exact Hlow. }
    unfold ParentLowFrame.
    split; [exact Hlow_eq |].
    split.
    - intros b Hcandidate_before.
      eapply preloop_parent_old_candidate_forward; eauto.
    - intros b Hcandidate_after.
      eapply preloop_parent_old_candidates_low_bound; eauto.
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

  Lemma preloop_initializes_loop_traversal_complete_empty (u: V):
    Hoare (EntryPre u)
          (preloop u)
          (fun _ s => LoopTraversalComplete u ∅ s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    unfold LoopTraversalComplete, LoopNoUnvisitedStep, LoopRestTargetCut.
    split.
    - intros x y Hpopped _ _.
      unfold PoppedSegment in Hpopped. simpl in Hpopped.
      unfold equiv_decb in Hpopped.
      destruct (equiv_dec u u) as [Hu_eq | Hu_neq].
      + simpl in Hpopped. destruct Hpopped as [Hx_eq | []].
        subst x. split; [reflexivity |].
        sets_unfold. tauto.
      + exfalso. apply Hu_neq. reflexivity.
    - intros x target Hpopped _ _.
      left.
      unfold PoppedSegment in Hpopped. simpl in Hpopped.
      unfold equiv_decb in Hpopped.
      destruct (equiv_dec u u) as [Hu_eq | Hu_neq].
      + simpl in Hpopped. destruct Hpopped as [Hx_eq | []].
        subst x. split; [reflexivity |].
        sets_unfold. tauto.
      + exfalso. apply Hu_neq. reflexivity.
  Qed.

  Theorem preloop_initializes_edge_loop_pre (u: V):
    Hoare (EntryPre u)
          (preloop u)
          (fun _ s =>
             LoopInv u ∅ s /\
             LoopTraversalComplete u ∅ s).
  Proof.
    apply Hoare_conj with
      (Q1 := fun _ s => LoopInv u ∅ s).
    - apply preloop_initializes_loop_inv.
    - apply preloop_initializes_loop_traversal_complete_empty.
  Qed.

  Lemma preloop_parent_shape_done_after
        (parent child: V) (done: V -> Prop)
        (s_before s_after: St) (retv: unit):
    ParentRecursivePre parent child done s_before ->
    (s_before, retv, s_after) ∈ preloop child ->
    LoopCoreShape parent (done_after done child) s_after.
  Proof.
    intros Hpre Hexec.
    destruct Hpre as
      [Hloop [Hedge [Hentry [Hfa_child Hfane_child]]]].
    destruct Hentry as
      [Hwf_pre [Hsettled [Hclosed [Htree_pre [Horder Hincoming]]]]].
    destruct Hloop as [_ [Hshape _]].
    destruct Hshape as
      [Hwf_parent [Htree_parent [Hparent_vis
        [Hdone_edge [Hdone_vis Hprocessed]]]]].
    assert (Hwf_after: wf_scc_state g root s_after).
    { assert (Hhoare:
                Hoare
                  (fun s: St => wf_scc_state_pre g root child s)
                  (preloop child)
                  (fun _ s => wf_scc_state g root s)).
      { apply preloop_preserves_wf_scc_state. }
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after Hwf_pre Hexec). }
    assert (Htree_after: TreeEdgesAreGraphEdges s_after).
    { pose proof (preloop_preserves_tree_edges_are_graph_edges child)
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after
                    (conj Hwf_pre (conj Htree_pre Hincoming))
                    Hexec). }
    assert (Hparent_vis_after: Visited parent s_after).
    { pose proof (preloop_keep_visited child parent) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after Hparent_vis Hexec). }
    assert (Hdone_after_edge:
              forall a, done_after done child a -> Edge parent a).
    { intros a Hdone_after.
      destruct (done_after_elim done child a Hdone_after)
        as [Hdone_a | Ha_eq_child].
      - apply Hdone_edge. exact Hdone_a.
      - subst a. exact Hedge. }
    assert (Hdone_after_vis:
              forall a, done_after done child a -> Visited a s_after).
    { intros a Hdone_after.
      destruct (done_after_elim done child a Hdone_after)
        as [Hdone_a | Ha_eq_child].
      - pose proof (preloop_keep_visited child a) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s_before retv s_after
                      (Hdone_vis a Hdone_a) Hexec).
      - subst a.
        pose proof (preloop_self_visited child) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s_before retv s_after I Hexec). }
    assert (Hprocessed_after:
              ProcessedTreeChild parent (done_after done child) s_after).
    { unfold ProcessedTreeChild.
      intros v Hvis_after Hfa_after Hfane_after.
      destruct (preloop_visited_post_cases
                  child v s_before s_after retv Hexec Hvis_after)
        as [Hvis_before | Hv_eq_child].
      - assert (Hfa_pres: fa s_after v = fa s_before v).
        { pose proof (preloop_preserves_any_fa
                        child v (fa s_before v)) as Hhoare.
          unfold Hoare in Hhoare.
          exact (Hhoare s_before retv s_after eq_refl Hexec). }
        assert (Hfa_before: fa s_before v = parent).
        { rewrite <- Hfa_pres. exact Hfa_after. }
        assert (Hfane_before: fa s_before v <> v).
        { intros Hfa_eq_v.
          apply Hfane_after.
          rewrite Hfa_pres. exact Hfa_eq_v. }
        apply done_after_intro_old.
        exact (Hprocessed v Hvis_before Hfa_before Hfane_before).
      - subst v. apply done_after_intro_new. }
    exact (conj Hwf_after
            (conj Htree_after
              (conj Hparent_vis_after
                (conj Hdone_after_edge
                  (conj Hdone_after_vis Hprocessed_after))))).
  Qed.

  Lemma preloop_preserves_loop_aux_facts_for_entry
        (center u: V) (s_before s_after: St) (retv: unit):
    EntryPre u s_before ->
    LoopAuxFacts center s_before ->
    (s_before, retv, s_after) ∈ preloop u ->
    LoopAuxFacts center s_after.
  Proof.
    intros Hentry Haux Hexec.
    destruct Hentry as
      [Hwf_pre [Hsettled [Hclosed [Htree [Horder_entry Hincoming]]]]].
    destruct Hwf_pre as
      [[Hstack_vis [Hdfn_inv [Hdfn_valid Hfa_vis]]] Hunvis].
    destruct Haux as [Hsettled_aux [Hactive_center Horder_aux]].
    destruct Horder_aux as [Hstack_order [Hdfn_inj Hnodup]].
    unfold LoopAuxFacts, OrderFacts.
    split.
    - assert (Hhoare:
                Hoare
                  (fun s: St => NoUnvisitedReach s)
                  (preloop u)
                  (fun _ s => NoUnvisitedReach s)).
      { apply preloop_keep_settled_closed. }
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after Hsettled_aux Hexec).
    - split.
      + assert (Hhoare:
                  Hoare
                    (fun s: St => Active center s)
                    (preloop u)
                    (fun _ s => Active center s)).
        { apply preloop_keep_in_stack. }
        unfold Hoare in Hhoare.
        exact (Hhoare s_before retv s_after Hactive_center Hexec).
      + split.
        * assert (Hhoare:
                    Hoare
                      (fun s: St =>
                         stack_dfn_order s /\ dfn_inv s /\
                         stack_in_visited s /\ ~ Visited u s)
                      (preloop u)
                      (fun _ s => stack_dfn_order s)).
          { apply preloop_preserves_stack_dfn_order. }
          unfold Hoare in Hhoare.
          exact (Hhoare s_before retv s_after
                        (conj Hstack_order
                          (conj Hdfn_inv
                            (conj Hstack_vis Hunvis)))
                        Hexec).
        * split.
          -- assert (Hhoare:
                       Hoare
                         (fun s: St =>
                            dfn_injective s /\ dfn_inv s /\
                            ~ Visited u s)
                         (preloop u)
                         (fun _ s => dfn_injective s)).
             { apply preloop_preserves_dfn_injective. }
             unfold Hoare in Hhoare.
             exact (Hhoare s_before retv s_after
                           (conj Hdfn_inj (conj Hdfn_inv Hunvis))
                           Hexec).
          -- pose proof (preloop_preserves_stack_nodup u) as Hhoare.
             unfold Hoare in Hhoare.
             exact (Hhoare s_before retv s_after
                           (conj Hnodup (conj Hstack_vis Hunvis))
                           Hexec).
  Qed.

  Lemma preloop_establishes_parent_frame_for_child_exact
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         s = s_before /\ ParentRecursivePre parent child done s)
      (preloop child)
      (fun _ s =>
         LoopInv child ∅ s /\
         LoopInv parent done s_before /\
         ParentFrameForChild parent child done s_before s).
  Proof.
    unfold Hoare.
    intros s0 retv s_after [Hs0 Hpre] Hexec.
    subst s0.
    pose proof Hpre as Hpre_all.
    destruct Hpre as
      [Hloop_parent [Hedge [Hentry_child [Hfa_child Hfane_child]]]].
    destruct Hloop_parent as [Haux_parent [Hshape_parent Hcore_rest]].
    pose proof Hshape_parent as Hshape_parent_full.
    destruct Hshape_parent as [_ [_ [Hparent_vis _]]].
    assert (Hchild_loop: LoopInv child ∅ s_after).
    { pose proof (preloop_initializes_loop_inv child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after Hentry_child Hexec). }
    assert (Hparent_loop_before:
              LoopInv parent done s_before).
    { exact (conj Haux_parent (conj Hshape_parent_full Hcore_rest)). }
    assert (Hchild_ne_parent: child <> parent).
    { intros Hchild_eq_parent. apply Hfane_child.
      rewrite Hfa_child. symmetry. exact Hchild_eq_parent. }
    assert (Hlow_frame:
              ParentLowFrame parent done s_before s_after).
    { assert (Hlow_eq: low s_after parent = low s_before parent).
      { pose proof (preloop_keep_low child parent (low s_before parent))
          as Hhoare.
        unfold Hoare in Hhoare.
        destruct (Hhoare s_before retv s_after
                         (conj Hchild_ne_parent
                           (conj Hparent_vis eq_refl))
                         Hexec)
          as [_ [_ Hlow]].
        exact Hlow. }
      unfold ParentLowFrame. simpl.
      split; [exact Hlow_eq |].
      split.
      - intros b Hcandidate_before.
        eapply preloop_parent_old_candidate_forward; eauto.
      - intros b Hcandidate_after.
        eapply preloop_parent_old_candidates_low_bound; eauto. }
    assert (Hshape_after:
              LoopCoreShape parent (done_after done child) s_after).
    { eapply preloop_parent_shape_done_after; eauto. }
    assert (Haux_after: LoopAuxFacts parent s_after).
    { eapply preloop_preserves_loop_aux_facts_for_entry; eauto. }
    assert (Hclosed_after: Closed s_after).
    { pose proof (preloop_preserves_closed child) as Hhoare.
      unfold Hoare in Hhoare.
      destruct Hentry_child as [Hwf_pre [Hsettled [Hclosed _]]].
      exact (Hhoare s_before retv s_after
                    (conj Hwf_pre (conj Hsettled Hclosed))
                    Hexec). }
    assert (Htree_after: TreeEdgesAreGraphEdges s_after).
    { destruct Hshape_after as [_ [Htree_after _]].
      exact Htree_after. }
    assert (Hchild_vis_after: Visited child s_after).
    { pose proof (preloop_self_visited child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after I Hexec). }
    assert (Hfa_child_pres: fa s_after child = fa s_before child).
    { pose proof (preloop_preserves_any_fa
                    child child (fa s_before child)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_before retv s_after eq_refl Hexec). }
    assert (Hfa_child_after: fa s_after child = parent).
    { rewrite Hfa_child_pres. exact Hfa_child. }
    assert (Hfane_child_after: fa s_after child <> child).
    { intros Hfa_eq_child.
      apply Hfane_child.
      rewrite <- Hfa_child_pres. exact Hfa_eq_child. }
    assert (Hparent_lt_child:
              dfn s_after parent < dfn s_after child).
    { pose proof (preloop_after_visited_dfn_lt parent child) as Hhoare.
      unfold Hoare in Hhoare.
      destruct Hentry_child as [[[_ [Hdfn_inv _]] Hchild_notvis] _].
      exact (Hhoare s_before retv s_after
                    (conj Hparent_vis
                      (conj Hchild_notvis Hdfn_inv))
                    Hexec). }
    assert (Hnot_done_child: ~ done child).
    { intros Hdone_child.
      destruct Hshape_parent_full as [_ [_ [_ [_ [Hdone_vis _]]]]].
      destruct Hentry_child as [[_ Hchild_notvis] _].
      exact (Hchild_notvis (Hdone_vis child Hdone_child)). }
    assert (Hbelow_child:
              ParentOldCandidatesBelowChild
                parent child done s_before s_after).
    { eapply preloop_parent_old_candidates_below_child; eauto. }
    assert (Hstack_frame:
              ParentTraversalStackFrame parent child s_before s_after).
    { eapply preloop_parent_traversal_stack_frame; eauto. }
    split; [exact Hchild_loop |].
    split; [exact Hparent_loop_before |].
    unfold ParentFrameForChild.
    split; [exact Hlow_frame |].
    split; [exact Hshape_after |].
    split; [exact Haux_after |].
    split; [exact Hclosed_after |].
    split; [exact Htree_after |].
    split; [exact Hedge |].
    split; [exact Hchild_vis_after |].
    split; [exact Hfa_child_after |].
    split; [exact Hfane_child_after |].
    split; [exact Hparent_lt_child |].
    split; [exact Hnot_done_child |].
    exact (conj Hbelow_child Hstack_frame).
  Qed.

  Lemma preloop_establishes_parent_frame_for_child
        (parent child: V) (done: V -> Prop):
    Hoare
      (ParentRecursivePre parent child done)
      (preloop child)
      (fun _ s =>
         exists s_before,
           LoopInv child ∅ s /\
           LoopInv parent done s_before /\
           ParentFrameForChild parent child done s_before s).
  Proof.
    unfold Hoare.
    intros s_before retv s_after Hpre Hexec.
    exists s_before.
    pose proof (preloop_establishes_parent_frame_for_child_exact
                  parent child done s_before) as Hhoare.
    unfold Hoare in Hhoare.
    exact (Hhoare s_before retv s_after
                  (conj eq_refl Hpre) Hexec).
  Qed.

  Lemma nested_frame_pre_parent_recursive_pre
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s: St):
    NestedFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s ->
    ParentRecursivePre loop_root next loop_done s.
  Proof.
    intros Hpre.
    destruct Hpre as
      [Hloop [_ [_ [Hedge [Hnot_done [Hentry [Hfa Hfane]]]]]]].
    unfold ParentRecursivePre.
    exact (conj Hloop
            (conj Hedge
              (conj Hentry
                (conj Hfa Hfane)))).
  Qed.

  Lemma nested_frame_loop_root_not_ancestor
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s: St):
    NestedFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s ->
    loop_root <> ancestor.
  Proof.
    intros Hpre Hloop_eq.
    destruct Hpre as
      [_ [Hframe [Hdisjoint _]]].
    destruct Hdisjoint as [Hreach_current_loop _].
    destruct Hframe as
      [_ [Hshape [_ [_ [_ [_ [_ [_ [_ Hdfn_ancestor_current]]]]]]]]].
    destruct Hshape as [Hwf _].
    subst loop_root.
    pose proof (tree_reachable_dfn_monotone
                  s current ancestor Hwf Hreach_current_loop)
      as Hdfn_current_ancestor.
    lia.
  Qed.

  Lemma preloop_nested_done_child_not_reach_next
        (ancestor current loop_root next old_child: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    (s_mid, retv, s_after) ∈ preloop next ->
    ancestor_done old_child ->
    fa s_after old_child = ancestor ->
    fa s_after old_child <> old_child ->
    ~ dg_reachable (state_to_dfs_tree g s_after root) old_child next.
  Proof.
    intros Hnested Hexec Hdone_old Hfa_old_after Hfane_old_after Hreach.
    pose proof Hnested as Hnested_all.
    pose proof (nested_frame_pre_parent_recursive_pre
                  ancestor current loop_root next ancestor_done loop_done
                  s_before s_mid Hnested_all) as Hrecursive_pre.
    destruct Hnested as
      [Hloop [Hframe [Hdisjoint [_ [_ [Hentry [Hfa_next Hfane_next]]]]]]].
    destruct Hentry as [[_ Hnext_notvis] _].
    destruct Hdisjoint as [_ Hold_disjoint].
    destruct Hframe as
      [_ [Hshape [_ [_ [_ [_ [_ [_ [_ _]]]]]]]]].
    destruct Hshape as [_ [_ [_ [_ [Hdone_vis _]]]]].
    assert (Hold_vis: Visited old_child s_mid).
    { apply Hdone_vis. apply done_after_intro_old. exact Hdone_old. }
    assert (Hold_ne_next: old_child <> next).
    { intros Hold_eq_next. apply Hnext_notvis.
      rewrite <- Hold_eq_next. exact Hold_vis. }
    destruct (dg_reachable_vertex_path
                (state_to_dfs_tree g s_after root)
                old_child next Hreach)
      as [path Hpath].
    assert (Hnext_not_ne: ~ (next = next -> False)).
    { intros Hneq. apply Hneq. reflexivity. }
    destruct (dg_vertex_path_last_exit_from_pred
                (state_to_dfs_tree g s_after root)
                (fun z => z = next -> False)
                old_child next path
                Hold_ne_next Hnext_not_ne Hpath)
      as [a [b [suffix
        [Ha_ne_next [Hb_not_ne_next
          [Hstep_ab [Hreach_old_a_post [_ _]]]]]]]].
    assert (Hb_eq_next: b = next).
    { apply NNPP. exact Hb_not_ne_next. }
    subst b.
    destruct (preloop_tree_edge_post_cases
                loop_root next a next loop_done s_mid s_after retv
                Hrecursive_pre Hexec Hstep_ab)
      as [Hstep_old | [Ha_eq_loop _]].
    - apply tree_step_char in Hstep_old as [_ [_ Hnext_vis_pre]].
      exact (Hnext_notvis Hnext_vis_pre).
    - subst a.
      assert (Hloop_ne_next: loop_root <> next).
      { intros Hloop_eq_next. apply Hfane_next.
        rewrite Hfa_next. exact Hloop_eq_next. }
      assert (Hreach_old_loop_pre:
                dg_reachable (state_to_dfs_tree g s_mid root)
                             old_child loop_root).
      { eapply preloop_reachable_backward_not_child; eauto. }
      assert (Hfa_old_pres:
                fa s_after old_child = fa s_mid old_child).
      { pose proof (preloop_preserves_any_fa
                      next old_child (fa s_mid old_child)) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s_mid retv s_after eq_refl Hexec). }
      assert (Hfa_old_before: fa s_mid old_child = ancestor).
      { rewrite <- Hfa_old_pres. exact Hfa_old_after. }
      assert (Hfane_old_before: fa s_mid old_child <> old_child).
      { intros Hfa_eq_old.
        apply Hfane_old_after.
        rewrite Hfa_old_pres. exact Hfa_eq_old. }
      exact (Hold_disjoint old_child Hdone_old Hfa_old_before
                           Hfane_old_before Hreach_old_loop_pre).
  Qed.

  Lemma preloop_nested_old_candidate_forward
        (ancestor current loop_root next b: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    (s_mid, retv, s_after) ∈ preloop next ->
    PartialLowCandidate ancestor ancestor_done s_mid b ->
    PartialLowCandidate ancestor ancestor_done s_after b /\
    dfn s_after b = dfn s_mid b.
  Proof.
    intros Hnested Hexec Hcandidate.
    pose proof Hnested as Hnested_all.
    pose proof (nested_frame_pre_parent_recursive_pre
                  ancestor current loop_root next ancestor_done loop_done
                  s_before s_mid Hnested_all) as Hrecursive_pre.
    destruct Hnested as
      [Hloop [Hframe [_ [_ [_ [Hentry _]]]]]].
    destruct Hentry as [[_ Hnext_notvis] _].
    destruct Hframe as
      [_ [Hshape [_ [_ [_ [_ [_ [_ [_ _]]]]]]]]].
    destruct Hshape as [Hwf [_ [Hancestor_vis [_ [Hdone_vis _]]]]].
    destruct Hwf as [Hstack_vis _].
    unfold PartialLowCandidate in Hcandidate |- *.
    destruct Hcandidate as [Hb_ancestor | Htarget].
    - subst b. split.
      + left. reflexivity.
      + assert (Hnext_ne_ancestor: next <> ancestor).
        { intros Hnext_eq_ancestor. apply Hnext_notvis.
          rewrite Hnext_eq_ancestor. exact Hancestor_vis. }
        eapply preloop_preserves_dfn_of_visited; eauto.
    - unfold PartialActiveTarget in Htarget |- *.
      destruct Htarget as [Hdirect | Hsubtree].
      + destruct Hdirect as
          [a [Hdone_a [Hb_eq_a [Hedge [Hactive Hnot_tree]]]]].
        subst b.
        assert (Ha_vis: Visited a s_mid).
        { apply Hdone_vis. apply done_after_intro_old. exact Hdone_a. }
        assert (Hnext_ne_a: next <> a).
        { intros Hnext_eq_a. apply Hnext_notvis.
          rewrite Hnext_eq_a. exact Ha_vis. }
        split.
        * right. left. exists a.
          repeat split; auto.
          -- eapply preloop_preserves_active; eauto.
          -- intros Htree_post.
             destruct (preloop_tree_edge_post_cases
                         loop_root next ancestor a loop_done
                         s_mid s_after retv
                         Hrecursive_pre Hexec Htree_post)
               as [Htree_old | [_ Ha_eq_next]].
             ++ exact (Hnot_tree Htree_old).
             ++ subst a. exact (Hnext_notvis Ha_vis).
        * eapply preloop_preserves_dfn_of_visited; eauto.
      + destruct Hsubtree as
          [old_child [x
            [Hdone_old [Hedge_old [Hfa_old [Hfane_old
              [Hreach_old_x [Hedge_x_b [Hactive_b Hnot_tree]]]]]]]]].
        assert (Hold_vis: Visited old_child s_mid).
        { apply Hdone_vis. apply done_after_intro_old. exact Hdone_old. }
        assert (Hb_vis: Visited b s_mid).
        { apply Hstack_vis. exact Hactive_b. }
        assert (Hnext_ne_b: next <> b).
        { intros Hnext_eq_b. apply Hnext_notvis.
          rewrite Hnext_eq_b. exact Hb_vis. }
        assert (Hfa_old_pres:
                  fa s_after old_child = fa s_mid old_child).
        { pose proof (preloop_preserves_any_fa
                        next old_child (fa s_mid old_child))
            as Hhoare.
          unfold Hoare in Hhoare.
          exact (Hhoare s_mid retv s_after eq_refl Hexec). }
        assert (Hreach_after:
                  dg_reachable (state_to_dfs_tree g s_after root)
                               old_child x).
        { eapply preloop_tree_reachable_pre_lift; eauto. }
        split.
        * right. right. exists old_child, x.
          repeat split; auto.
          -- rewrite Hfa_old_pres. exact Hfa_old.
          -- intros Hfa_eq_old. apply Hfane_old.
             rewrite <- Hfa_old_pres. exact Hfa_eq_old.
          -- eapply preloop_preserves_active; eauto.
          -- intros Htree_post.
             destruct (preloop_tree_edge_post_cases
                         loop_root next x b loop_done
                         s_mid s_after retv
                         Hrecursive_pre Hexec Htree_post)
               as [Htree_old | [_ Hb_eq_next]].
             ++ exact (Hnot_tree Htree_old).
             ++ subst b. exact (Hnext_notvis Hb_vis).
        * eapply preloop_preserves_dfn_of_visited; eauto.
  Qed.

  Lemma preloop_nested_post_candidate_cases
        (ancestor current loop_root next b: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    (s_mid, retv, s_after) ∈ preloop next ->
    PartialLowCandidate ancestor ancestor_done s_after b ->
    PartialLowCandidate ancestor ancestor_done s_mid b \/ b = next.
  Proof.
    intros Hnested Hexec Hcandidate.
    pose proof Hnested as Hnested_all.
    pose proof (nested_frame_pre_parent_recursive_pre
                  ancestor current loop_root next ancestor_done loop_done
                  s_before s_mid Hnested_all) as Hrecursive_pre.
    destruct Hnested as
      [Hloop [Hframe [_ [_ [_ [Hentry _]]]]]].
    destruct Hentry as [[_ Hnext_notvis] _].
    destruct Hframe as
      [_ [Hshape [_ [_ [_ [_ [_ [_ [_ _]]]]]]]]].
    destruct Hshape as [Hwf [_ [_ [_ [Hdone_vis _]]]]].
    unfold PartialLowCandidate in Hcandidate |- *.
    destruct Hcandidate as [Hb_ancestor | Htarget].
    - left. left. exact Hb_ancestor.
    - unfold PartialActiveTarget in Htarget |- *.
      destruct Htarget as [Hdirect | Hsubtree].
      + destruct Hdirect as
          [a [Hdone_a [Hb_eq_a [Hedge [Hactive_after Hnot_tree_after]]]]].
        subst b.
        assert (Ha_vis: Visited a s_mid).
        { apply Hdone_vis. apply done_after_intro_old. exact Hdone_a. }
        destruct (preloop_active_post_cases
                    next a s_mid s_after retv Hexec Hactive_after)
          as [Hactive_before | Ha_eq_next].
        * left. right. left. exists a.
          repeat split; auto.
          intros Htree_before.
          apply Hnot_tree_after.
          eapply preloop_tree_edge_pre_lift; eauto.
        * subst a. exfalso. exact (Hnext_notvis Ha_vis).
      + destruct Hsubtree as
          [old_child [x
            [Hdone_old [Hedge_old [Hfa_old_after [Hfane_old_after
              [Hreach_after [Hedge_x_b [Hactive_b_after Hnot_tree_after]]]]]]]]].
        destruct (classic (x = next)) as [Hx_eq_next | Hx_ne_next].
        * subst x. exfalso.
          eapply preloop_nested_done_child_not_reach_next; eauto.
        * destruct (preloop_active_post_cases
                      next b s_mid s_after retv Hexec Hactive_b_after)
            as [Hactive_b_before | Hb_eq_next].
          -- assert (Hreach_before:
                       dg_reachable (state_to_dfs_tree g s_mid root)
                                    old_child x).
             { eapply preloop_reachable_backward_not_child; eauto. }
             assert (Hfa_old_pres:
                       fa s_after old_child = fa s_mid old_child).
             { pose proof (preloop_preserves_any_fa
                             next old_child (fa s_mid old_child))
                 as Hhoare.
               unfold Hoare in Hhoare.
               exact (Hhoare s_mid retv s_after eq_refl Hexec). }
             assert (Hfa_old_before: fa s_mid old_child = ancestor).
             { rewrite <- Hfa_old_pres. exact Hfa_old_after. }
             assert (Hfane_old_before: fa s_mid old_child <> old_child).
             { intros Hfa_eq_old.
               apply Hfane_old_after.
               rewrite Hfa_old_pres. exact Hfa_eq_old. }
             left. right. right.
             exists old_child, x.
             repeat split; auto.
             intros Htree_before.
             apply Hnot_tree_after.
             eapply preloop_tree_edge_pre_lift; eauto.
          -- right. exact Hb_eq_next.
  Qed.

  Lemma preloop_nested_old_candidates_low_bound
        (ancestor current loop_root next b: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    (s_mid, retv, s_after) ∈ preloop next ->
    PartialLowCandidate ancestor ancestor_done s_after b ->
    low s_before ancestor <= dfn s_after b.
  Proof.
    intros Hnested Hexec Hcandidate_after.
    pose proof Hnested as Hnested_all.
    destruct Hnested as
      [Hloop [Hframe [Hdisjoint [_ [_ [Hentry [Hfa_next Hfane_next]]]]]]].
    destruct Hentry as [[Hwf_pre Hnext_notvis] _].
    destruct Hwf_pre as [_ [Hdfn_inv _]].
    destruct Hdisjoint as [Hreach_current_loop _].
    destruct Hloop as [_ [Hshape_loop _]].
    destruct Hshape_loop as [_ [_ [Hloop_vis _]]].
    destruct Hframe as
      [Hlow_frame [Hshape_ancestor [_ [_ [_ [_ [_ [_ [_ Hdfn_ancestor_current]]]]]]]]].
    destruct Hlow_frame as [_ [Hframe_forward Hframe_bound]].
    destruct Hshape_ancestor as [Hwf_ancestor _].
    destruct (preloop_nested_post_candidate_cases
                ancestor current loop_root next b ancestor_done loop_done
                s_before s_mid s_after retv Hnested_all Hexec
                Hcandidate_after)
      as [Hcandidate_before | Hb_eq_next].
    - destruct (preloop_nested_old_candidate_forward
                  ancestor current loop_root next b ancestor_done loop_done
                  s_before s_mid s_after retv Hnested_all Hexec
                  Hcandidate_before)
        as [_ Hdfn_eq].
      pose proof (Hframe_bound b Hcandidate_before) as Hbound.
      lia.
    - subst b.
      assert (Hroot_candidate:
                PartialLowCandidate ancestor ancestor_done s_mid ancestor).
      { apply partial_low_candidate_root. }
      pose proof (Hframe_bound ancestor Hroot_candidate)
        as Hlow_le_ancestor.
      pose proof (tree_reachable_dfn_monotone
                    s_mid current loop_root Hwf_ancestor
                    Hreach_current_loop)
        as Hdfn_current_loop.
      assert (Hloop_ne_next: loop_root <> next).
      { intros Hloop_eq_next. apply Hfane_next.
        rewrite Hfa_next. exact Hloop_eq_next. }
      assert (Hdfn_loop_eq:
                dfn s_after loop_root = dfn s_mid loop_root).
      { eapply preloop_preserves_dfn_of_visited; eauto. }
      assert (Hloop_lt_next:
                dfn s_after loop_root < dfn s_after next).
      { pose proof (preloop_after_visited_dfn_lt loop_root next) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s_mid retv s_after
                      (conj Hloop_vis
                        (conj Hnext_notvis Hdfn_inv))
                      Hexec). }
      lia.
  Qed.

  Lemma preloop_preserves_nested_parent_low_frame
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    (s_mid, retv, s_after) ∈ preloop next ->
    ParentLowFrame ancestor ancestor_done s_before s_after.
  Proof.
    intros Hnested Hexec.
    pose proof Hnested as Hnested_all.
    destruct Hnested as
      [_ [Hframe [_ [_ [_ [Hentry _]]]]]].
    destruct Hentry as [[_ Hnext_notvis] _].
    destruct Hframe as
      [Hlow_frame [Hshape [_ [_ [_ [_ [_ [_ [_ _]]]]]]]]].
    destruct Hlow_frame as [Hlow_eq_mid [Hframe_forward _]].
    destruct Hshape as [_ [_ [Hancestor_vis _]]].
    assert (Hnext_ne_ancestor: next <> ancestor).
    { intros Hnext_eq_ancestor. apply Hnext_notvis.
      rewrite Hnext_eq_ancestor. exact Hancestor_vis. }
    assert (Hlow_eq_after: low s_after ancestor = low s_before ancestor).
    { pose proof (preloop_keep_low next ancestor (low s_mid ancestor))
        as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s_mid retv s_after
                       (conj Hnext_ne_ancestor
                         (conj Hancestor_vis eq_refl))
                       Hexec)
        as [_ [_ Hlow_pres]].
      rewrite Hlow_pres. exact Hlow_eq_mid. }
    unfold ParentLowFrame.
    split; [exact Hlow_eq_after |].
    split.
    - intros b Hcandidate_before.
      destruct (Hframe_forward b Hcandidate_before)
        as [Hcandidate_mid Hdfn_mid_eq].
      destruct (preloop_nested_old_candidate_forward
                  ancestor current loop_root next b ancestor_done loop_done
                  s_before s_mid s_after retv Hnested_all Hexec
                  Hcandidate_mid)
        as [Hcandidate_after Hdfn_after_eq].
      split; [exact Hcandidate_after | lia].
    - intros b Hcandidate_after.
      eapply preloop_nested_old_candidates_low_bound; eauto.
  Qed.

  Lemma preloop_preserves_nested_parent_old_candidates_below_child
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    (s_mid, retv, s_after) ∈ preloop next ->
    ParentOldCandidatesBelowChild ancestor current ancestor_done
      s_before s_after.
  Proof.
    intros Hnested Hexec b Hcandidate.
    destruct Hnested as
      [_ [Hframe [_ [_ [_ [Hentry _]]]]]].
    destruct Hentry as [[_ Hnext_notvis] _].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [Hshape Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [Hcurrent_vis Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ [Hbelow_mid _]].
    assert (Hnext_ne_current: next <> current).
    { intros Hnext_eq_current. apply Hnext_notvis.
      rewrite Hnext_eq_current. exact Hcurrent_vis. }
    pose proof (Hbelow_mid b Hcandidate) as Hrest_mid.
    pose proof (preloop_preserves_rest_stack next current b Hnext_ne_current)
      as Hhoare.
    unfold Hoare in Hhoare.
    exact (Hhoare s_mid retv s_after Hrest_mid Hexec).
  Qed.

  Lemma preloop_preserves_nested_parent_shape
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before s_mid s_after: St) (retv: unit):
    NestedFramePre ancestor current loop_root next
      ancestor_done loop_done s_before s_mid ->
    (s_mid, retv, s_after) ∈ preloop next ->
    LoopCoreShape ancestor (done_after ancestor_done current) s_after.
  Proof.
    intros Hnested Hexec.
    pose proof Hnested as Hnested_all.
    pose proof (nested_frame_pre_parent_recursive_pre
                  ancestor current loop_root next ancestor_done loop_done
                  s_before s_mid Hnested_all) as Hrecursive_pre.
    destruct Hnested as
      [_ [Hframe [Hdisjoint [_ [_ [Hentry_full [Hfa_next Hfane_next]]]]]]].
    pose proof Hentry_full as Hentry_for_tree.
    destruct Hentry_full as [Hwf_pre _].
    destruct Hdisjoint as [Hreach_current_loop _].
    destruct Hframe as
      [_ [Hshape [_ [_ [_ [_ [_ [_ [_ Hdfn_ancestor_current]]]]]]]]].
    destruct Hshape as
      [Hwf [Htree_sound [Hancestor_vis
        [Hdone_edge [Hdone_vis Hprocessed]]]]].
    assert (Hwf_after: wf_scc_state g root s_after).
    { assert (Hhoare:
                Hoare
                  (fun s: St => wf_scc_state_pre g root next s)
                  (preloop next)
                  (fun _ s => wf_scc_state g root s)).
      { apply preloop_preserves_wf_scc_state. }
      unfold Hoare in Hhoare.
      exact (Hhoare s_mid retv s_after Hwf_pre Hexec). }
    assert (Htree_after: TreeEdgesAreGraphEdges s_after).
    { pose proof (preloop_preserves_tree_edges_are_graph_edges next)
        as Hhoare.
      unfold Hoare in Hhoare.
      destruct Hentry_for_tree as
        [Hwf_pre' [_ [_ [Htree_pre [_ Hincoming]]]]].
      exact (Hhoare s_mid retv s_after
                    (conj Hwf_pre' (conj Htree_pre Hincoming))
                    Hexec). }
    assert (Hancestor_vis_after: Visited ancestor s_after).
    { pose proof (preloop_keep_visited next ancestor) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_mid retv s_after Hancestor_vis Hexec). }
    assert (Hdone_vis_after:
              forall a,
                done_after ancestor_done current a -> Visited a s_after).
    { intros a Hdone_a.
      pose proof (preloop_keep_visited next a) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_mid retv s_after
                    (Hdone_vis a Hdone_a) Hexec). }
    assert (Hloop_root_ne_ancestor: loop_root <> ancestor).
    { eapply nested_frame_loop_root_not_ancestor; eauto. }
    assert (Hprocessed_after:
              ProcessedTreeChild ancestor
                (done_after ancestor_done current) s_after).
    { unfold ProcessedTreeChild.
      intros v Hvis_after Hfa_after Hfane_after.
      destruct (preloop_visited_post_cases
                  next v s_mid s_after retv Hexec Hvis_after)
        as [Hvis_before | Hv_eq_next].
      - assert (Hfa_pres: fa s_after v = fa s_mid v).
        { pose proof (preloop_preserves_any_fa
                        next v (fa s_mid v)) as Hhoare.
          unfold Hoare in Hhoare.
          exact (Hhoare s_mid retv s_after eq_refl Hexec). }
        assert (Hfa_before: fa s_mid v = ancestor).
        { rewrite <- Hfa_pres. exact Hfa_after. }
        assert (Hfane_before: fa s_mid v <> v).
        { intros Hfa_eq_v.
          apply Hfane_after.
          rewrite Hfa_pres. exact Hfa_eq_v. }
        exact (Hprocessed v Hvis_before Hfa_before Hfane_before).
      - subst v.
        assert (Hfa_next_after: fa s_after next = loop_root).
        { pose proof (preloop_preserves_any_fa
                        next next (fa s_mid next)) as Hhoare.
          unfold Hoare in Hhoare.
          assert (Hfa_pres:
                    fa s_after next = fa s_mid next).
          { exact (Hhoare s_mid retv s_after eq_refl Hexec). }
          rewrite Hfa_pres. exact Hfa_next. }
        exfalso. apply Hloop_root_ne_ancestor.
        rewrite <- Hfa_next_after. exact Hfa_after. }
    exact (conj Hwf_after
            (conj Htree_after
              (conj Hancestor_vis_after
                (conj Hdone_edge
                  (conj Hdone_vis_after Hprocessed_after))))).
  Qed.

  Lemma preloop_preserves_nested_parent_frame
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St):
    Hoare
      (NestedFramePre ancestor current loop_root next
         ancestor_done loop_done s_before)
      (preloop next)
      (fun _ s =>
         LoopInv next ∅ s /\
         ParentFrameForChild ancestor current ancestor_done s_before s).
  Proof.
    unfold Hoare.
    intros s_mid retv s_after Hnested Hexec.
    pose proof Hnested as Hnested_all.
    destruct Hnested as
      [_ [Hframe [_ [_ [_ [Hentry _]]]]]].
    pose proof Hentry as Hentry_for_loop.
    pose proof Hentry as Hentry_for_aux.
    pose proof Hentry as Hentry_for_closed.
    destruct Hframe as [Hlow_frame_mid Hframe].
    destruct Hframe as [Hshape_mid Hframe].
    destruct Hframe as [Haux_mid Hframe].
    destruct Hframe as [Hclosed_mid Hframe].
    destruct Hframe as [Htree_mid Hframe].
    destruct Hframe as [Hedge_ancestor_current Hframe].
    destruct Hframe as [Hcurrent_vis_mid Hframe].
    destruct Hframe as [Hfa_current_mid Hframe].
    destruct Hframe as [Hfane_current_mid Hframe].
    destruct Hframe as [Hdfn_ancestor_current_mid Hframe].
    destruct Hframe as [Hnot_done_current Hframe].
    destruct Hframe as [Hbelow_current_mid Hstack_frame_current_mid].
    destruct Hshape_mid as [Hwf_mid [_ [Hancestor_vis_mid _]]].
    destruct Hwf_mid as [Hstack_vis_mid _].
    destruct Hentry as [[_ Hnext_notvis] _].
    assert (Hloop_next: LoopInv next ∅ s_after).
    { pose proof (preloop_initializes_loop_inv next) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_mid retv s_after Hentry_for_loop Hexec). }
    assert (Hlow_frame_after:
              ParentLowFrame ancestor ancestor_done s_before s_after).
    { eapply preloop_preserves_nested_parent_low_frame; eauto. }
    assert (Hshape_after:
              LoopCoreShape ancestor
                (done_after ancestor_done current) s_after).
    { eapply preloop_preserves_nested_parent_shape; eauto. }
    assert (Haux_after: LoopAuxFacts ancestor s_after).
    { eapply preloop_preserves_loop_aux_facts_for_entry; eauto. }
    assert (Hclosed_after: Closed s_after).
    { pose proof (preloop_preserves_closed next) as Hhoare.
      unfold Hoare in Hhoare.
      destruct Hentry_for_closed as [Hwf_pre [Hsettled [Hclosed [_]]]].
      exact (Hhoare s_mid retv s_after
                    (conj Hwf_pre (conj Hsettled Hclosed))
                    Hexec). }
    assert (Htree_after: TreeEdgesAreGraphEdges s_after).
    { destruct Hshape_after as [_ [Htree_after _]].
      exact Htree_after. }
    assert (Hcurrent_vis_after: Visited current s_after).
    { pose proof (preloop_keep_visited next current) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_mid retv s_after Hcurrent_vis_mid Hexec). }
    assert (Hfa_current_pres:
              fa s_after current = fa s_mid current).
    { pose proof (preloop_preserves_any_fa
                    next current (fa s_mid current)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s_mid retv s_after eq_refl Hexec). }
    assert (Hfa_current_after: fa s_after current = ancestor).
    { rewrite Hfa_current_pres. exact Hfa_current_mid. }
    assert (Hfane_current_after: fa s_after current <> current).
    { intros Hfa_eq_current.
      apply Hfane_current_mid.
      rewrite <- Hfa_current_pres. exact Hfa_eq_current. }
    assert (Hnext_ne_ancestor: next <> ancestor).
    { intros Hnext_eq_ancestor. apply Hnext_notvis.
      rewrite Hnext_eq_ancestor. exact Hancestor_vis_mid. }
    assert (Hnext_ne_current: next <> current).
    { intros Hnext_eq_current. apply Hnext_notvis.
      rewrite Hnext_eq_current. exact Hcurrent_vis_mid. }
    assert (Hdfn_ancestor_eq:
              dfn s_after ancestor = dfn s_mid ancestor).
    { eapply preloop_preserves_dfn_of_visited; eauto. }
    assert (Hdfn_current_eq:
              dfn s_after current = dfn s_mid current).
    { eapply preloop_preserves_dfn_of_visited; eauto. }
    assert (Hdfn_ancestor_current_after:
              dfn s_after ancestor < dfn s_after current).
    { lia. }
    assert (Hbelow_current_after:
              ParentOldCandidatesBelowChild
                ancestor current ancestor_done s_before s_after).
    { eapply preloop_preserves_nested_parent_old_candidates_below_child;
        eauto. }
    assert (Hstack_frame_current_after:
              ParentTraversalStackFrame ancestor current s_before s_after).
    { exact (preloop_preserves_parent_traversal_stack_frame_nested
               ancestor current next s_before s_mid s_after retv
               Hnext_ne_ancestor Hnext_ne_current Hnext_notvis
               Hstack_vis_mid Hexec Hstack_frame_current_mid). }
    split; [exact Hloop_next |].
    unfold ParentFrameForChild.
    split; [exact Hlow_frame_after |].
    split; [exact Hshape_after |].
    split; [exact Haux_after |].
    split; [exact Hclosed_after |].
    split; [exact Htree_after |].
    split; [exact Hedge_ancestor_current |].
    split; [exact Hcurrent_vis_after |].
    split; [exact Hfa_current_after |].
    split; [exact Hfane_current_after |].
    split; [exact Hdfn_ancestor_current_after |].
    split; [exact Hnot_done_current |].
    exact (conj Hbelow_current_after Hstack_frame_current_after).
  Qed.

  Lemma preloop_preserves_nested_frame_disjoint
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St):
    Hoare
      (NestedFramePre ancestor current loop_root next
         ancestor_done loop_done s_before)
      (preloop next)
      (fun _ s =>
         NestedFrameDisjoint ancestor current next ancestor_done s).
  Proof.
    unfold Hoare.
    intros s_mid retv s_after Hnested Hexec.
    pose proof Hnested as Hnested_all.
    pose proof (nested_frame_pre_parent_recursive_pre
                  ancestor current loop_root next ancestor_done loop_done
                  s_before s_mid Hnested_all) as Hrecursive_pre.
    destruct Hnested as
      [Hloop [Hframe [Hdisjoint [Hedge [Hnot_done [Hentry [Hfa_next Hfane_next]]]]]]].
    destruct Hdisjoint as [Hreach_current_loop Hno_old].
    destruct Hentry as [[_ Hnext_notvis] _].
    destruct Hloop as [_ [Hshape_loop _]].
    destruct Hshape_loop as [_ [_ [Hloop_vis _]]].
    destruct Hframe as
      [_ [Hshape_ancestor [_ [_ [_ [_ [_ [_ [_ _]]]]]]]]].
    destruct Hshape_ancestor as [_ [_ [_ [_ [Hdone_vis _]]]]].
    split.
    - assert (Hreach_current_loop_after:
                dg_reachable (state_to_dfs_tree g s_after root)
                             current loop_root).
      { eapply preloop_tree_reachable_pre_lift; eauto. }
      assert (Hfa_next_after: fa s_after next = loop_root).
      { pose proof (preloop_preserves_any_fa
                      next next (fa s_mid next)) as Hhoare.
        unfold Hoare in Hhoare.
        rewrite (Hhoare s_mid retv s_after eq_refl Hexec).
        exact Hfa_next. }
      assert (Hnext_vis_after: Visited next s_after).
      { pose proof (preloop_self_visited next) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s_mid retv s_after I Hexec). }
      assert (Hstep_loop_next:
                tree_edge s_after loop_root next).
      { assert (Hfane_next_after: fa s_after next <> next).
        { rewrite Hfa_next_after. rewrite Hfa_next in Hfane_next.
          exact Hfane_next. }
        eapply tree_step_char_backward; eauto. }
      eapply dg_reachable_trans.
      + exact Hreach_current_loop_after.
      + apply dg_reachable_step. exact Hstep_loop_next.
    - intros old_child Hdone_old Hfa_old_after Hfane_old_after Hreach_old_next.
      eapply preloop_nested_done_child_not_reach_next; eauto.
  Qed.

  Lemma parent_frame_child_active
        (parent child: V) (done: V -> Prop)
        (s_before s: St):
    ParentFrameForChild parent child done s_before s ->
    Active child s.
  Proof.
    intros Hframe.
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [Hbelow_child _].
    pose proof (Hbelow_child parent
                  (partial_low_candidate_root parent done s_before))
      as Hparent_below_child.
    eapply rest_stack_root_active; eauto.
  Qed.

  Lemma preloop_preserves_nested_rest_stack
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St):
    Hoare
      (NestedFramePre ancestor current loop_root next
         ancestor_done loop_done s_before)
      (preloop next)
      (fun _ s => RestStack next s current).
  Proof.
    unfold Hoare.
    intros s_mid retv s_after Hnested Hexec.
    destruct Hnested as [_ [Hframe _]].
    assert (Hcurrent_active: Active current s_mid).
    { eapply parent_frame_child_active; eauto. }
    pose proof (preloop_old_stack_element_rest next current) as Hhoare.
    unfold Hoare in Hhoare.
    exact (Hhoare s_mid retv s_after Hcurrent_active Hexec).
  Qed.

  Lemma preloop_preserves_nested_parent_context
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St):
    Hoare
      (NestedFramePre ancestor current loop_root next
         ancestor_done loop_done s_before)
      (preloop next)
      (fun _ s =>
         LoopInv next ∅ s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current next ancestor_done s).
  Proof.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s =>
                 LoopInv next ∅ s /\
                 ParentFrameForChild ancestor current ancestor_done s_before s).
      - apply preloop_preserves_nested_parent_frame.
      - apply preloop_preserves_nested_frame_disjoint. }
    intros _ s [[Hloop Hframe] Hdisjoint].
    exact (conj Hloop (conj Hframe Hdisjoint)).
  Qed.

  Lemma preloop_preserves_nested_parent_context_with_rest
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St):
    Hoare
      (NestedFramePre ancestor current loop_root next
         ancestor_done loop_done s_before)
      (preloop next)
      (fun _ s =>
         LoopInv next ∅ s /\
         LoopTraversalComplete next ∅ s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current next ancestor_done s /\
         RestStack next s current).
  Proof.
    unfold Hoare.
    intros s_mid retv s_after Hnested Hexec.
    pose proof Hnested as Hnested_for_ctx.
    pose proof Hnested as Hnested_for_rest.
    destruct Hnested as [_ [_ [_ [_ [_ [Hentry _]]]]]].
    pose proof (preloop_preserves_nested_parent_context
                  ancestor current loop_root next ancestor_done loop_done
                  s_before) as Hctx_hoare.
    unfold Hoare in Hctx_hoare.
    destruct (Hctx_hoare s_mid retv s_after
                          Hnested_for_ctx Hexec)
      as [Hloop [Hframe Hdisjoint]].
    pose proof (preloop_initializes_loop_traversal_complete_empty next)
      as Htraversal_hoare.
    unfold Hoare in Htraversal_hoare.
    assert (Htraversal: LoopTraversalComplete next ∅ s_after).
    { exact (Htraversal_hoare s_mid retv s_after Hentry Hexec). }
    pose proof (preloop_preserves_nested_rest_stack
                  ancestor current loop_root next ancestor_done loop_done
                  s_before) as Hrest_hoare.
    unfold Hoare in Hrest_hoare.
    assert (Hrest: RestStack next s_after current).
    { exact (Hrest_hoare s_mid retv s_after
                         Hnested_for_rest Hexec). }
    exact (conj Hloop
            (conj Htraversal
              (conj Hframe
                (conj Hdisjoint Hrest)))).
  Qed.

  (* edge loop *)

  Lemma parent_frame_nested_disjoint_self
        (parent child: V) (done: V -> Prop)
        (s_before s: St):
    ParentFrameForChild parent child done s_before s ->
    NestedFrameDisjoint parent child child done s.
  Proof.
    intros Hframe.
    destruct Hframe as [_ Hframe].
    destruct Hframe as [Hshape Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [Hchild_vis Hframe].
    destruct Hframe as [Hfa_child Hframe].
    destruct Hframe as [Hfane_child Hframe].
    destruct Hframe as [Hdfn_parent_child Hnot_done_child].
    destruct Hnot_done_child as [Hnot_done_child Hbelow_child].
    destruct Hbelow_child as [Hbelow_child Hstack_frame_child].
    destruct Hshape as
      [Hwf [_ [_ [Hdone_edge [Hdone_vis _]]]]].
    split.
    - unfold dg_reachable.
      apply Coq.Relations.Relation_Operators.rt_refl.
    - intros old_child Hdone_old Hfa_old Hfane_old Hreach.
      assert (Hold_vis: Visited old_child s).
      { apply Hdone_vis. apply done_after_intro_old. exact Hdone_old. }
      assert (Hold_ne_child: old_child <> child).
      { intros Hold_eq_child. apply Hnot_done_child.
        rewrite <- Hold_eq_child. exact Hdone_old. }
      destruct (dg_reachable_vertex_path
                  (state_to_dfs_tree g s root)
                  old_child child Hreach)
        as [path Hpath].
      assert (Hchild_not_ne: ~ (child = child -> False)).
      { intros Hneq. apply Hneq. reflexivity. }
      destruct (dg_vertex_path_last_exit_from_pred
                  (state_to_dfs_tree g s root)
                  (fun z => z = child -> False)
                  old_child child path
                  Hold_ne_child Hchild_not_ne Hpath)
        as [a [b [suffix
          [Ha_ne_child [Hb_not_ne_child
            [Hstep_ab [Hreach_old_a [_ _]]]]]]]].
      assert (Hb_eq_child: b = child).
      { apply NNPP. exact Hb_not_ne_child. }
      subst b.
      apply tree_step_char in Hstep_ab as [Hfa_child_from_a [_ _]].
      assert (Ha_eq_parent: a = parent).
      { rewrite Hfa_child in Hfa_child_from_a. symmetry. exact Hfa_child_from_a. }
      subst a.
      assert (Hparent_lt_old:
                dfn s parent < dfn s old_child).
      { destruct Hwf as [_ [_ [Hdfn_valid _]]].
        eapply fa_parent_dfn_lt.
        - exact Hfa_old.
        - exact Hfane_old.
        - apply Hdone_edge. apply done_after_intro_old. exact Hdone_old.
        - exact Hold_vis.
        - exact Hdfn_valid. }
      assert (Hreach_old_parent:
                dg_reachable (state_to_dfs_tree g s root)
                             old_child parent).
      { rewrite <- Hfa_child. exact Hreach_old_a. }
      pose proof (tree_reachable_dfn_monotone
                    s old_child parent Hwf Hreach_old_parent)
        as Hold_le_parent.
      lia.
  Qed.

  Lemma nested_frame_disjoint_loop_root_not_ancestor
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (s_before s: St):
    ParentFrameForChild ancestor current ancestor_done s_before s ->
    NestedFrameDisjoint ancestor current loop_root ancestor_done s ->
    loop_root <> ancestor.
  Proof.
    intros Hframe [Hreach_current_loop _] Hloop_eq.
    destruct Hframe as
      [_ [Hshape [_ [_ [_ [_ [_ [_ [_ Hdfn_ancestor_current]]]]]]]]].
    destruct Hdfn_ancestor_current as [Hdfn_ancestor_current _].
    destruct Hshape as [Hwf _].
    subst loop_root.
    pose proof (tree_reachable_dfn_monotone
                  s current ancestor Hwf Hreach_current_loop)
      as Hdfn_current_ancestor.
    lia.
  Qed.

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

  Lemma update_low_preserves_loop_core_shape_any
        (center: V) (done: V -> Prop) (u: V) (n: nat):
    Hoare
      (LoopCoreShape center done)
      (update_low u n)
      (fun _ s => LoopCoreShape center done s).
  Proof.
    unfold LoopCoreShape.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma update_low_preserves_nested_frame_disjoint
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (u: V) (n: nat):
    Hoare
      (NestedFrameDisjoint ancestor current loop_root ancestor_done)
      (update_low u n)
      (fun _ s =>
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
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

  Lemma update_low_preserves_parent_low_frame
        (parent child: V) (done: V -> Prop) (s_before: St) (n: nat):
    Hoare
      (fun s: St =>
         ParentLowFrame parent done s_before s /\
         parent <> child)
      (update_low child n)
      (fun _ s => ParentLowFrame parent done s_before s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl.
      destruct H as [[Hlow_eq [Hframe_fwd Hframe_bound]] Hparent_ne_child].
      unfold ParentLowFrame.
      split.
      + change ((if equiv_decb parent child then n else low s0 parent) =
                low s_before parent).
        unfold equiv_decb.
        destruct (equiv_dec parent child) as [Hparent_eq_child | _].
        * exfalso. apply Hparent_ne_child. exact Hparent_eq_child.
        * exact Hlow_eq.
      + split.
        * intros target Hcandidate_before.
          destruct (Hframe_fwd target Hcandidate_before)
            as [Hcandidate_after Hdfn_eq].
          split.
          -- unfold PartialLowCandidate, PartialActiveTarget in *.
             simpl in *. exact Hcandidate_after.
          -- exact Hdfn_eq.
        * intros target Hcandidate_after.
          apply Hframe_bound.
          unfold PartialLowCandidate, PartialActiveTarget in *.
          simpl in *. exact Hcandidate_after.
    - destruct H1 as [Heq _]. subst s.
      exact (proj1 H).
  Qed.

  Lemma update_low_preserves_parent_old_candidates_below_child
        (parent child target: V) (done: V -> Prop)
        (s_before: St) (n: nat):
    Hoare
      (ParentOldCandidatesBelowChild parent child done s_before)
      (update_low target n)
      (fun _ s =>
         ParentOldCandidatesBelowChild parent child done s_before s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma update_low_preserves_parent_traversal_stack_frame
        (parent child target: V) (s_before: St) (n: nat):
    Hoare
      (ParentTraversalStackFrame parent child s_before)
      (update_low target n)
      (fun _ s =>
         ParentTraversalStackFrame parent child s_before s).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma update_low_preserves_parent_frame_for_child
        (parent child: V) (done: V -> Prop) (s_before: St) (n: nat):
    Hoare
      (ParentFrameForChild parent child done s_before)
      (update_low child n)
      (fun _ s => ParentFrameForChild parent child done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 Hframe Hexec.
    destruct Hframe as [Hlow_frame Hframe].
    destruct Hframe as [Hshape Hframe].
    destruct Hframe as [Haux Hframe].
    destruct Hframe as [Hclosed Hframe].
    destruct Hframe as [Htree Hframe].
    destruct Hframe as [Hedge Hframe].
    destruct Hframe as [Hchild_vis Hframe].
    destruct Hframe as [Hfa_child Hframe].
    destruct Hframe as [Hfane_child Hframe].
    destruct Hframe as [Hdfn_parent_child Hnot_done_child].
    destruct Hnot_done_child as [Hnot_done_child Hbelow_child].
    destruct Hbelow_child as [Hbelow_child Hstack_frame_child].
    assert (Hparent_ne_child: parent <> child).
    { intros Hparent_eq_child. subst child. lia. }
    assert (Hlow_frame_after:
              ParentLowFrame parent done s_before s2).
    { pose proof (update_low_preserves_parent_low_frame
                    parent child done s_before n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hlow_frame Hparent_ne_child) Hexec). }
    assert (Hbelow_child_after:
              ParentOldCandidatesBelowChild parent child done s_before s2).
    { pose proof (update_low_preserves_parent_old_candidates_below_child
                    parent child child done s_before n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hbelow_child Hexec). }
    assert (Hstack_frame_child_after:
              ParentTraversalStackFrame parent child s_before s2).
    { pose proof (update_low_preserves_parent_traversal_stack_frame
                    parent child child s_before n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hstack_frame_child Hexec). }
    assert (Hshape_after:
              LoopCoreShape parent (done_after done child) s2).
    { pose proof (update_low_preserves_loop_core_shape
                    parent (done_after done child) child n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 (conj Hshape Hchild_vis) Hexec). }
    assert (Haux_after: LoopAuxFacts parent s2).
    { pose proof (update_low_preserves_loop_aux_facts parent child n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Haux Hexec). }
    assert (Hclosed_after: Closed s2).
    { pose proof (update_low_preserves_closed child n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hclosed Hexec). }
    assert (Htree_after: TreeEdgesAreGraphEdges s2).
    { pose proof (update_low_preserves_tree_edges_are_graph_edges child n)
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Htree Hexec). }
    assert (Hchild_vis_after: Visited child s2).
    { pose proof (update_low_keep_visited child child n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hchild_vis Hexec). }
    assert (Hfa_child_pres:
              fa s2 child = fa s1 child).
    { pose proof (update_low_keep_fa child child n (fa s1 child)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hfa_child_after: fa s2 child = parent).
    { rewrite Hfa_child_pres. exact Hfa_child. }
    assert (Hfane_child_after: fa s2 child <> child).
    { intros Hfa_eq_child.
      apply Hfane_child.
      rewrite <- Hfa_child_pres. exact Hfa_eq_child. }
    assert (Hdfn_parent_pres:
              dfn s2 parent = dfn s1 parent).
    { pose proof (update_low_keep_dfn child parent n (dfn s1 parent))
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hdfn_child_pres:
              dfn s2 child = dfn s1 child).
    { pose proof (update_low_keep_dfn child child n (dfn s1 child))
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hdfn_parent_child_after:
              dfn s2 parent < dfn s2 child).
    { lia. }
    unfold ParentFrameForChild.
    split; [exact Hlow_frame_after |].
    split; [exact Hshape_after |].
    split; [exact Haux_after |].
    split; [exact Hclosed_after |].
    split; [exact Htree_after |].
    split; [exact Hedge |].
    split; [exact Hchild_vis_after |].
    split; [exact Hfa_child_after |].
    split; [exact Hfane_child_after |].
    split; [exact Hdfn_parent_child_after |].
    split; [exact Hnot_done_child |].
    exact (conj Hbelow_child_after Hstack_frame_child_after).
  Qed.

  Lemma update_low_preserves_parent_frame_for_child_at
        (parent child target: V) (done: V -> Prop)
        (s_before: St) (n: nat):
    Hoare
      (fun s: St =>
         ParentFrameForChild parent child done s_before s /\
         target <> parent)
      (update_low target n)
      (fun _ s => ParentFrameForChild parent child done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hframe Htarget_ne_parent] Hexec.
    destruct Hframe as [Hlow_frame Hframe].
    destruct Hframe as [Hshape Hframe].
    destruct Hframe as [Haux Hframe].
    destruct Hframe as [Hclosed Hframe].
    destruct Hframe as [Htree Hframe].
    destruct Hframe as [Hedge Hframe].
    destruct Hframe as [Hchild_vis Hframe].
    destruct Hframe as [Hfa_child Hframe].
    destruct Hframe as [Hfane_child Hframe].
    destruct Hframe as [Hdfn_parent_child Hnot_done_child].
    destruct Hnot_done_child as [Hnot_done_child Hbelow_child].
    destruct Hbelow_child as [Hbelow_child Hstack_frame_child].
    assert (Hparent_ne_target: parent <> target).
    { intros Hparent_eq_target. apply Htarget_ne_parent.
      symmetry. exact Hparent_eq_target. }
    assert (Hlow_frame_after:
              ParentLowFrame parent done s_before s2).
    { pose proof (update_low_preserves_parent_low_frame
                    parent target done s_before n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hlow_frame Hparent_ne_target) Hexec). }
    assert (Hbelow_child_after:
              ParentOldCandidatesBelowChild parent child done s_before s2).
    { pose proof (update_low_preserves_parent_old_candidates_below_child
                    parent child target done s_before n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hbelow_child Hexec). }
    assert (Hstack_frame_child_after:
              ParentTraversalStackFrame parent child s_before s2).
    { pose proof (update_low_preserves_parent_traversal_stack_frame
                    parent child target s_before n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hstack_frame_child Hexec). }
    assert (Hshape_after:
              LoopCoreShape parent (done_after done child) s2).
    { pose proof (update_low_preserves_loop_core_shape_any
                    parent (done_after done child) target n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hshape Hexec). }
    assert (Haux_after: LoopAuxFacts parent s2).
    { pose proof (update_low_preserves_loop_aux_facts parent target n)
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Haux Hexec). }
    assert (Hclosed_after: Closed s2).
    { pose proof (update_low_preserves_closed target n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hclosed Hexec). }
    assert (Htree_after: TreeEdgesAreGraphEdges s2).
    { pose proof (update_low_preserves_tree_edges_are_graph_edges target n)
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Htree Hexec). }
    assert (Hchild_vis_after: Visited child s2).
    { pose proof (update_low_keep_visited target child n) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hchild_vis Hexec). }
    assert (Hfa_child_pres:
              fa s2 child = fa s1 child).
    { pose proof (update_low_keep_fa target child n (fa s1 child)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hfa_child_after: fa s2 child = parent).
    { rewrite Hfa_child_pres. exact Hfa_child. }
    assert (Hfane_child_after: fa s2 child <> child).
    { intros Hfa_eq_child.
      apply Hfane_child.
      rewrite <- Hfa_child_pres. exact Hfa_eq_child. }
    assert (Hdfn_parent_pres:
              dfn s2 parent = dfn s1 parent).
    { pose proof (update_low_keep_dfn target parent n (dfn s1 parent))
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hdfn_child_pres:
              dfn s2 child = dfn s1 child).
    { pose proof (update_low_keep_dfn target child n (dfn s1 child))
        as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hdfn_parent_child_after:
              dfn s2 parent < dfn s2 child).
    { lia. }
    unfold ParentFrameForChild.
    split; [exact Hlow_frame_after |].
    split; [exact Hshape_after |].
    split; [exact Haux_after |].
    split; [exact Hclosed_after |].
    split; [exact Htree_after |].
    split; [exact Hedge |].
    split; [exact Hchild_vis_after |].
    split; [exact Hfa_child_after |].
    split; [exact Hfane_child_after |].
    split; [exact Hdfn_parent_child_after |].
    split; [exact Hnot_done_child |].
    exact (conj Hbelow_child_after Hstack_frame_child_after).
  Qed.

  Lemma get_low_update_low_preserves_nested_parent_context
        (ancestor current loop_root target: V)
        (ancestor_done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s)
      (lv <- get' (fun s => low s target);; update_low loop_root lv)
      (fun _ s =>
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    eapply Hoare_conj with
      (Q1 := fun _ s =>
               ParentFrameForChild ancestor current ancestor_done s_before s).
    - eapply Hoare_conseq_pre.
      2: apply update_low_preserves_parent_frame_for_child_at.
      intros s1 [Hs1 _]. subst s1.
      destruct H as [Hframe Hdisjoint].
      assert (Hloop_ne_ancestor: loop_root <> ancestor).
      { eapply nested_frame_disjoint_loop_root_not_ancestor; eauto. }
      exact (conj Hframe Hloop_ne_ancestor).
    - eapply Hoare_conseq_pre.
      2: apply update_low_preserves_nested_frame_disjoint.
      intros s1 [Hs1 _]. subst s1.
      destruct H as [_ Hdisjoint]. exact Hdisjoint.
  Qed.

  Lemma get_dfn_update_low_preserves_nested_parent_context
        (ancestor current loop_root target: V)
        (ancestor_done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s)
      (dv <- get' (fun s => dfn s target);; update_low loop_root dv)
      (fun _ s =>
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    eapply Hoare_conj with
      (Q1 := fun _ s =>
               ParentFrameForChild ancestor current ancestor_done s_before s).
    - eapply Hoare_conseq_pre.
      2: apply update_low_preserves_parent_frame_for_child_at.
      intros s1 [Hs1 _]. subst s1.
      destruct H as [Hframe Hdisjoint].
      assert (Hloop_ne_ancestor: loop_root <> ancestor).
      { eapply nested_frame_disjoint_loop_root_not_ancestor; eauto. }
      exact (conj Hframe Hloop_ne_ancestor).
    - eapply Hoare_conseq_pre.
      2: apply update_low_preserves_nested_frame_disjoint.
      intros s1 [Hs1 _]. subst s1.
      destruct H as [_ Hdisjoint]. exact Hdisjoint.
  Qed.

  Lemma get_low_update_low_preserves_parent_frame_for_child
        (parent child target: V) (done: V -> Prop) (s_before: St):
    Hoare
      (ParentFrameForChild parent child done s_before)
      (lv <- get' (fun s => low s target);; update_low child lv)
      (fun _ s => ParentFrameForChild parent child done s_before s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_parent_frame_for_child.
    intros s1 Hs1. destruct Hs1 as [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma get_dfn_update_low_preserves_parent_frame_for_child
        (parent child target: V) (done: V -> Prop) (s_before: St):
    Hoare
      (ParentFrameForChild parent child done s_before)
      (dv <- get' (fun s => dfn s target);; update_low child dv)
      (fun _ s => ParentFrameForChild parent child done s_before s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_parent_frame_for_child.
    intros s1 Hs1. destruct Hs1 as [Hs1 _]. subst s1. exact H.
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

  Lemma set_fa_state_pending_preserves_nested_frame_disjoint
        (ancestor current loop_root a p: V)
        (ancestor_done: V -> Prop) (s: St):
    (forall old_child, ancestor_done old_child -> Visited old_child s) ->
    ~ Visited a s ->
    NestedFrameDisjoint ancestor current loop_root ancestor_done s ->
    NestedFrameDisjoint ancestor current loop_root ancestor_done
      (set_fa_state s a p).
  Proof.
    intros Hdone_vis Hnotvis [Hreach_current_loop Hno_old].
    split.
    - apply (proj2 (set_fa_pending_tree_reachable_iff
                      s a p current loop_root Hnotvis)).
      exact Hreach_current_loop.
    - intros old_child Hdone_old Hfa_old_post Hfane_old_post Hreach_post.
      assert (Hold_vis: Visited old_child s).
      { apply Hdone_vis. exact Hdone_old. }
      assert (Hold_ne_a: old_child <> a).
      { intros Hold_eq_a. apply Hnotvis.
        rewrite <- Hold_eq_a. exact Hold_vis. }
      apply (Hno_old old_child Hdone_old).
      + rewrite set_fa_state_keep_other_fa in Hfa_old_post; auto.
      + rewrite set_fa_state_keep_other_fa in Hfane_old_post; auto.
      + apply (proj1 (set_fa_pending_tree_reachable_iff
                        s a p old_child loop_root Hnotvis)).
        exact Hreach_post.
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

  Lemma set_fa_pending_preserves_loop_traversal_complete
        (center: V) (done: V -> Prop) (s: St) (v p: V):
    ~ Visited v s ->
    (forall a, done a -> Visited a s) ->
    LoopTraversalComplete center done s ->
    LoopTraversalComplete center done (set_fa_state s v p).
  Proof.
    intros Hnotvis Hdone_vis [Hno Hcut].
    split.
    - intros x y Hpopped Hedge Hnotvis_y.
      simpl in Hpopped, Hnotvis_y.
      exact (Hno x y Hpopped Hedge Hnotvis_y).
    - intros x b Hpopped Hedge Hrest.
      simpl in Hpopped, Hrest.
      destruct (Hcut x b Hpopped Hedge Hrest) as
        [[Hx Hnot_done] | [target [Hcandidate Hdfn]]].
      + left. split; [exact Hx | exact Hnot_done].
      + right. exists target. split; [| simpl; exact Hdfn].
        apply (proj2 (set_fa_pending_partial_low_candidate_iff
                        center done s v p target Hnotvis Hdone_vis)).
        exact Hcandidate.
  Qed.

  Lemma set_fa_pending_preserves_loop_traversal_complete_cmd
        (center: V) (done: V -> Prop) (v p: V):
    Hoare
      (fun s: St =>
         ~ Visited v s /\
         (forall a, done a -> Visited a s) /\
         LoopTraversalComplete center done s)
      (set_fa v p)
      (fun _ s => LoopTraversalComplete center done s).
  Proof.
    unfold set_fa.
    intro_state. hoare_auto_s.
    subst s.
    destruct H as [Hnotvis [Hdone_vis Htraversal]].
    apply set_fa_pending_preserves_loop_traversal_complete; auto.
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

  Lemma set_fa_state_pending_preserves_parent_low_frame
        (parent child a p: V) (done: V -> Prop)
        (s_before s: St):
    ParentLowFrame parent done s_before s ->
    LoopCoreShape parent (done_after done child) s ->
    ~ Visited a s ->
    ParentLowFrame parent done s_before (set_fa_state s a p).
  Proof.
    intros [Hlow_eq [Hframe_fwd Hframe_bound]]
           [_ [_ [_ [_ [Hdone_after_vis _]]]]] Hnotvis.
    assert (Hdone_vis: forall x, done x -> Visited x s).
    { intros x Hdone. apply Hdone_after_vis.
      apply done_after_intro_old. exact Hdone. }
    unfold ParentLowFrame.
    split.
    - simpl. exact Hlow_eq.
    - split.
      + intros b Hcandidate_before.
        destruct (Hframe_fwd b Hcandidate_before)
          as [Hcandidate_s Hdfn_eq].
        split.
        * apply (proj2 (set_fa_pending_partial_low_candidate_iff
                          parent done s a p b Hnotvis Hdone_vis)).
          exact Hcandidate_s.
        * simpl. exact Hdfn_eq.
      + intros b Hcandidate_after.
        apply Hframe_bound.
        apply (proj1 (set_fa_pending_partial_low_candidate_iff
                        parent done s a p b Hnotvis Hdone_vis)).
        exact Hcandidate_after.
  Qed.

  Lemma set_fa_state_pending_preserves_parent_old_candidates_below_child
        (parent child a p: V) (done: V -> Prop)
        (s_before s: St):
    ParentOldCandidatesBelowChild parent child done s_before s ->
    ParentOldCandidatesBelowChild parent child done s_before
      (set_fa_state s a p).
  Proof.
    intros Hbelow.
    unfold ParentOldCandidatesBelowChild in *.
    simpl. exact Hbelow.
  Qed.

  Lemma set_fa_state_pending_preserves_parent_traversal_stack_frame
        (parent child a p: V) (s_before s: St):
    ParentTraversalStackFrame parent child s_before s ->
    ParentTraversalStackFrame parent child s_before (set_fa_state s a p).
  Proof.
    intros Hstack_frame.
    unfold ParentTraversalStackFrame in *.
    simpl. exact Hstack_frame.
  Qed.

  Lemma set_fa_pending_preserves_parent_low_frame
        (parent child a p: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         ParentLowFrame parent done s_before s /\
         LoopCoreShape parent (done_after done child) s /\
         ~ Visited a s)
      (set_fa a p)
      (fun _ s => ParentLowFrame parent done s_before s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s.
    destruct H as [Hlow_frame [Hshape Hnotvis]].
    exact (set_fa_state_pending_preserves_parent_low_frame
             parent child a p done s_before s0
             Hlow_frame Hshape Hnotvis).
  Qed.

  Lemma set_fa_state_pending_preserves_parent_frame_for_child
        (parent child a: V) (done: V -> Prop)
        (s_before s: St):
    ParentFrameForChild parent child done s_before s ->
    ~ Visited a s ->
    ParentFrameForChild parent child done s_before (set_fa_state s a child).
  Proof.
    intros Hframe Hnotvis.
    destruct Hframe as [Hlow_frame Hframe].
    destruct Hframe as [Hshape Hframe].
    destruct Hframe as [Haux Hframe].
    destruct Hframe as [Hclosed Hframe].
    destruct Hframe as [Htree Hframe].
    destruct Hframe as [Hedge Hframe].
    destruct Hframe as [Hchild_vis Hframe].
    destruct Hframe as [Hfa_child Hframe].
    destruct Hframe as [Hfane_child Hframe].
    destruct Hframe as [Hdfn_parent_child Hnot_done_child].
    destruct Hnot_done_child as [Hnot_done_child Hbelow_child].
    destruct Hbelow_child as [Hbelow_child Hstack_frame_child].
    assert (Hchild_ne_a: child <> a).
    { intros Hchild_eq_a. apply Hnotvis.
      rewrite <- Hchild_eq_a. exact Hchild_vis. }
    assert (Hlow_frame_after:
              ParentLowFrame parent done s_before (set_fa_state s a child)).
    { exact (set_fa_state_pending_preserves_parent_low_frame
               parent child a child done s_before s
               Hlow_frame Hshape Hnotvis). }
    assert (Hbelow_child_after:
              ParentOldCandidatesBelowChild parent child done s_before
                (set_fa_state s a child)).
    { exact (set_fa_state_pending_preserves_parent_old_candidates_below_child
               parent child a child done s_before s Hbelow_child). }
    assert (Hstack_frame_child_after:
              ParentTraversalStackFrame parent child s_before
                (set_fa_state s a child)).
    { exact (set_fa_state_pending_preserves_parent_traversal_stack_frame
               parent child a child s_before s Hstack_frame_child). }
    assert (Hshape_after:
              LoopCoreShape parent (done_after done child)
                (set_fa_state s a child)).
    { exact (set_fa_pending_preserves_loop_core_shape
               parent (done_after done child) s a child
               Hchild_vis Hnotvis Hshape). }
    assert (Haux_after:
              LoopAuxFacts parent (set_fa_state s a child)).
    { unfold LoopAuxFacts, OrderFacts in *. simpl. exact Haux. }
    assert (Hclosed_after: Closed (set_fa_state s a child)).
    { apply set_fa_pending_preserves_closed. exact Hclosed. }
    assert (Htree_after: TreeEdgesAreGraphEdges (set_fa_state s a child)).
    { exact (set_fa_pending_preserves_tree_edges_are_graph_edges
               s a child Hnotvis Htree). }
    assert (Hchild_vis_after: Visited child (set_fa_state s a child)).
    { simpl. exact Hchild_vis. }
    assert (Hfa_child_after: fa (set_fa_state s a child) child = parent).
    { rewrite set_fa_state_keep_other_fa; auto. }
    assert (Hfane_child_after: fa (set_fa_state s a child) child <> child).
    { rewrite set_fa_state_keep_other_fa; auto. }
    assert (Hdfn_parent_child_after:
              dfn (set_fa_state s a child) parent <
              dfn (set_fa_state s a child) child).
    { simpl. exact Hdfn_parent_child. }
    unfold ParentFrameForChild.
    split; [exact Hlow_frame_after |].
    split; [exact Hshape_after |].
    split; [exact Haux_after |].
    split; [exact Hclosed_after |].
    split; [exact Htree_after |].
    split; [exact Hedge |].
    split; [exact Hchild_vis_after |].
    split; [exact Hfa_child_after |].
    split; [exact Hfane_child_after |].
    split; [exact Hdfn_parent_child_after |].
    split; [exact Hnot_done_child |].
    exact (conj Hbelow_child_after Hstack_frame_child_after).
  Qed.

  Lemma set_fa_pending_preserves_parent_frame_for_child
        (parent child a: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         ParentFrameForChild parent child done s_before s /\
         ~ Visited a s)
      (set_fa a child)
      (fun _ s => ParentFrameForChild parent child done s_before s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s.
    destruct H as [Hframe Hnotvis].
    exact (set_fa_state_pending_preserves_parent_frame_for_child
             parent child a done s_before s0 Hframe Hnotvis).
  Qed.

  Lemma set_fa_state_pending_preserves_parent_frame_for_child_at
        (parent child a p: V) (done: V -> Prop)
        (s_before s: St):
    Visited p s ->
    ParentFrameForChild parent child done s_before s ->
    ~ Visited a s ->
    ParentFrameForChild parent child done s_before (set_fa_state s a p).
  Proof.
    intros Hpvis Hframe Hnotvis.
    destruct Hframe as [Hlow_frame Hframe].
    destruct Hframe as [Hshape Hframe].
    destruct Hframe as [Haux Hframe].
    destruct Hframe as [Hclosed Hframe].
    destruct Hframe as [Htree Hframe].
    destruct Hframe as [Hedge Hframe].
    destruct Hframe as [Hchild_vis Hframe].
    destruct Hframe as [Hfa_child Hframe].
    destruct Hframe as [Hfane_child Hframe].
    destruct Hframe as [Hdfn_parent_child Hnot_done_child].
    destruct Hnot_done_child as [Hnot_done_child Hbelow_child].
    destruct Hbelow_child as [Hbelow_child Hstack_frame_child].
    assert (Hchild_ne_a: child <> a).
    { intros Hchild_eq_a. apply Hnotvis.
      rewrite <- Hchild_eq_a. exact Hchild_vis. }
    assert (Hlow_frame_after:
              ParentLowFrame parent done s_before (set_fa_state s a p)).
    { exact (set_fa_state_pending_preserves_parent_low_frame
               parent child a p done s_before s
               Hlow_frame Hshape Hnotvis). }
    assert (Hbelow_child_after:
              ParentOldCandidatesBelowChild parent child done s_before
                (set_fa_state s a p)).
    { exact (set_fa_state_pending_preserves_parent_old_candidates_below_child
               parent child a p done s_before s Hbelow_child). }
    assert (Hstack_frame_child_after:
              ParentTraversalStackFrame parent child s_before
                (set_fa_state s a p)).
    { exact (set_fa_state_pending_preserves_parent_traversal_stack_frame
               parent child a p s_before s Hstack_frame_child). }
    assert (Hshape_after:
              LoopCoreShape parent (done_after done child)
                (set_fa_state s a p)).
    { exact (set_fa_pending_preserves_loop_core_shape
               parent (done_after done child) s a p
               Hpvis Hnotvis Hshape). }
    assert (Haux_after:
              LoopAuxFacts parent (set_fa_state s a p)).
    { unfold LoopAuxFacts, OrderFacts in *. simpl. exact Haux. }
    assert (Hclosed_after: Closed (set_fa_state s a p)).
    { apply set_fa_pending_preserves_closed. exact Hclosed. }
    assert (Htree_after: TreeEdgesAreGraphEdges (set_fa_state s a p)).
    { exact (set_fa_pending_preserves_tree_edges_are_graph_edges
               s a p Hnotvis Htree). }
    assert (Hchild_vis_after: Visited child (set_fa_state s a p)).
    { simpl. exact Hchild_vis. }
    assert (Hfa_child_after: fa (set_fa_state s a p) child = parent).
    { rewrite set_fa_state_keep_other_fa; auto. }
    assert (Hfane_child_after: fa (set_fa_state s a p) child <> child).
    { rewrite set_fa_state_keep_other_fa; auto. }
    assert (Hdfn_parent_child_after:
              dfn (set_fa_state s a p) parent <
              dfn (set_fa_state s a p) child).
    { simpl. exact Hdfn_parent_child. }
    unfold ParentFrameForChild.
    split; [exact Hlow_frame_after |].
    split; [exact Hshape_after |].
    split; [exact Haux_after |].
    split; [exact Hclosed_after |].
    split; [exact Htree_after |].
    split; [exact Hedge |].
    split; [exact Hchild_vis_after |].
    split; [exact Hfa_child_after |].
    split; [exact Hfane_child_after |].
    split; [exact Hdfn_parent_child_after |].
    split; [exact Hnot_done_child |].
    exact (conj Hbelow_child_after Hstack_frame_child_after).
  Qed.

  Lemma set_fa_pending_prepares_nested_frame_pre
        (parent child a: V) (done current_done: V -> Prop)
        (s_before: St):
    Hoare
      (fun s: St =>
         LoopInv child current_done s /\
         ParentFrameForChild parent child done s_before s /\
         Edge child a /\
         ~ current_done a /\
         ~ Visited a s)
      (set_fa a child)
      (fun _ s =>
         NestedFramePre parent child child a done current_done s_before s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. change
      (NestedFramePre parent child child a done current_done
         s_before (set_fa_state s0 a child)).
    destruct H as [Hloop [Hframe [Hedge [Hnot_done Hnotvis]]]].
    destruct Hloop as [Haux Hcore].
    pose proof Hcore as Hcore_full.
    destruct Hcore as [Hshape_child [Hclosed Hlow]].
    destruct Hshape_child as
      [Hwf [Htree_sound [Hchild_vis_loop
        [Hdone_edge [Hdone_vis Hprocessed]]]]].
    destruct Haux as [Hsettled [Hactive Horder]].
    assert (Haux_after:
              LoopAuxFacts child (set_fa_state s0 a child)).
    { unfold LoopAuxFacts, OrderFacts. simpl.
      exact (conj Hsettled (conj Hactive Horder)). }
    assert (Hcore_after:
              LoopCoreInv child current_done (set_fa_state s0 a child)).
    { exact (set_fa_pending_preserves_loop_core_inv
               child current_done s0 a child
               Hchild_vis_loop Hnotvis Hcore_full). }
    assert (Hloop_after:
              LoopInv child current_done (set_fa_state s0 a child)).
    { exact (conj Haux_after Hcore_after). }
    assert (Hframe_after:
              ParentFrameForChild parent child done s_before
                (set_fa_state s0 a child)).
    { exact (set_fa_state_pending_preserves_parent_frame_for_child
               parent child a done s_before s0 Hframe Hnotvis). }
    assert (Hdisjoint_after:
              NestedFrameDisjoint parent child child done
                (set_fa_state s0 a child)).
    { exact (parent_frame_nested_disjoint_self
               parent child done s_before (set_fa_state s0 a child)
               Hframe_after). }
    assert (Hfa_new: fa (set_fa_state s0 a child) a = child).
    { unfold set_fa_state. simpl. unfold equiv_decb.
      destruct (equiv_dec a a) as [_ | Hneq].
      - reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    assert (Hchild_ne_a: child <> a).
    { intros Hchild_eq_a. apply Hnotvis.
      rewrite <- Hchild_eq_a. exact Hchild_vis_loop. }
    assert (Hfa_ne: fa (set_fa_state s0 a child) a <> a).
    { rewrite Hfa_new. exact Hchild_ne_a. }
    assert (Hentry: EntryPre a (set_fa_state s0 a child)).
    { assert (Hwf_pre: wf_scc_state_pre g root a (set_fa_state s0 a child)).
      { exact (conj
                 (set_fa_pending_preserves_wf_scc_state
                    s0 child a Hwf Hchild_vis_loop Hnotvis)
                 Hnotvis). }
      assert (Hclosed_post: Closed (set_fa_state s0 a child)).
      { apply set_fa_pending_preserves_closed. exact Hclosed. }
      assert (Htree_post: TreeEdgesAreGraphEdges (set_fa_state s0 a child)).
      { exact (set_fa_pending_preserves_tree_edges_are_graph_edges
                 s0 a child Hnotvis Htree_sound). }
      assert (Hincoming:
                fa (set_fa_state s0 a child) a <> a ->
                Edge (fa (set_fa_state s0 a child) a) a).
      { intros _. rewrite Hfa_new. exact Hedge. }
      exact (conj Hwf_pre
              (conj Hsettled
                (conj Hclosed_post
                  (conj Htree_post
                    (conj Horder Hincoming))))). }
    unfold NestedFramePre.
    exact (conj Hloop_after
            (conj Hframe_after
              (conj Hdisjoint_after
                (conj Hedge
                  (conj Hnot_done
                    (conj Hentry
                      (conj Hfa_new Hfa_ne))))))).
  Qed.

  Lemma set_fa_pending_prepares_external_nested_frame_pre
        (ancestor current loop_root a: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St):
    Hoare
      (fun s: St =>
         LoopInv loop_root loop_done s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s /\
         Edge loop_root a /\
         ~ loop_done a /\
         ~ Visited a s)
      (set_fa a loop_root)
      (fun _ s =>
         NestedFramePre ancestor current loop_root a
           ancestor_done loop_done s_before s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. change
      (NestedFramePre ancestor current loop_root a ancestor_done loop_done
         s_before (set_fa_state s0 a loop_root)).
    destruct H as
      [Hloop [Hframe [Hdisjoint [Hedge [Hnot_done Hnotvis]]]]].
    destruct Hloop as [Haux Hcore].
    pose proof Hcore as Hcore_full.
    destruct Hcore as [Hshape_loop [Hclosed Hlow]].
    destruct Hshape_loop as
      [Hwf [Htree_sound [Hloop_vis [Hdone_edge [Hdone_vis Hprocessed]]]]].
    destruct Haux as [Hsettled [Hactive Horder]].
    destruct Hframe as [Hframe_low Hframe_rest].
    pose proof (conj Hframe_low Hframe_rest) as Hframe_full.
    destruct Hframe_rest as [Hshape_ancestor _].
    destruct Hshape_ancestor as [_ [_ [_ [_ [Hancestor_done_vis _]]]]].
    assert (Haux_after:
              LoopAuxFacts loop_root (set_fa_state s0 a loop_root)).
    { unfold LoopAuxFacts, OrderFacts. simpl.
      exact (conj Hsettled (conj Hactive Horder)). }
    assert (Hcore_after:
              LoopCoreInv loop_root loop_done
                (set_fa_state s0 a loop_root)).
    { exact (set_fa_pending_preserves_loop_core_inv
               loop_root loop_done s0 a loop_root
               Hloop_vis Hnotvis Hcore_full). }
    assert (Hloop_after:
              LoopInv loop_root loop_done
                (set_fa_state s0 a loop_root)).
    { exact (conj Haux_after Hcore_after). }
    assert (Hframe_after:
              ParentFrameForChild ancestor current ancestor_done s_before
                (set_fa_state s0 a loop_root)).
    { exact (set_fa_state_pending_preserves_parent_frame_for_child_at
               ancestor current a loop_root ancestor_done s_before s0
               Hloop_vis Hframe_full Hnotvis). }
    assert (Hdisjoint_after:
              NestedFrameDisjoint ancestor current loop_root ancestor_done
                (set_fa_state s0 a loop_root)).
    { apply set_fa_state_pending_preserves_nested_frame_disjoint.
      - intros old_child Hdone_old.
        apply Hancestor_done_vis.
        apply done_after_intro_old. exact Hdone_old.
      - exact Hnotvis.
      - exact Hdisjoint. }
    assert (Hfa_new: fa (set_fa_state s0 a loop_root) a = loop_root).
    { unfold set_fa_state. simpl. unfold equiv_decb.
      destruct (equiv_dec a a) as [_ | Hneq].
      - reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    assert (Hloop_ne_a: loop_root <> a).
    { intros Hloop_eq_a. apply Hnotvis.
      rewrite <- Hloop_eq_a. exact Hloop_vis. }
    assert (Hfa_ne: fa (set_fa_state s0 a loop_root) a <> a).
    { rewrite Hfa_new. exact Hloop_ne_a. }
    assert (Hentry: EntryPre a (set_fa_state s0 a loop_root)).
    { assert (Hwf_pre:
                wf_scc_state_pre g root a
                  (set_fa_state s0 a loop_root)).
      { exact (conj
                 (set_fa_pending_preserves_wf_scc_state
                    s0 loop_root a Hwf Hloop_vis Hnotvis)
                 Hnotvis). }
      assert (Hclosed_post: Closed (set_fa_state s0 a loop_root)).
      { apply set_fa_pending_preserves_closed. exact Hclosed. }
      assert (Htree_post:
                TreeEdgesAreGraphEdges (set_fa_state s0 a loop_root)).
      { exact (set_fa_pending_preserves_tree_edges_are_graph_edges
                 s0 a loop_root Hnotvis Htree_sound). }
      assert (Hincoming:
                fa (set_fa_state s0 a loop_root) a <> a ->
                Edge (fa (set_fa_state s0 a loop_root) a) a).
      { intros _. rewrite Hfa_new. exact Hedge. }
      exact (conj Hwf_pre
              (conj Hsettled
                (conj Hclosed_post
                  (conj Htree_post
                    (conj Horder Hincoming))))). }
    unfold NestedFramePre.
    exact (conj Hloop_after
            (conj Hframe_after
              (conj Hdisjoint_after
                (conj Hedge
                  (conj Hnot_done
                    (conj Hentry
                      (conj Hfa_new Hfa_ne))))))).
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

  Lemma set_fa_pending_prepares_parent_recursive_pre
        (u v: V) (done: V -> Prop):
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         Edge u v /\
         ~ Visited v s)
      (set_fa v u)
      (fun _ s => ParentRecursivePre u v done s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 Hpre Hexec.
    pose proof (set_fa_pending_prepares_child_entry u v done)
      as Hentry_hoare.
    unfold Hoare in Hentry_hoare.
    pose proof (Hentry_hoare s1 retv s2 Hpre Hexec)
      as Hpost.
    destruct Hpre as [_ [Hedge _]].
    destruct Hpost as [Hloop [Hentry [Hfa Hfane]]].
    unfold ParentRecursivePre.
    exact (conj Hloop
            (conj Hedge
              (conj Hentry
                (conj Hfa Hfane)))).
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

  Lemma update_low_preserves_loop_traversal_complete
        (center: V) (done: V -> Prop) (u: V) (n: nat):
    Hoare
      (LoopTraversalComplete center done)
      (update_low u n)
      (fun _ s => LoopTraversalComplete center done s).
  Proof.
    unfold update_low. unfold_op.
    intro_state. hoare_auto_s.
    - subst s. simpl. exact H.
    - destruct H1 as [Heq _]. subst s. exact H.
  Qed.

  Lemma get_dfn_update_low_preserves_loop_traversal_complete
        (center: V) (done: V -> Prop) (u v: V):
    Hoare
      (LoopTraversalComplete center done)
      (dv <- get' (fun s => dfn s v);; update_low u dv)
      (fun _ s => LoopTraversalComplete center done s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_loop_traversal_complete.
    intros s1 [Hs1 _]. subst s1. exact H.
  Qed.

  Lemma get_low_update_low_preserves_loop_traversal_complete
        (center: V) (done: V -> Prop) (u v: V):
    Hoare
      (LoopTraversalComplete center done)
      (lv <- get' (fun s => low s v);; update_low u lv)
      (fun _ s => LoopTraversalComplete center done s).
  Proof.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: apply update_low_preserves_loop_traversal_complete.
    intros s1 [Hs1 _]. subst s1. exact H.
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
          [[Hv_active [Hchild_shape [[Hchild_sound _] _]]] |
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
      + pose proof (Hframe_bwd target Hcandidate_old_after)
          as Hlow_before_le_target.
        pose proof (Nat.le_min_l (low s_before u) (low s v))
          as Hmin_le_old.
        lia.
      + destruct Hchild_contrib as
          [[Hv_active [Hchild_shape [[_ Hchild_complete] _]]] |
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

  Lemma process_edge_preserves_parent_frame_for_child
        (parent child a: V) (done current_done: V -> Prop)
        (s_before: St) (W: RecProgram):
    VisitFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv child current_done s /\
         ParentFrameForChild parent child done s_before s /\
         Edge child a /\
         ~ current_done a)
      (process_edge child W a)
      (fun _ s =>
         ParentFrameForChild parent child done s_before s).
  Proof.
    intros Hframe_contract.
    unfold process_edge, if_else.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: {
        eapply Hoare_bind with
          (Q := fun (_: unit) s =>
                  NestedFramePre parent child child a
                    done current_done s_before s).
        - apply set_fa_pending_prepares_nested_frame_pre.
        - simpl. intros _.
          eapply Hoare_bind with
            (Q := fun (_: unit) s =>
                    ParentFrameForChild parent child done s_before s).
          + eapply Hoare_conseq_post.
            2: {
              apply (Hframe_contract parent child child a
                       done current_done s_before). }
            intros _ s [Hparent_frame _].
            exact Hparent_frame.
          + simpl. intros _.
            apply (get_low_update_low_preserves_parent_frame_for_child
                     parent child a done s_before). }
      intros s1 [Hnotvis Hs1]. subst s1.
      destruct H as [Hloop [Hframe [Hedge Hnot_done]]].
      exact (conj Hloop
              (conj Hframe
                (conj Hedge
                  (conj Hnot_done Hnotvis)))).
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hvisited_by_classic Hs1]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: apply (get_dfn_update_low_preserves_parent_frame_for_child
                    parent child a done s_before).
        intros s1 [_ Hs1]. subst s1.
        destruct H as [_ [Hframe _]].
        exact Hframe.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        simpl. intros _ s [Heq _]. subst s.
        destruct H as [_ [Hframe _]].
        exact Hframe.
  Qed.

  Lemma process_edge_preserves_nested_parent_frame
        (ancestor current loop_root a: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St) (W: RecProgram):
    VisitFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv loop_root loop_done s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s /\
         Edge loop_root a /\
         ~ loop_done a)
      (process_edge loop_root W a)
      (fun _ s =>
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
  Proof.
    intros Hframe_contract.
    unfold process_edge, if_else.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: {
        eapply Hoare_bind with
          (Q := fun (_: unit) s =>
                  NestedFramePre ancestor current loop_root a
                    ancestor_done loop_done s_before s).
        - apply set_fa_pending_prepares_external_nested_frame_pre.
        - simpl. intros _.
          eapply Hoare_bind with
            (Q := fun (_: unit) s =>
                    ParentFrameForChild ancestor current ancestor_done
                      s_before s /\
                    NestedFrameDisjoint ancestor current loop_root
                      ancestor_done s).
          + apply (Hframe_contract ancestor current loop_root a
                     ancestor_done loop_done s_before).
          + simpl. intros _.
            apply (get_low_update_low_preserves_nested_parent_context
                     ancestor current loop_root a ancestor_done s_before). }
      intros s1 [Hnotvis Hs1]. subst s1.
      destruct H as [Hloop [Hframe [Hdisjoint [Hedge Hnot_done]]]].
      exact (conj Hloop
              (conj Hframe
                (conj Hdisjoint
                  (conj Hedge
                    (conj Hnot_done Hnotvis))))).
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hvisited_by_classic Hs1]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: apply (get_dfn_update_low_preserves_nested_parent_context
                    ancestor current loop_root a ancestor_done s_before).
        intros s1 [_ Hs1]. subst s1.
        destruct H as [_ [Hframe [Hdisjoint _]]].
        exact (conj Hframe Hdisjoint).
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        simpl. intros _ s [Heq _]. subst s.
        destruct H as [_ [Hframe [Hdisjoint _]]].
        exact (conj Hframe Hdisjoint).
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

  Lemma edge_loop_preserves_loop_inv_from_visit_contract
        (u: V) (W: RecProgram):
    VisitChildContract W ->
    Hoare
      (fun s: St => LoopInv u ∅ s)
      (forset (edge_set u) (process_edge u W))
      (fun _ s => LoopInv u (edge_set u) s).
  Proof.
    intros Hchild.
    apply edge_loop_preserves_loop_inv.
    intros done v _ Hedge _.
    eapply Hoare_conseq_pre.
    2: apply Hchild.
    intros s [Hloop [Hedge' [Hentry [Hfa Hfane]]]].
    unfold ParentRecursivePre.
    exact (conj Hloop
            (conj Hedge'
              (conj Hentry
                (conj Hfa Hfane)))).
  Qed.

  Lemma edge_loop_preserves_parent_frame_for_child
        (parent child: V) (done: V -> Prop) (s_before: St)
        (W: RecProgram):
    VisitChildContract W ->
    VisitFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv child ∅ s /\
         ParentFrameForChild parent child done s_before s)
      (forset (edge_set child) (process_edge child W))
      (fun _ s =>
         LoopInv child (edge_set child) s /\
         ParentFrameForChild parent child done s_before s).
  Proof.
    intros Hchild Hframe.
    apply Hoare_forset with
      (P := fun current_done s =>
              LoopInv child current_done s /\
              ParentFrameForChild parent child done s_before s)
      (universe := edge_set child).
    - intros done1 done2 Hdone s1 s2 Heq. subst s2.
      split; intros [Hloop Hparent_frame].
      + split.
        * eapply loop_inv_done_equiv; eauto.
        * exact Hparent_frame.
      + split.
        * eapply loop_inv_done_equiv.
          -- symmetry. exact Hdone.
          -- exact Hloop.
        * exact Hparent_frame.
    - intros current_done a Hdone_sub Hedge Hnot_done.
      apply Hoare_conj with
        (Q1 := fun _ s => LoopInv child (done_after current_done a) s).
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
      + eapply Hoare_conseq_pre.
        2: {
          apply (process_edge_preserves_parent_frame_for_child
                   parent child a done current_done s_before W Hframe). }
        intros s [Hloop Hparent_frame].
        exact (conj Hloop
                (conj Hparent_frame
                  (conj Hedge Hnot_done))).
  Qed.

  Lemma edge_loop_preserves_nested_parent_frame
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (s_before: St)
        (W: RecProgram):
    VisitChildContract W ->
    VisitFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv loop_root ∅ s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s)
      (forset (edge_set loop_root) (process_edge loop_root W))
      (fun _ s =>
         LoopInv loop_root (edge_set loop_root) s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
  Proof.
    intros Hchild Hframe.
    apply Hoare_forset with
      (P := fun loop_done s =>
              LoopInv loop_root loop_done s /\
              ParentFrameForChild ancestor current ancestor_done s_before s /\
              NestedFrameDisjoint ancestor current loop_root ancestor_done s)
      (universe := edge_set loop_root).
    - intros done1 done2 Hdone s1 s2 Heq. subst s2.
      split; intros [Hloop [Hparent_frame Hdisjoint]].
      + split.
        * eapply loop_inv_done_equiv; eauto.
        * exact (conj Hparent_frame Hdisjoint).
      + split.
        * eapply loop_inv_done_equiv.
          -- symmetry. exact Hdone.
          -- exact Hloop.
        * exact (conj Hparent_frame Hdisjoint).
    - intros loop_done a Hdone_sub Hedge Hnot_done.
      apply Hoare_conj with
        (Q1 := fun _ s =>
                 LoopInv loop_root (done_after loop_done a) s).
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
      + eapply Hoare_conseq_pre.
        2: {
          apply (process_edge_preserves_nested_parent_frame
                   ancestor current loop_root a ancestor_done loop_done
                   s_before W Hframe). }
        intros s [Hloop [Hparent_frame Hdisjoint]].
        exact (conj Hloop
                (conj Hparent_frame
                  (conj Hdisjoint
                    (conj Hedge Hnot_done)))).
  Qed.

  Lemma rest_stack_below_root (u b: V) (s: St):
    Active u s ->
    RestStack u s b ->
    exists l1 l2,
      stack s = l1 ++ u :: l2 /\ In b l2.
  Proof.
    unfold Active, RestStack.
    intros Hu_active Hb_rest.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    simpl in Hb_rest.
    destruct (stack_split_at_decomp
                (stack s) u Hu_active popped rest Hsplit)
      as [prefix Hstk].
    exists prefix, rest.
    exact (conj Hstk Hb_rest).
  Qed.

  Lemma list_prefix_member_before_tail
        (prefix tail: list V) (x u: V):
    In x prefix ->
    exists l1 l2,
      prefix ++ u :: tail = l1 ++ x :: l2 /\ In u l2.
  Proof.
    induction prefix as [| a prefix IH]; intros Hin.
    - simpl in Hin. destruct Hin.
    - simpl in Hin.
      destruct Hin as [Hx | Hin].
      + subst a. exists nil, (prefix ++ u :: tail).
        split; [reflexivity |].
        rewrite List.in_app_iff. right. simpl. left. reflexivity.
      + destruct (IH Hin) as [l1 [l2 [Hstk Hu_in]]].
        exists (a :: l1), l2.
        split; [simpl; rewrite Hstk; reflexivity | exact Hu_in].
  Qed.

  Lemma active_dfn_lt_root_rest_stack
        (u x: V) (s: St):
    OrderFacts s ->
    Active u s ->
    Active x s ->
    dfn s x < dfn s u ->
    RestStack u s x.
  Proof.
    intros [Horder _] Hu_active Hx_active Hdfn_lt.
    unfold RestStack.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    destruct (stack_split_at_decomp
                (stack s) u Hu_active popped rest Hsplit)
      as [prefix Hstk].
    apply NNPP. intros Hnot_rest.
    unfold Active in Hx_active.
    rewrite Hstk in Hx_active.
    rewrite List.in_app_iff in Hx_active.
    destruct Hx_active as [Hx_prefix | [Hx_eq_u | Hx_rest]].
    - destruct (list_prefix_member_before_tail prefix rest x u Hx_prefix)
        as [l1 [l2 [Habove Hu_in_l2]]].
      assert (Habove_stack:
                exists l1' l2',
                  stack s = l1' ++ x :: l2' /\ In u l2').
      { exists l1, l2. rewrite Hstk. exact (conj Habove Hu_in_l2). }
      pose proof (Horder x u) as Horder_x_u.
      assert (Hroot_active: In u (stack s)) by exact Hu_active.
      assert (Hx_stack: In x (stack s)).
      { rewrite Hstk. rewrite List.in_app_iff.
        left. exact Hx_prefix. }
      pose proof (Horder_x_u Hx_stack Hroot_active Habove_stack) as Hle.
      lia.
    - subst x. lia.
    - exact (Hnot_rest Hx_rest).
  Qed.

  Lemma stack_rest_member_ne_root
        (u b: V) (s: St) (l1 l2: list V):
    StackNoDup s ->
    stack s = l1 ++ u :: l2 ->
    In b l2 ->
    u <> b.
  Proof.
    intros Hnodup Hstk Hb_in Hu_eq_b.
    subst b.
    unfold StackNoDup in Hnodup.
    rewrite Hstk in Hnodup.
    apply NoDup_remove_2 in Hnodup.
    apply Hnodup.
    rewrite List.in_app_iff.
    right. exact Hb_in.
  Qed.

  Lemma rest_stack_member_ne_root
        (u b: V) (s: St):
    StackNoDup s ->
    Active u s ->
    RestStack u s b ->
    b <> u.
  Proof.
    intros Hnodup Hu_active Hb_rest Hb_eq_u.
    subst b.
    destruct (rest_stack_below_root u u s Hu_active Hb_rest)
      as [l1 [l2 [Hstk Hu_in]]].
    pose proof (stack_rest_member_ne_root u u s l1 l2
                  Hnodup Hstk Hu_in) as Hneq.
    exact (Hneq eq_refl).
  Qed.

  Lemma nested_context_derives_rest_stack
        (ancestor current loop_root: V)
        (loop_done ancestor_done: V -> Prop)
        (s_before s: St):
    LoopInv loop_root loop_done s ->
    ParentFrameForChild ancestor current ancestor_done s_before s ->
    NestedFrameDisjoint ancestor current loop_root ancestor_done s ->
    current <> loop_root ->
    RestStack loop_root s current.
  Proof.
    intros Hloop Hframe Hdisjoint Hcurrent_ne_root.
    destruct Hloop as [Haux [Hshape_root [Hclosed _]]].
    destruct Haux as [_ [Hroot_active Horder]].
    destruct Horder as [Hstack_order [Hdfn_inj Hnodup]].
    destruct Hshape_root as [Hwf [Htree_sound [Hroot_vis _]]].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [_ Hframe].
    destruct Hframe as [Hcurrent_vis _].
    destruct Hdisjoint as [Hreach_current_root _].
    assert (Hgraph_reach: dg_reachable g current loop_root).
    { eapply tree_reachable_to_graph_reachable; eauto. }
    assert (Hcurrent_active: Active current s).
    { apply NNPP. intros Hnot_active.
      exact (Hclosed current loop_root
               Hcurrent_vis Hnot_active Hgraph_reach Hroot_active). }
    assert (Hdfn_le:
              dfn s current <= dfn s loop_root).
    { eapply tree_reachable_dfn_monotone; eauto. }
    assert (Hdfn_ne:
              dfn s current <> dfn s loop_root).
    { apply (Hdfn_inj current loop_root Hcurrent_ne_root
               Hcurrent_vis Hroot_vis). }
    assert (Hdfn_lt:
              dfn s current < dfn s loop_root).
    { lia. }
    eapply active_dfn_lt_root_rest_stack.
    - exact (conj Hstack_order (conj Hdfn_inj Hnodup)).
    - exact Hroot_active.
    - exact Hcurrent_active.
    - exact Hdfn_lt.
  Qed.

  Lemma loop_inv_derives_stack_rest_older_than_root
        (u: V) (s: St):
    LoopInv u (edge_set u) s ->
    StackRestOlderThanRoot u s.
  Proof.
    intros Hinv.
    destruct Hinv as [Haux [Hshape _]].
    destruct Haux as [_ [Hu_active [Hstack_order [Hdfn_inj Hnodup]]]].
    destruct Hshape as [Hwf _].
    unfold wf_scc_state in Hwf.
    destruct Hwf as [Hstack_vis [Hdfn_inv [Hdfn_valid Hfa_vis]]].
    unfold StackRestOlderThanRoot.
    split; [exact Hu_active |].
    intros b Hb_rest.
    destruct (rest_stack_below_root u b s Hu_active Hb_rest)
      as [l1 [l2 [Hstk Hb_in_l2]]].
    assert (Hb_active: Active b s).
    { unfold Active. rewrite Hstk.
      rewrite List.in_app_iff.
      right. simpl. right. exact Hb_in_l2. }
    assert (Habove:
              exists l1' l2',
                stack s = l1' ++ u :: l2' /\ In b l2').
    { exists l1, l2. exact (conj Hstk Hb_in_l2). }
    assert (Hu_ne_b: u <> b).
    { eapply stack_rest_member_ne_root; eauto. }
    eapply stack_dfn_order_strict; eauto.
  Qed.

  Lemma loop_aux_shape_derives_stack_rest_older_than_root
        (u: V) (done: V -> Prop) (s: St):
    LoopAuxFacts u s ->
    LoopCoreShape u done s ->
    StackRestOlderThanRoot u s.
  Proof.
    intros Haux Hshape.
    destruct Haux as [_ [Hu_active [Hstack_order [Hdfn_inj Hnodup]]]].
    destruct Hshape as [Hwf _].
    unfold wf_scc_state in Hwf.
    destruct Hwf as [Hstack_vis [Hdfn_inv [Hdfn_valid Hfa_vis]]].
    unfold StackRestOlderThanRoot.
    split; [exact Hu_active |].
    intros b Hb_rest.
    destruct (rest_stack_below_root u b s Hu_active Hb_rest)
      as [l1 [l2 [Hstk Hb_in_l2]]].
    assert (Hb_active: Active b s).
    { unfold Active. rewrite Hstk.
      rewrite List.in_app_iff.
      right. simpl. right. exact Hb_in_l2. }
    assert (Habove:
              exists l1' l2',
                stack s = l1' ++ u :: l2' /\ In b l2').
    { exists l1, l2. exact (conj Hstk Hb_in_l2). }
    assert (Hu_ne_b: u <> b).
    { eapply stack_rest_member_ne_root; eauto. }
    eapply stack_dfn_order_strict; eauto.
  Qed.

  Lemma edge_loop_post_to_root_pre_pop (u: V) (s: St):
    LoopInv u (edge_set u) s ->
    StackRestOlderThanRoot u s ->
    RootPrePop u s.
  Proof.
    intros Hloop Hstack_rest.
    unfold RootPrePop.
    exact (conj Hloop Hstack_rest).
  Qed.

  Lemma loop_inv_to_root_pre_pop (u: V) (s: St):
    LoopInv u (edge_set u) s ->
    RootPrePop u s.
  Proof.
    intros Hloop.
    apply edge_loop_post_to_root_pre_pop.
    - exact Hloop.
    - apply loop_inv_derives_stack_rest_older_than_root.
      exact Hloop.
  Qed.

  Lemma edge_loop_post_to_root_pre_maybe_pop (u: V) (s: St):
    LoopInv u (edge_set u) s ->
    RootTraversalComplete u s ->
    RootPreMaybePop u s.
  Proof.
    intros Hloop Htraversal.
    unfold RootPreMaybePop.
    split.
    - apply loop_inv_to_root_pre_pop. exact Hloop.
    - exact Htraversal.
  Qed.

  Lemma edge_loop_preserves_root_pre_maybe_pop_from_visit_contract
        (u: V) (W: RecProgram):
    VisitChildContract W ->
    Hoare
      (fun s: St => LoopInv u ∅ s)
      (forset (edge_set u) (process_edge u W))
      (fun _ s => RootTraversalComplete u s) ->
    Hoare
      (fun s: St => LoopInv u ∅ s)
      (forset (edge_set u) (process_edge u W))
      (fun _ s => RootPreMaybePop u s).
  Proof.
    intros Hchild Htraversal.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s => LoopInv u (edge_set u) s).
      - apply edge_loop_preserves_loop_inv_from_visit_contract.
        exact Hchild.
      - exact Htraversal. }
    intros _ s [Hloop Htrav].
      eapply edge_loop_post_to_root_pre_maybe_pop; eauto.
  Qed.

  Lemma edge_loop_post_to_child_return_pre_maybe_pop
        (parent child: V) (done: V -> Prop)
        (s_before s: St):
    LoopInv child (edge_set child) s ->
    RootTraversalComplete child s ->
    ParentFrameForChild parent child done s_before s ->
    ChildReturnPreMaybePop parent child done s_before s.
  Proof.
    intros Hloop Htraversal Hframe.
    unfold ChildReturnPreMaybePop.
    split.
    - eapply edge_loop_post_to_root_pre_maybe_pop; eauto.
    - exact Hframe.
  Qed.

  (* maybe pop *)

  Lemma partial_low_candidate_to_scc_low_tree
        (u b: V) (s: St):
    LoopCoreShape u (edge_set u) s ->
    PartialLowCandidate u (edge_set u) s b ->
    scc_low_tree s u b.
  Proof.
    intros Hshape Hcandidate.
    destruct Hshape as [_ [_ [_ [_ [Hdone_vis _]]]]].
    unfold scc_low_tree, scc_low_reachable.
    unfold PartialLowCandidate in Hcandidate.
    destruct Hcandidate as [Hb_eq_u | Htarget].
    - subst b. exists u. split.
      + apply Coq.Relations.Relation_Operators.rt_refl.
      + left. reflexivity.
    - unfold PartialActiveTarget in Htarget.
      destruct Htarget as [Hdirect | Hsubtree].
      + destruct Hdirect as
          [a [Hdone_a [Hb_eq_a [Hedge [Hactive Hnot_tree]]]]].
        subst b. exists u. split.
        * apply Coq.Relations.Relation_Operators.rt_refl.
        * right. unfold scc_back_edge. repeat split; auto.
      + destruct Hsubtree as
          [child [x [Hdone_child [Hedge_child
            [Hfa_child [Hfane_child
              [Hreach_child_x [Hedge_x_b [Hactive_b Hnot_tree]]]]]]]]].
        assert (Hchild_vis: Visited child s).
        { apply Hdone_vis. exact Hdone_child. }
        assert (Htree_u_child: tree_edge s u child).
        { unfold tree_edge.
          eapply tree_step_char_backward; eauto. }
        assert (Hreach_u_x:
                  dg_reachable (state_to_dfs_tree g s root) u x).
        { eapply dg_step_reachable_reachable; eauto. }
        exists x. split; [exact Hreach_u_x |].
        right. unfold scc_back_edge. repeat split; auto.
  Qed.

  Lemma scc_low_tree_target_lower_bound
        (u target: V) (s: St):
    LoopCoreShape u (edge_set u) s ->
    RootLowCorrect u s ->
    scc_low_tree s u target ->
    low s u <= dfn s target.
  Proof.
    intros Hshape Hlow Htarget.
    destruct Hshape as [Hwf [Htree_sound Hshape_rest]].
    destruct Hlow as [_ Hcomplete].
    unfold scc_low_tree, scc_low_reachable in Htarget.
    destruct Htarget as [x [Hreach [Hx_eq_target | Hback]]].
    - subst target.
      assert (Hroot_candidate:
                PartialLowCandidate u (edge_set u) s u).
      { apply partial_low_candidate_root. }
      pose proof (Hcomplete u Hroot_candidate) as Hlow_le_u.
      pose proof (tree_reachable_dfn_monotone s u x Hwf Hreach)
        as Hu_le_x.
      lia.
    - destruct Hback as [Hedge [Hactive Hnot_tree]].
      assert (Hcandidate:
                PartialLowCandidate u (edge_set u) s target).
      { eapply tree_escape_to_child_candidate; eauto. }
      apply Hcomplete. exact Hcandidate.
  Qed.

  Lemma root_low_correct_to_scc_is_low_v (u: V) (s: St):
    LoopCoreShape u (edge_set u) s ->
    RootLowCorrect u s ->
    scc_is_low_v s u.
  Proof.
    intros Hshape Hlow.
    pose proof Hlow as Hlow_all.
    destruct Hlow as [[witness [Hcandidate Hlow_eq]] Hcomplete].
    unfold scc_is_low_v, scc_is_low_v_val.
    unfold min_value_of_subset.
    exists witness. split.
    - unfold min_object_of_subset. split.
      + eapply partial_low_candidate_to_scc_low_tree; eauto.
      + intros target Htarget.
        rewrite <- Hlow_eq.
        eapply scc_low_tree_target_lower_bound; eauto.
    - symmetry. exact Hlow_eq.
  Qed.

  Lemma maybe_pop_skip_produces_root_final (u: V) (s: St):
    RootSkipBranchPre u s ->
    RootFinal u s.
  Proof.
    intros Hpre.
    destruct Hpre as [[Hloop _] _].
    destruct Hloop as [Haux [Hshape [Hclosed Hlow]]].
    destruct Haux as [Hsettled _].
    unfold RootFinal, RootAfterMaybePop.
    split.
    - destruct Hshape as [Hwf _]. exact Hwf.
    - split; [exact Hsettled |].
      split; [exact Hclosed |].
      eapply root_low_correct_to_scc_is_low_v; eauto.
  Qed.

  Lemma maybe_pop_skip_produces_child_contribution
        (parent child: V) (done: V -> Prop) (s_before s: St):
    ChildReturnPreMaybePop parent child done s_before s ->
    low s child <> dfn s child ->
    ChildContributionContract parent child done s_before s.
  Proof.
    intros [Hroot Hframe] _.
    destruct Hroot as [Hpre Htraversal].
    destruct Hpre as [Hloop _].
    destruct Hloop as [Haux_child [Hshape_child [_ Hlow_child]]].
    destruct Haux_child as [_ [Hchild_active _]].
    destruct Hframe as
      [Hparent_low [Hparent_shape [Hparent_aux
        [Hclosed [Htree [_ [Hchild_vis [Hfa_child [Hfane_child _]]]]]]]]].
    unfold ChildContributionContract.
    split; [exact Hparent_low |].
    split; [exact Hparent_shape |].
    split; [exact Hparent_aux |].
    split; [exact Hclosed |].
    split; [exact Htree |].
    split; [exact Hchild_vis |].
    split; [exact Hfa_child |].
    split; [exact Hfane_child |].
    left.
    split; [exact Hchild_active |].
    split; [exact Hshape_child |].
    split; [exact Hlow_child |].
    exact Htraversal.
  Qed.

  Lemma stack_split_at_in_cases
        (stk: list V) (u x: V) (popped rest: list V):
    stack_split_at stk u = (popped, rest) ->
    In x stk ->
    In x popped \/ In x rest.
  Proof.
    revert u x popped rest.
    induction stk as [| a stk IH]; intros u x popped rest Hsplit Hin.
    - simpl in Hin. destruct Hin.
    - simpl in Hsplit.
      destruct (equiv_decb a u) eqn:Ha_u.
      + inversion Hsplit. subst popped rest. simpl in Hin |- *.
        destruct Hin as [Hx | Hin].
        * left. left. exact Hx.
        * right. exact Hin.
      + destruct (stack_split_at stk u) as [popped' rest'] eqn:Hinner.
        inversion Hsplit. subst popped rest. simpl in Hin |- *.
        destruct Hin as [Hx | Hin].
        * left. left. exact Hx.
        * destruct (IH u x popped' rest' Hinner Hin) as [Hp | Hr].
          -- left. right. exact Hp.
          -- right. exact Hr.
  Qed.

  Lemma stack_split_at_in_original
        (stk: list V) (u x: V) (popped rest: list V):
    stack_split_at stk u = (popped, rest) ->
    In x popped \/ In x rest ->
    In x stk.
  Proof.
    revert u x popped rest.
    induction stk as [| a stk IH]; intros u x popped rest Hsplit Hin.
    - simpl in Hsplit. inversion Hsplit. subst popped rest.
      destruct Hin as [Hin | Hin]; exact Hin.
    - simpl in Hsplit.
      destruct (equiv_decb a u) eqn:Ha_u.
      + inversion Hsplit. subst popped rest. simpl in Hin |- *.
        destruct Hin as [[Hx | Hin_nil] | Hin_rest].
        * left. exact Hx.
        * destruct Hin_nil.
        * right. exact Hin_rest.
      + destruct (stack_split_at stk u) as [popped' rest'] eqn:Hinner.
        inversion Hsplit. subst popped rest. simpl in Hin |- *.
        destruct Hin as [[Hx | Hin_popped] | Hin_rest].
        * left. exact Hx.
        * right. apply (IH u x popped' rest' Hinner).
          left. exact Hin_popped.
        * right. apply (IH u x popped' rest' Hinner).
          right. exact Hin_rest.
  Qed.

  Lemma stack_split_at_rest_trans
        (stk: list V) (u v x: V):
    NoDup stk ->
    (match stack_split_at stk u with
     | (_, rest) => In v rest
     end) ->
    (match stack_split_at stk v with
     | (_, rest) => In x rest
     end) ->
    match stack_split_at stk u with
    | (_, rest) => In x rest
    end.
  Proof.
    revert u v x.
    induction stk as [| a stk IH]; intros u v x Hnodup Huv Hvx.
    - simpl in Huv. exact Huv.
    - simpl in Huv, Hvx |- *.
      inversion Hnodup as [| ? ? Ha_notin Hnodup_tail]. subst.
      destruct (equiv_decb a u) eqn:Hau.
      + destruct (equiv_decb a v) eqn:Hav.
        * exact Hvx.
        * destruct (stack_split_at stk v) as [pv rv] eqn:Hsv.
          apply (stack_split_at_in_original stk v x pv rv Hsv).
          right. exact Hvx.
      + destruct (stack_split_at stk u) as [pu ru] eqn:Hsu.
        simpl in Huv |- *.
        destruct (equiv_decb a v) eqn:Hav.
        * exfalso.
          assert (Ha_eq_v: a = v).
          { unfold equiv_decb in Hav.
            destruct (equiv_dec a v) as [Heq | Hneq].
            - exact Heq.
            - inversion Hav. }
          subst v.
          apply Ha_notin.
          apply (stack_split_at_in_original stk u a pu ru Hsu).
          right. exact Huv.
        * destruct (stack_split_at stk v) as [pv rv] eqn:Hsv.
          simpl in Hvx.
          pose proof (IH u v x Hnodup_tail) as HIH.
          rewrite Hsu in HIH. simpl in HIH.
          rewrite Hsv in HIH. simpl in HIH.
          exact (HIH Huv Hvx).
  Qed.

  Lemma stack_split_at_suffix_rest_preserves
        (stk: list V) (u v x: V):
    NoDup stk ->
    (match stack_split_at stk u with
     | (_, rest) => In v rest
     end) ->
    (match stack_split_at stk v with
     | (_, rest) => In x rest
     end) ->
    match stack_split_at (snd (stack_split_at stk u)) v with
    | (_, rest) => In x rest
    end.
  Proof.
    revert u v x.
    induction stk as [| a stk IH]; intros u v x Hnodup Huv Hvx.
    - simpl in Huv. exact Huv.
    - simpl in Huv, Hvx |- *.
      inversion Hnodup as [| ? ? Ha_notin Hnodup_tail]. subst.
      destruct (equiv_decb a u) eqn:Hau.
      + destruct (equiv_decb a v) eqn:Hav.
        * exfalso.
          assert (Ha_eq_v: a = v).
          { unfold equiv_decb in Hav.
            destruct (equiv_dec a v) as [Heq | Hneq].
            - exact Heq.
            - inversion Hav. }
          subst v. exact (Ha_notin Huv).
        * destruct (stack_split_at stk v) as [pv rv] eqn:Hsv.
          change
            (match stack_split_at stk v with
             | (_, rest) => In x rest
             end).
          rewrite Hsv. exact Hvx.
      + destruct (stack_split_at stk u) as [pu ru] eqn:Hsu.
        simpl in Huv |- *.
        destruct (equiv_decb a v) eqn:Hav.
        * exfalso.
          assert (Ha_eq_v: a = v).
          { unfold equiv_decb in Hav.
            destruct (equiv_dec a v) as [Heq | Hneq].
            - exact Heq.
            - inversion Hav. }
          subst v.
          apply Ha_notin.
          apply (stack_split_at_in_original stk u a pu ru Hsu).
          right. exact Huv.
        * destruct (stack_split_at stk v) as [pv rv] eqn:Hsv.
          simpl in Hvx.
          pose proof (IH u v x Hnodup_tail) as HIH.
          rewrite Hsu in HIH. simpl in HIH.
	          rewrite Hsv in HIH. simpl in HIH.
	          exact (HIH Huv Hvx).
	  Qed.

	  Lemma rest_stack_trans
	        (u v x: V) (s: St):
    StackNoDup s ->
    RestStack u s v ->
    RestStack v s x ->
    RestStack u s x.
  Proof.
    unfold StackNoDup, RestStack.
    intros Hnodup Huv Hvx.
    eapply stack_split_at_rest_trans; eauto.
  Qed.

  Lemma rest_stack_after_pop_preserves_nested
        (u v x: V) (s: St):
    StackNoDup s ->
    RestStack u s v ->
    RestStack v s x ->
    RestStack v (pop_scc_state s u) x.
  Proof.
    unfold StackNoDup, RestStack.
    intros Hnodup Huv Hvx.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    simpl.
    pose proof
      (stack_split_at_suffix_rest_preserves
         (stack s) u v x Hnodup) as Hsuffix.
    rewrite Hsplit in Hsuffix. simpl in Hsuffix.
    exact (Hsuffix Huv Hvx).
  Qed.

  Lemma stack_split_at_popped_rest_disjoint
        (stk: list V) (u x: V) (popped rest: list V):
    stack_split_at stk u = (popped, rest) ->
    NoDup stk ->
    In x popped ->
    In x rest ->
    False.
  Proof.
    revert u x popped rest.
    induction stk as [| a stk IH]; intros u x popped rest Hsplit Hnodup Hp Hr.
    - simpl in Hsplit. inversion Hsplit. subst popped rest.
      exact Hp.
    - simpl in Hsplit.
      inversion Hnodup as [| ? ? Ha_notin Hnodup_tail]. subst.
      destruct (equiv_decb a u) eqn:Ha_u.
      + inversion Hsplit. subst popped rest.
        simpl in Hp.
        destruct Hp as [Hx | []].
        subst x. exact (Ha_notin Hr).
      + destruct (stack_split_at stk u) as [popped' rest'] eqn:Hinner.
        inversion Hsplit. subst popped rest'.
        simpl in Hp.
        destruct Hp as [Hx | Hpopped'].
        * subst x.
          apply Ha_notin.
          exact (stack_split_at_in_original
                   stk u a popped' rest Hinner (or_intror Hr)).
        * eapply IH; eauto.
  Qed.

  Lemma stack_split_at_popped_of_not_rest
        (stk: list V) (u x: V) (popped rest: list V):
    stack_split_at stk u = (popped, rest) ->
    In x stk ->
    ~ In x rest ->
    In x popped.
  Proof.
    intros Hsplit Hin Hnot_rest.
    destruct (stack_split_at_in_cases stk u x popped rest Hsplit Hin)
      as [Hpopped | Hrest].
    - exact Hpopped.
    - exfalso. exact (Hnot_rest Hrest).
  Qed.

  Lemma stack_split_at_root_in_popped
        (stk: list V) (u: V) (popped rest: list V):
    stack_split_at stk u = (popped, rest) ->
    In u stk ->
    In u popped.
  Proof.
    revert u popped rest.
    induction stk as [| a stk IH]; intros u popped rest Hsplit Hin.
    - simpl in Hin. destruct Hin.
    - simpl in Hsplit.
      destruct (equiv_decb a u) eqn:Ha_u.
      + inversion Hsplit. subst popped rest.
        simpl. left.
        unfold equiv_decb in Ha_u.
        destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq].
        * exact Ha_eq_u.
        * inversion Ha_u.
      + simpl in Hin.
        destruct Hin as [Ha_eq_u | Hin_tail].
        * subst a.
          unfold equiv_decb in Ha_u.
          destruct (equiv_dec u u) as [_ | Hu_neq].
          -- inversion Ha_u.
          -- exfalso. apply Hu_neq. reflexivity.
        * destruct (stack_split_at stk u) as [popped' rest'] eqn:Hinner.
          inversion Hsplit. subst popped rest.
          simpl. right. eapply IH; eauto.
  Qed.

  Lemma stack_split_at_rest_nodup
        (stk: list V) (u: V) (popped rest: list V):
    stack_split_at stk u = (popped, rest) ->
    NoDup stk ->
    NoDup rest.
  Proof.
    revert u popped rest.
    induction stk as [| a stk IH]; intros u popped rest Hsplit Hnodup.
    - simpl in Hsplit. inversion Hsplit. subst rest. constructor.
    - simpl in Hsplit.
      inversion Hnodup as [| ? ? Ha_notin Hnodup_tail]. subst.
      destruct (equiv_decb a u) eqn:Ha_u.
      + inversion Hsplit. subst popped rest. exact Hnodup_tail.
      + destruct (stack_split_at stk u) as [popped' rest'] eqn:Hinner.
        inversion Hsplit. subst popped rest.
        eapply IH; eauto.
  Qed.

  Lemma stack_split_at_suffix_decompose
        (stk: list V) (u v: V) (pu su pv rv: list V):
    NoDup stk ->
    stack_split_at stk u = (pu, su) ->
    In v su ->
    stack_split_at su v = (pv, rv) ->
    stack_split_at stk v = (pu ++ pv, rv).
  Proof.
    revert u v pu su pv rv.
    induction stk as [| a stk IH];
      intros u v pu su pv rv Hnodup Hsplit Hv_su Hsplit_su.
    - simpl in Hsplit. inversion Hsplit. subst su.
      simpl in Hv_su. contradiction.
    - simpl in Hsplit.
      inversion Hnodup as [| ? ? Ha_notin Hnodup_tail]. subst.
      destruct (equiv_decb a u) eqn:Hau.
      + inversion Hsplit. subst pu su.
        simpl.
        destruct (equiv_decb a v) eqn:Hav.
        * assert (Ha_eq_v: a = v).
          { unfold equiv_decb in Hav.
            destruct (equiv_dec a v) as [Heq | Hneq].
            - exact Heq.
            - inversion Hav. }
          subst v. exfalso. exact (Ha_notin Hv_su).
        * rewrite Hsplit_su. reflexivity.
      + destruct (stack_split_at stk u) as [pu' su'] eqn:Hinner.
        inversion Hsplit. subst pu su.
        simpl.
        destruct (equiv_decb a v) eqn:Hav.
        * assert (Ha_eq_v: a = v).
          { unfold equiv_decb in Hav.
            destruct (equiv_dec a v) as [Heq | Hneq].
            - exact Heq.
            - inversion Hav. }
          subst v. exfalso. apply Ha_notin.
          eapply stack_split_at_in_original; eauto.
        * rewrite (IH u v pu' su' pv rv
                     Hnodup_tail Hinner Hv_su Hsplit_su).
          reflexivity.
  Qed.

  Lemma stack_split_at_suffix_popped_lift
        (stk: list V) (u v x: V):
    NoDup stk ->
    (match stack_split_at stk u with
     | (_, rest) => In v rest
     end) ->
    (match stack_split_at (snd (stack_split_at stk u)) v with
     | (popped, _) => In x popped
     end) ->
    match stack_split_at stk v with
    | (popped, _) => In x popped
    end.
  Proof.
    intros Hnodup Huv Hx.
    destruct (stack_split_at stk u) as [pu su] eqn:Hsu.
    destruct (stack_split_at su v) as [pv rv] eqn:Hsv.
    simpl in Huv, Hx |- *.
    assert (Hx_pv: In x pv).
    { change (match (pv, rv) with
              | (popped, _) => In x popped
              end).
      rewrite <- Hsv. exact Hx. }
    rewrite (stack_split_at_suffix_decompose
               stk u v pu su pv rv Hnodup Hsu Huv Hsv).
    apply in_or_app. right. exact Hx_pv.
  Qed.

  Lemma stack_split_at_suffix_rest_lift
        (stk: list V) (u v x: V):
    NoDup stk ->
    (match stack_split_at stk u with
     | (_, rest) => In v rest
     end) ->
    (match stack_split_at (snd (stack_split_at stk u)) v with
     | (_, rest) => In x rest
     end) ->
    match stack_split_at stk v with
    | (_, rest) => In x rest
    end.
  Proof.
    intros Hnodup Huv Hx.
    destruct (stack_split_at stk u) as [pu su] eqn:Hsu.
    destruct (stack_split_at su v) as [pv rv] eqn:Hsv.
    simpl in Huv, Hx |- *.
    assert (Hx_rv: In x rv).
    { change (match (pv, rv) with
              | (_, rest) => In x rest
              end).
      rewrite <- Hsv. exact Hx. }
    rewrite (stack_split_at_suffix_decompose
               stk u v pu su pv rv Hnodup Hsu Huv Hsv).
    exact Hx_rv.
  Qed.

  Lemma stack_split_at_suffix_popped_preserves_of_rest
        (stk: list V) (u v x: V):
    NoDup stk ->
    (match stack_split_at stk u with
     | (_, rest) => In v rest
     end) ->
    (match stack_split_at stk u with
     | (_, rest) => In x rest
     end) ->
    (match stack_split_at stk v with
     | (popped, _) => In x popped
     end) ->
    match stack_split_at (snd (stack_split_at stk u)) v with
    | (popped, _) => In x popped
    end.
  Proof.
    intros Hnodup Huv Hux Hx_popped.
    destruct (stack_split_at stk u) as [pu su] eqn:Hsu.
    destruct (stack_split_at su v) as [pv rv] eqn:Hsv.
    simpl in Huv, Hux, Hx_popped |- *.
    assert (Hdecomp:
              stack_split_at stk v = (pu ++ pv, rv)).
    { eapply stack_split_at_suffix_decompose; eauto. }
    rewrite Hdecomp in Hx_popped.
    apply in_app_or in Hx_popped as [Hx_pu | Hx_pv].
    - exfalso.
      exact (stack_split_at_popped_rest_disjoint
               stk u x pu su Hsu Hnodup Hx_pu Hux).
    - rewrite Hsv. exact Hx_pv.
  Qed.

  Lemma popped_segment_after_pop_lift_original
        (u v x: V) (s: St):
    StackNoDup s ->
    RestStack u s v ->
    PoppedSegment v (pop_scc_state s u) x ->
    PoppedSegment v s x.
  Proof.
    unfold StackNoDup, RestStack, PoppedSegment.
    intros Hnodup Huv Hpopped.
    unfold pop_scc_state in Hpopped.
    destruct (stack_split_at (stack s) u) as [pu su] eqn:Hsu.
    simpl in Hpopped.
    assert (Huv_full:
              match stack_split_at (stack s) u with
              | (_, rest) => In v rest
              end).
    { rewrite Hsu. simpl. exact Huv. }
    assert (Hpopped_full:
              match stack_split_at (snd (stack_split_at (stack s) u)) v with
              | (popped, _) => In x popped
              end).
    { rewrite Hsu. simpl. exact Hpopped. }
    exact (stack_split_at_suffix_popped_lift
             (stack s) u v x Hnodup Huv_full Hpopped_full).
  Qed.

  Lemma rest_stack_after_pop_lift_original
        (u v x: V) (s: St):
    StackNoDup s ->
    RestStack u s v ->
    RestStack v (pop_scc_state s u) x ->
    RestStack v s x.
  Proof.
    unfold StackNoDup, RestStack.
    intros Hnodup Huv Hrest.
    unfold pop_scc_state in Hrest.
    destruct (stack_split_at (stack s) u) as [pu su] eqn:Hsu.
    simpl in Hrest.
    assert (Huv_full:
              match stack_split_at (stack s) u with
              | (_, rest) => In v rest
              end).
    { rewrite Hsu. simpl. exact Huv. }
    assert (Hrest_full:
              match stack_split_at (snd (stack_split_at (stack s) u)) v with
              | (_, rest) => In x rest
              end).
    { rewrite Hsu. simpl. exact Hrest. }
    exact (stack_split_at_suffix_rest_lift
             (stack s) u v x Hnodup Huv_full Hrest_full).
  Qed.

  Lemma popped_segment_after_pop_preserves_of_rest
        (u v x: V) (s: St):
    StackNoDup s ->
    RestStack u s v ->
    RestStack u s x ->
    PoppedSegment v s x ->
    PoppedSegment v (pop_scc_state s u) x.
  Proof.
    unfold StackNoDup, RestStack, PoppedSegment.
    intros Hnodup Huv Hux Hpopped.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s) u) as [pu su] eqn:Hsu.
    simpl.
    assert (Huv_full:
              match stack_split_at (stack s) u with
              | (_, rest) => In v rest
              end).
    { rewrite Hsu. simpl. exact Huv. }
    assert (Hux_full:
              match stack_split_at (stack s) u with
              | (_, rest) => In x rest
              end).
    { rewrite Hsu. simpl. exact Hux. }
    assert (Hres:
              match stack_split_at (snd (stack_split_at (stack s) u)) v with
              | (popped, _) => In x popped
              end).
    { exact (stack_split_at_suffix_popped_preserves_of_rest
               (stack s) u v x Hnodup Huv_full Hux_full Hpopped). }
    rewrite Hsu in Hres. simpl in Hres. exact Hres.
  Qed.

  Lemma popped_segment_after_pop_in_root_rest
        (u v x: V) (s: St):
    PoppedSegment v (pop_scc_state s u) x ->
    RestStack u s x.
  Proof.
    unfold PoppedSegment, RestStack.
    intros Hpopped.
    unfold pop_scc_state in Hpopped.
    destruct (stack_split_at (stack s) u) as [pu su] eqn:Hsu.
    simpl in Hpopped.
    destruct (stack_split_at su v) as [pv rv] eqn:Hsv.
    exact (stack_split_at_in_original
             su v x pv rv Hsv (or_introl Hpopped)).
  Qed.

  Lemma pop_scc_preserves_parent_traversal_stack_frame_from_rest
        (ancestor current root0: V) (s_before s: St):
    StackNoDup s ->
    RestStack root0 s current ->
    RestStack root0 s ancestor ->
    ParentTraversalStackFrame ancestor current s_before s ->
    ParentTraversalStackFrame ancestor current s_before (pop_scc_state s root0).
  Proof.
    intros Hnodup Hroot_current Hroot_ancestor Hframe.
    destruct Hframe as [Hpopped_frame [Hrest_frame [Hvis_frame Hdfn_frame]]].
    split.
    - intros x Hpopped_after.
      assert (Hpopped_before:
                PoppedSegment ancestor s x).
      { eapply popped_segment_after_pop_lift_original; eauto. }
      destruct (Hpopped_frame x Hpopped_before)
        as [Hpopped_current_before | Hpopped_old].
      + left.
        assert (Hroot_x: RestStack root0 s x).
        { eapply popped_segment_after_pop_in_root_rest; eauto. }
        eapply popped_segment_after_pop_preserves_of_rest; eauto.
      + right. exact Hpopped_old.
    - split.
      + intros b Hrest_after.
        apply Hrest_frame.
        eapply rest_stack_after_pop_lift_original; eauto.
      + split.
        * intros y Hvis_before.
          unfold Visited in *. unfold pop_scc_state. simpl.
          destruct (stack_split_at (stack s) root0) as [popped rest].
          simpl.
          exact (Hvis_frame y Hvis_before).
        * intros b Hrest_after.
          assert (Hrest_before: RestStack ancestor s b).
          { eapply rest_stack_after_pop_lift_original; eauto. }
          unfold pop_scc_state.
          destruct (stack_split_at (stack s) root0) as [popped rest].
          simpl.
          exact (Hdfn_frame b Hrest_before).
  Qed.

  Lemma pop_scc_preserves_parent_traversal_stack_frame_from_rest_hoare
        (ancestor current root0: V) (s_before: St):
    Hoare
      (fun s: St =>
         StackNoDup s /\
         RestStack root0 s current /\
         RestStack root0 s ancestor /\
         ParentTraversalStackFrame ancestor current s_before s)
      (pop_scc root0)
      (fun _ s =>
         ParentTraversalStackFrame ancestor current s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hnodup [Hroot_current [Hroot_ancestor Hframe]]] Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    eapply pop_scc_preserves_parent_traversal_stack_frame_from_rest; eauto.
  Qed.

  Lemma pop_scc_preserves_stack_nodup (u: V):
    Hoare
      (StackNoDup)
      (pop_scc u)
      (fun _ s => StackNoDup s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 Hnodup Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold pop_scc_state, StackNoDup in *.
    destruct (stack_split_at (stack s1) u) as [popped rest] eqn:Hsplit.
    simpl.
    eapply stack_split_at_rest_nodup; eauto.
  Qed.

  Lemma pop_scc_preserves_order_facts (u: V):
    Hoare
      (fun s: St => OrderFacts s /\ Active u s)
      (pop_scc u)
      (fun _ s => OrderFacts s).
  Proof.
    unfold OrderFacts.
    apply Hoare_conj with
      (Q1 := fun _ s => stack_dfn_order s).
    { eapply Hoare_conseq_pre.
      2: apply pop_scc_preserves_stack_dfn_order.
      intros s [[Horder _] Hu_active].
      exact (conj Horder Hu_active). }
    apply Hoare_conj with
      (Q1 := fun _ s => dfn_injective s).
    { unfold pop_scc. intro_state. hoare_auto_s.
      subst s. unfold pop_scc_state.
      destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
      simpl. exact (proj1 (proj2 (proj1 H))). }
    { eapply Hoare_conseq_pre.
      2: apply pop_scc_preserves_stack_nodup.
      intros s [[_ [_ Hnodup]] _]. exact Hnodup. }
  Qed.

  Lemma pop_scc_removes_root (u: V):
    Hoare
      (fun s: St => Active u s /\ StackNoDup s)
      (pop_scc u)
      (fun _ s => ~ Active u s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hu_active Hnodup] Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold Active, pop_scc_state in *.
    destruct (stack_split_at (stack s1) u) as [popped rest] eqn:Hsplit.
    simpl.
    intros Hu_rest.
    assert (Hu_popped: In u popped).
    { eapply stack_split_at_root_in_popped; eauto. }
    unfold StackNoDup in Hnodup.
    eapply stack_split_at_popped_rest_disjoint; eauto.
  Qed.

  Lemma popped_segment_in_stack
        (u: V) (s: St):
    forall x, PoppedSegment u s x -> In x (stack s).
  Proof.
    intros x Hpopped.
    unfold PoppedSegment in Hpopped.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    apply (stack_split_at_in_original (stack s) u x popped rest Hsplit).
    left. exact Hpopped.
  Qed.

  Lemma rest_stack_active
        (u: V) (s: St):
    forall x, RestStack u s x -> Active x s.
  Proof.
    intros x Hrest.
    unfold RestStack in Hrest.
    unfold Active.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    apply (stack_split_at_in_original (stack s) u x popped rest Hsplit).
    right. exact Hrest.
  Qed.

  Lemma pop_scc_preserves_parent_low_frame_from_below
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         ParentLowFrame parent done s_before s /\
         ParentOldCandidatesBelowChild parent child done s_before s)
      (pop_scc child)
      (fun _ s => ParentLowFrame parent done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hframe Hbelow] Hexec.
    destruct Hframe as [Hlow_eq [Hframe_fwd Hframe_bound]].
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s1) child) as [popped rest] eqn:Hsplit.
    simpl.
    unfold ParentLowFrame.
    split; [exact Hlow_eq |].
    split.
    - intros b Hcandidate_before.
      destruct (Hframe_fwd b Hcandidate_before)
        as [Hcandidate_s Hdfn_eq].
      assert (Hb_rest: In b rest).
      { pose proof (Hbelow b Hcandidate_before) as Hrest.
        unfold RestStack in Hrest. rewrite Hsplit in Hrest.
        exact Hrest. }
      split.
      + unfold PartialLowCandidate in Hcandidate_s |- *.
        destruct Hcandidate_s as [Hb_parent | Htarget].
        * left. exact Hb_parent.
        * right. unfold PartialActiveTarget in Htarget |- *.
          destruct Htarget as [Hdirect | Hsubtree].
          -- destruct Hdirect as
               [a [Hdone_a [Hb_eq_a [Hedge_pa [Hactive_a Hnot_tree]]]]].
             left. exists a.
             split; [exact Hdone_a |].
             split; [exact Hb_eq_a |].
             split; [exact Hedge_pa |].
             split.
             ++ subst b. unfold Active. exact Hb_rest.
             ++ intros Htree. exact (Hnot_tree Htree).
          -- destruct Hsubtree as
               [old_child [x
                 [Hdone_old [Hedge_old [Hfa_old [Hfane_old
                   [Hreach [Hedge_x_b [Hactive_b Hnot_tree]]]]]]]]].
             right. exists old_child, x.
             split; [exact Hdone_old |].
             split; [exact Hedge_old |].
             split; [exact Hfa_old |].
             split; [exact Hfane_old |].
             split; [exact Hreach |].
             split; [exact Hedge_x_b |].
             split.
             ++ unfold Active. exact Hb_rest.
             ++ intros Htree. exact (Hnot_tree Htree).
      + exact Hdfn_eq.
    - intros b Hcandidate_after.
      apply Hframe_bound.
      unfold PartialLowCandidate in Hcandidate_after |- *.
      destruct Hcandidate_after as [Hb_parent | Htarget].
      + left. exact Hb_parent.
      + right. unfold PartialActiveTarget in Htarget |- *.
        destruct Htarget as [Hdirect | Hsubtree].
        * destruct Hdirect as
            [a [Hdone_a [Hb_eq_a [Hedge_pa [Hactive_a_post Hnot_tree]]]]].
          left. exists a. repeat split; auto.
          unfold Active in *.
          apply (stack_split_at_in_original
                   (stack s1) child a popped rest Hsplit).
          right. exact Hactive_a_post.
        * destruct Hsubtree as
            [old_child [x
              [Hdone_old [Hedge_old [Hfa_old [Hfane_old
                [Hreach [Hedge_x_b [Hactive_b_post Hnot_tree]]]]]]]]].
          right. exists old_child, x. repeat split; auto.
          unfold Active in *.
          apply (stack_split_at_in_original
                   (stack s1) child b popped rest Hsplit).
          right. exact Hactive_b_post.
  Qed.

  Lemma pop_scc_preserves_loop_core_shape_any
        (center u: V) (done: V -> Prop):
    Hoare
      (LoopCoreShape center done)
      (pop_scc u)
      (fun _ s => LoopCoreShape center done s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 Hshape Hexec.
    destruct Hshape as
      [Hwf [Htree [Hcenter_vis [Hdone_edge [Hdone_vis Hprocessed]]]]].
    assert (Hwf_after: wf_scc_state g root s2).
    { pose proof (pop_scc_preserves_wf_scc_state g root u) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hwf Hexec). }
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s1) u) as [popped rest] eqn:Hsplit.
    simpl.
    unfold pop_scc_state in Hwf_after.
    rewrite Hsplit in Hwf_after. simpl in Hwf_after.
    split; [exact Hwf_after |].
    split.
    - unfold TreeEdgesAreGraphEdges in *. simpl in *. exact Htree.
    - split; [exact Hcenter_vis |].
      split; [exact Hdone_edge |].
      split.
      + intros a Hdone. exact (Hdone_vis a Hdone).
      + unfold ProcessedTreeChild in *. simpl in *.
        exact Hprocessed.
  Qed.

  Lemma pop_scc_produces_child_no_active_target
        (child: V):
    Hoare
      (fun s: St =>
         TreeEdgesAreGraphEdges s /\
         PoppedSegmentNoActiveReach child s /\
         Active child s)
      (pop_scc child)
      (fun _ s => ChildNoActiveTarget child s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Htree [Hno_active_reach Hchild_active]] Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s1) child) as [popped rest] eqn:Hsplit.
    simpl.
    unfold ChildNoActiveTarget.
    intros x b Hreach_child_x Hedge_x_b Hb_active_post _.
    assert (Hchild_popped: PoppedSegment child s1 child).
    { unfold PoppedSegment. rewrite Hsplit.
      eapply stack_split_at_root_in_popped; eauto. }
    assert (Hb_rest: RestStack child s1 b).
    { unfold RestStack. rewrite Hsplit. exact Hb_active_post. }
    assert (Hgraph_child_x: dg_reachable g child x).
    { eapply tree_reachable_to_graph_reachable; eauto. }
    assert (Hgraph_child_b: dg_reachable g child b).
    { eapply dg_reachable_step_reachable; eauto. }
    exact (Hno_active_reach child b
             Hchild_popped Hgraph_child_b Hb_rest).
  Qed.

  Lemma loop_traversal_add_active_edge
        (u v: V) (done: V -> Prop) (s: St):
    LoopInv u done s ->
    LoopTraversalComplete u done s ->
    Edge u v ->
    ~ done v ->
    Visited v s ->
    Active v s ->
    LoopTraversalComplete u (done_after done v) s.
  Proof.
    intros Hinv [Hno Hcut] Hedge Hnot_done Hvis Hactive.
    split.
    - intros x y Hpopped Hxy Hnotvis_y.
      destruct (Hno x y Hpopped Hxy Hnotvis_y) as [Hx Hnot_done_y].
      split; [exact Hx |].
      intros Hdone_after_y.
      destruct (done_after_elim done v y Hdone_after_y)
        as [Hdone_y | Hy_eq_v].
      + exact (Hnot_done_y Hdone_y).
      + subst y. exact (Hnotvis_y Hvis).
    - intros x b Hpopped Hxb Hrest.
      destruct (Hcut x b Hpopped Hxb Hrest) as
        [[Hx Hnot_done_b] | [target [Hcandidate Hdfn]]].
      + destruct (classic (b = v)) as [Hb_eq_v | Hb_ne_v].
        * subst b. right. exists v. split.
          -- apply partial_low_candidate_direct_active; auto.
             eapply current_active_edge_not_tree; eauto.
          -- lia.
        * left. split; [exact Hx |].
          intros Hdone_after_b.
          destruct (done_after_elim done v b Hdone_after_b)
            as [Hdone_b | Hb_eq_v].
          -- exact (Hnot_done_b Hdone_b).
          -- exact (Hb_ne_v Hb_eq_v).
      + right. exists target. split; [| exact Hdfn].
        apply partial_low_candidate_done_mono. exact Hcandidate.
  Qed.

  Lemma loop_traversal_add_inactive_edge
        (u v: V) (done: V -> Prop) (s: St):
    LoopTraversalComplete u done s ->
    ~ done v ->
    Visited v s ->
    ~ Active v s ->
    LoopTraversalComplete u (done_after done v) s.
  Proof.
    intros [Hno Hcut] Hnot_done Hvis Hnot_active.
    split.
    - intros x y Hpopped Hxy Hnotvis_y.
      destruct (Hno x y Hpopped Hxy Hnotvis_y) as [Hx Hnot_done_y].
      split; [exact Hx |].
      intros Hdone_after_y.
      destruct (done_after_elim done v y Hdone_after_y)
        as [Hdone_y | Hy_eq_v].
      + exact (Hnot_done_y Hdone_y).
      + subst y. exact (Hnotvis_y Hvis).
    - intros x b Hpopped Hxb Hrest.
      destruct (Hcut x b Hpopped Hxb Hrest) as
        [[Hx Hnot_done_b] | [target [Hcandidate Hdfn]]].
      + destruct (classic (b = v)) as [Hb_eq_v | Hb_ne_v].
        * subst b. exfalso.
          apply Hnot_active.
          eapply rest_stack_active; eauto.
        * left. split; [exact Hx |].
          intros Hdone_after_b.
          destruct (done_after_elim done v b Hdone_after_b)
            as [Hdone_b | Hb_eq_v].
          -- exact (Hnot_done_b Hdone_b).
          -- exact (Hb_ne_v Hb_eq_v).
      + right. exists target. split; [| exact Hdfn].
        apply partial_low_candidate_done_mono. exact Hcandidate.
  Qed.

  Lemma loop_traversal_complete_to_root_traversal_complete
        (u: V) (s: St):
    LoopTraversalComplete u (edge_set u) s ->
    RootTraversalComplete u s.
  Proof.
    intros [Hno Hcut].
    split.
    - intros x y Hpopped Hedge Hnotvis.
      destruct (Hno x y Hpopped Hedge Hnotvis) as [Hx Hnot_done].
      subst x. exact (Hnot_done Hedge).
    - intros x b Hpopped Hedge Hrest.
      destruct (Hcut x b Hpopped Hedge Hrest) as
        [[Hx Hnot_done] | [target [Hcandidate Hdfn]]].
      + subst x. exfalso. exact (Hnot_done Hedge).
      + exists target. split; [exact Hcandidate | exact Hdfn].
  Qed.

  Lemma process_edge_preserves_loop_traversal_complete
        (u v: V) (done: V -> Prop) (W: RecProgram):
    VisitChildTraversalContract W ->
    Hoare
      (fun s: St =>
         LoopInv u done s /\
         LoopTraversalComplete u done s /\
         Edge u v /\
         ~ done v)
      (process_edge u W v)
      (fun _ s => LoopTraversalComplete u (done_after done v) s).
  Proof.
    intros Hchild_traversal.
    unfold process_edge, if_else.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_bind with
        (Q := fun (_: unit) s =>
                ParentRecursivePre u v done s /\
                LoopTraversalComplete u done s).
      + apply Hoare_conj with
          (Q1 := fun _ s => ParentRecursivePre u v done s).
        * eapply Hoare_conseq_pre.
          2: apply set_fa_pending_prepares_parent_recursive_pre.
          intros s1 [Hnotvis Hs1]. subst s1.
          destruct H as [Hloop [_ [Hedge _]]].
          exact (conj Hloop (conj Hedge Hnotvis)).
        * eapply Hoare_conseq_pre.
          2: apply set_fa_pending_preserves_loop_traversal_complete_cmd.
          intros s1 [Hnotvis Hs1]. subst s1.
          destruct H as [Hloop [Htraversal _]].
          destruct Hloop as [_ [Hshape _]].
          destruct Hshape as [_ [_ [_ [_ [Hdone_vis _]]]]].
          exact (conj Hnotvis (conj Hdone_vis Htraversal)).
      + simpl. intros _.
        eapply Hoare_bind with
          (Q := fun (_: unit) s =>
                  LoopTraversalComplete u (done_after done v) s).
        * eapply Hoare_conseq_post.
          2: { apply Hchild_traversal. }
          intros _ s [s_before [_ [_ [_ Htraversal_after]]]].
          exact Htraversal_after.
        * simpl. intros _.
          apply get_low_update_low_preserves_loop_traversal_complete.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hvisited_by_classic Hs1]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: apply get_dfn_update_low_preserves_loop_traversal_complete.
        intros s1 [Hactive Hs1]. subst s1.
        destruct H as [Hloop [Htraversal [Hedge Hnot_done]]].
        assert (Hvis: Visited v s0).
        { unfold Visited. apply NNPP. exact Hvisited_by_classic. }
        assert (Hactive': Active v s0).
        { unfold Active. exact Hactive. }
        eapply loop_traversal_add_active_edge; eauto.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        simpl. intros _ s [Heq Hnotactive]. subst s.
        destruct H as [_ [Htraversal [_ Hnot_done]]].
        assert (Hvis: Visited v s0).
        { unfold Visited. apply NNPP. exact Hvisited_by_classic. }
        assert (Hnotactive': ~ Active v s0).
        { unfold Active. exact Hnotactive. }
        eapply loop_traversal_add_inactive_edge; eauto.
  Qed.

  Lemma edge_loop_preserves_loop_inv_and_root_traversal_complete
        (u: V) (W: RecProgram):
    VisitChildContract W ->
    VisitChildTraversalContract W ->
    Hoare
      (fun s: St =>
         LoopInv u ∅ s /\
         LoopTraversalComplete u ∅ s)
      (forset (edge_set u) (process_edge u W))
      (fun _ s =>
         LoopInv u (edge_set u) s /\
         RootTraversalComplete u s).
  Proof.
    intros Hchild Hchild_traversal.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_forset with
        (P := fun done s =>
                LoopInv u done s /\
                LoopTraversalComplete u done s)
        (universe := edge_set u).
      - intros done1 done2 Hdone s1 s2 Heq. subst s2.
        split; intros [Hloop Htraversal]; split.
        + eapply loop_inv_done_equiv; eauto.
        + eapply loop_traversal_complete_done_equiv; eauto.
        + eapply loop_inv_done_equiv.
          * symmetry. exact Hdone.
          * exact Hloop.
        + eapply loop_traversal_complete_done_equiv.
          * symmetry. exact Hdone.
          * exact Htraversal.
      - intros done a _ Hedge Hnot_done.
        apply Hoare_conj with
          (Q1 := fun _ s => LoopInv u (done_after done a) s).
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
        + eapply Hoare_conseq_pre.
          2: {
            eapply process_edge_preserves_loop_traversal_complete.
            exact Hchild_traversal. }
          intros s [Hloop Htraversal].
          exact (conj Hloop
                  (conj Htraversal
                    (conj Hedge Hnot_done))). }
    intros _ s [Hloop Htraversal].
    split; [exact Hloop |].
    apply loop_traversal_complete_to_root_traversal_complete.
    exact Htraversal.
  Qed.

  Lemma edge_loop_produces_root_traversal_complete
        (u: V) (W: RecProgram):
    VisitChildContract W ->
    VisitChildTraversalContract W ->
    Hoare
      (fun s: St =>
         LoopInv u ∅ s /\
         LoopTraversalComplete u ∅ s)
      (forset (edge_set u) (process_edge u W))
      (fun _ s => RootTraversalComplete u s).
  Proof.
    intros Hchild Hchild_traversal.
    eapply Hoare_conseq_post.
    2: {
      apply edge_loop_preserves_loop_inv_and_root_traversal_complete;
        auto. }
    intros _ s [_ Htraversal]. exact Htraversal.
  Qed.

  Lemma edge_loop_preserves_nested_parent_context_with_rest
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (s_before: St)
        (W: RecProgram):
    VisitChildContract W ->
    VisitChildTraversalContract W ->
    VisitFrameContract W ->
    Hoare
      (fun s: St =>
         LoopInv loop_root ∅ s /\
         LoopTraversalComplete loop_root ∅ s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s /\
         RestStack loop_root s current)
      (forset (edge_set loop_root) (process_edge loop_root W))
      (fun _ s =>
         LoopInv loop_root (edge_set loop_root) s /\
         RootTraversalComplete loop_root s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s /\
         RestStack loop_root s current).
  Proof.
    intros Hchild Hchild_traversal Hframe_contract.
    unfold Hoare.
    intros s1 retv s2
      [Hloop_pre [Htraversal_pre
        [Hframe_pre [Hdisjoint_pre Hrest_pre]]]] Hexec.
    assert (Hcurrent_ne_root: current <> loop_root).
    { intros Hcurrent_eq_root.
      subst current.
      destruct Hloop_pre as [Haux_pre _].
      destruct Haux_pre as [_ [Hroot_active_pre [_ [_ Hnodup_pre]]]].
      exact (rest_stack_member_ne_root
               loop_root loop_root s1 Hnodup_pre
               Hroot_active_pre Hrest_pre eq_refl). }
    assert (Hloop_and_traversal:
              LoopInv loop_root (edge_set loop_root) s2 /\
              RootTraversalComplete loop_root s2).
    { pose proof
        (edge_loop_preserves_loop_inv_and_root_traversal_complete
           loop_root W Hchild Hchild_traversal) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hloop_pre Htraversal_pre) Hexec). }
    assert (Hframe_and_disjoint:
              ParentFrameForChild ancestor current ancestor_done
                s_before s2 /\
              NestedFrameDisjoint ancestor current loop_root
                ancestor_done s2).
    { pose proof
        (edge_loop_preserves_nested_parent_frame
           ancestor current loop_root ancestor_done s_before W
           Hchild Hframe_contract) as Hhoare.
      unfold Hoare in Hhoare.
      destruct (Hhoare s1 retv s2
                       (conj Hloop_pre
                         (conj Hframe_pre Hdisjoint_pre))
                       Hexec)
        as [_ [Hframe_post Hdisjoint_post]].
      exact (conj Hframe_post Hdisjoint_post). }
    destruct Hloop_and_traversal as [Hloop_post Htraversal_post].
    destruct Hframe_and_disjoint as [Hframe_post Hdisjoint_post].
    assert (Hrest_post: RestStack loop_root s2 current).
    { eapply nested_context_derives_rest_stack; eauto. }
    exact (conj Hloop_post
            (conj Htraversal_post
              (conj Hframe_post
                (conj Hdisjoint_post Hrest_post)))).
  Qed.

  Lemma edge_loop_preserves_root_pre_maybe_pop_from_traversal_contract
        (u: V) (W: RecProgram):
    VisitChildContract W ->
    VisitChildTraversalContract W ->
    Hoare
      (fun s: St =>
         LoopInv u ∅ s /\
         LoopTraversalComplete u ∅ s)
      (forset (edge_set u) (process_edge u W))
      (fun _ s => RootPreMaybePop u s).
  Proof.
    intros Hchild Hchild_traversal.
    eapply Hoare_conseq_post.
    2: {
      apply edge_loop_preserves_loop_inv_and_root_traversal_complete;
        auto. }
    intros _ s [Hloop Htraversal].
    eapply edge_loop_post_to_root_pre_maybe_pop; eauto.
  Qed.

  Lemma root_pre_pop_low_eq_derives_no_active_reach_with_traversal
        (u: V) (s: St):
    RootPrePop u s ->
    RootTraversalComplete u s ->
    low s u = dfn s u ->
    PoppedSegmentNoActiveReach u s.
  Proof.
    intros Hpre Htraversal Hlow_eq.
    destruct Hpre as [Hloop [_ Hrest_older]].
    destruct Hloop as [Haux [Hshape [Hclosed [_ Hcomplete]]]].
    destruct Haux as [_ [_ [_ [_ Hnodup]]]].
    destruct Htraversal as [Hno_unvisited_step Htarget_cut].
    unfold PoppedSegmentNoActiveReach.
    intros x b Hpopped Hreach Hb_rest.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    assert (Hpopped_in: In x popped).
    { unfold PoppedSegment in Hpopped. rewrite Hsplit in Hpopped.
      exact Hpopped. }
    assert (Hb_rest_in: In b rest).
    { unfold RestStack in Hb_rest. rewrite Hsplit in Hb_rest.
      exact Hb_rest. }
    assert (Hnot_b_popped: ~ In b popped).
    { intros Hb_popped.
      unfold StackNoDup in Hnodup.
      eapply stack_split_at_popped_rest_disjoint; eauto. }
    assert (Hnot_b_popped_seg: ~ PoppedSegment u s b).
    { unfold PoppedSegment. rewrite Hsplit. exact Hnot_b_popped. }
    destruct (dg_reachable_vertex_path g x b Hreach) as [path Hpath].
    destruct (dg_vertex_path_exit_from_pred
                g (fun z => PoppedSegment u s z) x b path
                Hpopped Hnot_b_popped_seg Hpath)
      as [a [c [Ha_popped [Hc_not_popped [Hstep_ac [Hreach_x_a Hreach_c_b]]]]]].
    destruct (classic (Visited c s)) as [Hvis_c | Hnotvis_c].
    - destruct (classic (In c (stack s))) as [Hc_stack | Hc_not_stack].
      + destruct (stack_split_at_in_cases
                    (stack s) u c popped rest Hsplit Hc_stack)
          as [Hc_popped | Hc_rest].
        * exfalso. apply Hc_not_popped.
          unfold PoppedSegment. rewrite Hsplit. exact Hc_popped.
        * destruct (Htarget_cut a c Ha_popped Hstep_ac) as
            [target [Hcandidate Htarget_le_c]].
          { unfold RestStack. rewrite Hsplit. exact Hc_rest. }
          assert (Hc_lt_u: dfn s c < dfn s u).
          { apply Hrest_older.
            unfold RestStack. rewrite Hsplit. exact Hc_rest. }
          pose proof (Hcomplete target Hcandidate) as Hlow_le_target.
          rewrite Hlow_eq in Hlow_le_target. lia.
      + assert (Hb_active: Active b s).
        { unfold Active.
          apply (stack_split_at_in_original
                   (stack s) u b popped rest Hsplit).
          right. exact Hb_rest_in. }
        exact (Hclosed c b Hvis_c Hc_not_stack Hreach_c_b Hb_active).
    - eapply Hno_unvisited_step; eauto.
  Qed.

  Lemma root_pre_pop_low_eq_derives_popped_segment_closed_with_traversal
        (u: V) (s: St):
    RootPrePop u s ->
    RootTraversalComplete u s ->
    low s u = dfn s u ->
    PoppedSegmentClosed u s.
  Proof.
    intros Hpre Htraversal Hlow_eq.
    pose proof
      (root_pre_pop_low_eq_derives_no_active_reach_with_traversal
         u s Hpre Htraversal Hlow_eq) as Hno_active_reach.
    destruct Hpre as [Hloop _].
    destruct Hloop as [Haux [Hshape _]].
    destruct Haux as [Hsettled _].
    destruct Hshape as [Hwf _].
    destruct Hwf as [Hstack_vis _].
    destruct Htraversal as [Hno_unvisited_step _].
    unfold PoppedSegmentClosed.
    intros x y Hpopped Hreach.
    destruct (classic (Visited y s)) as [Hvis_y | Hnotvis_y].
    - exact Hvis_y.
    - exfalso.
      assert (Hx_stack: In x (stack s)).
      { eapply popped_segment_in_stack; eauto. }
      assert (Hx_vis: Visited x s).
      { apply Hstack_vis. exact Hx_stack. }
      destruct (dg_reachable_vertex_path g x y Hreach) as [path Hpath].
      destruct (dg_vertex_path_last_exit_from_pred
                  g (fun z => Visited z s) x y path
                  Hx_vis Hnotvis_y Hpath)
        as [a [b [suffix
          [Hvis_a [Hnotvis_b [Hstep_ab [Hreach_x_a [_ _]]]]]]]].
      destruct (classic (In a (stack s))) as [Ha_stack | Ha_not_stack].
      + destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
        destruct (stack_split_at_in_cases
                    (stack s) u a popped rest Hsplit Ha_stack)
          as [Ha_popped | Ha_rest].
        * apply (Hno_unvisited_step a b).
          -- unfold PoppedSegment. rewrite Hsplit. exact Ha_popped.
          -- exact Hstep_ab.
          -- exact Hnotvis_b.
        * eapply Hno_active_reach.
          -- exact Hpopped.
          -- exact Hreach_x_a.
          -- unfold RestStack. rewrite Hsplit. exact Ha_rest.
      + apply Hnotvis_b.
        unfold NoUnvisitedReach, settled_closed in Hsettled.
        apply (Hsettled a b).
        * exact Hvis_a.
        * exact Ha_not_stack.
        * apply dg_reachable_step. exact Hstep_ab.
  Qed.

  Lemma root_pre_pop_low_eq_derives_pop_cuts_with_traversal
        (u: V) (s: St):
    RootPrePop u s ->
    RootTraversalComplete u s ->
    low s u = dfn s u ->
    RootPopCuts u s.
  Proof.
    intros Hpre Htraversal Hlow_eq.
    split.
    - eapply root_pre_pop_low_eq_derives_popped_segment_closed_with_traversal;
        eauto.
    - eapply root_pre_pop_low_eq_derives_no_active_reach_with_traversal;
        eauto.
  Qed.

  Lemma root_pre_maybe_pop_low_eq_derives_pop_cuts
        (u: V) (s: St):
    RootPreMaybePop u s ->
    low s u = dfn s u ->
    RootPopCuts u s.
  Proof.
    intros [Hroot Htraversal] Hlow_eq.
    eapply root_pre_pop_low_eq_derives_pop_cuts_with_traversal; eauto.
  Qed.

  Lemma pop_scc_restores_no_unvisited_reach (u: V):
    Hoare
      (fun s: St => NoUnvisitedReach s /\ PoppedSegmentClosed u s)
      (pop_scc u)
      (fun _ s => NoUnvisitedReach s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hsettled Hpopped_closed] Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec.
    subst s2.
    unfold NoUnvisitedReach, settled_closed in *.
    unfold pop_scc_state. simpl.
    destruct (stack_split_at (stack s1) u) as [popped rest] eqn:Hsplit.
    simpl.
    intros v w Hvis Hnot_rest Hreach.
    destruct (classic (In v (stack s1))) as [Hv_stack | Hv_not_stack].
    - assert (Hv_popped: In v popped).
      { eapply stack_split_at_popped_of_not_rest; eauto. }
      assert (Hv_popped_seg: PoppedSegment u s1 v).
      { unfold PoppedSegment. rewrite Hsplit. exact Hv_popped. }
      exact (Hpopped_closed v w Hv_popped_seg Hreach).
    - exact (Hsettled v w Hvis Hv_not_stack Hreach).
  Qed.

  Lemma pop_scc_preserves_parent_loop_aux_facts
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         LoopAuxFacts parent s /\
         Active child s /\
         PoppedSegmentClosed child s /\
         ParentOldCandidatesBelowChild parent child done s_before s)
      (pop_scc child)
      (fun _ s => LoopAuxFacts parent s).
  Proof.
    unfold Hoare.
    intros s1 retv s2
      [Haux [Hchild_active [Hpopped_closed Hbelow]]] Hexec.
    destruct Haux as [Hsettled [Hparent_active Horder]].
    assert (Hsettled_after: NoUnvisitedReach s2).
    { pose proof (pop_scc_restores_no_unvisited_reach child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hsettled Hpopped_closed) Hexec). }
    assert (Horder_after: OrderFacts s2).
    { pose proof (pop_scc_preserves_order_facts child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 (conj Horder Hchild_active) Hexec). }
    assert (Hparent_active_after: Active parent s2).
    { pose proof
        (Hbelow parent (partial_low_candidate_root parent done s_before))
        as Hparent_rest.
      assert (Hparent_in_pre: In parent (stack s1)).
      { eapply rest_stack_active; eauto. }
      assert (Hparent_rest_fun:
                forall popped rest,
                  stack_split_at (stack s1) child = (popped, rest) ->
                  In parent rest).
      { intros popped rest Hsplit.
        unfold RestStack in Hparent_rest.
        rewrite Hsplit in Hparent_rest.
        exact Hparent_rest. }
      pose proof (pop_scc_keep_in_stack_below child parent) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hparent_in_pre Hparent_rest_fun)
                    Hexec). }
    unfold LoopAuxFacts.
    exact (conj Hsettled_after (conj Hparent_active_after Horder_after)).
  Qed.

  Lemma pop_scc_restores_closed (u: V):
    Hoare
      (fun s: St =>
         Closed s /\
         PoppedSegmentNoActiveReach u s)
      (pop_scc u)
      (fun _ s => Closed s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hclosed Hno_active_reach] Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec.
    subst s2.
    unfold Closed, Active, Visited in *.
    unfold pop_scc_state. simpl.
    destruct (stack_split_at (stack s1) u) as [popped rest] eqn:Hsplit.
    simpl.
    intros v b Hvis Hnot_rest Hreach Hb_rest.
    assert (Hb_stack: In b (stack s1)).
    { apply (stack_split_at_in_original
               (stack s1) u b popped rest Hsplit).
      right. exact Hb_rest. }
    destruct (classic (In v (stack s1))) as [Hv_stack | Hv_not_stack].
    - assert (Hv_popped: In v popped).
      { eapply stack_split_at_popped_of_not_rest; eauto. }
      assert (Hv_popped_seg: PoppedSegment u s1 v).
      { unfold PoppedSegment. rewrite Hsplit. exact Hv_popped. }
      assert (Hb_rest_seg: RestStack u s1 b).
      { unfold RestStack. rewrite Hsplit. exact Hb_rest. }
      exact (Hno_active_reach v b Hv_popped_seg Hreach Hb_rest_seg).
    - exact (Hclosed v b Hvis Hv_not_stack Hreach Hb_stack).
  Qed.

  Lemma maybe_pop_pop_produces_child_contribution_from_pop_cuts
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         ChildReturnPreMaybePop parent child done s_before s /\
         low s child = dfn s child /\
         RootPopCuts child s)
      (pop_scc child)
      (fun _ s =>
         ChildContributionContract parent child done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hreturn [Hlow_eq_child Hcuts]] Hexec.
    destruct Hreturn as [Hroot Hframe].
    destruct Hroot as [Hpre _].
    destruct Hpre as [Hloop_child _].
    destruct Hloop_child as [Haux_child _].
    destruct Haux_child as [_ [Hchild_active Horder_child]].
    destruct Horder_child as [_ [_ Hnodup_child]].
    destruct Hcuts as [Hpopped_closed Hno_active_reach].
    destruct Hframe as [Hparent_low Hframe].
    destruct Hframe as [Hparent_shape Hframe].
    destruct Hframe as [Hparent_aux Hframe].
    destruct Hframe as [Hclosed Hframe].
    destruct Hframe as [Htree Hframe].
    destruct Hframe as [Hedge_parent_child Hframe].
    destruct Hframe as [Hchild_vis Hframe].
    destruct Hframe as [Hfa_child Hframe].
    destruct Hframe as [Hfane_child Hframe].
    destruct Hframe as [Hdfn_parent_child Hframe].
    destruct Hframe as [Hnot_done_child Hbelow_child].
    destruct Hbelow_child as [Hbelow_child Hstack_frame_child].
    assert (Hparent_low_after:
              ParentLowFrame parent done s_before s2).
    { pose proof (pop_scc_preserves_parent_low_frame_from_below
                    parent child done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hparent_low Hbelow_child) Hexec). }
    assert (Hparent_shape_after:
              LoopCoreShape parent (done_after done child) s2).
    { pose proof (pop_scc_preserves_loop_core_shape_any
                    parent child (done_after done child)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hparent_shape Hexec). }
    assert (Hparent_aux_after: LoopAuxFacts parent s2).
    { pose proof (pop_scc_preserves_parent_loop_aux_facts
                    parent child done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hparent_aux
                      (conj Hchild_active
                        (conj Hpopped_closed Hbelow_child)))
                    Hexec). }
    assert (Hclosed_after: Closed s2).
    { pose proof (pop_scc_restores_closed child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hclosed Hno_active_reach) Hexec). }
    assert (Htree_after: TreeEdgesAreGraphEdges s2).
    { destruct Hparent_shape_after as [_ [Htree_after _]].
      exact Htree_after. }
    assert (Hchild_vis_after: Visited child s2).
    { pose proof (pop_scc_keep_visited child child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hchild_vis Hexec). }
    assert (Hfa_child_after: fa s2 child = parent).
    { pose proof (pop_scc_keep_fa child child parent) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hfa_child Hexec). }
    assert (Hfane_child_after: fa s2 child <> child).
    { rewrite Hfa_child_after.
      intros Hparent_eq_child.
      apply Hfane_child.
      rewrite Hfa_child. exact Hparent_eq_child. }
    assert (Hnot_child_active_after: ~ Active child s2).
    { pose proof (pop_scc_removes_root child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hchild_active Hnodup_child) Hexec). }
    assert (Hlow_child_after: low s2 child = low s1 child).
    { pose proof (pop_scc_keep_low child child (low s1 child)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hdfn_child_after: dfn s2 child = dfn s1 child).
    { pose proof (pop_scc_keep_dfn child child (dfn s1 child)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hdfn_parent_after: dfn s2 parent = dfn s1 parent).
    { pose proof (pop_scc_keep_dfn child parent (dfn s1 parent)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hchild_no_active_target: ChildNoActiveTarget child s2).
    { pose proof (pop_scc_produces_child_no_active_target child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Htree
                      (conj Hno_active_reach Hchild_active))
                    Hexec). }
    unfold ChildContributionContract.
    split; [exact Hparent_low_after |].
    split; [exact Hparent_shape_after |].
    split; [exact Hparent_aux_after |].
    split; [exact Hclosed_after |].
    split; [exact Htree_after |].
    split; [exact Hchild_vis_after |].
    split; [exact Hfa_child_after |].
    split; [exact Hfane_child_after |].
    right.
    split; [exact Hnot_child_active_after |].
    split.
    - lia.
    - split.
      + lia.
      + exact Hchild_no_active_target.
  Qed.

  Lemma maybe_pop_produces_child_contribution
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (ChildReturnPreMaybePop parent child done s_before)
      (If (fun s => low s child = dfn s child) (pop_scc child))
      (fun _ s =>
         ChildContributionContract parent child done s_before s).
  Proof.
    unfold If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: apply maybe_pop_pop_produces_child_contribution_from_pop_cuts.
      intros s1 [Hcond Hs1]. subst s1.
      destruct H as [Hroot Hframe].
      assert (Hcuts: RootPopCuts child s0).
      { eapply root_pre_maybe_pop_low_eq_derives_pop_cuts; eauto. }
      exact (conj (conj Hroot Hframe) (conj Hcond Hcuts)).
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume_s. }
      simpl. intros _ s [Heq Hnot_cond]. subst s.
      eapply maybe_pop_skip_produces_child_contribution; eauto.
  Qed.

  Lemma active_child_return_advances_parent_traversal
        (parent child: V) (done: V -> Prop)
        (s_before s: St):
    LoopInv parent done s_before ->
    LoopTraversalComplete parent done s_before ->
    ParentFrameForChild parent child done s_before s ->
    LoopCoreShape child (edge_set child) s ->
    RootTraversalComplete child s ->
    Active child s ->
    LoopTraversalComplete parent (done_after done child) s.
  Proof.
    intros Hparent_loop Hparent_traversal Hframe Hchild_shape
           Hchild_traversal Hchild_active.
    destruct Hparent_traversal as [Hparent_no Hparent_cut].
    destruct Hchild_traversal as [Hchild_no Hchild_cut].
    destruct Hframe as [Hparent_low Hframe].
    destruct Hframe as [Hparent_shape Hframe].
    destruct Hframe as [Hparent_aux Hframe].
    destruct Hframe as [Hclosed Hframe].
    destruct Hframe as [Htree Hframe].
    destruct Hframe as [Hedge_parent_child Hframe].
    destruct Hframe as [Hchild_vis Hframe].
    destruct Hframe as [Hfa_child Hframe].
    destruct Hframe as [Hfane_child Hframe].
    destruct Hframe as [Hdfn_parent_child Hframe].
    destruct Hframe as [Hnot_done_child Hframe].
    destruct Hframe as [Hbelow_child Hstack_frame].
    destruct Hstack_frame as
      [Hpopped_frame [Hrest_frame [Hvis_frame Hdfn_rest_frame]]].
    pose proof Hparent_low as Hparent_low_all.
    destruct Hparent_low as [_ [Hlow_fwd _]].
    pose proof
      (loop_aux_shape_derives_stack_rest_older_than_root
         parent (done_after done child) s Hparent_aux Hparent_shape)
      as [_ Hrest_older].
    destruct Hparent_aux as [_ [_ [_ [_ Hnodup_parent]]]].
    assert (Hchild_rest_parent: RestStack child s parent).
    { apply Hbelow_child.
      apply partial_low_candidate_root. }
    split.
    - intros x y Hpopped_parent Hedge_xy Hnotvis_y.
      destruct (Hpopped_frame x Hpopped_parent)
        as [Hpopped_child | Hpopped_old].
      + exfalso. eapply Hchild_no; eauto.
      + assert (Hnotvis_before: ~ Visited y s_before).
        { intros Hvis_before. exact (Hnotvis_y (Hvis_frame y Hvis_before)). }
        destruct (Hparent_no x y Hpopped_old Hedge_xy Hnotvis_before)
          as [Hx_parent Hnot_done_y].
        split; [exact Hx_parent |].
        intros Hdone_after_y.
        destruct (done_after_elim done child y Hdone_after_y)
          as [Hdone_y | Hy_eq_child].
        * exact (Hnot_done_y Hdone_y).
        * subst y. exact (Hnotvis_y Hchild_vis).
    - intros x b Hpopped_parent Hedge_xb Hrest_parent_b.
      destruct (Hpopped_frame x Hpopped_parent)
        as [Hpopped_child | Hpopped_old].
      + assert (Hrest_child_b: RestStack child s b).
        { eapply rest_stack_trans; eauto. }
        destruct (Hchild_cut x b Hpopped_child Hedge_xb Hrest_child_b)
          as [target [Hchild_candidate Hdfn_target_b]].
        destruct (child_candidate_lifts_to_parent
                    parent child target done s Hchild_shape
                    Hedge_parent_child Hfa_child Hfane_child
                    Hchild_candidate)
          as [Htarget_eq_child | Hparent_target].
        * subst target. right. exists parent. split.
          -- apply partial_low_candidate_root.
          -- lia.
        * right. exists target. split; [right; exact Hparent_target |].
          exact Hdfn_target_b.
      + assert (Hrest_before_b: RestStack parent s_before b).
        { exact (Hrest_frame b Hrest_parent_b). }
        destruct (Hparent_cut x b Hpopped_old Hedge_xb Hrest_before_b)
          as [[Hx_parent Hnot_done_b] | [target [Hcandidate_old Hdfn_old]]].
        * left. split; [exact Hx_parent |].
          intros Hdone_after_b.
          destruct (done_after_elim done child b Hdone_after_b)
            as [Hdone_b | Hb_eq_child].
          -- exact (Hnot_done_b Hdone_b).
          -- subst b.
             pose proof (Hrest_older child Hrest_parent_b) as Hchild_lt_parent.
             lia.
        * destruct (Hlow_fwd target Hcandidate_old)
            as [Hcandidate_after Hdfn_target_eq].
          pose proof (Hdfn_rest_frame b Hrest_parent_b) as Hdfn_b_eq.
          right. exists target. split.
          -- apply partial_low_candidate_done_mono. exact Hcandidate_after.
          -- lia.
  Qed.

  Lemma pop_child_return_advances_parent_traversal_from_pop_cuts
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         ChildReturnPreMaybePop parent child done s_before s /\
         LoopInv parent done s_before /\
         LoopTraversalComplete parent done s_before /\
         low s child = dfn s child /\
         RootPopCuts child s)
      (pop_scc child)
      (fun _ s =>
         LoopTraversalComplete parent (done_after done child) s).
  Proof.
    unfold Hoare.
    intros s1 retv s2
      [Hreturn [Hparent_loop [Hparent_traversal [Hlow_eq Hcuts]]]] Hexec.
    destruct Hreturn as [Hroot Hframe].
    destruct Hroot as [Hpre _].
    destruct Hpre as [Hloop_child _].
    destruct Hloop_child as [Haux_child _].
    destruct Haux_child as [_ [Hchild_active [_ [_ Hnodup_child]]]].
    destruct Hparent_traversal as [Hparent_no Hparent_cut].
    destruct Hframe as [Hparent_low Hframe].
    destruct Hframe as [Hparent_shape Hframe].
    destruct Hframe as [Hparent_aux Hframe].
    destruct Hframe as [Hclosed Hframe].
    destruct Hframe as [Htree Hframe].
    destruct Hframe as [Hedge_parent_child Hframe].
    destruct Hframe as [Hchild_vis Hframe].
    destruct Hframe as [Hfa_child Hframe].
    destruct Hframe as [Hfane_child Hframe].
    destruct Hframe as [Hdfn_parent_child Hframe].
    destruct Hframe as [Hnot_done_child Hframe].
    destruct Hframe as [Hbelow_child Hstack_frame].
    destruct Hstack_frame as
      [Hpopped_frame [Hrest_frame [Hvis_frame Hdfn_rest_frame]]].
    pose proof Hparent_low as Hparent_low_all.
    destruct Hparent_low as [_ [Hlow_fwd _]].
    assert (Hchild_rest_parent: RestStack child s1 parent).
    { apply Hbelow_child.
      apply partial_low_candidate_root. }
    assert (Hchild_not_active_after: ~ Active child s2).
    { pose proof (pop_scc_removes_root child) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hchild_active Hnodup_child) Hexec). }
    assert (Hpop_preserves_visited:
              forall y, Visited y s1 -> Visited y s2).
    { intros y Hvis.
      pose proof (pop_scc_keep_visited child y) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hvis Hexec). }
    assert (Hpop_preserves_dfn:
              forall y, dfn s2 y = dfn s1 y).
    { intros y.
      pose proof (pop_scc_keep_dfn child y (dfn s1 y)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hchild_popped_rest_absurd:
              forall x,
                PoppedSegment child s1 x ->
                RestStack child s1 x ->
                False).
    { intros x Hpopped Hrest.
      unfold PoppedSegment, RestStack in *.
      destruct (stack_split_at (stack s1) child)
        as [popped rest] eqn:Hsplit.
      eapply stack_split_at_popped_rest_disjoint; eauto. }
    assert (Hs2_state: s2 = pop_scc_state s1 child).
    { unfold pop_scc in Hexec.
      unfold update', update in Hexec.
      sets_unfold in Hexec.
      simpl in Hexec. exact Hexec. }
    subst s2.
    split.
    - intros x y Hpopped_parent_after Hedge_xy Hnotvis_y_after.
      assert (Hpopped_parent_before: PoppedSegment parent s1 x).
      { exact (popped_segment_after_pop_lift_original
                 child parent x s1 Hnodup_child Hchild_rest_parent
                 Hpopped_parent_after). }
      destruct (Hpopped_frame x Hpopped_parent_before)
        as [Hpopped_child | Hpopped_old].
      + assert (Hrest_child_x: RestStack child s1 x).
        { exact (popped_segment_after_pop_in_root_rest
                   child parent x s1 Hpopped_parent_after). }
        exfalso. eapply Hchild_popped_rest_absurd; eauto.
      + assert (Hnotvis_before: ~ Visited y s_before).
        { intros Hvis_before.
          apply Hnotvis_y_after.
          apply Hpop_preserves_visited.
          exact (Hvis_frame y Hvis_before). }
        destruct (Hparent_no x y Hpopped_old Hedge_xy Hnotvis_before)
          as [Hx_parent Hnot_done_y].
        split; [exact Hx_parent |].
        intros Hdone_after_y.
        destruct (done_after_elim done child y Hdone_after_y)
          as [Hdone_y | Hy_eq_child].
        * exact (Hnot_done_y Hdone_y).
        * subst y. apply Hnotvis_y_after.
          apply Hpop_preserves_visited. exact Hchild_vis.
    - intros x b Hpopped_parent_after Hedge_xb Hrest_parent_after.
      assert (Hpopped_parent_before: PoppedSegment parent s1 x).
      { exact (popped_segment_after_pop_lift_original
                 child parent x s1 Hnodup_child Hchild_rest_parent
                 Hpopped_parent_after). }
      assert (Hrest_parent_before: RestStack parent s1 b).
      { exact (rest_stack_after_pop_lift_original
                 child parent b s1 Hnodup_child Hchild_rest_parent
                 Hrest_parent_after). }
      destruct (Hpopped_frame x Hpopped_parent_before)
        as [Hpopped_child | Hpopped_old].
      + assert (Hrest_child_x: RestStack child s1 x).
        { exact (popped_segment_after_pop_in_root_rest
                   child parent x s1 Hpopped_parent_after). }
        exfalso. eapply Hchild_popped_rest_absurd; eauto.
      + assert (Hrest_before_b: RestStack parent s_before b).
        { exact (Hrest_frame b Hrest_parent_before). }
        destruct (Hparent_cut x b Hpopped_old Hedge_xb Hrest_before_b)
          as [[Hx_parent Hnot_done_b] | [target [Hcandidate_old Hdfn_old]]].
        * left. split; [exact Hx_parent |].
          intros Hdone_after_b.
          destruct (done_after_elim done child b Hdone_after_b)
            as [Hdone_b | Hb_eq_child].
          -- exact (Hnot_done_b Hdone_b).
          -- subst b.
             apply Hchild_not_active_after.
             eapply rest_stack_active; eauto.
        * destruct (Hlow_fwd target Hcandidate_old)
            as [Hcandidate_after Hdfn_target_eq].
          assert (Hparent_low_after:
                    ParentLowFrame parent done s_before
                      (pop_scc_state s1 child)).
          { pose proof (pop_scc_preserves_parent_low_frame_from_below
                          parent child done s_before) as Hhoare.
            unfold Hoare in Hhoare.
            exact (Hhoare s1 retv (pop_scc_state s1 child)
                          (conj Hparent_low_all Hbelow_child) Hexec). }
          destruct Hparent_low_after as [_ [Hlow_fwd_after _]].
          destruct (Hlow_fwd_after target Hcandidate_old)
            as [Hcandidate_final Hdfn_target_final].
          pose proof (Hdfn_rest_frame b Hrest_parent_before) as Hdfn_b_eq.
          pose proof (Hpop_preserves_dfn b) as Hdfn_b_pop.
          right. exists target. split.
          -- apply partial_low_candidate_done_mono. exact Hcandidate_final.
          -- lia.
  Qed.

  Lemma maybe_pop_produces_child_traversal
        (parent child: V) (done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         ChildReturnPreMaybePop parent child done s_before s /\
         LoopInv parent done s_before /\
         LoopTraversalComplete parent done s_before)
      (If (fun s => low s child = dfn s child) (pop_scc child))
      (fun _ s =>
         ChildContributionContract parent child done s_before s /\
         LoopTraversalComplete parent (done_after done child) s).
  Proof.
    unfold If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conj with
        (Q1 := fun _ s =>
                 ChildContributionContract parent child done s_before s).
      + eapply Hoare_conseq_pre.
        2: apply maybe_pop_pop_produces_child_contribution_from_pop_cuts.
        intros s1 [Hcond Hs1]. subst s1.
        destruct H as [Hreturn [_ _]].
        destruct Hreturn as [Hroot Hframe].
        assert (Hcuts: RootPopCuts child s0).
        { eapply root_pre_maybe_pop_low_eq_derives_pop_cuts; eauto. }
        exact (conj (conj Hroot Hframe) (conj Hcond Hcuts)).
      + eapply Hoare_conseq_pre.
        2: apply pop_child_return_advances_parent_traversal_from_pop_cuts.
        intros s1 [Hcond Hs1]. subst s1.
        destruct H as [Hreturn [Hparent_loop Hparent_traversal]].
        destruct Hreturn as [Hroot Hframe].
        assert (Hcuts: RootPopCuts child s0).
        { eapply root_pre_maybe_pop_low_eq_derives_pop_cuts; eauto. }
        exact (conj (conj Hroot Hframe)
                (conj Hparent_loop
                  (conj Hparent_traversal
                    (conj Hcond Hcuts)))).
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume_s. }
      simpl. intros _ s [Heq Hnot_cond]. subst s.
      destruct H as [Hreturn [Hparent_loop Hparent_traversal]].
      assert (Hcontrib:
                ChildContributionContract parent child done s_before s0).
      { eapply maybe_pop_skip_produces_child_contribution; eauto. }
      assert (Htraversal:
                LoopTraversalComplete parent (done_after done child) s0).
      { destruct Hreturn as [Hroot Hframe].
        destruct Hroot as [[Hloop_child Hstack_rest] Hroot_traversal].
        destruct Hloop_child as [_ [Hchild_shape _]].
        destruct Hstack_rest as [Hchild_active _].
        eapply active_child_return_advances_parent_traversal; eauto. }
      exact (conj Hcontrib Htraversal).
  Qed.

  Lemma parent_old_candidates_below_trans
        (parent child root0: V) (done: V -> Prop)
        (s_before s: St):
    StackNoDup s ->
    RestStack root0 s child ->
    ParentOldCandidatesBelowChild parent child done s_before s ->
    ParentOldCandidatesBelowChild parent root0 done s_before s.
  Proof.
    intros Hnodup Hchild_rest Hbelow b Hcandidate.
    eapply rest_stack_trans.
    - exact Hnodup.
    - exact Hchild_rest.
    - exact (Hbelow b Hcandidate).
  Qed.

  Lemma pop_scc_preserves_parent_old_candidates_below_child_from_rest
        (parent child root0: V) (done: V -> Prop)
        (s_before: St):
    Hoare
      (fun s: St =>
         StackNoDup s /\
         RestStack root0 s child /\
         ParentOldCandidatesBelowChild parent child done s_before s)
      (pop_scc root0)
      (fun _ s =>
         ParentOldCandidatesBelowChild parent child done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hnodup [Hchild_rest Hbelow]] Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold ParentOldCandidatesBelowChild.
    intros b Hcandidate.
    apply rest_stack_after_pop_preserves_nested.
    - exact Hnodup.
    - exact Hchild_rest.
    - exact (Hbelow b Hcandidate).
  Qed.

  Lemma pop_scc_preserves_nested_frame_disjoint_any
        (ancestor current loop_root root0: V)
        (ancestor_done: V -> Prop):
    Hoare
      (NestedFrameDisjoint ancestor current loop_root ancestor_done)
      (pop_scc root0)
      (fun _ s =>
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 Hdisjoint Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s1) root0) as [popped rest] eqn:Hsplit.
    simpl. exact Hdisjoint.
  Qed.

  Lemma pop_scc_preserves_parent_frame_for_child_from_nested_root
        (ancestor current root0: V)
        (ancestor_done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         RootPreMaybePop root0 s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         RestStack root0 s current /\
         RootPopCuts root0 s)
      (pop_scc root0)
      (fun _ s =>
         ParentFrameForChild ancestor current ancestor_done s_before s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hroot [Hframe [Hcurrent_rest Hcuts]]] Hexec.
    destruct Hroot as [Hpre _].
    destruct Hpre as [Hloop_root _].
    destruct Hloop_root as [Haux_root _].
    destruct Haux_root as [_ [Hroot_active Horder_root]].
    destruct Horder_root as [_ [_ Hnodup_root]].
    destruct Hcuts as [Hpopped_closed Hno_active_reach].
    destruct Hframe as [Hparent_low Hframe].
    destruct Hframe as [Hparent_shape Hframe].
    destruct Hframe as [Hparent_aux Hframe].
    destruct Hframe as [Hclosed Hframe].
    destruct Hframe as [Htree Hframe].
    destruct Hframe as [Hedge_ancestor_current Hframe].
    destruct Hframe as [Hcurrent_vis Hframe].
    destruct Hframe as [Hfa_current Hframe].
    destruct Hframe as [Hfane_current Hframe].
    destruct Hframe as [Hdfn_ancestor_current Hframe].
    destruct Hframe as [Hnot_done_current Hbelow_current].
    destruct Hbelow_current as [Hbelow_current Hstack_frame_current].
    assert (Hcurrent_rest_ancestor: RestStack current s1 ancestor).
    { apply Hbelow_current.
      apply partial_low_candidate_root. }
    assert (Hroot_rest_ancestor: RestStack root0 s1 ancestor).
    { eapply rest_stack_trans; eauto. }
    assert (Hbelow_root:
              ParentOldCandidatesBelowChild
                ancestor root0 ancestor_done s_before s1).
    { exact (parent_old_candidates_below_trans
               ancestor current root0 ancestor_done s_before s1
               Hnodup_root Hcurrent_rest Hbelow_current). }
    assert (Hparent_low_after:
              ParentLowFrame ancestor ancestor_done s_before s2).
    { pose proof (pop_scc_preserves_parent_low_frame_from_below
                    ancestor root0 ancestor_done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hparent_low Hbelow_root) Hexec). }
    assert (Hparent_shape_after:
              LoopCoreShape ancestor
                (done_after ancestor_done current) s2).
    { pose proof (pop_scc_preserves_loop_core_shape_any
                    ancestor root0
                    (done_after ancestor_done current)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hparent_shape Hexec). }
    assert (Hparent_aux_after: LoopAuxFacts ancestor s2).
    { pose proof (pop_scc_preserves_parent_loop_aux_facts
                    ancestor root0 ancestor_done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hparent_aux
                      (conj Hroot_active
                        (conj Hpopped_closed Hbelow_root)))
                    Hexec). }
    assert (Hclosed_after: Closed s2).
    { pose proof (pop_scc_restores_closed root0) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hclosed Hno_active_reach) Hexec). }
    assert (Htree_after: TreeEdgesAreGraphEdges s2).
    { destruct Hparent_shape_after as [_ [Htree_after _]].
      exact Htree_after. }
    assert (Hcurrent_vis_after: Visited current s2).
    { pose proof (pop_scc_keep_visited root0 current) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hcurrent_vis Hexec). }
    assert (Hfa_current_after: fa s2 current = ancestor).
    { pose proof (pop_scc_keep_fa root0 current ancestor) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hfa_current Hexec). }
    assert (Hfane_current_after: fa s2 current <> current).
    { rewrite Hfa_current_after.
      intros Hancestor_eq_current.
      apply Hfane_current.
      rewrite Hfa_current. exact Hancestor_eq_current. }
    assert (Hdfn_ancestor_after:
              dfn s2 ancestor = dfn s1 ancestor).
    { pose proof (pop_scc_keep_dfn
                    root0 ancestor (dfn s1 ancestor)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hdfn_current_after:
              dfn s2 current = dfn s1 current).
    { pose proof (pop_scc_keep_dfn
                    root0 current (dfn s1 current)) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 eq_refl Hexec). }
    assert (Hbelow_current_after:
              ParentOldCandidatesBelowChild
                ancestor current ancestor_done s_before s2).
    { pose proof
        (pop_scc_preserves_parent_old_candidates_below_child_from_rest
           ancestor current root0 ancestor_done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hnodup_root
                      (conj Hcurrent_rest Hbelow_current))
                    Hexec). }
    assert (Hstack_frame_current_after:
              ParentTraversalStackFrame ancestor current s_before s2).
    { pose proof
        (pop_scc_preserves_parent_traversal_stack_frame_from_rest_hoare
           ancestor current root0 s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2
                    (conj Hnodup_root
                      (conj Hcurrent_rest
                        (conj Hroot_rest_ancestor Hstack_frame_current)))
                    Hexec). }
    unfold ParentFrameForChild.
    split; [exact Hparent_low_after |].
    split; [exact Hparent_shape_after |].
    split; [exact Hparent_aux_after |].
    split; [exact Hclosed_after |].
    split; [exact Htree_after |].
    split; [exact Hedge_ancestor_current |].
    split; [exact Hcurrent_vis_after |].
    split; [exact Hfa_current_after |].
    split; [exact Hfane_current_after |].
    split.
    - lia.
    - split; [exact Hnot_done_current |].
      exact (conj Hbelow_current_after Hstack_frame_current_after).
  Qed.

  Lemma maybe_pop_pop_preserves_nested_parent_frame_from_pop_cuts
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         RootPreMaybePop loop_root s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s /\
         RestStack loop_root s current /\
         RootPopCuts loop_root s)
      (pop_scc loop_root)
      (fun _ s =>
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
  Proof.
    apply Hoare_conj with
      (Q1 := fun _ s =>
               ParentFrameForChild ancestor current ancestor_done
                 s_before s).
    - eapply Hoare_conseq_pre.
      2: apply pop_scc_preserves_parent_frame_for_child_from_nested_root.
      intros s [Hroot [Hframe [_ [Hrest Hcuts]]]].
      exact (conj Hroot (conj Hframe (conj Hrest Hcuts))).
    - eapply Hoare_conseq_pre.
      2: apply pop_scc_preserves_nested_frame_disjoint_any.
      intros s [_ [_ [Hdisjoint _]]]. exact Hdisjoint.
  Qed.

  Lemma maybe_pop_preserves_nested_parent_frame
        (ancestor current loop_root: V)
        (ancestor_done: V -> Prop) (s_before: St):
    Hoare
      (fun s: St =>
         RootPreMaybePop loop_root s /\
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s /\
         RestStack loop_root s current)
      (If (fun s => low s loop_root = dfn s loop_root)
          (pop_scc loop_root))
      (fun _ s =>
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
  Proof.
    unfold If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: apply maybe_pop_pop_preserves_nested_parent_frame_from_pop_cuts.
      intros s1 [Hcond Hs1]. subst s1.
      destruct H as [Hroot [Hframe [Hdisjoint Hrest]]].
      assert (Hcuts: RootPopCuts loop_root s0).
      { eapply root_pre_maybe_pop_low_eq_derives_pop_cuts; eauto. }
      exact (conj Hroot
              (conj Hframe
                (conj Hdisjoint
                  (conj Hrest Hcuts)))).
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume_s. }
      simpl. intros _ s [Heq _]. subst s.
      destruct H as [_ [Hframe [Hdisjoint _]]].
      exact (conj Hframe Hdisjoint).
  Qed.

  Lemma child_contribution_tree_edge
        (parent child: V) (done: V -> Prop)
        (s_before s: St):
    ChildContributionContract parent child done s_before s ->
    tree_edge s parent child.
  Proof.
    intros Hcontrib.
    destruct Hcontrib as [_ Hcontrib].
    destruct Hcontrib as [Hshape Hcontrib].
    destruct Hcontrib as [_ Hcontrib].
    destruct Hcontrib as [_ Hcontrib].
    destruct Hcontrib as [_ Hcontrib].
    destruct Hcontrib as [Hchild_vis Hcontrib].
    destruct Hcontrib as [Hfa Hcontrib].
    destruct Hcontrib as [Hfane _].
    destruct Hshape as [_ [_ [_ [Hdone_edge _]]]].
    assert (Hedge: Edge parent child).
    { apply Hdone_edge. apply done_after_intro_new. }
    eapply tree_step_char_backward; eauto.
  Qed.

  Lemma tree_reachable_parent_of_target
        (s: St) (x parent child: V):
    dg_reachable (state_to_dfs_tree g s root) x child ->
    tree_edge s parent child ->
    x <> child ->
    dg_reachable (state_to_dfs_tree g s root) x parent.
  Proof.
    intros Hreach Htree_parent_child Hx_ne_child.
    destruct (dg_reachable_vertex_path
                (state_to_dfs_tree g s root) x child Hreach)
      as [path Hpath].
    assert (Hchild_not_ne: ~ (child = child -> False)).
    { intros Hneq. apply Hneq. reflexivity. }
    destruct (dg_vertex_path_last_exit_from_pred
                (state_to_dfs_tree g s root)
                (fun z => z = child -> False)
                x child path Hx_ne_child Hchild_not_ne Hpath)
      as [a [b [suffix
        [Ha_ne_child [Hb_not_ne_child
          [Hstep_ab [Hreach_x_a [_ _]]]]]]]].
    assert (Hb_eq_child: b = child).
    { apply NNPP. exact Hb_not_ne_child. }
    subst b.
    apply tree_step_char in Hstep_ab as [Hfa_child_from_a [_ _]].
    apply tree_step_char in Htree_parent_child
      as [Hfa_child_from_parent [_ _]].
    assert (Ha_eq_parent: a = parent) by congruence.
    rewrite Ha_eq_parent in Hreach_x_a.
    exact Hreach_x_a.
  Qed.

  Lemma nested_frame_disjoint_parent_from_child
        (ancestor current parent child: V)
        (ancestor_done: V -> Prop) (s: St):
    NestedFrameDisjoint ancestor current child ancestor_done s ->
    tree_edge s parent child ->
    current <> child ->
    NestedFrameDisjoint ancestor current parent ancestor_done s.
  Proof.
    intros [Hreach_current_child Hno_old_child]
           Htree_parent_child Hcurrent_ne_child.
    split.
    - eapply tree_reachable_parent_of_target; eauto.
    - intros old_child Hdone_old Hfa_old Hfane_old Hreach_old_parent.
      apply (Hno_old_child old_child Hdone_old Hfa_old Hfane_old).
      eapply dg_reachable_trans.
      + exact Hreach_old_parent.
      + apply dg_reachable_step. exact Htree_parent_child.
  Qed.

  Lemma root_pop_branch_pre_scc_is_low_after_pop_state
        (u: V) (s: St):
    RootPopBranchPre u s ->
    scc_is_low_v (pop_scc_state s u) u.
  Proof.
    intros Hpre.
    destruct Hpre as [[Hloop _] Hlow_eq].
    destruct Hloop as [_ [Hshape [_ Hlow]]].
    destruct Hshape as [Hwf [Htree_sound Hshape_rest]].
    destruct Hlow as [_ Hcomplete].
    unfold scc_is_low_v, scc_is_low_v_val.
    unfold min_value_of_subset.
    exists u. split.
    - unfold min_object_of_subset. split.
      + unfold scc_low_tree, scc_low_reachable.
        unfold pop_scc_state.
        destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
        simpl. exists u. split.
        * apply Coq.Relations.Relation_Operators.rt_refl.
        * left. reflexivity.
      + intros target Htarget.
        unfold pop_scc_state in Htarget |- *.
        destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
        simpl in Htarget |- *.
        unfold scc_low_tree, scc_low_reachable in Htarget.
        destruct Htarget as [x [Hreach [Hx_eq_target | Hback]]].
        * subst target.
          eapply tree_reachable_dfn_monotone; eauto.
        * destruct Hback as [Hedge [Hactive_post Hnot_tree_post]].
          assert (Hactive_pre: Active target s).
          { unfold Active.
            apply (stack_split_at_in_original
                     (stack s) u target popped rest Hsplit).
            right. exact Hactive_post. }
          assert (Hnot_tree_pre: ~ tree_edge s x target).
          { intros Htree_pre. exact (Hnot_tree_post Htree_pre). }
          assert (Hcandidate:
                    PartialLowCandidate u (edge_set u) s target).
          { eapply tree_escape_to_child_candidate; eauto. }
          pose proof (Hcomplete target Hcandidate) as Hbound.
          lia.
    - unfold pop_scc_state.
      destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
      simpl. symmetry. exact Hlow_eq.
  Qed.

  Lemma pop_scc_root_pop_branch_preserves_scc_is_low_v (u: V):
    Hoare
      (RootPopBranchPre u)
      (pop_scc u)
      (fun _ s => scc_is_low_v s u).
  Proof.
    unfold Hoare.
    intros s1 retv s2 Hpre Hexec.
    unfold pop_scc in Hexec.
    unfold update', update in Hexec.
    sets_unfold in Hexec.
    simpl in Hexec. subst s2.
    apply root_pop_branch_pre_scc_is_low_after_pop_state.
    exact Hpre.
  Qed.

  Lemma maybe_pop_pop_produces_root_final_from_pop_cuts (u: V):
    Hoare
      (RootPopBranchWithCuts u)
      (pop_scc u)
      (fun _ s => RootFinal u s).
  Proof.
    unfold Hoare.
    intros s1 retv s2 [Hroot [Hpopped_closed Hno_active]] Hexec.
    destruct Hroot as [[Hloop Hstack_rest] Hlow_eq].
    pose proof Hloop as Hloop_all.
    destruct Hloop as [Haux [Hshape [Hclosed Hlow]]].
    destruct Haux as [Hsettled _].
    destruct Hshape as [Hwf _].
    unfold RootFinal, RootAfterMaybePop.
    split.
    - pose proof (pop_scc_preserves_wf_scc_state g root u) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s1 retv s2 Hwf Hexec).
    - split.
      + pose proof (pop_scc_restores_no_unvisited_reach u) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s1 retv s2
                      (conj Hsettled Hpopped_closed) Hexec).
      + split.
        * pose proof (pop_scc_restores_closed u) as Hhoare.
          unfold Hoare in Hhoare.
          exact (Hhoare s1 retv s2
                        (conj Hclosed Hno_active) Hexec).
        * pose proof (pop_scc_root_pop_branch_preserves_scc_is_low_v u)
            as Hhoare.
          unfold Hoare in Hhoare.
          exact (Hhoare s1 retv s2
                        (conj (conj Hloop_all Hstack_rest) Hlow_eq)
                        Hexec).
  Qed.

  Lemma maybe_pop_produces_root_final (u: V):
    Hoare
      (RootPreMaybePop u)
      (If (fun s => low s u = dfn s u) (pop_scc u))
      (fun _ s => RootFinal u s).
  Proof.
    unfold If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: apply maybe_pop_pop_produces_root_final_from_pop_cuts.
      intros s1 [Hcond Hs1]. subst s1.
      destruct H as [Hroot Htraversal].
      destruct (root_pre_maybe_pop_low_eq_derives_pop_cuts
                  u _ (conj Hroot Htraversal) Hcond)
        as [Hpopped_closed Hno_active].
      exact (conj (conj Hroot Hcond)
              (conj Hpopped_closed Hno_active)).
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume_s. }
      simpl. intros _ s [Heq Hnot_cond]. subst s.
      destruct H as [Hroot _].
      apply maybe_pop_skip_produces_root_final.
      unfold RootSkipBranchPre.
      exact (conj Hroot Hnot_cond).
  Qed.

  Theorem tarjan_scc_f_produces_child_contribution
        (W: RecProgram) (parent child: V) (done: V -> Prop):
    VisitContract W ->
    Hoare
      (ParentRecursivePre parent child done)
      (tarjan_scc_f g W child)
      (fun _ s =>
         exists s_before,
           LoopInv parent done s_before /\
           Edge parent child /\
           ChildContributionContract parent child done s_before s).
  Proof.
    intros [_ [Hchild [Hchild_traversal Hframe]]].
    unfold tarjan_scc_f.
    eapply Hoare_bind with
      (Q := fun (_: unit) s =>
              exists s_before,
                LoopInv child ∅ s /\
                LoopTraversalComplete child ∅ s /\
                LoopInv parent done s_before /\
                Edge parent child /\
                ParentFrameForChild parent child done s_before s).
    { unfold Hoare.
      intros s0 retv s1 Hpre Hexec.
      pose proof Hpre as Hpre_all.
      destruct Hpre as [_ [Hedge [Hentry _]]].
      pose proof (preloop_establishes_parent_frame_for_child_exact
                    parent child done s0) as Hframe_hoare.
      unfold Hoare in Hframe_hoare.
      destruct (Hframe_hoare s0 retv s1
                             (conj eq_refl Hpre_all) Hexec)
        as [Hloop_child [Hparent_loop Hparent_frame]].
      assert (Htraversal_empty: LoopTraversalComplete child ∅ s1).
      { pose proof (preloop_initializes_loop_traversal_complete_empty child)
          as Htraversal_hoare.
        unfold Hoare in Htraversal_hoare.
        exact (Htraversal_hoare s0 retv s1 Hentry Hexec). }
      exists s0.
      exact (conj Hloop_child
              (conj Htraversal_empty
                (conj Hparent_loop
                  (conj Hedge Hparent_frame)))). }
    simpl. intros _.
    eapply Hoare_bind with
      (Q := fun (_: unit) s =>
              exists s_before,
                LoopInv child (edge_set child) s /\
                RootTraversalComplete child s /\
                LoopInv parent done s_before /\
                Edge parent child /\
                ParentFrameForChild parent child done s_before s).
    { unfold Hoare.
      intros s1 retv s2
        [s_before
          [Hloop_child [Htraversal_empty
            [Hparent_loop [Hedge Hparent_frame]]]]] Hexec.
      assert (Hloop_and_frame:
                LoopInv child (edge_set child) s2 /\
                ParentFrameForChild parent child done s_before s2).
      { pose proof (edge_loop_preserves_parent_frame_for_child
                      parent child done s_before W Hchild Hframe)
          as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s1 retv s2
                      (conj Hloop_child Hparent_frame) Hexec). }
      assert (Htraversal_root: RootTraversalComplete child s2).
      { pose proof (edge_loop_produces_root_traversal_complete
                      child W Hchild Hchild_traversal) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s1 retv s2
                      (conj Hloop_child Htraversal_empty) Hexec). }
      destruct Hloop_and_frame as [Hloop_child_done Hparent_frame_after].
      exists s_before.
      exact (conj Hloop_child_done
              (conj Htraversal_root
                (conj Hparent_loop
                  (conj Hedge Hparent_frame_after)))). }
    simpl. intros _.
    unfold Hoare.
    intros s2 retv s3
      [s_before
        [Hloop_child_done [Htraversal_root
          [Hparent_loop [Hedge Hparent_frame]]]]] Hexec.
    assert (Hreturn:
              ChildReturnPreMaybePop parent child done s_before s2).
    { eapply edge_loop_post_to_child_return_pre_maybe_pop; eauto. }
    assert (Hchild_contribution:
              ChildContributionContract parent child done s_before s3).
    { pose proof (maybe_pop_produces_child_contribution
                    parent child done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s2 retv s3 Hreturn Hexec). }
    exists s_before.
    exact (conj Hparent_loop (conj Hedge Hchild_contribution)).
  Qed.

  Theorem tarjan_scc_f_produces_child_traversal
        (W: RecProgram) (parent child: V) (done: V -> Prop):
    VisitContract W ->
    Hoare
      (fun s: St =>
         ParentRecursivePre parent child done s /\
         LoopTraversalComplete parent done s)
      (tarjan_scc_f g W child)
      (fun _ s =>
         exists s_before,
           LoopInv parent done s_before /\
           Edge parent child /\
           ChildContributionContract parent child done s_before s /\
           LoopTraversalComplete parent (done_after done child) s).
  Proof.
    intros [_ [Hchild [Hchild_traversal Hframe]]].
    unfold tarjan_scc_f.
    eapply Hoare_bind with
      (Q := fun (_: unit) s =>
              exists s_before,
                LoopInv child ∅ s /\
                LoopTraversalComplete child ∅ s /\
                LoopInv parent done s_before /\
                LoopTraversalComplete parent done s_before /\
                Edge parent child /\
                ParentFrameForChild parent child done s_before s).
    { unfold Hoare.
      intros s0 retv s1 [Hpre Hparent_traversal] Hexec.
      pose proof Hpre as Hpre_all.
      destruct Hpre as [_ [Hedge [Hentry _]]].
      pose proof (preloop_establishes_parent_frame_for_child_exact
                    parent child done s0) as Hframe_hoare.
      unfold Hoare in Hframe_hoare.
      destruct (Hframe_hoare s0 retv s1
                             (conj eq_refl Hpre_all) Hexec)
        as [Hloop_child [Hparent_loop Hparent_frame]].
      assert (Htraversal_empty: LoopTraversalComplete child ∅ s1).
      { pose proof (preloop_initializes_loop_traversal_complete_empty child)
          as Htraversal_hoare.
        unfold Hoare in Htraversal_hoare.
        exact (Htraversal_hoare s0 retv s1 Hentry Hexec). }
      exists s0.
      exact (conj Hloop_child
              (conj Htraversal_empty
                (conj Hparent_loop
                  (conj Hparent_traversal
                    (conj Hedge Hparent_frame))))). }
    simpl. intros _.
    eapply Hoare_bind with
      (Q := fun (_: unit) s =>
              exists s_before,
                LoopInv child (edge_set child) s /\
                RootTraversalComplete child s /\
                LoopInv parent done s_before /\
                LoopTraversalComplete parent done s_before /\
                Edge parent child /\
                ParentFrameForChild parent child done s_before s).
    { unfold Hoare.
      intros s1 retv s2
        [s_before
          [Hloop_child [Htraversal_empty
            [Hparent_loop [Hparent_traversal
              [Hedge Hparent_frame]]]]]] Hexec.
      assert (Hloop_and_frame:
                LoopInv child (edge_set child) s2 /\
                ParentFrameForChild parent child done s_before s2).
      { pose proof (edge_loop_preserves_parent_frame_for_child
                      parent child done s_before W Hchild Hframe)
          as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s1 retv s2
                      (conj Hloop_child Hparent_frame) Hexec). }
      assert (Htraversal_root: RootTraversalComplete child s2).
      { pose proof (edge_loop_produces_root_traversal_complete
                      child W Hchild Hchild_traversal) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s1 retv s2
                      (conj Hloop_child Htraversal_empty) Hexec). }
      destruct Hloop_and_frame as [Hloop_child_done Hparent_frame_after].
      exists s_before.
      exact (conj Hloop_child_done
              (conj Htraversal_root
                (conj Hparent_loop
                  (conj Hparent_traversal
                    (conj Hedge Hparent_frame_after))))). }
    simpl. intros _.
    unfold Hoare.
    intros s2 retv s3
      [s_before
        [Hloop_child_done [Htraversal_root
          [Hparent_loop [Hparent_traversal
            [Hedge Hparent_frame]]]]]] Hexec.
    assert (Hreturn:
              ChildReturnPreMaybePop parent child done s_before s2).
    { eapply edge_loop_post_to_child_return_pre_maybe_pop; eauto. }
    assert (Hpost:
              ChildContributionContract parent child done s_before s3 /\
              LoopTraversalComplete parent (done_after done child) s3).
    { pose proof (maybe_pop_produces_child_traversal
                    parent child done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s2 retv s3
                    (conj Hreturn
                      (conj Hparent_loop Hparent_traversal))
                    Hexec). }
    destruct Hpost as [Hchild_contribution Hparent_traversal_after].
    exists s_before.
    exact (conj Hparent_loop
            (conj Hedge
              (conj Hchild_contribution Hparent_traversal_after))).
  Qed.

  Theorem tarjan_scc_f_produces_root_final_from_traversal_contract
        (W: RecProgram) (u: V):
    VisitChildContract W ->
    VisitChildTraversalContract W ->
    Hoare
      (EntryPre u)
      (tarjan_scc_f g W u)
      (fun _ s => RootFinal u s).
  Proof.
    intros Hchild Hchild_traversal.
    unfold tarjan_scc_f.
    eapply Hoare_bind.
    { apply preloop_initializes_edge_loop_pre. }
    simpl. intros _.
    eapply Hoare_bind.
    { apply edge_loop_preserves_root_pre_maybe_pop_from_traversal_contract;
        auto. }
    simpl. intros _.
    apply maybe_pop_produces_root_final.
  Qed.

  Theorem tarjan_scc_f_produces_root_final
        (W: RecProgram) (u: V):
    VisitContract W ->
    Hoare
      (EntryPre u)
      (tarjan_scc_f g W u)
      (fun _ s => RootFinal u s).
  Proof.
    intros [_ [Hchild [Hchild_traversal _]]].
    apply tarjan_scc_f_produces_root_final_from_traversal_contract; auto.
  Qed.

  Theorem tarjan_scc_f_preserves_nested_parent_frame
        (W: RecProgram)
        (ancestor current loop_root next: V)
        (ancestor_done loop_done: V -> Prop)
        (s_before: St):
    VisitContract W ->
    Hoare
      (NestedFramePre ancestor current loop_root next
         ancestor_done loop_done s_before)
      (tarjan_scc_f g W next)
      (fun _ s =>
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
  Proof.
    intros [_ [Hchild [Hchild_traversal Hframe_contract]]].
    unfold tarjan_scc_f.
    eapply Hoare_bind with
      (Q := fun (_: unit) s =>
              exists child_before,
                LoopInv next ∅ s /\
                LoopTraversalComplete next ∅ s /\
                ParentFrameForChild ancestor current ancestor_done
                  s_before s /\
                NestedFrameDisjoint ancestor current next
                  ancestor_done s /\
                RestStack next s current /\
                ParentFrameForChild loop_root next loop_done
                  child_before s).
    { unfold Hoare.
      intros s0 retv s1 Hnested Hexec.
      pose proof Hnested as Hnested_for_outer.
      pose proof
        (nested_frame_pre_parent_recursive_pre
           ancestor current loop_root next ancestor_done loop_done
           s_before s0 Hnested) as Hrecursive_pre.
      pose proof
        (preloop_preserves_nested_parent_context_with_rest
           ancestor current loop_root next ancestor_done loop_done
           s_before) as Houter_hoare.
      unfold Hoare in Houter_hoare.
      destruct (Houter_hoare s0 retv s1
                             Hnested_for_outer Hexec)
        as [Hloop_next [Htraversal_next
          [Houter_frame [Hinner_disjoint Hrest_next_current]]]].
      pose proof
        (preloop_establishes_parent_frame_for_child
           loop_root next loop_done) as Himmediate_hoare.
      unfold Hoare in Himmediate_hoare.
      destruct (Himmediate_hoare s0 retv s1
                                 Hrecursive_pre Hexec)
        as [child_before [_ [_ Himmediate_frame]]].
      exists child_before.
      exact (conj Hloop_next
              (conj Htraversal_next
                (conj Houter_frame
                  (conj Hinner_disjoint
                    (conj Hrest_next_current Himmediate_frame))))). }
    simpl. intros _.
    eapply Hoare_bind with
      (Q := fun (_: unit) s =>
              exists child_before,
                LoopInv next (edge_set next) s /\
                RootTraversalComplete next s /\
                ParentFrameForChild ancestor current ancestor_done
                  s_before s /\
                NestedFrameDisjoint ancestor current next
                  ancestor_done s /\
                RestStack next s current /\
                ParentFrameForChild loop_root next loop_done
                  child_before s).
    { unfold Hoare.
      intros s1 retv s2
        [child_before
          [Hloop_next [Htraversal_next
            [Houter_frame [Hinner_disjoint
              [Hrest_next_current Himmediate_frame]]]]]] Hexec.
      assert (Houter_context:
                LoopInv next (edge_set next) s2 /\
                RootTraversalComplete next s2 /\
                ParentFrameForChild ancestor current ancestor_done
                  s_before s2 /\
                NestedFrameDisjoint ancestor current next
                  ancestor_done s2 /\
                RestStack next s2 current).
      { pose proof
          (edge_loop_preserves_nested_parent_context_with_rest
             ancestor current next ancestor_done s_before W
             Hchild Hchild_traversal Hframe_contract) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s1 retv s2
                      (conj Hloop_next
                        (conj Htraversal_next
                          (conj Houter_frame
                            (conj Hinner_disjoint
                                  Hrest_next_current))))
                      Hexec). }
      assert (Himmediate_after:
                LoopInv next (edge_set next) s2 /\
                ParentFrameForChild loop_root next loop_done
                  child_before s2).
      { pose proof
          (edge_loop_preserves_parent_frame_for_child
             loop_root next loop_done child_before W
             Hchild Hframe_contract) as Hhoare.
        unfold Hoare in Hhoare.
        exact (Hhoare s1 retv s2
                      (conj Hloop_next Himmediate_frame) Hexec). }
      destruct Houter_context as
        [Hloop_done [Hroot_traversal
          [Houter_after [Hinner_after Hrest_after]]]].
      destruct Himmediate_after as [_ Himmediate_after].
      exists child_before.
      exact (conj Hloop_done
              (conj Hroot_traversal
                (conj Houter_after
                  (conj Hinner_after
                    (conj Hrest_after Himmediate_after))))). }
    simpl. intros _.
    unfold Hoare.
    intros s2 retv s3
      [child_before
        [Hloop_done [Hroot_traversal
          [Houter_frame [Hinner_disjoint
            [Hrest_next_current Himmediate_frame]]]]]] Hexec.
    assert (Hroot_pre: RootPreMaybePop next s2).
    { eapply edge_loop_post_to_root_pre_maybe_pop; eauto. }
    assert (Hcurrent_ne_next: current <> next).
    { intros Hcurrent_eq_next.
      subst current.
      destruct Hloop_done as [Haux_done _].
      destruct Haux_done as [_ [Hnext_active [_ [_ Hnodup_done]]]].
      exact (rest_stack_member_ne_root
               next next s2 Hnodup_done Hnext_active
               Hrest_next_current eq_refl). }
    assert (Houter_inner_after:
              ParentFrameForChild ancestor current ancestor_done
                s_before s3 /\
              NestedFrameDisjoint ancestor current next
                ancestor_done s3).
    { pose proof
        (maybe_pop_preserves_nested_parent_frame
           ancestor current next ancestor_done s_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s2 retv s3
                    (conj Hroot_pre
                      (conj Houter_frame
                        (conj Hinner_disjoint
                              Hrest_next_current)))
                    Hexec). }
    assert (Hchild_contribution:
              ChildContributionContract loop_root next loop_done
                child_before s3).
    { pose proof
        (maybe_pop_produces_child_contribution
           loop_root next loop_done child_before) as Hhoare.
      unfold Hoare in Hhoare.
      exact (Hhoare s2 retv s3
                    (conj Hroot_pre Himmediate_frame) Hexec). }
    destruct Houter_inner_after as [Houter_after Hinner_after].
    assert (Htree_loop_next: tree_edge s3 loop_root next).
    { eapply child_contribution_tree_edge; eauto. }
    assert (Horiginal_disjoint:
              NestedFrameDisjoint ancestor current loop_root
                ancestor_done s3).
    { eapply nested_frame_disjoint_parent_from_child; eauto. }
    exact (conj Houter_after Horiginal_disjoint).
  Qed.

  Theorem tarjan_scc_f_preserves_visit_contract
        (W: RecProgram):
    VisitContract W ->
    VisitContract (tarjan_scc_f g W).
  Proof.
    intros Hcontract.
    unfold VisitContract.
    split.
    - intro u0.
      apply tarjan_scc_f_produces_root_final.
      exact Hcontract.
    - split.
      + intros parent child done.
        apply tarjan_scc_f_produces_child_contribution.
        exact Hcontract.
      + split.
        * intros parent child done.
          apply tarjan_scc_f_produces_child_traversal.
          exact Hcontract.
        * intros ancestor current loop_root next
                 ancestor_done loop_done s_before.
          apply tarjan_scc_f_preserves_nested_parent_frame.
          exact Hcontract.
  Qed.

  Lemma empty_rec_program_satisfies_visit_contract:
    VisitContract (∅ : RecProgram).
  Proof.
    unfold VisitContract, VisitMainContract, VisitChildContract,
      VisitChildTraversalContract, VisitFrameContract, Hoare.
    repeat split; intros; sets_unfold in H0; tauto.
  Qed.

  Lemma tarjan_scc_iter_satisfies_visit_contract (n: nat):
    VisitContract (Nat.iter n (tarjan_scc_f g) (∅ : RecProgram)).
  Proof.
    induction n as [| n IH].
    - simpl. apply empty_rec_program_satisfies_visit_contract.
    - simpl. apply tarjan_scc_f_preserves_visit_contract. exact IH.
  Qed.

  Theorem tarjan_scc_satisfies_visit_contract:
    VisitContract (tarjan_scc g).
  Proof.
    unfold VisitContract.
    split.
    - unfold VisitMainContract, Hoare.
      intros u s1 retv s2 Hpre Hexec.
      unfold tarjan_scc in Hexec.
      change (exists n,
                (s1, retv, s2) ∈
                  Nat.iter n (tarjan_scc_f g) (∅ : RecProgram) u)
        in Hexec.
      destruct Hexec as [n Hexec].
      pose proof (tarjan_scc_iter_satisfies_visit_contract n)
        as [Hmain _].
      unfold VisitMainContract, Hoare in Hmain.
      exact (Hmain u s1 retv s2 Hpre Hexec).
    - split.
      + unfold VisitChildContract, Hoare.
        intros parent child done s1 retv s2 Hpre Hexec.
        unfold tarjan_scc in Hexec.
        change (exists n,
                  (s1, retv, s2) ∈
                    Nat.iter n (tarjan_scc_f g) (∅ : RecProgram) child)
          in Hexec.
        destruct Hexec as [n Hexec].
        pose proof (tarjan_scc_iter_satisfies_visit_contract n)
          as [_ [Hchild _]].
        unfold VisitChildContract, Hoare in Hchild.
        exact (Hchild parent child done s1 retv s2 Hpre Hexec).
      + split.
        * unfold VisitChildTraversalContract, Hoare.
          intros parent child done s1 retv s2 Hpre Hexec.
          unfold tarjan_scc in Hexec.
          change (exists n,
                    (s1, retv, s2) ∈
                      Nat.iter n (tarjan_scc_f g) (∅ : RecProgram) child)
            in Hexec.
          destruct Hexec as [n Hexec].
          pose proof (tarjan_scc_iter_satisfies_visit_contract n)
            as [_ [_ [Hchild_traversal _]]].
          unfold VisitChildTraversalContract, Hoare in Hchild_traversal.
          exact (Hchild_traversal parent child done
                                  s1 retv s2 Hpre Hexec).
        * unfold VisitFrameContract, Hoare.
          intros ancestor current loop_root next ancestor_done loop_done
                 s_before s1 retv s2 Hpre Hexec.
          unfold tarjan_scc in Hexec.
          change (exists n,
                    (s1, retv, s2) ∈
                      Nat.iter n (tarjan_scc_f g) (∅ : RecProgram) next)
            in Hexec.
          destruct Hexec as [n Hexec].
          pose proof (tarjan_scc_iter_satisfies_visit_contract n)
            as [_ [_ [_ Hframe]]].
          unfold VisitFrameContract, Hoare in Hframe.
          exact (Hframe ancestor current loop_root next
                        ancestor_done loop_done s_before
                        s1 retv s2 Hpre Hexec).
  Qed.
  
End IS_LOW.
