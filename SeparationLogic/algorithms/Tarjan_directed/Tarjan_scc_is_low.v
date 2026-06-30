Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

(**
  This file is intentionally a theorem skeleton.

  The goal is to fix the proof dependency shape before committing to the
  concrete predicates used by the low-link proof.  Existing predicates and
  lemmas should be mapped into this interface only after their producer,
  consumer, lifetime, and pop-stability have been audited.

  There are no [Admitted] proofs and no axioms in this file.  Each theorem
  below is represented as a [Prop]-valued statement, so the skeleton compiles
  without pretending that any proof obligation has been discharged.
 *)

Section IS_LOW_SKELETON.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  Local Definition St : Type := @SCCSt V.
  Local Definition RecProgram : Type := V -> program St unit.

  (* ================================================================ *)
  (* Program cuts                                                     *)
  (* ================================================================ *)

  Definition edge_set (u: V): V -> Prop :=
    dg_step g u.

  Definition done_after (done: V -> Prop) (a: V): V -> Prop :=
    done ∪ [a].

  Definition edge_loop (u: V) (W: RecProgram): program St unit :=
    forset (edge_set u) (process_edge u W).

  Definition root_pop_guard (u: V) (s: St): Prop :=
    low s u = dfn s u.

  Definition maybe_pop (u: V): program St unit :=
    If (root_pop_guard u) (pop_scc u).

  (* ================================================================ *)
  (* Candidate semantic aliases                                       *)
  (* ================================================================ *)

  (**
    These are the first low-risk predicate candidates from the predicate
    ledger.  They are small field-level facts or deliberately named wrappers
    around already existing structural invariants.

    The wrappers below are still candidates.  In particular,
    [GlobalShapePreCandidate] names the transitional state where a vertex may
    already have a parent pointer but has not yet been visited by [preloop].
   *)

  Definition Edge (u v: V): Prop :=
    dg_step g u v.

  Definition Visited (u: V) (s: St): Prop :=
    u ∈ visited s.

  Definition Unvisited (u: V) (s: St): Prop :=
    ~ Visited u s.

  Definition Active (u: V) (s: St): Prop :=
    In u (stack s).

  Definition GlobalShapeCandidate (s: St): Prop :=
    wf_scc_state g root s.

  Definition GlobalShapePreCandidate (u: V) (s: St): Prop :=
    wf_scc_state_pre g root u s.

  Definition SettledClosedCandidate (s: St): Prop :=
    settled_closed g s.

  Definition OrderFactsCandidate (s: St): Prop :=
    stack_dfn_order s /\ dfn_injective s.

  Definition EntryPreCandidate (u: V) (s: St): Prop :=
    GlobalShapePreCandidate u s /\
    SettledClosedCandidate s /\
    OrderFactsCandidate s.

  (**
    The state immediately after [preloop u] should satisfy at least these
    entry-level facts.  This is not the final [LoopInv]; it is the base audit
    target used before adding low-equation and segment fields.
   *)
  Definition LoopEntryBaseCandidate (u: V) (s: St): Prop :=
    GlobalShapeCandidate s /\
    SettledClosedCandidate s /\
    Visited u s /\
    Active u s /\
    low s u = dfn s u /\
    OrderFactsCandidate s.

  (**
    [set_fa child parent] creates a phase where [child] is assigned a parent
    but has not yet been visited by [preloop child].  This candidate records
    that phase explicitly instead of assuming the normal entry predicate is
    automatically preserved.
   *)
  Definition PendingChildShapeCandidate
             (parent child: V) (s: St): Prop :=
    GlobalShapePreCandidate child s /\
    SettledClosedCandidate s /\
    Visited parent s /\
    Edge parent child /\
    fa s child = parent /\
    OrderFactsCandidate s.

  Definition ParentActiveBaseCandidate (parent: V) (s: St): Prop :=
    GlobalShapeCandidate s /\
    SettledClosedCandidate s /\
    Visited parent s /\
    Active parent s /\
    OrderFactsCandidate s.

  Definition ParentLoopSuspendedBaseCandidate
             (parent child: V) (done: V -> Prop) (s: St): Prop :=
    ParentActiveBaseCandidate parent s /\
    ~ done child.

  Definition ChildEntryCandidate
             (parent child: V) (done: V -> Prop) (s: St): Prop :=
    ParentLoopSuspendedBaseCandidate parent child done s /\
    PendingChildShapeCandidate parent child s.

  (**
    The first loop invariant candidate contains only facts consumed at the
    edge-loop boundary itself: the current root is active and structurally
    usable as a parent, and no outgoing edge has been processed yet.

    Low equations, child summaries, and segment accounting are deliberately
    excluded until their consumers are audited.
   *)
  Definition LocalActiveRootCandidate (u: V) (s: St): Prop :=
    GlobalShapeCandidate s /\
    SettledClosedCandidate s /\
    Visited u s /\
    Active u s /\
    OrderFactsCandidate s.

  Definition DoneEmptyCandidate (done: V -> Prop): Prop :=
    forall a, ~ done a.

  Definition LoopInvBaseCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    LocalActiveRootCandidate u s /\
    DoneEmptyCandidate done.

  (**
    Phase-4 [done] discipline.  This is the first real meaning of [done]:
    every processed target is an outgoing edge target of the current root, and
    every processed target has been visited.

    Reachability closedness and tree-child summaries are not included here;
    they will be added only after their consumers are audited.
   *)
  Definition DoneSubsetOfOutgoingCandidate
             (u: V) (done: V -> Prop): Prop :=
    forall a, done a -> Edge u a.

  Definition DoneVisitedCandidate
             (done: V -> Prop) (s: St): Prop :=
    forall a, done a -> Visited a s.

  Definition DoneDisciplineCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    DoneSubsetOfOutgoingCandidate u done /\
    DoneVisitedCandidate done s.

  Definition LoopInvDoneCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    LocalActiveRootCandidate u s /\
    DoneDisciplineCandidate u done s.

  (**
    Phase-5 partial low equation.

    This is intentionally split into two consumer-facing halves:

    - [LowFrontierCandidate] says the current [low u] is a lower bound for
      all low contributors that have already been processed.
    - [LowSourceCandidate] says the current [low u] still has a concrete
      source: either [u] itself, a processed tree child, or a processed active
      edge target.

    The exact root correctness theorem is not encoded here.  At loop done,
    later root-bridge phases may combine this field with child correctness,
    parent-tree discipline, and segment/closedness facts.
   *)
  Definition LowFrontierCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    low s u <= dfn s u /\
    forall a,
      done a ->
      Edge u a ->
      (fa s a = u -> low s u <= low s a) /\
      (Active a s -> low s u <= dfn s a).

  Definition LowSourceCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
       low s u = dfn s u
    \/ (exists a,
          done a /\ Edge u a /\
          fa s a = u /\ fa s a <> a /\
          low s u = low s a)
    \/ (exists a,
          done a /\ Edge u a /\
          Active a s /\ fa s a <> u /\
          low s u = dfn s a).

  Definition PartialRootLowEquationCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    LowFrontierCandidate u done s /\
    LowSourceCandidate u done s.

  Definition LoopInvLowCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    LoopInvDoneCandidate u done s /\
    PartialRootLowEquationCandidate u done s.

  (* ================================================================ *)
  (* First audit statements                                           *)
  (* ================================================================ *)

  Definition PreloopEntryBaseCandidate_statement: Prop :=
    forall u,
      Hoare
        (EntryPreCandidate u)
        (preloop u)
        (fun _ s => LoopEntryBaseCandidate u s).

  Definition PreloopGlobalShapeCandidate_statement: Prop :=
    forall u,
      Hoare
        (GlobalShapePreCandidate u)
        (preloop u)
        (fun _ s => GlobalShapeCandidate s).

  Definition PreloopSettledClosedCandidate_statement: Prop :=
    forall u,
      Hoare
        (SettledClosedCandidate)
        (preloop u)
        (fun _ s => SettledClosedCandidate s).

  Definition PreloopOrderFactsCandidate_statement: Prop :=
    forall u,
      Hoare
        (fun s =>
           OrderFactsCandidate s /\
           GlobalShapePreCandidate u s)
        (preloop u)
        (fun _ s => OrderFactsCandidate s).

  Definition PreloopActiveSelfLowCandidate_statement: Prop :=
    forall u,
      Hoare
        (GlobalShapePreCandidate u)
        (preloop u)
        (fun _ s =>
           Visited u s /\
           Active u s /\
           low s u = dfn s u).

  Definition SetFaCreatesPendingChildCandidate_statement: Prop :=
    forall parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           ParentActiveBaseCandidate parent s /\
           Unvisited child s /\
           OrderFactsCandidate s)
        (set_fa child parent)
        (fun _ s => ChildEntryCandidate parent child done s).

  Definition SetFaGlobalShapePreCandidate_statement: Prop :=
    forall parent child,
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           Visited parent s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s =>
           GlobalShapePreCandidate child s /\
           Visited parent s).

  Definition SetFaSettledClosedCandidate_statement: Prop :=
    forall parent child,
      Hoare
        (SettledClosedCandidate)
        (set_fa child parent)
        (fun _ s => SettledClosedCandidate s).

  Definition SetFaOrderFactsCandidate_statement: Prop :=
    forall parent child,
      Hoare
        (OrderFactsCandidate)
        (set_fa child parent)
        (fun _ s => OrderFactsCandidate s).

  Definition SetFaParentPointerCandidate_statement: Prop :=
    forall parent child,
      Hoare
        (fun _ => True)
        (set_fa child parent)
        (fun _ s => fa s child = parent).

  Definition SetFaKeepsChildUnvisitedCandidate_statement: Prop :=
    forall parent child,
      Hoare
        (Unvisited child)
        (set_fa child parent)
        (fun _ s => Unvisited child s).

  Definition SetFaParentActiveCandidate_statement: Prop :=
    forall parent child,
      Hoare
        (fun s =>
           ParentActiveBaseCandidate parent s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s => ParentActiveBaseCandidate parent s).

  Definition GlobalShapeCandidate_pending_child_audit: Prop :=
    forall parent child,
      Edge parent child ->
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           Visited parent s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s =>
           GlobalShapePreCandidate child s /\
           Visited parent s).

  (* ================================================================ *)
  (* Loop-entry consumer audit statements                             *)
  (* ================================================================ *)

  Definition LoopEntryImpliesLocalActiveRootCandidate_statement: Prop :=
    forall u s,
      LoopEntryBaseCandidate u s ->
      LocalActiveRootCandidate u s.

  Definition DoneEmptyCandidate_empty_statement: Prop :=
    DoneEmptyCandidate ∅.

  Definition LoopEntryImpliesBaseCandidate_statement: Prop :=
    forall u s,
      LoopEntryBaseCandidate u s ->
      LoopInvBaseCandidate u ∅ s.

  Definition LoopInvBaseProvidesSetFaPreCandidate_statement: Prop :=
    forall parent child done s,
      LoopInvBaseCandidate parent done s ->
      Unvisited child s ->
      ParentActiveBaseCandidate parent s /\
      Unvisited child s /\
      OrderFactsCandidate s.

  Definition LoopInvBaseConsumesUnvisitedSetFaCandidate_statement: Prop :=
    forall parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           LoopInvBaseCandidate parent done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s => ChildEntryCandidate parent child done s).

  (* ================================================================ *)
  (* Done-discipline audit statements                                 *)
  (* ================================================================ *)

  Definition DoneSubsetOfOutgoingCandidate_empty_statement: Prop :=
    forall u,
      DoneSubsetOfOutgoingCandidate u ∅.

  Definition DoneVisitedCandidate_empty_statement: Prop :=
    forall s,
      DoneVisitedCandidate ∅ s.

  Definition DoneDisciplineCandidate_empty_statement: Prop :=
    forall u s,
      DoneDisciplineCandidate u ∅ s.

  Definition DoneSubsetOfOutgoingCandidate_step_statement: Prop :=
    forall u done a,
      DoneSubsetOfOutgoingCandidate u done ->
      Edge u a ->
      DoneSubsetOfOutgoingCandidate u (done_after done a).

  Definition DoneVisitedCandidate_step_statement: Prop :=
    forall done a s,
      DoneVisitedCandidate done s ->
      Visited a s ->
      DoneVisitedCandidate (done_after done a) s.

  Definition DoneDisciplineCandidate_step_statement: Prop :=
    forall u done a s,
      DoneDisciplineCandidate u done s ->
      Edge u a ->
      Visited a s ->
      DoneDisciplineCandidate u (done_after done a) s.

  Definition LoopEntryImpliesDoneCandidate_statement: Prop :=
    forall u s,
      LoopEntryBaseCandidate u s ->
      LoopInvDoneCandidate u ∅ s.

  Definition LoopInvDoneProvidesSetFaPreCandidate_statement: Prop :=
    forall parent child done s,
      LoopInvDoneCandidate parent done s ->
      Unvisited child s ->
      ParentActiveBaseCandidate parent s /\
      Unvisited child s /\
      OrderFactsCandidate s.

  Definition LoopInvDoneConsumesUnvisitedSetFaCandidate_statement: Prop :=
    forall parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           LoopInvDoneCandidate parent done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s => ChildEntryCandidate parent child done s).

  (* ================================================================ *)
  (* Done-discipline branch-integration statements                    *)
  (* ================================================================ *)

  Definition ChildReturnsVisitedCandidate (W: RecProgram): Prop :=
    forall parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (ChildEntryCandidate parent child done)
        (W child)
        (fun _ s => Visited child s).

  Definition ChildPreservesDoneVisitedCandidate (W: RecProgram): Prop :=
    forall child done,
      Hoare
        (DoneVisitedCandidate done)
        (W child)
        (fun _ s => DoneVisitedCandidate done s).

  Definition ProcessEdgeProducesVisitedTargetCandidate_statement: Prop :=
    forall W u a done,
      ChildReturnsVisitedCandidate W ->
      Edge u a ->
      ~ done a ->
      Hoare
        (LoopInvDoneCandidate u done)
        (process_edge u W a)
        (fun _ s => Visited a s).

  Definition ProcessEdgeExtendsDoneDisciplineCandidate_statement: Prop :=
    forall W u a done,
      ChildReturnsVisitedCandidate W ->
      ChildPreservesDoneVisitedCandidate W ->
      Edge u a ->
      ~ done a ->
      Hoare
        (LoopInvDoneCandidate u done)
        (process_edge u W a)
        (fun _ s => DoneDisciplineCandidate u (done_after done a) s).

  (* ================================================================ *)
  (* Partial-low-equation audit statements                            *)
  (* ================================================================ *)

  Definition LowFrontierCandidate_empty_statement: Prop :=
    forall u s,
      low s u = dfn s u ->
      LowFrontierCandidate u ∅ s.

  Definition LowSourceCandidate_empty_statement: Prop :=
    forall u s,
      low s u = dfn s u ->
      LowSourceCandidate u ∅ s.

  Definition PartialRootLowEquationCandidate_empty_statement: Prop :=
    forall u s,
      low s u = dfn s u ->
      PartialRootLowEquationCandidate u ∅ s.

  Definition LoopEntryImpliesPartialLowCandidate_statement: Prop :=
    forall u s,
      LoopEntryBaseCandidate u s ->
      PartialRootLowEquationCandidate u ∅ s.

  Definition LoopEntryImpliesLowCandidate_statement: Prop :=
    forall u s,
      LoopEntryBaseCandidate u s ->
      LoopInvLowCandidate u ∅ s.

  Definition LowFrontierCandidate_step_statement: Prop :=
    forall u done a s,
      LowFrontierCandidate u done s ->
      Edge u a ->
      (fa s a = u -> low s u <= low s a) ->
      (Active a s -> low s u <= dfn s a) ->
      LowFrontierCandidate u (done_after done a) s.

  Definition LowSourceCandidate_step_keep_statement: Prop :=
    forall u done a s,
      LowSourceCandidate u done s ->
      LowSourceCandidate u (done_after done a) s.

  Definition LowSourceCandidate_step_tree_statement: Prop :=
    forall u done a s,
      Edge u a ->
      fa s a = u ->
      fa s a <> a ->
      low s u = low s a ->
      LowSourceCandidate u (done_after done a) s.

  Definition LowSourceCandidate_step_stack_statement: Prop :=
    forall u done a s,
      Edge u a ->
      Active a s ->
      fa s a <> u ->
      low s u = dfn s a ->
      LowSourceCandidate u (done_after done a) s.

  Definition PartialRootLowEquationCandidate_step_keep_statement: Prop :=
    forall u done a s,
      PartialRootLowEquationCandidate u done s ->
      Edge u a ->
      (fa s a = u -> low s u <= low s a) ->
      (Active a s -> low s u <= dfn s a) ->
      PartialRootLowEquationCandidate u (done_after done a) s.

  Definition UpdateLowBoundedByOldCandidate_statement: Prop :=
    forall u n old_low,
      Hoare
        (fun s : St => low s u = old_low)
        (update_low u n)
        (fun _ s => low s u <= old_low).

  Definition UpdateLowBoundedByIncomingCandidate_statement: Prop :=
    forall u n,
      Hoare
        (fun _ : St => True)
        (update_low u n)
        (fun _ s => low s u <= n).

  Definition UpdateLowSourceCandidate_statement: Prop :=
    forall u n old_low,
      Hoare
        (fun s : St => low s u = old_low)
        (update_low u n)
        (fun _ s => low s u = old_low \/ low s u = n).

  Definition UpdateLowKeepsSnapshotFieldsCandidate_statement: Prop :=
    forall u n snap,
      Hoare
        (fun s : St => s = snap)
        (update_low u n)
        (fun _ s =>
           (forall x, dfn s x = dfn snap x) /\
           (forall x, fa s x = fa snap x) /\
           (forall x, Active x s <-> Active x snap) /\
           (forall x, x <> u -> low s x = low snap x)).

  Definition UpdateLowPreservesFrontierWithIncomingBound_statement: Prop :=
    forall u done n,
      Hoare
        (fun s : St =>
           LowFrontierCandidate u done s /\
           n <= dfn s u /\
           forall a,
             done a ->
             Edge u a ->
             (fa s a = u -> n <= low s a) /\
             (Active a s -> n <= dfn s a))
        (update_low u n)
        (fun _ s => LowFrontierCandidate u done s).

  Definition UpdateLowPreservesFrontierCandidate_statement: Prop :=
    forall u done n,
      Hoare
        (LowFrontierCandidate u done)
        (update_low u n)
        (fun _ s => LowFrontierCandidate u done s).

  Definition UpdateLowSourceOrIncomingCandidate_statement: Prop :=
    forall u done n,
      Hoare
        (LowSourceCandidate u done)
        (update_low u n)
        (fun _ s => LowSourceCandidate u done s \/ low s u = n).

  Definition GetLowUpdateLowExtendsFrontierTreeCandidate_statement: Prop :=
    forall u done a,
      Edge u a ->
      Hoare
        (fun s : St =>
           LowFrontierCandidate u done s /\
           fa s a = u /\
           fa s a <> a /\
           low s a <= dfn s a)
        (lv <- get' (fun s => low s a);; update_low u lv)
        (fun _ s => LowFrontierCandidate u (done_after done a) s).

  Definition GetDfnUpdateLowExtendsFrontierStackCandidate_statement: Prop :=
    forall u done a,
      Edge u a ->
      Hoare
        (fun s : St =>
           LowFrontierCandidate u done s /\
           Active a s /\
           fa s a <> u)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s => LowFrontierCandidate u (done_after done a) s).

  Definition GetLowUpdateLowProducesTreeSourceCandidate_statement: Prop :=
    forall u done a,
      Edge u a ->
      Hoare
        (fun s : St =>
           LowSourceCandidate u done s /\
           fa s a = u /\
           fa s a <> a)
        (lv <- get' (fun s => low s a);; update_low u lv)
        (fun _ s => LowSourceCandidate u (done_after done a) s).

  Definition GetDfnUpdateLowProducesStackSourceCandidate_statement: Prop :=
    forall u done a,
      Edge u a ->
      Hoare
        (fun s : St =>
           LowSourceCandidate u done s /\
           Active a s /\
           fa s a <> u)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s => LowSourceCandidate u (done_after done a) s).

  Definition SetFaPreservesPartialLowCandidate_statement: Prop :=
    forall parent child done,
      ~ done child ->
      Hoare
        (PartialRootLowEquationCandidate parent done)
        (set_fa child parent)
        (fun _ s => PartialRootLowEquationCandidate parent done s).

  Definition ChildProvidesLowContributionCandidate (W: RecProgram): Prop :=
    forall parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           ChildEntryCandidate parent child done s /\
           PartialRootLowEquationCandidate parent done s)
        (W child)
        (fun _ s =>
           PartialRootLowEquationCandidate parent done s /\
           fa s child = parent /\
           fa s child <> child /\
           low s child <= dfn s child).

  Definition GetLowUpdateLowExtendsPartialLowTreeCandidate_statement: Prop :=
    forall u done a,
      Edge u a ->
      Hoare
        (fun s : St =>
           PartialRootLowEquationCandidate u done s /\
           fa s a = u /\
           fa s a <> a /\
           low s a <= dfn s a)
        (lv <- get' (fun s => low s a);; update_low u lv)
        (fun _ s => PartialRootLowEquationCandidate u (done_after done a) s).

  Definition GetDfnUpdateLowExtendsPartialLowStackCandidate_statement: Prop :=
    forall u done a,
      Edge u a ->
      Hoare
        (fun s : St =>
           PartialRootLowEquationCandidate u done s /\
           Active a s /\
           fa s a <> u)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s => PartialRootLowEquationCandidate u (done_after done a) s).

  Definition ProcessEdgeTreeBranchExtendsPartialLowCandidate_statement: Prop :=
    forall W u a done,
      ChildProvidesLowContributionCandidate W ->
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvLowCandidate u done s /\
           Unvisited a s)
        (set_fa a u;; W a;;
         lv <- get' (fun s => low s a);; update_low u lv)
        (fun _ s => PartialRootLowEquationCandidate u (done_after done a) s).

  Definition ProcessEdgeExtendsPartialLowCandidate_statement: Prop :=
    forall W u a done,
      ChildProvidesLowContributionCandidate W ->
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvLowCandidate u done s /\
           (Visited a s -> Active a s -> fa s a <> u) /\
           (Visited a s ->
            ~ Active a s ->
            fa s a = u ->
           low s u <= low s a))
        (process_edge u W a)
        (fun _ s => PartialRootLowEquationCandidate u (done_after done a) s).

  Definition ProcessEdgeVisitedActiveExtendsPartialLowCandidate_statement: Prop :=
    forall W u a done,
      Edge u a ->
      Hoare
        (fun s =>
           PartialRootLowEquationCandidate u done s /\
           Visited a s /\
           Active a s /\
           fa s a <> u)
        (process_edge u W a)
        (fun _ s => PartialRootLowEquationCandidate u (done_after done a) s).

  Definition ProcessEdgeVisitedNonStackExtendsPartialLowCandidate_statement: Prop :=
    forall W u a done,
      Edge u a ->
      Hoare
        (fun s =>
           PartialRootLowEquationCandidate u done s /\
           Visited a s /\
           ~ Active a s /\
           (fa s a = u -> low s u <= low s a) /\
           (Active a s -> low s u <= dfn s a))
        (process_edge u W a)
        (fun _ s => PartialRootLowEquationCandidate u (done_after done a) s).

  (* ================================================================ *)
  (* Producer audit proofs                                            *)
  (* ================================================================ *)

  Lemma preloop_self_low_eq_dfn (u: V):
    Hoare
      (fun _ : St => True)
      (preloop u)
      (fun _ s => low s u = dfn s u).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    unfold equiv_decb.
    destruct (equiv_dec u u) as [_ | Hneq];
      [ reflexivity | exfalso; apply Hneq; reflexivity ].
  Qed.

  Lemma PreloopGlobalShapeCandidate_proof:
    PreloopGlobalShapeCandidate_statement.
  Proof.
    intro u.
    unfold GlobalShapePreCandidate, GlobalShapeCandidate.
    apply preloop_preserves_wf_scc_state.
  Qed.

  Lemma PreloopSettledClosedCandidate_proof:
    PreloopSettledClosedCandidate_statement.
  Proof.
    intro u.
    unfold SettledClosedCandidate.
    apply preloop_keep_settled_closed.
  Qed.

  Lemma PreloopOrderFactsCandidate_proof:
    PreloopOrderFactsCandidate_statement.
  Proof.
    intro u.
    unfold OrderFactsCandidate, GlobalShapePreCandidate.
    apply Hoare_conj.
    - eapply Hoare_conseq_pre.
      2: apply preloop_preserves_stack_dfn_order.
      intros s [[Horder _] [[Hsiv [Hinv _]] Hunvis]].
      split; [exact Horder | split; [exact Hinv | split; [exact Hsiv | exact Hunvis]]].
    - eapply Hoare_conseq_pre.
      2: apply preloop_preserves_dfn_injective.
      intros s [[_ Hinj] [[_ [Hinv _]] Hunvis]].
      split; [exact Hinj | split; [exact Hinv | exact Hunvis]].
  Qed.

  Lemma PreloopActiveSelfLowCandidate_proof:
    PreloopActiveSelfLowCandidate_statement.
  Proof.
    intro u.
    apply Hoare_conj.
    - eapply Hoare_conseq_pre.
      2: apply preloop_self_visited.
      intros s _. exact I.
    - apply Hoare_conj.
      + eapply Hoare_conseq_pre.
        2: apply preloop_in_stack.
        intros s _. exact I.
      + eapply Hoare_conseq_pre.
        2: apply preloop_self_low_eq_dfn.
        intros s _. exact I.
  Qed.

  Lemma SetFaGlobalShapePreCandidate_proof:
    SetFaGlobalShapePreCandidate_statement.
  Proof.
    intros parent child.
    unfold GlobalShapeCandidate, GlobalShapePreCandidate,
      Visited, Unvisited.
    apply set_fa_preserves_wf_scc_state_pre.
  Qed.

  Lemma SetFaSettledClosedCandidate_proof:
    SetFaSettledClosedCandidate_statement.
  Proof.
    intros parent child.
    unfold SettledClosedCandidate.
    apply set_fa_keep_settled_closed.
  Qed.

  Lemma SetFaOrderFactsCandidate_proof:
    SetFaOrderFactsCandidate_statement.
  Proof.
    intros parent child.
    unfold OrderFactsCandidate.
    apply Hoare_conj.
    - eapply Hoare_conseq_pre.
      2: apply set_fa_keep_stack_dfn_order.
      intros s [Horder _]. exact Horder.
    - eapply Hoare_conseq_pre.
      2: apply set_fa_keep_dfn_injective.
      intros s [_ Hinj]. exact Hinj.
  Qed.

  Lemma SetFaParentPointerCandidate_proof:
    SetFaParentPointerCandidate_statement.
  Proof.
    intros parent child.
    apply set_fa_new_fa.
  Qed.

  Lemma SetFaKeepsChildUnvisitedCandidate_proof:
    SetFaKeepsChildUnvisitedCandidate_statement.
  Proof.
    intros parent child.
    unfold Unvisited, Visited.
    apply set_fa_keep_not_visited.
  Qed.

  Lemma SetFaParentActiveCandidate_proof:
    SetFaParentActiveCandidate_statement.
  Proof.
    intros parent child.
    unfold ParentActiveBaseCandidate.
    apply Hoare_conj.
    - eapply Hoare_conseq_post.
      2: {
        eapply Hoare_conseq_pre.
        2: apply (SetFaGlobalShapePreCandidate_proof parent child).
        intros s [[Hglobal [_ [Hparent _]]] Hunvis].
        split; [exact Hglobal | split; [exact Hparent | exact Hunvis]]. }
      intros _ s [[Hglobal _] _]. exact Hglobal.
    - apply Hoare_conj.
      + eapply Hoare_conseq_pre.
        2: apply SetFaSettledClosedCandidate_proof.
        intros s [[_ [Hsettled _]] _]. exact Hsettled.
      + apply Hoare_conj.
        * eapply Hoare_conseq_pre.
          2: apply set_fa_keep_visited.
          intros s [[_ [_ [Hparent _]]] _]. exact Hparent.
        * apply Hoare_conj.
          -- eapply Hoare_conseq_pre.
             2: apply set_fa_keep_in_stack.
             intros s [[_ [_ [_ [Hactive _]]]] _]. exact Hactive.
          -- eapply Hoare_conseq_pre.
             2: apply SetFaOrderFactsCandidate_proof.
             intros s [[_ [_ [_ [_ Horder]]]] _]. exact Horder.
  Qed.

  Lemma SetFaKeepsDoneExclusionCandidate_proof
        (parent child: V) (done: V -> Prop):
    ~ done child ->
    Hoare
      (fun _ : St => True)
      (set_fa child parent)
      (fun _ _ => ~ done child).
  Proof.
    intros Hnot_done.
    unfold Hoare. intros _ _ _ _ _. exact Hnot_done.
  Qed.

  Lemma SetFaKeepsEdgeCandidate_proof
        (parent child: V):
    Edge parent child ->
    Hoare
      (fun _ : St => True)
      (set_fa child parent)
      (fun _ _ => Edge parent child).
  Proof.
    intros Hedge.
    unfold Hoare. intros _ _ _ _ _. exact Hedge.
  Qed.

  Lemma GlobalShapeCandidate_pending_child_audit_proof:
    GlobalShapeCandidate_pending_child_audit.
  Proof.
    intros parent child _.
    apply SetFaGlobalShapePreCandidate_proof.
  Qed.

  Lemma PreloopEntryBaseCandidate_proof:
    PreloopEntryBaseCandidate_statement.
  Proof.
    intro u.
    unfold EntryPreCandidate, LoopEntryBaseCandidate.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => GlobalShapeCandidate s)
             (Q2 := fun _ s =>
                      SettledClosedCandidate s /\
                      (Visited u s /\ Active u s /\ low s u = dfn s u) /\
                      OrderFactsCandidate s).
      - eapply Hoare_conseq_pre.
        2: apply (PreloopGlobalShapeCandidate_proof u).
        intros s [Hglobal _]. exact Hglobal.
      - apply Hoare_conj
          with (Q1 := fun _ s => SettledClosedCandidate s)
               (Q2 := fun _ s =>
                        (Visited u s /\ Active u s /\ low s u = dfn s u) /\
                        OrderFactsCandidate s).
        + eapply Hoare_conseq_pre.
          2: apply (PreloopSettledClosedCandidate_proof u).
          intros s [_ [Hsettled _]]. exact Hsettled.
        + apply Hoare_conj
            with (Q1 := fun _ s =>
                         Visited u s /\ Active u s /\ low s u = dfn s u)
                 (Q2 := fun _ s => OrderFactsCandidate s).
          * eapply Hoare_conseq_pre.
            2: apply (PreloopActiveSelfLowCandidate_proof u).
            intros s [Hglobal _]. exact Hglobal.
          * eapply Hoare_conseq_pre.
            2: apply (PreloopOrderFactsCandidate_proof u).
            intros s [Hglobal [_ Horder]]. split; assumption. }
    intros _ s [Hglobal [Hsettled [Hactive Horder]]].
    destruct Hactive as [Hvis [Hact Hlow]].
    split; [exact Hglobal |].
    split; [exact Hsettled |].
    split; [exact Hvis |].
    split; [exact Hact |].
    split; [exact Hlow | exact Horder].
  Qed.

  Lemma SetFaCreatesPendingChildCandidate_proof:
    SetFaCreatesPendingChildCandidate_statement.
  Proof.
    intros parent child done Hedge Hnot_done.
    unfold ChildEntryCandidate, ParentLoopSuspendedBaseCandidate,
      PendingChildShapeCandidate.
    apply Hoare_conj.
    - apply Hoare_conj.
      + eapply Hoare_conseq_pre.
        2: apply (SetFaParentActiveCandidate_proof parent child).
        intros s [Hparent [Hunvis _]].
        split; [exact Hparent | exact Hunvis].
      + eapply Hoare_conseq_pre.
        2: apply (SetFaKeepsDoneExclusionCandidate_proof parent child done Hnot_done).
        intros s _. exact I.
    - apply Hoare_conj.
      + eapply Hoare_conseq_post.
        2: {
          eapply Hoare_conseq_pre.
          2: apply (SetFaGlobalShapePreCandidate_proof parent child).
          intros s [Hparent [Hunvis _]].
          destruct Hparent as [Hglobal [_ [Hvisited _]]].
          split; [exact Hglobal | split; [exact Hvisited | exact Hunvis]]. }
        intros _ s [Hglobalpre _]. exact Hglobalpre.
      + apply Hoare_conj.
        * eapply Hoare_conseq_pre.
          2: apply (SetFaSettledClosedCandidate_proof parent child).
          intros s [[_ [Hsettled _]] _]. exact Hsettled.
        * apply Hoare_conj.
          -- eapply Hoare_conseq_pre.
             2: apply set_fa_keep_visited.
             intros s [[_ [_ [Hvisited _]]] _]. exact Hvisited.
          -- apply Hoare_conj.
             ++ eapply Hoare_conseq_pre.
                2: apply (SetFaKeepsEdgeCandidate_proof parent child Hedge).
                intros s _. exact I.
             ++ apply Hoare_conj.
                ** eapply Hoare_conseq_pre.
                   2: apply (SetFaParentPointerCandidate_proof parent child).
                   intros s _. exact I.
                ** eapply Hoare_conseq_pre.
                   2: apply (SetFaOrderFactsCandidate_proof parent child).
                   intros s [_ [_ Horder]]. exact Horder.
  Qed.

  (* ================================================================ *)
  (* Loop-entry consumer audit proofs                                 *)
  (* ================================================================ *)

  Lemma LoopEntryImpliesLocalActiveRootCandidate_proof:
    LoopEntryImpliesLocalActiveRootCandidate_statement.
  Proof.
    unfold LoopEntryImpliesLocalActiveRootCandidate_statement,
      LoopEntryBaseCandidate, LocalActiveRootCandidate.
    intros u s [Hglobal [Hsettled [Hvis [Hactive [_ Horder]]]]].
    split; [exact Hglobal |].
    split; [exact Hsettled |].
    split; [exact Hvis |].
    split; [exact Hactive | exact Horder].
  Qed.

  Lemma DoneEmptyCandidate_empty_proof:
    DoneEmptyCandidate_empty_statement.
  Proof.
    unfold DoneEmptyCandidate_empty_statement, DoneEmptyCandidate.
    intros a Hempty. sets_unfold in Hempty. exact Hempty.
  Qed.

  Lemma LoopEntryImpliesBaseCandidate_proof:
    LoopEntryImpliesBaseCandidate_statement.
  Proof.
    unfold LoopEntryImpliesBaseCandidate_statement,
      LoopInvBaseCandidate.
    intros u s Hentry.
    split.
    - apply LoopEntryImpliesLocalActiveRootCandidate_proof.
      exact Hentry.
    - apply DoneEmptyCandidate_empty_proof.
  Qed.

  Lemma LoopInvBaseProvidesSetFaPreCandidate_proof:
    LoopInvBaseProvidesSetFaPreCandidate_statement.
  Proof.
    unfold LoopInvBaseProvidesSetFaPreCandidate_statement,
      LoopInvBaseCandidate, LocalActiveRootCandidate,
      ParentActiveBaseCandidate.
    intros parent child done s
           [[Hglobal [Hsettled [Hvisited [Hactive Horder]]]] _]
           Hunvis.
    split.
    - split; [exact Hglobal |].
      split; [exact Hsettled |].
      split; [exact Hvisited |].
      split; [exact Hactive | exact Horder].
    - split; [exact Hunvis | exact Horder].
  Qed.

  Lemma LoopInvBaseConsumesUnvisitedSetFaCandidate_proof:
    LoopInvBaseConsumesUnvisitedSetFaCandidate_statement.
  Proof.
    intros parent child done Hedge Hnot_done.
    eapply Hoare_conseq_pre.
    2: apply (SetFaCreatesPendingChildCandidate_proof
                parent child done Hedge Hnot_done).
    intros s [Hbase Hunvis].
    exact (LoopInvBaseProvidesSetFaPreCandidate_proof
             parent child done s Hbase Hunvis).
  Qed.

  (* ================================================================ *)
  (* Done-discipline audit proofs                                     *)
  (* ================================================================ *)

  Lemma DoneSubsetOfOutgoingCandidate_empty_proof:
    DoneSubsetOfOutgoingCandidate_empty_statement.
  Proof.
    unfold DoneSubsetOfOutgoingCandidate_empty_statement,
      DoneSubsetOfOutgoingCandidate.
    intros u a Hempty. sets_unfold in Hempty. destruct Hempty.
  Qed.

  Lemma DoneVisitedCandidate_empty_proof:
    DoneVisitedCandidate_empty_statement.
  Proof.
    unfold DoneVisitedCandidate_empty_statement,
      DoneVisitedCandidate.
    intros s a Hempty. sets_unfold in Hempty. destruct Hempty.
  Qed.

  Lemma DoneDisciplineCandidate_empty_proof:
    DoneDisciplineCandidate_empty_statement.
  Proof.
    unfold DoneDisciplineCandidate_empty_statement,
      DoneDisciplineCandidate.
    intros u s.
    split.
    - apply DoneSubsetOfOutgoingCandidate_empty_proof.
    - apply DoneVisitedCandidate_empty_proof.
  Qed.

  Lemma DoneSubsetOfOutgoingCandidate_step_proof:
    DoneSubsetOfOutgoingCandidate_step_statement.
  Proof.
    unfold DoneSubsetOfOutgoingCandidate_step_statement,
      DoneSubsetOfOutgoingCandidate, done_after.
    intros u done a Hdone_sub Hedge x Hx.
    sets_unfold in Hx.
    destruct Hx as [Hx_done | Hx_eq_a].
    - apply Hdone_sub. exact Hx_done.
    - subst x. exact Hedge.
  Qed.

  Lemma DoneVisitedCandidate_step_proof:
    DoneVisitedCandidate_step_statement.
  Proof.
    unfold DoneVisitedCandidate_step_statement,
      DoneVisitedCandidate, done_after.
    intros done a s Hdone_vis Ha_vis x Hx.
    sets_unfold in Hx.
    destruct Hx as [Hx_done | Hx_eq_a].
    - apply Hdone_vis. exact Hx_done.
    - subst x. exact Ha_vis.
  Qed.

  Lemma DoneDisciplineCandidate_step_proof:
    DoneDisciplineCandidate_step_statement.
  Proof.
    unfold DoneDisciplineCandidate_step_statement,
      DoneDisciplineCandidate.
    intros u done a s [Hsubset Hvisited] Hedge Ha_vis.
    split.
    - apply DoneSubsetOfOutgoingCandidate_step_proof; assumption.
    - apply DoneVisitedCandidate_step_proof; assumption.
  Qed.

  Lemma LoopEntryImpliesDoneCandidate_proof:
    LoopEntryImpliesDoneCandidate_statement.
  Proof.
    unfold LoopEntryImpliesDoneCandidate_statement,
      LoopInvDoneCandidate.
    intros u s Hentry.
    split.
    - apply LoopEntryImpliesLocalActiveRootCandidate_proof.
      exact Hentry.
    - apply DoneDisciplineCandidate_empty_proof.
  Qed.

  Lemma LoopInvDoneProvidesSetFaPreCandidate_proof:
    LoopInvDoneProvidesSetFaPreCandidate_statement.
  Proof.
    unfold LoopInvDoneProvidesSetFaPreCandidate_statement,
      LoopInvDoneCandidate, LocalActiveRootCandidate,
      ParentActiveBaseCandidate.
    intros parent child done s
           [[Hglobal [Hsettled [Hvisited [Hactive Horder]]]] _]
           Hunvis.
    split.
    - split; [exact Hglobal |].
      split; [exact Hsettled |].
      split; [exact Hvisited |].
      split; [exact Hactive | exact Horder].
    - split; [exact Hunvis | exact Horder].
  Qed.

  Lemma LoopInvDoneConsumesUnvisitedSetFaCandidate_proof:
    LoopInvDoneConsumesUnvisitedSetFaCandidate_statement.
  Proof.
    intros parent child done Hedge Hnot_done.
    eapply Hoare_conseq_pre.
    2: apply (SetFaCreatesPendingChildCandidate_proof
                parent child done Hedge Hnot_done).
    intros s [Hdone Hunvis].
    exact (LoopInvDoneProvidesSetFaPreCandidate_proof
             parent child done s Hdone Hunvis).
  Qed.

  (* ================================================================ *)
  (* Done-discipline branch-integration proofs                        *)
  (* ================================================================ *)

  Lemma ProcessEdgeProducesVisitedTargetCandidate_proof:
    ProcessEdgeProducesVisitedTargetCandidate_statement.
  Proof.
    unfold ProcessEdgeProducesVisitedTargetCandidate_statement,
      ChildReturnsVisitedCandidate.
    intros W u a done Hchild Hedge Hnot_done.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - (* Tree edge: [a] was unvisited, so the recursive callback visits it. *)
      apply Hoare_assume_bind. simpl.
      eapply Hoare_bind.
      { eapply Hoare_conseq_pre.
        2: apply (LoopInvDoneConsumesUnvisitedSetFaCandidate_proof
                    u a done Hedge Hnot_done).
        intros s [Hunvis Heq]. subst s.
        split; [exact H | exact Hunvis]. }
      simpl. intros _.
      eapply Hoare_bind.
      { apply (Hchild u a done Hedge Hnot_done). }
      simpl. intros _.
      apply get_low_update_low_keep_visited.
    - (* Non-tree edge: the branch condition gives [~~ Visited a]. *)
      apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hnnvis Heq0]. subst s1.
      assert (Hvis: Visited a s0).
      { unfold Visited. apply NNPP. exact Hnnvis. }
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        intro_state.
        destruct H1 as [_ Heq1]. subst s1.
        eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
        eapply Hoare_conseq_pre.
        2: apply (update_low_keep_visited u a dv).
        intros s [Heq_s _]. subst s. exact Hvis.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _]. subst s. exact Hvis.
  Qed.

  Lemma ProcessEdgeExtendsDoneDisciplineCandidate_proof:
    ProcessEdgeExtendsDoneDisciplineCandidate_statement.
  Proof.
    intros W u a done Hchild Hpreserve_done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s =>
                      DoneSubsetOfOutgoingCandidate u done /\
                      DoneVisitedCandidate done s)
             (Q2 := fun _ s => Visited a s).
      - apply Hoare_conj.
        + unfold Hoare. intros s1 _ s2 Hpre _.
          destruct Hpre as [_ [Hsubset _]]. exact Hsubset.
        + eapply Hoare_conseq_pre.
          2: apply (process_edge_keep_visited_forall u a W done).
          * intros s [_ [_ Hdone_visited]].
            exact Hdone_visited.
          * intros x. apply Hpreserve_done.
      - apply (ProcessEdgeProducesVisitedTargetCandidate_proof
                 W u a done Hchild Hedge Hnot_done). }
    intros _ s [[Hsubset Hdone_vis] Ha_vis].
    exact (DoneDisciplineCandidate_step_proof
             u done a s (conj Hsubset Hdone_vis) Hedge Ha_vis).
  Qed.

  (* ================================================================ *)
  (* Partial-low-equation audit proofs                                *)
  (* ================================================================ *)

  Lemma LowFrontierCandidate_empty_proof:
    LowFrontierCandidate_empty_statement.
  Proof.
    unfold LowFrontierCandidate_empty_statement,
      LowFrontierCandidate.
    intros u s Hlow.
    split.
    - rewrite Hlow. apply le_n.
    - intros a Hempty _.
      sets_unfold in Hempty. destruct Hempty.
  Qed.

  Lemma LowSourceCandidate_empty_proof:
    LowSourceCandidate_empty_statement.
  Proof.
    unfold LowSourceCandidate_empty_statement,
      LowSourceCandidate.
    intros u s Hlow. left. exact Hlow.
  Qed.

  Lemma PartialRootLowEquationCandidate_empty_proof:
    PartialRootLowEquationCandidate_empty_statement.
  Proof.
    unfold PartialRootLowEquationCandidate_empty_statement,
      PartialRootLowEquationCandidate.
    intros u s Hlow.
    split.
    - apply LowFrontierCandidate_empty_proof. exact Hlow.
    - apply LowSourceCandidate_empty_proof. exact Hlow.
  Qed.

  Lemma LoopEntryImpliesPartialLowCandidate_proof:
    LoopEntryImpliesPartialLowCandidate_statement.
  Proof.
    unfold LoopEntryImpliesPartialLowCandidate_statement,
      LoopEntryBaseCandidate.
    intros u s [_ [_ [_ [_ [Hlow _]]]]].
    apply PartialRootLowEquationCandidate_empty_proof.
    exact Hlow.
  Qed.

  Lemma LoopEntryImpliesLowCandidate_proof:
    LoopEntryImpliesLowCandidate_statement.
  Proof.
    unfold LoopEntryImpliesLowCandidate_statement,
      LoopInvLowCandidate.
    intros u s Hentry.
    split.
    - apply LoopEntryImpliesDoneCandidate_proof.
      exact Hentry.
    - apply LoopEntryImpliesPartialLowCandidate_proof.
      exact Hentry.
  Qed.

  Lemma LowFrontierCandidate_step_proof:
    LowFrontierCandidate_step_statement.
  Proof.
    unfold LowFrontierCandidate_step_statement,
      LowFrontierCandidate, done_after.
    intros u done a s [Hself Hfront] Hedge Ha_tree Ha_stack.
    split.
    - exact Hself.
    - intros x Hx Hxedge.
      sets_unfold in Hx.
      destruct Hx as [Hx_done | Hx_eq_a].
      + exact (Hfront x Hx_done Hxedge).
      + subst x. split; [exact Ha_tree | exact Ha_stack].
  Qed.

  Lemma LowSourceCandidate_step_keep_proof:
    LowSourceCandidate_step_keep_statement.
  Proof.
    unfold LowSourceCandidate_step_keep_statement,
      LowSourceCandidate, done_after.
    intros u done a s Hsrc.
    destruct Hsrc as [Hself | [Htree | Hstack]].
    - left. exact Hself.
    - right. left.
      destruct Htree as
        (x & Hdone_x & Hedge_x & Hfa_x & Hfa_neq_x & Hlow_x).
      exists x.
      split.
      + sets_unfold. left. exact Hdone_x.
      + repeat split; assumption.
    - right. right.
      destruct Hstack as
        (x & Hdone_x & Hedge_x & Hactive_x & Hfa_neq_x & Hlow_x).
      exists x.
      split.
      + sets_unfold. left. exact Hdone_x.
      + repeat split; assumption.
  Qed.

  Lemma LowSourceCandidate_step_tree_proof:
    LowSourceCandidate_step_tree_statement.
  Proof.
    unfold LowSourceCandidate_step_tree_statement,
      LowSourceCandidate, done_after.
    intros u done a s Hedge Hfa Hfa_neq Hlow.
    right. left.
    exists a.
    split.
    - sets_unfold. right. reflexivity.
    - repeat split; assumption.
  Qed.

  Lemma LowSourceCandidate_step_stack_proof:
    LowSourceCandidate_step_stack_statement.
  Proof.
    unfold LowSourceCandidate_step_stack_statement,
      LowSourceCandidate, done_after.
    intros u done a s Hedge Hactive Hfa_neq Hlow.
    right. right.
    exists a.
    split.
    - sets_unfold. right. reflexivity.
    - repeat split; assumption.
  Qed.

  Lemma PartialRootLowEquationCandidate_step_keep_proof:
    PartialRootLowEquationCandidate_step_keep_statement.
  Proof.
    unfold PartialRootLowEquationCandidate_step_keep_statement,
      PartialRootLowEquationCandidate.
    intros u done a s [Hfront Hsrc] Hedge Ha_tree Ha_stack.
    split.
    - exact (LowFrontierCandidate_step_proof
               u done a s Hfront Hedge Ha_tree Ha_stack).
    - apply LowSourceCandidate_step_keep_proof.
      exact Hsrc.
  Qed.

  Lemma UpdateLowBoundedByOldCandidate_proof:
    UpdateLowBoundedByOldCandidate_statement.
  Proof.
    unfold UpdateLowBoundedByOldCandidate_statement.
    intros u n old_low.
    apply update_low_nonincreasing.
  Qed.

  Lemma UpdateLowBoundedByIncomingCandidate_proof:
    UpdateLowBoundedByIncomingCandidate_statement.
  Proof.
    unfold UpdateLowBoundedByIncomingCandidate_statement.
    intros u n.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst s. simpl.
      unfold equiv_decb.
      destruct (equiv_dec u u) as [_ | Hneq];
        [lia | exfalso; apply Hneq; reflexivity].
    - destruct H1 as [Heq Hnot_lt]. subst s. lia.
  Qed.

  Lemma UpdateLowSourceCandidate_proof:
    UpdateLowSourceCandidate_statement.
  Proof.
    unfold UpdateLowSourceCandidate_statement.
    intros u n old_low.
    apply Hoare_normalize. intros snap Hsnap.
    unfold update_low.
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros lu.
    eapply Hoare_conseq_pre with (P2 := fun s : St => s = snap).
    2: {
    unfold If.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold set_low.
      intro_state. hoare_auto_s.
      subst s. simpl.
      unfold equiv_decb.
      destruct (equiv_dec u u) as [_ | Hneq].
      + right. reflexivity.
      + exfalso. apply Hneq. reflexivity.
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume_s. }
      intros _ s [Heq_s _].
      subst s.
      left. exact Hsnap. }
    intros s [Heq_s _]. exact Heq_s.
  Qed.

  Lemma UpdateLowKeepsSnapshotFieldsCandidate_proof:
    UpdateLowKeepsSnapshotFieldsCandidate_statement.
  Proof.
    unfold UpdateLowKeepsSnapshotFieldsCandidate_statement.
    intros u n snap.
    unfold update_low.
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros lu.
    eapply Hoare_conseq_pre with (P2 := fun s : St => s = snap).
    2: {
      unfold If.
      apply Hoare_choice.
      - apply Hoare_assume_bind. simpl.
        unfold set_low.
        intro_state. hoare_auto_s.
        destruct H as [_ Heq_snap].
        subst s s0. simpl.
        split.
        + intros x. reflexivity.
        + split.
          * intros x. reflexivity.
          * split.
            -- intros x. unfold Active. reflexivity.
            -- intros x Hneq.
               unfold equiv_decb.
               destruct (equiv_dec x u) as [Heq | _].
               ++ exfalso. apply Hneq. exact Heq.
               ++ reflexivity.
      - eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _].
        subst s.
        split.
        + intros x. reflexivity.
        + split.
          * intros x. reflexivity.
          * split.
            -- intros x. unfold Active. reflexivity.
            -- intros x _. reflexivity. }
    intros s [Heq_s _]. exact Heq_s.
  Qed.

  Lemma UpdateLowPreservesFrontierWithIncomingBound_proof:
    UpdateLowPreservesFrontierWithIncomingBound_statement.
  Proof.
    unfold UpdateLowPreservesFrontierWithIncomingBound_statement.
    intros u done n.
    apply Hoare_normalize.
    intros snap [Hfront [Hn_dfn Hn_front]].
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s =>
                      low s u <= low snap u /\ low s u <= n)
             (Q2 := fun _ s =>
                      (forall x, dfn s x = dfn snap x) /\
                      (forall x, fa s x = fa snap x) /\
                      (forall x, Active x s <-> Active x snap) /\
                      (forall x, x <> u -> low s x = low snap x)).
      - apply Hoare_conj.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowBoundedByOldCandidate_proof u n (low snap u)).
          intros s Heq_s. subst s. reflexivity.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowBoundedByIncomingCandidate_proof u n).
          intros s _. exact I.
      - apply UpdateLowKeepsSnapshotFieldsCandidate_proof. }
    intros _ s [[Hlow_old Hlow_n] [Hdfn_keep [Hfa_keep [Hactive_keep Hlow_other]]]].
    unfold LowFrontierCandidate in Hfront |- *.
    destruct Hfront as [Hold_self Hold_front].
    split.
    - rewrite Hdfn_keep. lia.
    - intros a Hdone_a Hedge_a.
      specialize (Hold_front a Hdone_a Hedge_a) as [Hold_tree Hold_stack].
      specialize (Hn_front a Hdone_a Hedge_a) as [Hn_tree Hn_stack].
      split.
      + intros Hfa_new.
        rewrite Hfa_keep in Hfa_new.
        destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq_u].
        * rewrite Ha_eq_u.
          lia.
        * rewrite (Hlow_other a Ha_neq_u).
          specialize (Hold_tree Hfa_new).
          specialize (Hn_tree Hfa_new).
          lia.
      + intros Hactive_new.
        rewrite Hdfn_keep.
        apply Hactive_keep in Hactive_new.
        specialize (Hold_stack Hactive_new).
        specialize (Hn_stack Hactive_new).
        lia.
  Qed.

  Lemma UpdateLowPreservesFrontierCandidate_proof:
    UpdateLowPreservesFrontierCandidate_statement.
  Proof.
    unfold UpdateLowPreservesFrontierCandidate_statement.
    intros u done n.
    apply Hoare_normalize.
    intros snap Hfront.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => low s u <= low snap u)
             (Q2 := fun _ s =>
                      (forall x, dfn s x = dfn snap x) /\
                      (forall x, fa s x = fa snap x) /\
                      (forall x, Active x s <-> Active x snap) /\
                      (forall x, x <> u -> low s x = low snap x)).
      - eapply Hoare_conseq_pre.
        2: apply (UpdateLowBoundedByOldCandidate_proof u n (low snap u)).
        intros s Heq_s. subst s. reflexivity.
      - apply UpdateLowKeepsSnapshotFieldsCandidate_proof. }
    intros _ s [Hlow_old [Hdfn_keep [Hfa_keep [Hactive_keep Hlow_other]]]].
    unfold LowFrontierCandidate in Hfront |- *.
    destruct Hfront as [Hold_self Hold_front].
    split.
    - rewrite Hdfn_keep. lia.
    - intros a Hdone_a Hedge_a.
      specialize (Hold_front a Hdone_a Hedge_a) as [Hold_tree Hold_stack].
      split.
      + intros Hfa_new.
        rewrite Hfa_keep in Hfa_new.
        destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq_u].
        * rewrite Ha_eq_u. lia.
        * rewrite (Hlow_other a Ha_neq_u).
          specialize (Hold_tree Hfa_new).
          lia.
      + intros Hactive_new.
        rewrite Hdfn_keep.
        apply Hactive_keep in Hactive_new.
        specialize (Hold_stack Hactive_new).
        lia.
  Qed.

  Lemma UpdateLowSourceOrIncomingCandidate_proof:
    UpdateLowSourceOrIncomingCandidate_statement.
  Proof.
    unfold UpdateLowSourceOrIncomingCandidate_statement.
    intros u done n.
    apply Hoare_normalize.
    intros snap Hsrc.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => low s u = low snap u \/ low s u = n)
             (Q2 := fun _ s =>
                      (forall x, dfn s x = dfn snap x) /\
                      (forall x, fa s x = fa snap x) /\
                      (forall x, Active x s <-> Active x snap) /\
                      (forall x, x <> u -> low s x = low snap x)).
      - eapply Hoare_conseq_pre.
        2: apply (UpdateLowSourceCandidate_proof u n (low snap u)).
        intros s Heq_s. subst s. reflexivity.
      - apply UpdateLowKeepsSnapshotFieldsCandidate_proof. }
    intros _ s [Hsource_choice [Hdfn_keep [Hfa_keep [Hactive_keep Hlow_other]]]].
    destruct Hsource_choice as [Hlow_old | Hlow_incoming].
    - left.
      unfold LowSourceCandidate in Hsrc |- *.
      destruct Hsrc as [Hself | [Htree | Hstack]].
      + left.
        rewrite Hdfn_keep.
        rewrite Hlow_old.
        exact Hself.
      + right. left.
        destruct Htree as
          (x & Hdone_x & Hedge_x & Hfa_x & Hfa_neq_x & Hlow_x).
        exists x.
        split; [exact Hdone_x |].
        split; [exact Hedge_x |].
        split.
        * rewrite Hfa_keep. exact Hfa_x.
        * split.
          -- rewrite Hfa_keep. exact Hfa_neq_x.
          -- destruct (equiv_dec x u) as [Hx_eq_u | Hx_neq_u].
             ++ rewrite Hx_eq_u. reflexivity.
             ++ rewrite (Hlow_other x Hx_neq_u).
                rewrite Hlow_old.
                exact Hlow_x.
      + right. right.
        destruct Hstack as
          (x & Hdone_x & Hedge_x & Hactive_x & Hfa_neq_x & Hlow_x).
        exists x.
        split; [exact Hdone_x |].
        split; [exact Hedge_x |].
        split.
        * apply Hactive_keep. exact Hactive_x.
        * split.
          -- rewrite Hfa_keep. exact Hfa_neq_x.
          -- rewrite Hdfn_keep.
             rewrite Hlow_old.
             exact Hlow_x.
	    - right. exact Hlow_incoming.
  Qed.

  Lemma GetLowUpdateLowExtendsFrontierTreeCandidate_proof:
    GetLowUpdateLowExtendsFrontierTreeCandidate_statement.
  Proof.
    unfold GetLowUpdateLowExtendsFrontierTreeCandidate_statement.
    intros u done a Hedge.
    apply Hoare_normalize.
    intros snap [Hfront [Hfa [Hfa_neq Hlow_le_dfn]]].
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s =>
                      LowFrontierCandidate u done s /\ low s u <= lv)
             (Q2 := fun _ s =>
                      lv = low snap a /\
                      (forall x, dfn s x = dfn snap x) /\
                      (forall x, fa s x = fa snap x) /\
                      (forall x, Active x s <-> Active x snap) /\
                      (forall x, x <> u -> low s x = low snap x)).
      - apply Hoare_conj.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowPreservesFrontierCandidate_proof u done lv).
          intros s [Heq_s _]. subst s. exact Hfront.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowBoundedByIncomingCandidate_proof u lv).
          intros s _. exact I.
      - apply Hoare_conj.
        + unfold Hoare. intros s1 _ s2 [_ Hlv] _. exact Hlv.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowKeepsSnapshotFieldsCandidate_proof u lv snap).
          intros s [Heq_s _]. exact Heq_s. }
    intros _ s [[Hfront_after Hlow_in]
                 [Hlv [Hdfn_keep [Hfa_keep [Hactive_keep Hlow_other]]]]].
    eapply LowFrontierCandidate_step_proof.
    - exact Hfront_after.
    - exact Hedge.
    - intros _.
      destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq_u].
      + rewrite Ha_eq_u. lia.
      + rewrite (Hlow_other a Ha_neq_u).
        rewrite <- Hlv.
        exact Hlow_in.
    - intros _.
      rewrite Hdfn_keep.
      rewrite Hlv in Hlow_in.
      lia.
  Qed.

  Lemma GetDfnUpdateLowExtendsFrontierStackCandidate_proof:
    GetDfnUpdateLowExtendsFrontierStackCandidate_statement.
  Proof.
    unfold GetDfnUpdateLowExtendsFrontierStackCandidate_statement.
    intros u done a Hedge.
    apply Hoare_normalize.
    intros snap [Hfront [Hactive Hfa_neq]].
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s =>
                      LowFrontierCandidate u done s /\ low s u <= dv)
             (Q2 := fun _ s =>
                      dv = dfn snap a /\
                      (forall x, dfn s x = dfn snap x) /\
                      (forall x, fa s x = fa snap x) /\
                      (forall x, Active x s <-> Active x snap) /\
                      (forall x, x <> u -> low s x = low snap x)).
      - apply Hoare_conj.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowPreservesFrontierCandidate_proof u done dv).
          intros s [Heq_s _]. subst s. exact Hfront.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowBoundedByIncomingCandidate_proof u dv).
          intros s _. exact I.
      - apply Hoare_conj.
        + unfold Hoare. intros s1 _ s2 [_ Hdv] _. exact Hdv.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowKeepsSnapshotFieldsCandidate_proof u dv snap).
          intros s [Heq_s _]. exact Heq_s. }
    intros _ s [[Hfront_after Hlow_in]
                 [Hdv [Hdfn_keep [Hfa_keep [Hactive_keep Hlow_other]]]]].
    eapply LowFrontierCandidate_step_proof.
    - exact Hfront_after.
    - exact Hedge.
    - intros Hfa_after.
      rewrite Hfa_keep in Hfa_after.
      exfalso. apply Hfa_neq. exact Hfa_after.
    - intros _.
      rewrite Hdfn_keep.
      rewrite <- Hdv.
      exact Hlow_in.
  Qed.

  Lemma GetLowUpdateLowProducesTreeSourceCandidate_proof:
    GetLowUpdateLowProducesTreeSourceCandidate_statement.
  Proof.
    unfold GetLowUpdateLowProducesTreeSourceCandidate_statement.
    intros u done a Hedge.
    apply Hoare_normalize.
    intros snap [Hsrc [Hfa Hfa_neq]].
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_post.
    2: {
	      apply Hoare_conj
	        with (Q1 := fun _ s =>
	                      LowSourceCandidate u done s \/ low s u = lv)
	             (Q2 := fun _ s =>
	                      lv = low snap a /\
	                      (forall x, dfn s x = dfn snap x) /\
	                      (forall x, fa s x = fa snap x) /\
	                      (forall x, Active x s <-> Active x snap) /\
	                      (forall x, x <> u -> low s x = low snap x)).
      - eapply Hoare_conseq_pre.
        2: apply (UpdateLowSourceOrIncomingCandidate_proof u done lv).
        intros s [Heq_s Hlv]. subst s lv.
        exact Hsrc.
	      - apply Hoare_conj.
	        + unfold Hoare. intros s1 _ s2 [_ Hlv] _. exact Hlv.
	        + eapply Hoare_conseq_pre.
	          2: apply (UpdateLowKeepsSnapshotFieldsCandidate_proof u lv snap).
	          intros s [Heq_s _]. exact Heq_s. }
	    intros _ s [[Hsrc_after | Hlow_incoming]
	                 [Hlv [Hdfn_keep [Hfa_keep [Hactive_keep Hlow_other]]]]].
    - apply LowSourceCandidate_step_keep_proof.
      exact Hsrc_after.
    - apply LowSourceCandidate_step_tree_proof; try exact Hedge.
      + rewrite Hfa_keep. exact Hfa.
      + rewrite Hfa_keep. exact Hfa_neq.
	      + destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq_u].
	        * rewrite Ha_eq_u. reflexivity.
	        * rewrite (Hlow_other a Ha_neq_u).
	          rewrite <- Hlv.
	          exact Hlow_incoming.
  Qed.

  Lemma GetDfnUpdateLowProducesStackSourceCandidate_proof:
    GetDfnUpdateLowProducesStackSourceCandidate_statement.
  Proof.
    unfold GetDfnUpdateLowProducesStackSourceCandidate_statement.
    intros u done a Hedge.
    apply Hoare_normalize.
    intros snap [Hsrc [Hactive Hfa_neq]].
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_post.
    2: {
	      apply Hoare_conj
	        with (Q1 := fun _ s =>
	                      LowSourceCandidate u done s \/ low s u = dv)
	             (Q2 := fun _ s =>
	                      dv = dfn snap a /\
	                      (forall x, dfn s x = dfn snap x) /\
	                      (forall x, fa s x = fa snap x) /\
	                      (forall x, Active x s <-> Active x snap) /\
	                      (forall x, x <> u -> low s x = low snap x)).
      - eapply Hoare_conseq_pre.
        2: apply (UpdateLowSourceOrIncomingCandidate_proof u done dv).
        intros s [Heq_s Hdv]. subst s dv.
        exact Hsrc.
	      - apply Hoare_conj.
	        + unfold Hoare. intros s1 _ s2 [_ Hdv] _. exact Hdv.
	        + eapply Hoare_conseq_pre.
	          2: apply (UpdateLowKeepsSnapshotFieldsCandidate_proof u dv snap).
	          intros s [Heq_s _]. exact Heq_s. }
	    intros _ s [[Hsrc_after | Hlow_incoming] [Hdv [Hdfn_keep [Hfa_keep [Hactive_keep _]]]]].
    - apply LowSourceCandidate_step_keep_proof.
      exact Hsrc_after.
    - apply LowSourceCandidate_step_stack_proof; try exact Hedge.
      + apply (proj2 (Hactive_keep a)). exact Hactive.
	      + rewrite Hfa_keep. exact Hfa_neq.
	      + rewrite Hlow_incoming.
	        rewrite Hdv.
        rewrite <- Hdfn_keep.
        reflexivity.
  Qed.

  Lemma GetLowUpdateLowExtendsPartialLowTreeCandidate_proof:
    GetLowUpdateLowExtendsPartialLowTreeCandidate_statement.
  Proof.
    unfold GetLowUpdateLowExtendsPartialLowTreeCandidate_statement.
    intros u done a Hedge.
    unfold PartialRootLowEquationCandidate.
    apply Hoare_conj.
    - eapply Hoare_conseq_pre.
      2: apply (GetLowUpdateLowExtendsFrontierTreeCandidate_proof
                  u done a Hedge).
      intros s [[Hfront _] [Hfa [Hfa_neq Hlow_le_dfn]]].
      split; [exact Hfront | split; [exact Hfa | split; assumption]].
    - eapply Hoare_conseq_pre.
      2: apply (GetLowUpdateLowProducesTreeSourceCandidate_proof
                  u done a Hedge).
      intros s [[_ Hsrc] [Hfa [Hfa_neq _]]].
      split; [exact Hsrc | split; assumption].
  Qed.

  Lemma GetDfnUpdateLowExtendsPartialLowStackCandidate_proof:
    GetDfnUpdateLowExtendsPartialLowStackCandidate_statement.
  Proof.
    unfold GetDfnUpdateLowExtendsPartialLowStackCandidate_statement.
    intros u done a Hedge.
    unfold PartialRootLowEquationCandidate.
    apply Hoare_conj.
    - eapply Hoare_conseq_pre.
      2: apply (GetDfnUpdateLowExtendsFrontierStackCandidate_proof
                  u done a Hedge).
      intros s [[Hfront _] [Hactive Hfa_neq]].
      split; [exact Hfront | split; assumption].
    - eapply Hoare_conseq_pre.
      2: apply (GetDfnUpdateLowProducesStackSourceCandidate_proof
                  u done a Hedge).
      intros s [[_ Hsrc] [Hactive Hfa_neq]].
      split; [exact Hsrc | split; assumption].
  Qed.

  Lemma SetFaPreservesPartialLowCandidate_proof:
    SetFaPreservesPartialLowCandidate_statement.
  Proof.
    unfold SetFaPreservesPartialLowCandidate_statement,
      PartialRootLowEquationCandidate,
      LowFrontierCandidate,
      LowSourceCandidate.
    intros parent child done Hnot_done.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [[Hlow_self Hfront] Hsrc].
    split.
    - split.
      + exact Hlow_self.
      + intros a Hdone Hedge.
        specialize (Hfront a Hdone Hedge) as [Htree Hstack].
        split.
        * intro Hfa.
          unfold equiv_decb in Hfa.
          destruct (equiv_dec a child) as [Ha_eq_child | Ha_neq_child].
          -- rewrite Ha_eq_child in Hdone.
             exfalso. apply Hnot_done. exact Hdone.
          -- simpl in Hfa. apply Htree. exact Hfa.
        * intro Hactive.
          apply Hstack. exact Hactive.
    - destruct Hsrc as [Hself | [Htree_src | Hstack_src]].
      + left. exact Hself.
      + right. left.
        destruct Htree_src as
          [a [Hdone [Hedge [Hfa [Hfa_neq Hlow_eq]]]]].
        exists a.
        split; [exact Hdone |].
        split; [exact Hedge |].
        split.
        * unfold equiv_decb.
          destruct (equiv_dec a child) as [Ha_eq_child | Ha_neq_child].
          -- rewrite Ha_eq_child in Hdone.
             exfalso. apply Hnot_done. exact Hdone.
          -- simpl. exact Hfa.
        * split.
          -- unfold equiv_decb.
             destruct (equiv_dec a child) as [Ha_eq_child | Ha_neq_child].
             ++ rewrite Ha_eq_child in Hdone.
                exfalso. apply Hnot_done. exact Hdone.
             ++ simpl. exact Hfa_neq.
          -- exact Hlow_eq.
      + right. right.
        destruct Hstack_src as
          [a [Hdone [Hedge [Hactive [Hfa_neq Hlow_eq]]]]].
        exists a.
        split; [exact Hdone |].
        split; [exact Hedge |].
        split; [exact Hactive |].
        split.
        * unfold equiv_decb.
          destruct (equiv_dec a child) as [Ha_eq_child | Ha_neq_child].
          -- rewrite Ha_eq_child in Hdone.
             exfalso. apply Hnot_done. exact Hdone.
          -- simpl. exact Hfa_neq.
        * exact Hlow_eq.
  Qed.

  Lemma ProcessEdgeTreeBranchExtendsPartialLowCandidate_proof:
    ProcessEdgeTreeBranchExtendsPartialLowCandidate_statement.
  Proof.
    unfold ProcessEdgeTreeBranchExtendsPartialLowCandidate_statement,
      ChildProvidesLowContributionCandidate.
    intros W u a done Hchild Hedge Hnot_done.
    eapply Hoare_bind.
    - apply Hoare_conj.
      + eapply Hoare_conseq_pre.
        2: apply (SetFaCreatesPendingChildCandidate_proof
                    u a done Hedge Hnot_done).
        intros s [[Hloop_done _] Hunvis].
        split.
        * destruct Hloop_done as [Hlocal _].
          exact Hlocal.
        * split; [exact Hunvis |].
          destruct Hloop_done as [Hlocal _].
          destruct Hlocal as [_ [_ [_ [_ Horder]]]].
          exact Horder.
      + eapply Hoare_conseq_pre.
        2: apply (SetFaPreservesPartialLowCandidate_proof
                    u a done Hnot_done).
        intros s [[_ Hpartial] _].
        exact Hpartial.
    - simpl. intros _.
      eapply Hoare_bind.
      + eapply Hoare_conseq_pre.
        2: apply (Hchild u a done Hedge Hnot_done).
        intros s [Hchild_entry Hpartial].
        split.
        * exact Hchild_entry.
        * exact Hpartial.
      + simpl. intros _.
        eapply Hoare_conseq_pre.
        2: apply (GetLowUpdateLowExtendsPartialLowTreeCandidate_proof
                    u done a Hedge).
        intros s [Hpartial [Hfa [Hfa_neq Hlow_le_dfn]]].
        split; [exact Hpartial |].
        split; [exact Hfa |].
        split; [exact Hfa_neq | exact Hlow_le_dfn].
  Qed.

  Lemma ProcessEdgeVisitedActiveExtendsPartialLowCandidate_proof:
    ProcessEdgeVisitedActiveExtendsPartialLowCandidate_statement.
  Proof.
    unfold ProcessEdgeVisitedActiveExtendsPartialLowCandidate_statement.
    intros W u a done Hedge.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hunvis Heq]. subst s1.
      destruct H as [_ [Hvis _]].
      exfalso. apply Hunvis. exact Hvis.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_ Heq0]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: apply (GetDfnUpdateLowExtendsPartialLowStackCandidate_proof
                    u done a Hedge).
        intros s [Hactive_guard Heq_s]. subst s.
        destruct H as [Hpartial [_ [_ Hfa_neq]]].
        split; [exact Hpartial | split; [exact Hactive_guard | exact Hfa_neq]].
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s Hnot_active].
        subst s.
        destruct H as [_ [_ [Hactive _]]].
        exfalso. apply Hnot_active. exact Hactive.
  Qed.

  Lemma ProcessEdgeVisitedNonStackExtendsPartialLowCandidate_proof:
    ProcessEdgeVisitedNonStackExtendsPartialLowCandidate_statement.
  Proof.
    unfold ProcessEdgeVisitedNonStackExtendsPartialLowCandidate_statement.
    intros W u a done Hedge.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hunvis Heq]. subst s1.
      destruct H as [_ [Hvis _]].
      exfalso. apply Hunvis. exact Hvis.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_ Heq0]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        intro_state.
        destruct H1 as [Hactive_guard Heq1]. subst s1.
        destruct H as [_ [_ [Hnot_active _]]].
        exfalso. apply Hnot_active. exact Hactive_guard.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _].
        subst s.
        destruct H as [Hpartial [_ [_ [Htree_bound Hstack_bound]]]].
        eapply PartialRootLowEquationCandidate_step_keep_proof; eauto.
  Qed.

  Lemma ProcessEdgeExtendsPartialLowCandidate_proof:
    ProcessEdgeExtendsPartialLowCandidate_statement.
  Proof.
    unfold ProcessEdgeExtendsPartialLowCandidate_statement.
    intros W u a done Hchild Hedge Hnot_done.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: apply (ProcessEdgeTreeBranchExtendsPartialLowCandidate_proof
                  W u a done Hchild Hedge Hnot_done).
      intros s [Hunvis Heq_s]. subst s.
      destruct H as [Hloop _].
      split; [exact Hloop | exact Hunvis].
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hvisited_guard Heq0]. subst s1.
      assert (Hvis: Visited a s0).
      { unfold Visited. apply NNPP. exact Hvisited_guard. }
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: apply (GetDfnUpdateLowExtendsPartialLowStackCandidate_proof
                    u done a Hedge).
        intros s [Hactive_guard Heq_s]. subst s.
        destruct H as [[_ Hpartial] [Hactive_to_not_fa _]].
        split; [exact Hpartial |].
        split; [exact Hactive_guard |].
        exact (Hactive_to_not_fa Hvis Hactive_guard).
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s Hnot_active].
        subst s.
        destruct H as [[_ Hpartial] [_ Hnonstack_bound]].
        apply PartialRootLowEquationCandidate_step_keep_proof;
          try exact Hpartial; try exact Hedge.
        * intro Hfa. apply Hnonstack_bound; assumption.
        * intro Hactive. exfalso. apply Hnot_active. exact Hactive.
  Qed.

  (* ================================================================ *)
  (* Unknown-first semantic interface                                 *)
  (* ================================================================ *)

  Record LowProofInterface: Type := {
    (*
      Entry and final predicates.  These are not definitions yet; they are
      interfaces that the final design must implement.
     *)
    EntryPre : V -> St -> Prop;
    RootFinal : V -> St -> Prop;

    (*
      Root correctness before [maybe_pop].  If the final root predicate is
      stack-sensitive, this must be connected to [RootFinal] by a root-pop
      bridge rather than by whole-subtree preservation.
     *)
    RootLowPrePop : V -> St -> Prop;

    (*
      Edge-loop cut.  [LoopInv u done s] means the outgoing edges in [done]
      have been processed and the facts needed by the next edge, by loop-done,
      and by pop are available.
     *)
    LoopInv : V -> (V -> Prop) -> St -> Prop;

    (*
      Recursive child call interface.  It is derived from the unvisited-child
      branch of [process_edge], not copied from an existing low-link predicate.
     *)
    ChildEntry : V -> V -> (V -> Prop) -> St -> Prop;
    ChildPost : V -> V -> (V -> Prop) -> St -> Prop;

    (*
      Suspended outer parent frame.  This is the Hoare-logic counterpart of a
      continuation: an inner recursive call must preserve enough outer state
      for the parent loop to resume.
     *)
    Frame : Type;
    FrameInv : Frame -> St -> Prop;
  }.

  Definition LoopEntry (I: LowProofInterface) (u: V): St -> Prop :=
    LoopInv I u ∅.

  Definition LoopDone (I: LowProofInterface) (u: V): St -> Prop :=
    LoopInv I u (edge_set u).

  Definition PrePopRootReady (I: LowProofInterface) (u: V) (s: St): Prop :=
    LoopDone I u s /\ RootLowPrePop I u s.

  (* ================================================================ *)
  (* Contracts generated by the top-down cuts                         *)
  (* ================================================================ *)

  Definition ChildContract (I: LowProofInterface) (W: RecProgram): Prop :=
    forall parent child done,
      dg_step g parent child ->
      ~ done child ->
      Hoare
        (ChildEntry I parent child done)
        (W child)
        (fun _ s => ChildPost I parent child done s).

  Definition FrameContract (I: LowProofInterface) (W: RecProgram): Prop :=
    forall (F: Frame I) direct_parent child direct_done,
      dg_step g direct_parent child ->
      ~ direct_done child ->
      Hoare
        (fun s =>
           FrameInv I F s /\
           ChildEntry I direct_parent child direct_done s)
        (W child)
        (fun _ s => FrameInv I F s).

  (* ================================================================ *)
  (* Cut-transition theorem statements                                *)
  (* ================================================================ *)

  Definition PreloopEntry_statement (I: LowProofInterface): Prop :=
    forall u,
      Hoare
        (EntryPre I u)
        (preloop u)
        (fun _ s => LoopEntry I u s).

  Definition ProcessEdgeStep_statement (I: LowProofInterface): Prop :=
    forall (W: RecProgram) u a done,
      ChildContract I W ->
      FrameContract I W ->
      dg_step g u a ->
      ~ done a ->
      Hoare
        (LoopInv I u done)
        (process_edge u W a)
        (fun _ s => LoopInv I u (done_after done a) s).

  Definition EdgeLoopDone_statement (I: LowProofInterface): Prop :=
    forall (W: RecProgram) u,
      ChildContract I W ->
      FrameContract I W ->
      Hoare
        (LoopEntry I u)
        (edge_loop u W)
        (fun _ s => LoopDone I u s).

  Definition RootBridge_statement (I: LowProofInterface): Prop :=
    forall u s,
      LoopDone I u s ->
      RootLowPrePop I u s.

  Definition MaybePopFinal_statement (I: LowProofInterface): Prop :=
    forall u,
      Hoare
        (PrePopRootReady I u)
        (maybe_pop u)
        (fun _ s => RootFinal I u s).

  (* ================================================================ *)
  (* Recursive-body theorem statements                                *)
  (* ================================================================ *)

  Definition BodySatisfiesChildContract_statement
             (I: LowProofInterface): Prop :=
    forall W,
      ChildContract I W ->
      FrameContract I W ->
      ChildContract I (tarjan_scc_f g W).

  Definition BodyPreservesFrameContract_statement
             (I: LowProofInterface): Prop :=
    forall W,
      ChildContract I W ->
      FrameContract I W ->
      FrameContract I (tarjan_scc_f g W).

  Definition FixpointLowLayerCorrect_statement
             (I: LowProofInterface): Prop :=
    forall u,
      Hoare
        (EntryPre I u)
        (tarjan_scc g u)
        (fun _ s => RootFinal I u s).

  Record LowProofObligations (I: LowProofInterface): Prop := {
    obligation_preloop_entry :
      PreloopEntry_statement I;
    obligation_process_edge_step :
      ProcessEdgeStep_statement I;
    obligation_edge_loop_done :
      EdgeLoopDone_statement I;
    obligation_root_bridge :
      RootBridge_statement I;
    obligation_maybe_pop_final :
      MaybePopFinal_statement I;
    obligation_body_satisfies_child_contract :
      BodySatisfiesChildContract_statement I;
    obligation_body_preserves_frame_contract :
      BodyPreservesFrameContract_statement I;
  }.

  Definition LowLayerCorrect_from_obligations_statement
             (I: LowProofInterface): Prop :=
    LowProofObligations I ->
    FixpointLowLayerCorrect_statement I.

  (* ================================================================ *)
  (* Fixed-point mode skeleton                                        *)
  (* ================================================================ *)

  Inductive LowFixMode (I: LowProofInterface): Type :=
  | LowRootMode
  | LowChildMode (parent: V) (done: V -> Prop)
  | LowFrameMode (outer: Frame I)
                 (direct_parent: V)
                 (direct_done: V -> Prop).

  Definition FixPre
             (I: LowProofInterface)
             (x: V) (mode: LowFixMode I) (s: St): Prop :=
    match mode with
    | LowRootMode _ =>
        EntryPre I x s
    | LowChildMode _ parent done =>
        ChildEntry I parent x done s /\
        dg_step g parent x /\
        ~ done x
    | LowFrameMode _ outer direct_parent direct_done =>
        FrameInv I outer s /\
        ChildEntry I direct_parent x direct_done s /\
        dg_step g direct_parent x /\
        ~ direct_done x
    end.

  Definition FixPost
             (I: LowProofInterface)
             (x: V) (mode: LowFixMode I)
             (_: unit) (s: St): Prop :=
    match mode with
    | LowRootMode _ =>
        RootFinal I x s
    | LowChildMode _ parent done =>
        ChildPost I parent x done s
    | LowFrameMode _ outer _ _ =>
        FrameInv I outer s
    end.

End IS_LOW_SKELETON.
