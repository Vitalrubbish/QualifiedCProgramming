Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Compare_dec.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From MaxMinLib Require Import MaxMin Interface.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn
  Tarjan_scc_low_defs Tarjan_scc_low_pure Tarjan_scc_low_primitives.

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

  Definition ChildEntryProvidesEntryPreCandidate_statement: Prop :=
    forall parent child done s,
      ChildEntryCandidate parent child done s ->
      EntryPreCandidate child s.

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

  Definition ParentLowBelowChildCandidate
             (u child: V) (s: St): Prop :=
    low s u <= low s child.

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

  Definition PreloopFromChildEntryProducesLoopEntryBaseCandidate_statement:
    Prop :=
    forall parent child done,
      Hoare
        (ChildEntryCandidate parent child done)
        (preloop child)
        (fun _ s => LoopEntryBaseCandidate child s).

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

  Definition ChildReturnsVisitedCandidate_statement: Prop :=
    forall W,
      ChildReturnsVisitedCandidate W.

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

  Definition UpdateLowKeepsVisitedCandidate_statement: Prop :=
    forall u n snap,
      Hoare
        (fun s : St => s = snap)
        (update_low u n)
        (fun _ s => forall x, Visited x s <-> Visited x snap).

  Definition GetLowUpdateLowKeepsTraversalSnapshotCandidate_statement: Prop :=
    forall u child snap,
      Hoare
        (fun s : St => s = snap)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s =>
           (forall x, Visited x s <-> Visited x snap) /\
           (forall x, dfn s x = dfn snap x) /\
           (forall x, fa s x = fa snap x) /\
           (forall x, Active x s <-> Active x snap) /\
           (forall x, x <> u -> low s x = low snap x) /\
           low s u <= low snap u).

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

  Definition GetLowUpdateLowProducesParentLowBelowChildCandidate_statement:
    Prop :=
    forall u child,
      Hoare
        (fun _ : St => True)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s => ParentLowBelowChildCandidate u child s).

  Definition GetLowUpdateLowPreservesGlobalShapeCandidate_statement:
    Prop :=
    forall u child,
      Hoare
        (fun s => GlobalShapeCandidate s /\ Visited u s)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s => GlobalShapeCandidate s).

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

  (* ================================================================ *)
  (* Phase 6 candidates: child post and segment summary               *)
  (* ================================================================ *)

  Definition ChildLowValidForParentCandidate (child: V) (s: St): Prop :=
    scc_low_valid_v g root s child.

  Definition ChildIsLowForParentCandidate (child: V) (s: St): Prop :=
    scc_is_low_v g root s child.

  Definition ChildRootCorrectForParentCandidate (child: V) (s: St): Prop :=
    ChildLowValidForParentCandidate child s /\
    ChildIsLowForParentCandidate child s.

  Definition ChildInactiveSelfLowForParentCandidate
             (child: V) (s: St): Prop :=
    ~ Active child s -> low s child = dfn s child.

  (**
    Child's contribution to parent's closedness reasoning.

    Consumer: parent extends [done_reachable_closed] and
    [done_tree_reachable_closed] when adding a popped child to [done].

    If child was popped (not active), its entire reachable region is
    settled — every vertex reachable from child is visited.  This is the
    exact fact parent needs for the new [done ∪ [child]] case.

    If child remains active, no contribution is claimed here; parent
    relies on the active segment summary instead.
   *)
  Definition ChildClosednessContributionCandidate
             (child: V) (s: St): Prop :=
    ~ Active child s -> forall v, dg_reachable g child v -> Visited v s.

  Definition ProcessedReachableFromCandidate
             (u: V) (done: V -> Prop) (s: St) (x: V): Prop :=
    x = u \/
    exists v,
      done v /\
      Edge u v /\
      dg_reachable g v x.

  Definition ProcessedTreeReachableFromCandidate
             (u: V) (done: V -> Prop) (s: St) (x: V): Prop :=
    x = u \/
    exists v,
      done v /\
      Edge u v /\
      fa s v = u /\
      fa s v <> v /\
      dg_reachable (state_to_dfs_tree g s root) v x /\
      dg_reachable g v x.

  Definition PendingRootEscapeCandidate
             (u: V) (done: V -> Prop) (s: St)
             (x w: V): Prop :=
    exists a,
      dg_reachable g x u /\
      Edge u a /\
      ~ done a /\
      dg_reachable g a w.

  Definition OldStackEscapeAnchorCandidate
             (u: V) (s: St) (x w: V): Prop :=
    exists b,
      Active b s /\
      dfn s b < dfn s u /\
      low s u <= dfn s b /\
      dg_reachable g x b /\
      dg_reachable g b w.

  Definition SegmentEscapeAccountingCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall x w,
      Active x s ->
      dfn s u <= dfn s x ->
      dg_reachable g x w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate u done s x w \/
      OldStackEscapeAnchorCandidate u s x w.

  Definition PendingChildSegmentCandidate
             (child: V) (s: St) (x: V): Prop :=
    Visited child s /\
    Active child s /\
    dg_reachable (state_to_dfs_tree g s root) child x.

  Definition SuspendedSegmentEscapeAccountingCandidate
             (u child: V) (done: V -> Prop) (s: St): Prop :=
    forall x w,
      Active x s ->
      dfn s u <= dfn s x ->
      ~ PendingChildSegmentCandidate child s x ->
      dg_reachable g x w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate u done s x w \/
      OldStackEscapeAnchorCandidate u s x w.

  Definition ParentPendingChildEscapeAccountedCandidate
             (u: V) (done: V -> Prop) (child: V) (s: St): Prop :=
    forall x w,
      Active x s ->
      dfn s u <= dfn s x ->
      dg_reachable g x u ->
      dg_reachable g child w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate u (done_after done child) s x w \/
      OldStackEscapeAnchorCandidate u s x w.

  Definition PendingChildSegmentEscapeAccountedCandidate
             (u: V) (done: V -> Prop) (child: V) (s: St): Prop :=
    forall x w,
      PendingChildSegmentCandidate child s x ->
      Active x s ->
      dfn s u <= dfn s x ->
      dg_reachable g x w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate u (done_after done child) s x w \/
      OldStackEscapeAnchorCandidate u s x w.

  Definition PendingChildSegmentOrderCandidate
             (child: V) (s: St): Prop :=
    forall x,
      PendingChildSegmentCandidate child s x ->
      Active x s ->
      dfn s child <= dfn s x.

  Definition PendingChildSegmentOldAnchorLiftsToParentCandidate
             (u: V) (done: V -> Prop) (child: V) (s: St): Prop :=
    forall x b w,
      PendingChildSegmentCandidate child s x ->
      Active x s ->
      Active b s ->
      dfn s b < dfn s child ->
      low s child <= dfn s b ->
      dg_reachable g x b ->
      dg_reachable g b w ->
      ~ Visited w s ->
      dfn s u <= dfn s x ->
      PendingRootEscapeCandidate u (done_after done child) s x w \/
      OldStackEscapeAnchorCandidate u s x w.

  Definition PendingChildSegmentOldAnchorsBelowParentCandidate
             (u child: V) (s: St): Prop :=
    forall x b,
      PendingChildSegmentCandidate child s x ->
      Active x s ->
      Active b s ->
      dfn s b < dfn s child ->
      low s child <= dfn s b ->
      dg_reachable g x b ->
      dfn s b < dfn s u.

  Definition PendingChildSegmentNonOlderAnchorAccountedByParentCandidate
             (u: V) (done: V -> Prop) (child: V) (s: St): Prop :=
    forall x b w,
      PendingChildSegmentCandidate child s x ->
      Active x s ->
      Active b s ->
      dfn s b < dfn s child ->
      low s child <= dfn s b ->
      dg_reachable g x b ->
      dg_reachable g b w ->
      ~ Visited w s ->
      dfn s u <= dfn s x ->
      dfn s u <= dfn s b ->
      PendingRootEscapeCandidate u (done_after done child) s x w \/
      OldStackEscapeAnchorCandidate u s x w.

  Definition ChildSelfPendingEscapeAccountedCandidate
             (u: V) (done: V -> Prop) (child: V) (s: St): Prop :=
    forall w,
      dg_reachable g child u ->
      dg_reachable g child w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate u (done_after done child) s child w \/
      OldStackEscapeAnchorCandidate u s child w.

  Definition ChildOldAnchorLiftsToParentCandidate
             (u: V) (done: V -> Prop) (child: V) (s: St): Prop :=
    forall b w,
      Active b s ->
      dfn s b < dfn s child ->
      low s child <= dfn s b ->
      dg_reachable g child b ->
      dg_reachable g b w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate u (done_after done child) s child w \/
      OldStackEscapeAnchorCandidate u s child w.

  Definition SegmentCoverageByDoneCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall x,
      Active x s ->
      dfn s u <= dfn s x ->
      ProcessedReachableFromCandidate u done s x.

  Definition SegmentTreeCoverageByDoneCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall x,
      Active x s ->
      dfn s u <= dfn s x ->
      ProcessedTreeReachableFromCandidate u done s x.

  Definition SuspendedSegmentTreeCoverageByDoneCandidate
             (u child: V) (done: V -> Prop) (s: St): Prop :=
    forall x,
      Active x s ->
      dfn s u <= dfn s x ->
      ~ PendingChildSegmentCandidate child s x ->
      ProcessedTreeReachableFromCandidate u done s x.

  Definition ActiveTargetSegmentEscapeAccountedCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall a w,
      Active a s ->
      dfn s u <= dfn s a ->
      ProcessedTreeReachableFromCandidate u done s a ->
      dg_reachable g a w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate u (done_after done a) s a w \/
      OldStackEscapeAnchorCandidate u s a w.

  Definition ActiveTargetBlockEscapeAccountedCandidate
             (u: V) (done block: V -> Prop) (s: St): Prop :=
    forall a w,
      block a ->
      (forall b,
          block b ->
          Edge u b /\
          ~ done b /\
          Active b s /\
          dfn s u <= dfn s b) ->
      dg_reachable g a w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate u (done ∪ block) s a w \/
      OldStackEscapeAnchorCandidate u s a w.

  Definition ActiveTargetBlocksEscapeAccountedCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall block,
      ActiveTargetBlockEscapeAccountedCandidate u done block s.

  Definition ActiveEdgeTargetSegmentEscapeAccountedCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall a w,
      Edge u a ->
      ~ done a ->
      Active a s ->
      dfn s u <= dfn s a ->
      dg_reachable g a w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate u (done_after done a) s a w \/
      OldStackEscapeAnchorCandidate u s a w.

  Definition RootSegmentInitialCandidate (u: V) (s: St): Prop :=
    forall x,
      Active x s ->
      dfn s u <= dfn s x ->
      x = u.

  Definition PreloopProducesRootSegmentInitialCandidate_statement: Prop :=
    forall u,
      Hoare
        (EntryPreCandidate u)
        (preloop u)
        (fun _ s => RootSegmentInitialCandidate u s).

  Definition PreloopFromChildEntryProducesRootSegmentInitialCandidate_statement:
    Prop :=
    forall parent child done,
      Hoare
        (ChildEntryCandidate parent child done)
        (preloop child)
        (fun _ s => RootSegmentInitialCandidate child s).

  Definition ChildSegmentSummaryCandidate (child: V) (s: St): Prop :=
    SegmentEscapeAccountingCandidate child (edge_set child) s /\
    SegmentCoverageByDoneCandidate child (edge_set child) s.

  Definition ChildSelfSegmentEscapeSummaryCandidate
             (child: V) (s: St): Prop :=
    forall w,
      dg_reachable g child w ->
      ~ Visited w s ->
      PendingRootEscapeCandidate child (edge_set child) s child w \/
      OldStackEscapeAnchorCandidate child s child w.

  Definition ActiveProcessedChildSegmentSummaryCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall child,
      done child ->
      Edge u child ->
      fa s child = u ->
      fa s child <> child ->
      Active child s ->
      ChildSelfSegmentEscapeSummaryCandidate child s.

  Definition ParentResumeShapeCandidate
             (parent child: V) (done: V -> Prop) (s: St): Prop :=
    Edge parent child /\
    ~ done child /\
    fa s child = parent /\
    fa s child <> child.

  Definition ParentFrameResumeCandidate
             (parent: V) (done: V -> Prop) (s: St): Prop :=
    done_visited done s /\
    fa_child_of_u g parent s /\
    fa_not_done_implies_eq_u parent done s.

  Definition SuspendedParentFrameResumeCandidate
             (parent child: V) (done: V -> Prop) (s: St): Prop :=
    done_visited done s /\
    fa_child_of_u g parent s /\
    forall v,
      ~ done v ->
      v <> child ->
      fa s v = parent ->
      v = parent.

  Definition DoneClosednessCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    done_reachable_closed g done s /\
    done_tree_reachable_closed g u done s.

  (**
    Consumer: parent extends [children_low_valid] when adding a tree child
    to [done].  This is distinct from the is-low summary consumed by the
    root is-low bridge.
   *)
  Definition ChildLowValidForParentCandidate_statement: Prop :=
    forall (W: RecProgram) parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s => ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s => ChildLowValidForParentCandidate child s).

  (**
    Consumer: parent extends [children_is_low] when adding a tree child to
    [done].  The later root is-low bridge consumes this field at loop done.
   *)
  Definition ChildIsLowForParentCandidate_statement: Prop :=
    forall (W: RecProgram) parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s => ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s => ChildIsLowForParentCandidate child s).

  Definition ChildRootCorrectForParentCandidate_statement: Prop :=
    ChildLowValidForParentCandidate_statement /\
    ChildIsLowForParentCandidate_statement.

  Definition ChildInactiveSelfLowForParentCandidate_statement: Prop :=
    forall (W: RecProgram) parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s => ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s => ChildInactiveSelfLowForParentCandidate child s).

  (**
    Consumer: parent extends [done_reachable_closed] and
    [done_tree_reachable_closed] when adding a popped child to [done].
    A popped child's reachable region is entirely visited (settled).
   *)
  Definition ChildClosednessContributionCandidate_statement: Prop :=
    forall (W: RecProgram) parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s => ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s => ChildClosednessContributionCandidate child s).

  (**
    Consumer: parent's active-descendant branch needs to know that any
    escape from within an active child's stack segment is already
    accounted for by that child's segment summary.

    The summary covers stack vertices whose dfn is at least the child's
    dfn; in a well-formed DFS stack this is exactly the child's segment.
   *)
  Definition ChildSegmentSummaryCandidate_statement: Prop :=
    forall (W: RecProgram) parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s => ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s =>
           Active child s -> ChildSegmentSummaryCandidate child s).

  (**
    Consumer: parent keeps the direct pending child facts needed to turn the
    recursive child result into the new processed-tree-child case.  The wider
    parent frame is audited separately; it is not bundled into child post.
   *)
  Definition ParentResumeShapeCandidate_statement: Prop :=
    forall (W: RecProgram) parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s => ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s => ParentResumeShapeCandidate parent child done s).

  (**
    Combined child-post obligation.

    Conjunction of the four independently-stated sub-obligations above.
    Phase 9 proves all of them together with Phase 5's
    [ChildProvidesLowContributionCandidate] for [tarjan_scc_f].
   *)
  Definition ProcessEdgeUnvisitedChildPostCandidate_statement: Prop :=
    ChildReturnsVisitedCandidate_statement /\
    ChildRootCorrectForParentCandidate_statement /\
    ChildInactiveSelfLowForParentCandidate_statement /\
    ChildClosednessContributionCandidate_statement /\
    ChildSegmentSummaryCandidate_statement /\
    ParentResumeShapeCandidate_statement /\
    (forall (W: RecProgram) parent child done,
        Edge parent child ->
        ~ done child ->
        Hoare
          (fun s => ChildEntryCandidate parent child done s)
          (W child)
          (fun _ s =>
             ParentPendingChildEscapeAccountedCandidate
               parent done child s)) /\
    (forall (W: RecProgram) parent child done,
        Edge parent child ->
        ~ done child ->
        Hoare
          (fun s => ChildEntryCandidate parent child done s)
          (W child)
          (fun _ s =>
             ActiveTargetBlocksEscapeAccountedCandidate
               parent (done_after done child) s)).

  Definition ChildPostCandidate
             (parent child: V) (done: V -> Prop) (s: St): Prop :=
    Visited child s /\
    ChildLowValidForParentCandidate child s /\
    ChildIsLowForParentCandidate child s /\
    ChildInactiveSelfLowForParentCandidate child s /\
    ChildClosednessContributionCandidate child s /\
    (Active child s -> ChildSegmentSummaryCandidate child s) /\
    ParentResumeShapeCandidate parent child done s /\
    ParentPendingChildEscapeAccountedCandidate parent done child s /\
    ActiveTargetBlocksEscapeAccountedCandidate
      parent (done_after done child) s.

  Definition ChildContractCandidate (W: RecProgram): Prop :=
    forall parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s => ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s => ChildPostCandidate parent child done s).

  Definition ChildContractCandidate_from_field_statements_statement:
    Prop :=
    ProcessEdgeUnvisitedChildPostCandidate_statement ->
    forall W,
      ChildContractCandidate W.

  Definition ChildContractCandidate_provides_returns_visited_statement:
    Prop :=
    forall W,
      ChildContractCandidate W ->
      ChildReturnsVisitedCandidate W.

  Definition ChildContractCandidate_provides_post_fields_statement: Prop :=
    forall W,
      ChildContractCandidate W ->
      ChildReturnsVisitedCandidate W /\
      (forall parent child done,
          Edge parent child ->
          ~ done child ->
          Hoare
            (ChildEntryCandidate parent child done)
            (W child)
            (fun _ s => ChildRootCorrectForParentCandidate child s)) /\
      (forall parent child done,
          Edge parent child ->
          ~ done child ->
          Hoare
            (ChildEntryCandidate parent child done)
            (W child)
            (fun _ s => ChildInactiveSelfLowForParentCandidate child s)) /\
      (forall parent child done,
          Edge parent child ->
          ~ done child ->
          Hoare
            (ChildEntryCandidate parent child done)
            (W child)
            (fun _ s => ChildClosednessContributionCandidate child s)) /\
      (forall parent child done,
          Edge parent child ->
          ~ done child ->
          Hoare
            (ChildEntryCandidate parent child done)
            (W child)
            (fun _ s =>
               Active child s -> ChildSegmentSummaryCandidate child s)) /\
      (forall parent child done,
          Edge parent child ->
          ~ done child ->
          Hoare
            (ChildEntryCandidate parent child done)
            (W child)
            (fun _ s => ParentResumeShapeCandidate parent child done s)).

  (* ---------------------------------------------------------------- *)
  (* Phase 6 loop-invariant extension                                  *)
  (* ---------------------------------------------------------------- *)

  (**
    Accumulated root correctness of processed direct tree children.

    Consumer: [RootBridge_statement] needs [RootTreeChildrenCorrect u s]
    at loop-done.  This field accumulates child-by-child in the edge
    loop so that when [done = edge_set u] it provides exactly that fact.

    The direct-tree-child test [fa s child = u /\ fa s child <> child]
    is available from [fa_child_of_u] and [fa_not_done_implies_eq_u]
    in [ParentResumeShapeCandidate] / existing parent invariants.
   *)
  Definition ProcessedTreeChildrenLowValidCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall child,
      done child ->
      dg_step g u child ->
      fa s child = u ->
      fa s child <> child ->
      ChildLowValidForParentCandidate child s.

  Definition ProcessedTreeChildrenIsLowCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall child,
      done child ->
      dg_step g u child ->
      fa s child = u ->
      fa s child <> child ->
      ChildIsLowForParentCandidate child s.

  Definition ProcessedTreeChildrenInactiveSelfLowCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    forall child,
      done child ->
      dg_step g u child ->
      fa s child = u ->
      fa s child <> child ->
      ChildInactiveSelfLowForParentCandidate child s.

  Definition ProcessedTreeChildrenCorrectCandidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    ProcessedTreeChildrenLowValidCandidate u done s /\
    ProcessedTreeChildrenIsLowCandidate u done s /\
    ProcessedTreeChildrenInactiveSelfLowCandidate u done s.

  (**
    Loop invariant with Phase 6 fields.

    Extends [LoopInvLowCandidate] (Phase 4 done discipline + Phase 5
    partial low equation) with exactly the child-post fields consumed by the
    root bridge and active-descendant branch.  Parent frame preservation is
    audited separately in the frame phase.
   *)
  Definition LoopInvPhase6Candidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    LoopInvLowCandidate u done s /\
    ParentFrameResumeCandidate u done s /\
    DoneClosednessCandidate u done s /\
    ProcessedTreeChildrenCorrectCandidate u done s /\
    ActiveProcessedChildSegmentSummaryCandidate u done s.

  Definition SuspendedLoopInvPhase6Candidate
             (u child: V) (done: V -> Prop) (s: St): Prop :=
    LoopInvLowCandidate u done s /\
    SuspendedParentFrameResumeCandidate u child done s /\
    DoneClosednessCandidate u done s /\
    ProcessedTreeChildrenCorrectCandidate u done s /\
    ActiveProcessedChildSegmentSummaryCandidate u done s.

  Definition DoneClosednessCandidate_empty_statement: Prop :=
    forall u s,
      DoneClosednessCandidate u ∅ s.

  Definition DoneClosednessCandidate_step_child_statement: Prop :=
    forall u done child s,
      DoneClosednessCandidate u done s ->
      ParentResumeShapeCandidate u child done s ->
      ChildClosednessContributionCandidate child s ->
      DoneClosednessCandidate u (done_after done child) s.

  Definition ProcessedTreeChildrenCorrectCandidate_empty_statement: Prop :=
    forall u s,
      ProcessedTreeChildrenCorrectCandidate u ∅ s.

  Definition ProcessedTreeChildrenCorrectCandidate_step_child_statement: Prop :=
    forall u done child s,
      ProcessedTreeChildrenCorrectCandidate u done s ->
      ParentResumeShapeCandidate u child done s ->
      ChildRootCorrectForParentCandidate child s ->
      ChildInactiveSelfLowForParentCandidate child s ->
      ProcessedTreeChildrenCorrectCandidate u (done_after done child) s.

  Definition ChildRootCorrectTransportCandidate
             (child: V) (snap s: St): Prop :=
    ChildRootCorrectForParentCandidate child snap ->
    ChildRootCorrectForParentCandidate child s.

  Definition ChildLowerStackAnchorsPreservedCandidate
             (child: V) (snap s: St): Prop :=
    forall b,
      Active b snap ->
      dfn snap b < dfn snap child ->
      Active b s.

  Definition ChildRootCorrectTransportFromStackShrinkCandidate_statement:
    Prop :=
    forall child snap s,
      (forall x, Visited x s <-> Visited x snap) ->
      (forall x, dfn s x = dfn snap x) ->
      (forall x, low s x = low snap x) ->
      (forall x, fa s x = fa snap x) ->
      (forall x, Active x s -> Active x snap) ->
      ChildLowerStackAnchorsPreservedCandidate child snap s ->
      ChildRootCorrectTransportCandidate child snap s.

  Definition ChildRootCorrectTransportFromInactiveSelfLowCandidate_statement:
    Prop :=
    forall child snap s,
      (forall x, Visited x s <-> Visited x snap) ->
      (forall x, dfn s x = dfn snap x) ->
      (forall x, low s x = low snap x) ->
      (forall x, fa s x = fa snap x) ->
      (forall x, Active x s -> Active x snap) ->
      ChildInactiveSelfLowForParentCandidate child snap ->
      ~ Active child snap ->
      ChildRootCorrectTransportCandidate child snap s.

  Definition ProcessedTreeChildrenCorrectCandidate_transport_statement:
    Prop :=
    forall u done snap s,
      (forall x, dfn s x = dfn snap x) ->
      (forall x, low s x = low snap x) ->
      ProcessedTreeChildrenCorrectCandidate u done snap ->
      (forall child,
          done child ->
          Edge u child ->
          fa s child = u ->
          fa s child <> child ->
          fa snap child = u /\
          fa snap child <> child /\
          (Active child snap -> Active child s) /\
          ChildRootCorrectTransportCandidate child snap s) ->
      ProcessedTreeChildrenCorrectCandidate u done s.

  Definition ActiveProcessedChildSegmentSummaryCandidate_empty_statement: Prop :=
    forall u s,
      ActiveProcessedChildSegmentSummaryCandidate u ∅ s.

  Definition ActiveProcessedChildSegmentSummaryCandidate_step_child_statement: Prop :=
    forall u done child s,
      ActiveProcessedChildSegmentSummaryCandidate u done s ->
      ParentResumeShapeCandidate u child done s ->
      (Active child s -> ChildSegmentSummaryCandidate child s) ->
      ActiveProcessedChildSegmentSummaryCandidate u (done_after done child) s.

  Definition PreloopPreservesChildSelfSegmentEscapeSummaryCandidate_statement:
    Prop :=
    forall child a,
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           Unvisited a s /\
           Active child s /\
           ChildSelfSegmentEscapeSummaryCandidate child s)
        (preloop a)
        (fun _ s => ChildSelfSegmentEscapeSummaryCandidate child s).

  Definition PreloopPreservesActiveProcessedChildSegmentSummaryCandidate_statement:
    Prop :=
    forall u done a,
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           DoneVisitedCandidate done s /\
           Unvisited a s /\
           ActiveProcessedChildSegmentSummaryCandidate u done s)
        (preloop a)
        (fun _ s => ActiveProcessedChildSegmentSummaryCandidate u done s).

  Definition LoopEntryImpliesPhase6Candidate_statement: Prop :=
    forall u s,
      LoopInvLowCandidate u ∅ s ->
      ParentFrameResumeCandidate u ∅ s ->
      DoneClosednessCandidate u ∅ s ->
      ProcessedTreeChildrenCorrectCandidate u ∅ s ->
      ActiveProcessedChildSegmentSummaryCandidate u ∅ s ->
      LoopInvPhase6Candidate u ∅ s.

  Definition Phase6ChildPostExtendsLoopFieldsCandidate_statement: Prop :=
    forall u done child s,
      DoneClosednessCandidate u done s ->
      ProcessedTreeChildrenCorrectCandidate u done s ->
      ActiveProcessedChildSegmentSummaryCandidate u done s ->
      ParentResumeShapeCandidate u child done s ->
      ChildRootCorrectForParentCandidate child s ->
      ChildInactiveSelfLowForParentCandidate child s ->
      ChildClosednessContributionCandidate child s ->
      (Active child s -> ChildSegmentSummaryCandidate child s) ->
      DoneClosednessCandidate u (done_after done child) s /\
      ProcessedTreeChildrenCorrectCandidate u (done_after done child) s /\
      ActiveProcessedChildSegmentSummaryCandidate u (done_after done child) s.

  (* ================================================================ *)
  (* Phase 7 candidates: root bridge before pop                       *)
  (* ================================================================ *)

  Definition LoopDonePhase6Candidate (u: V) (s: St): Prop :=
    LoopInvPhase6Candidate u (edge_set u) s.

  Definition RootLowEquationReadyCandidate (u: V) (s: St): Prop :=
    PartialRootLowEquationCandidate u (edge_set u) s.

  Definition RootTreeChildrenLowValidReadyCandidate
             (u: V) (s: St): Prop :=
    ProcessedTreeChildrenLowValidCandidate u (edge_set u) s.

  Definition RootTreeChildrenIsLowReadyCandidate
             (u: V) (s: St): Prop :=
    ProcessedTreeChildrenIsLowCandidate u (edge_set u) s.

  Definition RootLowValidPrePopCandidate (u: V) (s: St): Prop :=
    scc_low_valid_v g root s u.

  Definition RootIsLowPrePopCandidate (u: V) (s: St): Prop :=
    scc_is_low_v g root s u.

  Definition RootLowPrePopCandidate (u: V) (s: St): Prop :=
    RootLowValidPrePopCandidate u s /\
    RootIsLowPrePopCandidate u s.

  (**
    Consumer-facing root bridge input.  This is intentionally not the final
    root correctness statement; it is the exact pre-pop material that later
    root bridge lemmas will consume.
   *)
  Definition RootBridgeInputCandidate (u: V) (s: St): Prop :=
    LocalActiveRootCandidate u s /\
    DoneClosednessCandidate u (edge_set u) s /\
    ParentFrameResumeCandidate u (edge_set u) s /\
    RootLowEquationReadyCandidate u s /\
    RootTreeChildrenLowValidReadyCandidate u s /\
    RootTreeChildrenIsLowReadyCandidate u s /\
    OrderFactsCandidate s.

  Definition RootBridgeLowValidInputCandidate (u: V) (s: St): Prop :=
    LocalActiveRootCandidate u s /\
    DoneClosednessCandidate u (edge_set u) s /\
    ParentFrameResumeCandidate u (edge_set u) s /\
    RootLowEquationReadyCandidate u s /\
    RootTreeChildrenLowValidReadyCandidate u s /\
    OrderFactsCandidate s.

  Definition RootBridgeIsLowInputCandidate (u: V) (s: St): Prop :=
    RootBridgeLowValidInputCandidate u s /\
    RootTreeChildrenIsLowReadyCandidate u s.

  Definition LoopDoneProvidesRootBridgeInputCandidate_statement: Prop :=
    forall u s,
      LoopDonePhase6Candidate u s ->
      RootBridgeInputCandidate u s.

  Definition RootBridgeInputProvidesLowValidInputCandidate_statement: Prop :=
    forall u s,
      RootBridgeInputCandidate u s ->
      RootBridgeLowValidInputCandidate u s.

  Definition RootBridgeInputProvidesIsLowInputCandidate_statement: Prop :=
    forall u s,
      RootBridgeInputCandidate u s ->
      RootBridgeIsLowInputCandidate u s.

  Definition RootBridgeLowValidInputBuildsLowIterationDoneCandidate_statement:
    Prop :=
    forall u s,
      RootBridgeLowValidInputCandidate u s ->
      low_iteration_done g root u s.

  Definition RootBridgeLowValidCandidate_statement: Prop :=
    forall u s,
      RootBridgeLowValidInputCandidate u s ->
      RootLowValidPrePopCandidate u s.

  Definition RootBridgeIsLowCandidate_statement: Prop :=
    forall u s,
      RootBridgeIsLowInputCandidate u s ->
      RootIsLowPrePopCandidate u s.

  Definition RootBridgePrePopCandidate_statement: Prop :=
    forall u s,
      RootBridgeInputCandidate u s ->
      RootLowPrePopCandidate u s.

  (* ---------------------------------------------------------------- *)
  (* Phase 7 root-segment loop extension                               *)
  (* ---------------------------------------------------------------- *)

  Definition LoopInvPhase7Candidate
             (u: V) (done: V -> Prop) (s: St): Prop :=
    LoopInvPhase6Candidate u done s /\
    SegmentEscapeAccountingCandidate u done s /\
    SegmentTreeCoverageByDoneCandidate u done s /\
    ActiveTargetBlocksEscapeAccountedCandidate u done s.

  Definition SuspendedLoopInvPhase7Candidate
             (u child: V) (done: V -> Prop) (s: St): Prop :=
    SuspendedLoopInvPhase6Candidate u child done s /\
    SuspendedSegmentEscapeAccountingCandidate u child done s /\
    SuspendedSegmentTreeCoverageByDoneCandidate u child done s.

  Definition LoopDonePhase7Candidate (u: V) (s: St): Prop :=
    LoopInvPhase7Candidate u (edge_set u) s.

  Definition SegmentEscapeAccountingCandidate_empty_statement: Prop :=
    forall u s,
      LocalActiveRootCandidate u s ->
      RootSegmentInitialCandidate u s ->
      SegmentEscapeAccountingCandidate u ∅ s.

  Definition SegmentTreeCoverageByDoneCandidate_empty_statement: Prop :=
    forall u s,
      RootSegmentInitialCandidate u s ->
      SegmentTreeCoverageByDoneCandidate u ∅ s.

  Definition ActiveTargetSegmentEscapeAccountedCandidate_empty_statement:
    Prop :=
    forall u s,
      LocalActiveRootCandidate u s ->
      RootSegmentInitialCandidate u s ->
      ActiveTargetSegmentEscapeAccountedCandidate u ∅ s.

  Definition PreloopProducesParentFrameResumeEmptyCandidate_statement:
    Prop :=
    forall u,
      Hoare
        (EntryPreCandidate u)
        (preloop u)
        (fun _ s => ParentFrameResumeCandidate u ∅ s).

  Definition PreloopProducesLoopInvPhase7InitialCandidate_statement:
    Prop :=
    forall u,
      Hoare
        (EntryPreCandidate u)
        (preloop u)
        (fun _ s => LoopInvPhase7Candidate u ∅ s).

  Definition PreloopFromChildEntryProducesLoopInvPhase7InitialCandidate_statement:
    Prop :=
    forall parent child done,
      Hoare
        (ChildEntryCandidate parent child done)
        (preloop child)
        (fun _ s => LoopInvPhase7Candidate child ∅ s).

  Definition SegmentEscapeAccountingCandidate_step_child_statement: Prop :=
    forall u done child s,
      SegmentEscapeAccountingCandidate u done s ->
      ParentPendingChildEscapeAccountedCandidate u done child s ->
      SegmentEscapeAccountingCandidate u (done_after done child) s.

  Definition SegmentEscapeAccountingSuspendsCandidate_statement: Prop :=
    forall u done child s,
      SegmentEscapeAccountingCandidate u done s ->
      SuspendedSegmentEscapeAccountingCandidate u child done s.

  Definition SegmentTreeCoverageSuspendsCandidate_statement: Prop :=
    forall u done child s,
      SegmentTreeCoverageByDoneCandidate u done s ->
      SuspendedSegmentTreeCoverageByDoneCandidate u child done s.

  Definition SegmentTreeCoverageClosesAfterChildCandidate_statement: Prop :=
    forall u done child s,
      GlobalShapeCandidate s ->
      Edge u child ->
      fa s child = u ->
      fa s child <> child ->
      (Active child s -> ChildSegmentSummaryCandidate child s) ->
      SuspendedSegmentTreeCoverageByDoneCandidate u child done s ->
      SegmentTreeCoverageByDoneCandidate u (done_after done child) s.

  Definition ProcessEdgeVisitedActiveExtendsSegmentEscapeAccountingWithTargetCandidate_statement:
    Prop :=
    forall W u a done,
      Hoare
        (fun s =>
           SegmentEscapeAccountingCandidate u done s /\
           SegmentTreeCoverageByDoneCandidate u done s /\
           ActiveTargetSegmentEscapeAccountedCandidate u done s /\
           Edge u a /\
           Visited a s /\
           Active a s)
        (process_edge u W a)
        (fun _ s =>
           SegmentEscapeAccountingCandidate u (done_after done a) s).

  Definition SuspendedSegmentEscapeAccountingClosesAfterChildCandidate_statement:
    Prop :=
    forall u done child s,
      SuspendedSegmentEscapeAccountingCandidate u child done s ->
      ParentPendingChildEscapeAccountedCandidate u done child s ->
      PendingChildSegmentEscapeAccountedCandidate u done child s ->
      SegmentEscapeAccountingCandidate u (done_after done child) s.

  Definition ChildSegmentEscapeLiftsToParentCandidate_statement: Prop :=
    forall u done child s,
      ParentPendingChildEscapeAccountedCandidate u done child s ->
      SegmentEscapeAccountingCandidate u done s ->
      SegmentEscapeAccountingCandidate u (done_after done child) s.

  Definition ParentPendingChildEscapeAccountedCandidate_from_closed_statement:
    Prop :=
    forall u done child s,
      ChildClosednessContributionCandidate child s ->
      ~ Active child s ->
      ParentPendingChildEscapeAccountedCandidate u done child s.

  Definition ParentPendingChildEscapeAccountedCandidate_from_old_anchor_statement:
    Prop :=
    forall u done child s,
      Edge u child ->
      Active child s ->
      dfn s child < dfn s u ->
      low s u <= dfn s child ->
      ParentPendingChildEscapeAccountedCandidate u done child s.

  Definition ParentPendingChildEscapeAccountedCandidate_from_active_descendant_statement:
    Prop :=
    forall u done child s,
      Edge u child ->
      SegmentEscapeAccountingCandidate u done s ->
      Active child s ->
      dfn s u <= dfn s child ->
      ChildSelfPendingEscapeAccountedCandidate u done child s ->
      ParentPendingChildEscapeAccountedCandidate u done child s.

  Definition ChildSelfPendingEscapeAccountedCandidate_from_child_summary_statement:
    Prop :=
    forall u done child s,
      Active child s ->
      ChildSegmentSummaryCandidate child s ->
      ChildOldAnchorLiftsToParentCandidate u done child s ->
      ChildSelfPendingEscapeAccountedCandidate u done child s.

  Definition ChildSelfSegmentEscapeSummaryCandidate_from_child_summary_statement:
    Prop :=
    forall child s,
      Active child s ->
      ChildSegmentSummaryCandidate child s ->
      ChildSelfSegmentEscapeSummaryCandidate child s.

  Definition ChildSelfPendingEscapeAccountedCandidate_from_self_summary_statement:
    Prop :=
    forall u done child s,
      ChildSelfSegmentEscapeSummaryCandidate child s ->
      ChildOldAnchorLiftsToParentCandidate u done child s ->
      ChildSelfPendingEscapeAccountedCandidate u done child s.

  Definition PendingChildSegmentEscapeAccountedCandidate_from_child_summary_statement:
    Prop :=
    forall u done child s,
      ChildSegmentSummaryCandidate child s ->
      PendingChildSegmentOrderCandidate child s ->
      PendingChildSegmentOldAnchorLiftsToParentCandidate u done child s ->
      PendingChildSegmentEscapeAccountedCandidate u done child s.

  Definition PendingChildSegmentOrderCandidate_from_global_shape_statement:
    Prop :=
    forall child s,
      GlobalShapeCandidate s ->
      PendingChildSegmentOrderCandidate child s.

  Definition PendingChildSegmentOldAnchorLiftsToParentCandidate_from_all_older_segment_statement:
    Prop :=
    forall u done child s,
      low s u <= low s child ->
      PendingChildSegmentOldAnchorsBelowParentCandidate u child s ->
      PendingChildSegmentOldAnchorLiftsToParentCandidate u done child s.

  Definition PendingChildSegmentOldAnchorLiftsToParentCandidate_from_anchor_split_statement:
    Prop :=
    forall u done child s,
      ParentLowBelowChildCandidate u child s ->
      PendingChildSegmentNonOlderAnchorAccountedByParentCandidate
        u done child s ->
      PendingChildSegmentOldAnchorLiftsToParentCandidate u done child s.

  Definition PendingChildSegmentNonOlderAnchorAccountedBySuspendedParent_statement:
    Prop :=
    forall u done child s,
      PendingChildSegmentOrderCandidate child s ->
      SuspendedSegmentEscapeAccountingCandidate u child done s ->
      ParentPendingChildEscapeAccountedCandidate u done child s ->
      PendingChildSegmentNonOlderAnchorAccountedByParentCandidate
        u done child s.

  Definition PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_segment_producers_statement:
    Prop :=
    forall u done child s,
      GlobalShapeCandidate s ->
      ChildSegmentSummaryCandidate child s ->
      low s u <= low s child ->
      PendingChildSegmentOldAnchorsBelowParentCandidate u child s ->
      PendingChildSegmentEscapeAccountedCandidate u done child s.

  Definition PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_anchor_split_statement:
    Prop :=
    forall u done child s,
      GlobalShapeCandidate s ->
      ChildSegmentSummaryCandidate child s ->
      ParentLowBelowChildCandidate u child s ->
      PendingChildSegmentNonOlderAnchorAccountedByParentCandidate
        u done child s ->
      PendingChildSegmentEscapeAccountedCandidate u done child s.

  Definition PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_suspended_parent_statement:
    Prop :=
    forall u done child s,
      GlobalShapeCandidate s ->
      ChildSegmentSummaryCandidate child s ->
      ParentLowBelowChildCandidate u child s ->
      SuspendedSegmentEscapeAccountingCandidate u child done s ->
      ParentPendingChildEscapeAccountedCandidate u done child s ->
      PendingChildSegmentEscapeAccountedCandidate u done child s.

  Definition GetLowUpdateLowPreservesChildSegmentSummaryCandidate_statement:
    Prop :=
    forall u child,
      child <> u ->
      Hoare
        (ChildSegmentSummaryCandidate child)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s => ChildSegmentSummaryCandidate child s).

  Definition GetLowUpdateLowPreservesChildSegmentSummaryFromParentResumeCandidate_statement:
    Prop :=
    forall u done child,
      Hoare
        (fun s =>
           ParentResumeShapeCandidate u child done s /\
           ChildSegmentSummaryCandidate child s)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s => ChildSegmentSummaryCandidate child s).

  Definition GetLowUpdateLowProducesNonOlderAnchorAccountedByParentCandidate_statement:
    Prop :=
    forall u done child,
      child <> u ->
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           SuspendedSegmentEscapeAccountingCandidate u child done s /\
           ParentPendingChildEscapeAccountedCandidate u done child s)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s =>
           PendingChildSegmentNonOlderAnchorAccountedByParentCandidate
             u done child s).

  Definition GetLowUpdateLowProducesNonOlderAnchorAccountedByParentFromParentResumeCandidate_statement:
    Prop :=
    forall u done child,
      Hoare
        (fun s =>
           ParentResumeShapeCandidate u child done s /\
           GlobalShapeCandidate s /\
           SuspendedSegmentEscapeAccountingCandidate u child done s /\
           ParentPendingChildEscapeAccountedCandidate u done child s)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s =>
           PendingChildSegmentNonOlderAnchorAccountedByParentCandidate
             u done child s).

  Definition GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_statement:
    Prop :=
    forall u done child,
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           Visited u s /\
           ParentResumeShapeCandidate u child done s /\
           ChildSegmentSummaryCandidate child s /\
           SuspendedSegmentEscapeAccountingCandidate u child done s /\
           ParentPendingChildEscapeAccountedCandidate u done child s)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s => PendingChildSegmentEscapeAccountedCandidate u done child s).

  Definition ChildOldAnchorLiftsToParentCandidate_from_all_older_statement:
    Prop :=
    forall u done child s,
      low s u <= low s child ->
      (forall b,
          Active b s ->
          dfn s b < dfn s child ->
          low s child <= dfn s b ->
          dg_reachable g child b ->
          dfn s b < dfn s u) ->
      ChildOldAnchorLiftsToParentCandidate u done child s.

  Definition LoopEntryImpliesPhase7Candidate_statement: Prop :=
    forall u s,
      LoopInvPhase6Candidate u ∅ s ->
      SegmentEscapeAccountingCandidate u ∅ s ->
      SegmentTreeCoverageByDoneCandidate u ∅ s ->
      ActiveTargetBlocksEscapeAccountedCandidate u ∅ s ->
      LoopInvPhase7Candidate u ∅ s.

  Definition Phase7ChildPostExtendsLoopFieldsCandidate_statement: Prop :=
    forall u done child s,
      SegmentEscapeAccountingCandidate u done s ->
      ParentPendingChildEscapeAccountedCandidate u done child s ->
      SegmentEscapeAccountingCandidate u (done_after done child) s.

  (* ================================================================ *)
  (* Phase 8 candidates: suspended parent frame                       *)
  (* ================================================================ *)

  Record SuspendedFrameCandidate: Type := {
    frame_parent : V;
    frame_child : V;
    frame_done : V -> Prop;
  }.

  Definition FrameInvCandidate (F: SuspendedFrameCandidate) (s: St): Prop :=
    ParentResumeShapeCandidate
      (frame_parent F) (frame_child F) (frame_done F) s /\
    LoopInvLowCandidate (frame_parent F) (frame_done F) s /\
    SuspendedParentFrameResumeCandidate
      (frame_parent F) (frame_child F) (frame_done F) s /\
    DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
    ProcessedTreeChildrenCorrectCandidate (frame_parent F) (frame_done F) s /\
    ActiveProcessedChildSegmentSummaryCandidate
      (frame_parent F) (frame_done F) s /\
    SuspendedSegmentEscapeAccountingCandidate
      (frame_parent F) (frame_child F) (frame_done F) s /\
    SuspendedSegmentTreeCoverageByDoneCandidate
      (frame_parent F) (frame_child F) (frame_done F) s.

  Definition FrameOfCallCandidate
             (u child: V) (done: V -> Prop): SuspendedFrameCandidate :=
    {| frame_parent := u; frame_child := child; frame_done := done |}.

  Definition FrameCompatibleWithCallCandidate
             (F: SuspendedFrameCandidate)
             (direct_parent direct_child: V) (s: St): Prop :=
    (frame_parent F = direct_parent /\ frame_child F = direct_child) \/
    PendingChildSegmentCandidate (frame_child F) s direct_parent.

  Definition FrameProgressCandidate
             (F: SuspendedFrameCandidate) (direct_parent: V)
             (s: St): Prop :=
    PendingChildSegmentCandidate (frame_child F) s direct_parent /\
    dfn s (frame_parent F) < dfn s direct_parent /\
    forall v,
      frame_done F v ->
      Active v s ->
      dfn s v < dfn s direct_parent.

  Definition FrameCompatibleWithOwnCallCandidate_statement: Prop :=
    forall parent child done s,
      FrameCompatibleWithCallCandidate
        (FrameOfCallCandidate parent child done) parent child s.

  Definition FrameCompatibleWithPendingParentCandidate_statement: Prop :=
    forall F direct_parent direct_child s,
      PendingChildSegmentCandidate (frame_child F) s direct_parent ->
      FrameCompatibleWithCallCandidate F direct_parent direct_child s.

  Definition SuspendedLoopInvPhase7ProvidesFrameInvCandidate_statement: Prop :=
    forall u done child s,
      SuspendedLoopInvPhase7Candidate u child done s ->
      ParentResumeShapeCandidate u child done s ->
      FrameInvCandidate (FrameOfCallCandidate u child done) s.

  Definition SetFaCreatesSuspendedParentFrameCandidate_statement: Prop :=
    forall parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           LocalActiveRootCandidate parent s /\
           ParentFrameResumeCandidate parent done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s =>
           SuspendedParentFrameResumeCandidate parent child done s /\
           ParentResumeShapeCandidate parent child done s).

  Definition SetFaPreservesProcessedTreeChildrenCorrectCandidate_statement:
    Prop :=
    forall parent child done,
      ~ done child ->
      Hoare
        (fun s =>
           ProcessedTreeChildrenCorrectCandidate parent done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s =>
           ProcessedTreeChildrenCorrectCandidate parent done s).

  Definition FrameInvProvidesParentResumeShapeCandidate_statement: Prop :=
    forall F s,
      FrameInvCandidate F s ->
      ParentResumeShapeCandidate
        (frame_parent F) (frame_child F) (frame_done F) s.

  Definition FrameInvProvidesLoopInvLowCandidate_statement: Prop :=
    forall F s,
      FrameInvCandidate F s ->
      LoopInvLowCandidate (frame_parent F) (frame_done F) s.

  Definition FrameInvProvidesSuspendedParentFrameResumeCandidate_statement:
    Prop :=
    forall F s,
      FrameInvCandidate F s ->
      SuspendedParentFrameResumeCandidate
        (frame_parent F) (frame_child F) (frame_done F) s.

  Definition FrameInvProvidesDoneClosednessCandidate_statement: Prop :=
    forall F s,
      FrameInvCandidate F s ->
      DoneClosednessCandidate (frame_parent F) (frame_done F) s.

  Definition FrameInvProvidesProcessedTreeChildrenCorrectCandidate_statement:
    Prop :=
    forall F s,
      FrameInvCandidate F s ->
      ProcessedTreeChildrenCorrectCandidate
        (frame_parent F) (frame_done F) s.

  Definition FrameInvProvidesActiveProcessedChildSegmentSummaryCandidate_statement:
    Prop :=
    forall F s,
      FrameInvCandidate F s ->
      ActiveProcessedChildSegmentSummaryCandidate
        (frame_parent F) (frame_done F) s.

  Definition FrameInvProvidesSuspendedSegmentEscapeAccountingCandidate_statement:
    Prop :=
    forall F s,
      FrameInvCandidate F s ->
      SuspendedSegmentEscapeAccountingCandidate
        (frame_parent F) (frame_child F) (frame_done F) s.

  Definition FrameInvProvidesSuspendedSegmentTreeCoverageCandidate_statement:
    Prop :=
    forall F s,
      FrameInvCandidate F s ->
      SuspendedSegmentTreeCoverageByDoneCandidate
        (frame_parent F) (frame_child F) (frame_done F) s.

  Definition FrameInvForgetsSuspendedLoopInvPhase6Candidate_statement: Prop :=
    forall F s,
      FrameInvCandidate F s ->
      SuspendedLoopInvPhase6Candidate
        (frame_parent F) (frame_child F) (frame_done F) s.

  Definition SuspendedParentFrameResumeClosesAfterChildCandidate_statement:
    Prop :=
    forall parent child done s,
      SuspendedParentFrameResumeCandidate parent child done s ->
      Visited child s ->
      ParentFrameResumeCandidate parent (done_after done child) s.

  Definition SuspendedLoopInvPhase7ClosesAfterChildCandidate_statement:
    Prop :=
    forall parent child done s,
      LoopInvLowCandidate parent (done_after done child) s ->
      SuspendedParentFrameResumeCandidate parent child done s ->
      Visited child s ->
      DoneClosednessCandidate parent (done_after done child) s ->
      ProcessedTreeChildrenCorrectCandidate parent (done_after done child) s ->
      ActiveProcessedChildSegmentSummaryCandidate
        parent (done_after done child) s ->
      SegmentEscapeAccountingCandidate parent (done_after done child) s ->
      SegmentTreeCoverageByDoneCandidate parent (done_after done child) s ->
      ActiveTargetBlocksEscapeAccountedCandidate
        parent (done_after done child) s ->
      LoopInvPhase7Candidate parent (done_after done child) s.

  Definition FrameContractCandidate (W: RecProgram): Prop :=
    forall F parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           FrameCompatibleWithCallCandidate F parent child s /\
           ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s => FrameInvCandidate F s).

  Definition FrameProgressContractCandidate (W: RecProgram): Prop :=
    forall F parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameProgressCandidate F parent s /\
           ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s => FrameProgressCandidate F parent s).

  Definition FramedChildProvidesLowContributionCandidate
             (W: RecProgram): Prop :=
    forall parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate (FrameOfCallCandidate parent child done) s /\
           ChildEntryCandidate parent child done s /\
           PartialRootLowEquationCandidate parent done s)
        (W child)
        (fun _ s =>
           PartialRootLowEquationCandidate parent done s /\
           fa s child = parent /\
           fa s child <> child /\
           low s child <= dfn s child).

  Definition FrameFieldPreservationCandidate
             (Field: SuspendedFrameCandidate -> St -> Prop)
             (W: RecProgram): Prop :=
    forall F parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           FrameCompatibleWithCallCandidate F parent child s /\
           ChildEntryCandidate parent child done s)
        (W child)
        (fun _ s => Field F s).

  Definition FramePreservesParentResumeShapeCandidate
             (W: RecProgram): Prop :=
    FrameFieldPreservationCandidate
      (fun F s =>
         ParentResumeShapeCandidate
           (frame_parent F) (frame_child F) (frame_done F) s)
      W.

  Definition FramePreservesLoopInvLowCandidate
             (W: RecProgram): Prop :=
    FrameFieldPreservationCandidate
      (fun F s =>
         LoopInvLowCandidate (frame_parent F) (frame_done F) s)
      W.

  Definition FramePreservesSuspendedParentFrameResumeCandidate
             (W: RecProgram): Prop :=
    FrameFieldPreservationCandidate
      (fun F s =>
         SuspendedParentFrameResumeCandidate
           (frame_parent F) (frame_child F) (frame_done F) s)
      W.

  Definition FramePreservesDoneClosednessCandidate
             (W: RecProgram): Prop :=
    FrameFieldPreservationCandidate
      (fun F s =>
         DoneClosednessCandidate (frame_parent F) (frame_done F) s)
      W.

  Definition FramePreservesProcessedTreeChildrenCorrectCandidate
             (W: RecProgram): Prop :=
    FrameFieldPreservationCandidate
      (fun F s =>
         ProcessedTreeChildrenCorrectCandidate
           (frame_parent F) (frame_done F) s)
      W.

  Definition FramePreservesActiveProcessedChildSegmentSummaryCandidate
             (W: RecProgram): Prop :=
    FrameFieldPreservationCandidate
      (fun F s =>
         ActiveProcessedChildSegmentSummaryCandidate
           (frame_parent F) (frame_done F) s)
      W.

  Definition FramePreservesSuspendedSegmentEscapeAccountingCandidate
             (W: RecProgram): Prop :=
    FrameFieldPreservationCandidate
      (fun F s =>
         SuspendedSegmentEscapeAccountingCandidate
           (frame_parent F) (frame_child F) (frame_done F) s)
      W.

  Definition FramePreservesSuspendedSegmentTreeCoverageCandidate
             (W: RecProgram): Prop :=
    FrameFieldPreservationCandidate
      (fun F s =>
         SuspendedSegmentTreeCoverageByDoneCandidate
           (frame_parent F) (frame_child F) (frame_done F) s)
      W.

  Definition FramePreservationBundleCandidate (W: RecProgram): Prop :=
    FramePreservesParentResumeShapeCandidate W /\
    FramePreservesLoopInvLowCandidate W /\
    FramePreservesSuspendedParentFrameResumeCandidate W /\
    FramePreservesDoneClosednessCandidate W /\
    FramePreservesProcessedTreeChildrenCorrectCandidate W /\
    FramePreservesActiveProcessedChildSegmentSummaryCandidate W /\
    FramePreservesSuspendedSegmentEscapeAccountingCandidate W /\
    FramePreservesSuspendedSegmentTreeCoverageCandidate W.

  Definition FrameContractCandidate_from_field_preservation_statement:
    Prop :=
    forall W,
      FramePreservationBundleCandidate W ->
      FrameContractCandidate W.

  Definition FrameContractCandidate_provides_field_preservation_statement:
    Prop :=
    forall W Field,
      (forall F s, FrameInvCandidate F s -> Field F s) ->
      FrameContractCandidate W ->
      FrameFieldPreservationCandidate Field W.

  Definition FrameContractCandidate_to_field_preservation_bundle_statement:
    Prop :=
    forall W,
      FrameContractCandidate W ->
      FramePreservationBundleCandidate W.

  Definition RecursiveCallContractsCandidate (W: RecProgram): Prop :=
    ChildContractCandidate W /\
    FramedChildProvidesLowContributionCandidate W /\
    FrameContractCandidate W.

  Definition BodySatisfiesChildContractCandidate_statement: Prop :=
    forall W,
      RecursiveCallContractsCandidate W ->
      ChildContractCandidate (tarjan_scc_f g W).

  Definition BodyProvidesLowContributionCandidate_statement: Prop :=
    forall W,
      RecursiveCallContractsCandidate W ->
      FramedChildProvidesLowContributionCandidate (tarjan_scc_f g W).

  Definition BodyPreservesFrameContractCandidate_statement: Prop :=
    forall W,
      RecursiveCallContractsCandidate W ->
      FrameContractCandidate (tarjan_scc_f g W).

  Definition BodyRecursiveCallContractsCandidate_from_parts_statement: Prop :=
    BodySatisfiesChildContractCandidate_statement ->
    BodyProvidesLowContributionCandidate_statement ->
    BodyPreservesFrameContractCandidate_statement ->
    forall W,
      RecursiveCallContractsCandidate W ->
      RecursiveCallContractsCandidate (tarjan_scc_f g W).

  Definition BodyChildPostTailCandidate_statement: Prop :=
    forall W parent child done,
      RecursiveCallContractsCandidate W ->
      Edge parent child ->
      ~ done child ->
      Hoare
        (ChildEntryCandidate parent child done)
        (tarjan_scc_f g W child)
        (fun _ s =>
           (Active child s -> ChildSegmentSummaryCandidate child s) /\
           ParentResumeShapeCandidate parent child done s /\
           ParentPendingChildEscapeAccountedCandidate parent done child s /\
           ActiveTargetBlocksEscapeAccountedCandidate
             parent (done_after done child) s).

  Definition BodyPreservesPartialRootLowEquationCandidate_statement: Prop :=
    forall W parent child done,
      RecursiveCallContractsCandidate W ->
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate (FrameOfCallCandidate parent child done) s /\
           ChildEntryCandidate parent child done s /\
           PartialRootLowEquationCandidate parent done s)
        (tarjan_scc_f g W child)
        (fun _ s => PartialRootLowEquationCandidate parent done s).

  Definition BodyPreservesChildParentPointerCandidate_statement: Prop :=
    forall W parent child done,
      RecursiveCallContractsCandidate W ->
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate (FrameOfCallCandidate parent child done) s /\
           ChildEntryCandidate parent child done s /\
           PartialRootLowEquationCandidate parent done s)
        (tarjan_scc_f g W child)
        (fun _ s =>
           fa s child = parent /\
           fa s child <> child).

  Definition BodyProducesChildLowDfnBoundCandidate_statement: Prop :=
    forall W parent child done,
      RecursiveCallContractsCandidate W ->
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate (FrameOfCallCandidate parent child done) s /\
           ChildEntryCandidate parent child done s /\
           PartialRootLowEquationCandidate parent done s)
        (tarjan_scc_f g W child)
        (fun _ s => low s child <= dfn s child).

  Definition BodyFrameAfterPreloopCandidate_statement: Prop :=
    forall F parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           FrameCompatibleWithCallCandidate F parent child s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           FrameInvCandidate F s /\
           LoopInvPhase7Candidate child ∅ s /\
           PendingChildSegmentCandidate (frame_child F) s child /\
           dfn s (frame_parent F) < dfn s child /\
           forall v,
             frame_done F v ->
             dfn s v < dfn s child).

  Definition BodyFrameEdgeLoopPreservesCandidate_statement: Prop :=
    forall W F child,
      RecursiveCallContractsCandidate W ->
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           LoopInvPhase7Candidate child ∅ s /\
           FrameProgressCandidate F child s)
        (edge_loop child W)
        (fun _ s =>
           FrameInvCandidate F s /\
           LoopDonePhase7Candidate child s /\
           dfn s (frame_parent F) < dfn s child /\
           forall v,
             frame_done F v ->
             Active v s ->
             dfn s v < dfn s child).

  Definition ProcessEdgePreservesFrameAndOlderCandidate_statement: Prop :=
    forall W F child (done: V -> Prop) a,
      RecursiveCallContractsCandidate W ->
      Edge child a ->
      ~ done a ->
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           LoopInvPhase7Candidate child done s /\
           FrameProgressCandidate F child s)
        (process_edge child W a)
        (fun _ s =>
           FrameInvCandidate F s /\
           LoopInvPhase7Candidate child (done_after done a) s /\
           FrameProgressCandidate F child s).

  Definition PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement:
    Prop :=
    forall F parent child done,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           FrameCompatibleWithCallCandidate F parent child s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           ProcessedTreeChildrenCorrectCandidate
             (frame_parent F) (frame_done F) s).

  Definition FrameParentResumeShapeAfterPreloopCandidate_statement: Prop :=
    forall F parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           FrameCompatibleWithCallCandidate F parent child s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           ParentResumeShapeCandidate
             (frame_parent F) (frame_child F) (frame_done F) s /\
           Visited (frame_child F) s).

  Definition FrameParentResumeShapePreservedByMaybePopCandidate_statement:
    Prop :=
    forall F u,
      Hoare
        (ParentResumeShapeCandidate
           (frame_parent F) (frame_child F) (frame_done F))
        (maybe_pop u)
        (fun _ s =>
           ParentResumeShapeCandidate
             (frame_parent F) (frame_child F) (frame_done F) s).

  Definition FrameSuspendedParentFrameResumeAfterPreloopCandidate_statement:
    Prop :=
    forall F parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           FrameCompatibleWithCallCandidate F parent child s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           SuspendedParentFrameResumeCandidate
             (frame_parent F) (frame_child F) (frame_done F) s).

  Definition FrameSuspendedParentFrameResumePreservedByMaybePopCandidate_statement:
    Prop :=
    forall F u,
      Hoare
        (SuspendedParentFrameResumeCandidate
           (frame_parent F) (frame_child F) (frame_done F))
        (maybe_pop u)
        (fun _ s =>
           SuspendedParentFrameResumeCandidate
             (frame_parent F) (frame_child F) (frame_done F) s).

  Definition FramePopBoundaryCandidate
             (F: SuspendedFrameCandidate) (u: V) (s: St): Prop :=
    (forall popped rest,
        stack_split_at (stack s) u = (popped, rest) ->
        In (frame_parent F) rest) /\
    forall v,
      frame_done F v ->
      Active v s ->
      forall popped rest,
        stack_split_at (stack s) u = (popped, rest) ->
        In v rest.

  Definition FramePopBoundarySnapshotCandidate
             (F: SuspendedFrameCandidate) (snap s: St): Prop :=
    Active (frame_parent F) s /\
    (forall v, frame_done F v -> Active v snap -> Active v s) /\
    (forall x, Visited x s <-> Visited x snap) /\
    (forall x, dfn s x = dfn snap x) /\
    (forall x, low s x = low snap x) /\
    (forall x, fa s x = fa snap x).

  Definition MaybePopPreservesActiveProcessedChildSegmentSummaryCandidate_statement:
    Prop :=
    forall u done parent,
      Hoare
        (fun s =>
           ActiveProcessedChildSegmentSummaryCandidate parent done s /\
           LocalActiveRootCandidate parent s /\
           Active u s)
        (maybe_pop u)
        (fun _ s => ActiveProcessedChildSegmentSummaryCandidate parent done s).

  Definition MaybePopProducesFramePopBoundarySnapshotCandidate_statement:
    Prop :=
    forall F u snap,
      Hoare
        (fun s =>
           s = snap /\
           Active (frame_parent F) snap /\
           FramePopBoundaryCandidate F u snap)
        (maybe_pop u)
        (fun _ s => FramePopBoundarySnapshotCandidate F snap s).

  Definition MaybePopProducesChildLowerStackAnchorsPreservedCandidate_statement:
    Prop :=
    forall F u child snap,
      Hoare
        (fun s =>
           s = snap /\
           Active u snap /\
           OrderFactsCandidate snap /\
           frame_done F child /\
           Active child snap /\
           FramePopBoundaryCandidate F u snap)
        (maybe_pop u)
        (fun _ s =>
           ChildLowerStackAnchorsPreservedCandidate child snap s).

  Definition MaybePopActivePostImpliesPreSnapshotCandidate_statement:
    Prop :=
    forall u snap,
      Hoare
        (fun s => s = snap /\ Active u snap)
        (maybe_pop u)
        (fun _ s => forall x, Active x s -> Active x snap).

  Definition PopSccKeepsDfnInjectiveCandidate_statement: Prop :=
    forall u,
      Hoare
        (fun s => dfn_injective s)
        (pop_scc u)
        (fun _ s => dfn_injective s).

  Definition MaybePopPreservesGlobalShapeCandidate_statement: Prop :=
    forall u,
      Hoare
        (GlobalShapeCandidate)
        (maybe_pop u)
        (fun _ s => GlobalShapeCandidate s).

  Definition MaybePopPreservesOrderFactsCandidate_statement: Prop :=
    forall u,
      Hoare
        (fun s => OrderFactsCandidate s /\ Active u s)
        (maybe_pop u)
        (fun _ s => OrderFactsCandidate s).

  Definition FramePopBoundarySnapshotPreservesDoneClosednessCandidate_statement:
    Prop :=
    forall F snap s,
      FramePopBoundarySnapshotCandidate F snap s ->
      DoneClosednessCandidate (frame_parent F) (frame_done F) snap ->
      DoneClosednessCandidate (frame_parent F) (frame_done F) s.

  Definition FramePopBoundarySnapshotPreservesProcessedTreeChildrenCorrectWithTransportCandidate_statement:
    Prop :=
    forall F snap s,
      FramePopBoundarySnapshotCandidate F snap s ->
      ProcessedTreeChildrenCorrectCandidate
        (frame_parent F) (frame_done F) snap ->
      (forall child,
          frame_done F child ->
          Edge (frame_parent F) child ->
          fa snap child = frame_parent F ->
          fa snap child <> child ->
          ChildRootCorrectTransportCandidate child snap s) ->
      ProcessedTreeChildrenCorrectCandidate
        (frame_parent F) (frame_done F) s.

  Definition MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryAndTransportCandidate_statement:
    Prop :=
    forall F u,
      Hoare
        (fun snap =>
           ProcessedTreeChildrenCorrectCandidate
             (frame_parent F) (frame_done F) snap /\
           Active (frame_parent F) snap /\
           FramePopBoundaryCandidate F u snap /\
           (forall s,
               FramePopBoundarySnapshotCandidate F snap s ->
               forall child,
                 frame_done F child ->
                 Edge (frame_parent F) child ->
                 fa snap child = frame_parent F ->
                 fa snap child <> child ->
                 ChildRootCorrectTransportCandidate child snap s))
        (maybe_pop u)
        (fun _ s =>
           ProcessedTreeChildrenCorrectCandidate
             (frame_parent F) (frame_done F) s).

  Definition MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryCandidate_statement:
    Prop :=
    forall F u,
      Hoare
        (fun snap =>
           ProcessedTreeChildrenCorrectCandidate
             (frame_parent F) (frame_done F) snap /\
           Active (frame_parent F) snap /\
           Active u snap /\
           OrderFactsCandidate snap /\
           FramePopBoundaryCandidate F u snap)
        (maybe_pop u)
        (fun _ s =>
           ProcessedTreeChildrenCorrectCandidate
             (frame_parent F) (frame_done F) s).

  Definition MaybePopPreservesDoneClosednessWithFramePopBoundaryCandidate_statement:
    Prop :=
    forall F u,
      Hoare
        (fun s =>
           DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
           Active (frame_parent F) s /\
           FramePopBoundaryCandidate F u s)
        (maybe_pop u)
        (fun _ s =>
           DoneClosednessCandidate (frame_parent F) (frame_done F) s).

  Definition FramePopSnapshotsPreservePartialRootLowEquationCandidate_statement:
    Prop :=
    forall F snap s,
      FramePopBoundarySnapshotCandidate F snap s ->
      (forall x, Active x s -> Active x snap) ->
      PartialRootLowEquationCandidate
        (frame_parent F) (frame_done F) snap ->
      PartialRootLowEquationCandidate
        (frame_parent F) (frame_done F) s.

  Definition FramePopSnapshotsPreserveLoopInvLowCandidate_statement:
    Prop :=
    forall F snap s,
      FramePopBoundarySnapshotCandidate F snap s ->
      (forall x, Active x s -> Active x snap) ->
      GlobalShapeCandidate s ->
      SettledClosedCandidate s ->
      OrderFactsCandidate s ->
      LoopInvLowCandidate (frame_parent F) (frame_done F) snap ->
      LoopInvLowCandidate (frame_parent F) (frame_done F) s.

  (* ================================================================ *)
  (* Phase 7c candidates: pop bridge and final root state             *)
  (* ================================================================ *)

  Definition PoppedSegmentClosedCandidate (u: V) (s: St): Prop :=
    forall x w,
      Visited x s ->
      Active x s ->
      dfn s u <= dfn s x ->
      dg_reachable g x w ->
      Visited w s.

  Definition MaybePopPreservesSettledClosedWithSegmentClosedCandidate_statement:
    Prop :=
    forall u,
      Hoare
        (fun s =>
           SettledClosedCandidate s /\
           Active u s /\
           OrderFactsCandidate s /\
           PoppedSegmentClosedCandidate u s)
        (maybe_pop u)
        (fun _ s => SettledClosedCandidate s).

  Definition MaybePopPreservesLoopInvLowWithFramePopBoundaryCandidate_statement:
    Prop :=
    forall F u,
      Hoare
        (fun s =>
           LoopInvLowCandidate (frame_parent F) (frame_done F) s /\
           Active u s /\
           FramePopBoundaryCandidate F u s /\
           PoppedSegmentClosedCandidate u s)
        (maybe_pop u)
        (fun _ s =>
           LoopInvLowCandidate (frame_parent F) (frame_done F) s).

  Definition SegmentClosedAtRootInputCandidate (u: V) (s: St): Prop :=
    LoopDonePhase7Candidate u s /\
    root_pop_guard u s.

  Definition SegmentClosedAtRootCandidate_statement: Prop :=
    forall u s,
      SegmentClosedAtRootInputCandidate u s ->
      PoppedSegmentClosedCandidate u s.

  Definition RootFinalLowValidCandidate (u: V) (s: St): Prop :=
    scc_low_valid_v g root s u.

  Definition RootFinalIsLowCandidate (u: V) (s: St): Prop :=
    scc_is_low_v g root s u.

  Definition RootFinalCorrectCandidate (u: V) (s: St): Prop :=
    RootFinalLowValidCandidate u s /\
    RootFinalIsLowCandidate u s.

  Definition RootFinalLowValidStableFieldsCandidate
             (u: V) (s: St): Prop :=
    GlobalShapeCandidate s /\
    Visited u s /\
    RootFinalLowValidCandidate u s /\
    OrderFactsCandidate s.

  Definition RootFinalCandidate (u: V) (s: St): Prop :=
    GlobalShapeCandidate s /\
    SettledClosedCandidate s /\
    Visited u s /\
    RootFinalCorrectCandidate u s /\
    OrderFactsCandidate s.

  Definition RootFinalFromPrePopCandidate (u: V) (s: St): Prop :=
    GlobalShapeCandidate s /\
    SettledClosedCandidate s /\
    Visited u s /\
    RootLowPrePopCandidate u s /\
    OrderFactsCandidate s.

  Definition RootFinalFromPrePopCandidate_statement: Prop :=
    forall u s,
      RootFinalFromPrePopCandidate u s ->
      RootFinalCandidate u s.

  Definition PopBranchInputCandidate (u: V) (s: St): Prop :=
    LoopDonePhase7Candidate u s /\
    RootLowPrePopCandidate u s /\
    root_pop_guard u s.

  Definition SkipBranchInputCandidate (u: V) (s: St): Prop :=
    LoopDonePhase7Candidate u s /\
    RootLowPrePopCandidate u s /\
    ~ root_pop_guard u s.

  Definition RootPopBridgeCandidate_statement: Prop :=
    forall u,
      Hoare
        (fun s =>
           LoopDonePhase7Candidate u s /\
           RootLowPrePopCandidate u s /\
           root_pop_guard u s /\
           PoppedSegmentClosedCandidate u s)
        (pop_scc u)
        (fun _ s => RootFinalCandidate u s).

  Definition RootPopLowValidStableFieldsCandidate_statement: Prop :=
    forall u,
      Hoare
        (fun s =>
           LoopDonePhase7Candidate u s /\
           RootLowValidPrePopCandidate u s /\
           root_pop_guard u s)
        (pop_scc u)
        (fun _ s => RootFinalLowValidStableFieldsCandidate u s).

  Definition RootPopSettledClosedCandidate_statement: Prop :=
    forall u,
      Hoare
        (fun s =>
           LoopDonePhase7Candidate u s /\
           PoppedSegmentClosedCandidate u s)
        (pop_scc u)
        (fun _ s => SettledClosedCandidate s).

  Definition RootPopIsLowInputCandidate (u: V) (s: St): Prop :=
    Active u s /\
    RootIsLowPrePopCandidate u s /\
    root_pop_guard u s.

  Definition RootPopIsLowCandidate_statement: Prop :=
    forall u,
      Hoare
        (RootPopIsLowInputCandidate u)
        (pop_scc u)
        (fun _ s => RootFinalIsLowCandidate u s).

  Definition PopBranchProducesRootFinalCandidate_statement: Prop :=
    forall u,
      Hoare
        (PopBranchInputCandidate u)
        (pop_scc u)
        (fun _ s => RootFinalCandidate u s).

  Definition SkipBranchProducesRootFinalCandidate_statement: Prop :=
    forall u s,
      SkipBranchInputCandidate u s ->
      RootFinalCandidate u s.

  Definition MaybePopFinalCandidate_statement: Prop :=
    forall u,
      Hoare
        (fun s =>
           LoopDonePhase7Candidate u s /\
           RootLowPrePopCandidate u s)
        (maybe_pop u)
        (fun _ s => RootFinalCandidate u s).

  (* ---------------------------------------------------------------- *)
  (* Phase 5 branch statements (to be relocated)                       *)
  (* ---------------------------------------------------------------- *)

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

  Lemma ChildEntryProvidesEntryPreCandidate_proof:
    ChildEntryProvidesEntryPreCandidate_statement.
  Proof.
    unfold ChildEntryProvidesEntryPreCandidate_statement,
      ChildEntryCandidate,
      PendingChildShapeCandidate,
      EntryPreCandidate.
    intros parent child done s
           [_ [Hpre [Hsettled [_ [_ [_ Horder]]]]]].
    split; [exact Hpre |].
    split; [exact Hsettled | exact Horder].
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

  Lemma PreloopFromChildEntryProducesLoopEntryBaseCandidate_proof:
    PreloopFromChildEntryProducesLoopEntryBaseCandidate_statement.
  Proof.
    unfold PreloopFromChildEntryProducesLoopEntryBaseCandidate_statement.
    intros parent child done.
    eapply Hoare_conseq_pre.
    2: { apply PreloopEntryBaseCandidate_proof. }
    intros s Hentry.
    eapply ChildEntryProvidesEntryPreCandidate_proof.
    exact Hentry.
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

  Lemma UpdateLowKeepsVisitedCandidate_proof:
    UpdateLowKeepsVisitedCandidate_statement.
  Proof.
    unfold UpdateLowKeepsVisitedCandidate_statement.
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
        unfold Visited. simpl. reflexivity.
      - eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _].
        subst s.
        reflexivity. }
    intros s [Heq_s _]. exact Heq_s.
  Qed.

  Lemma GetLowUpdateLowKeepsTraversalSnapshotCandidate_proof:
    GetLowUpdateLowKeepsTraversalSnapshotCandidate_statement.
  Proof.
    unfold GetLowUpdateLowKeepsTraversalSnapshotCandidate_statement.
    intros u child snap.
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => forall x, Visited x s <-> Visited x snap)
             (Q2 := fun _ s =>
                      ((forall x, dfn s x = dfn snap x) /\
                       (forall x, fa s x = fa snap x) /\
                       (forall x, Active x s <-> Active x snap) /\
                       (forall x, x <> u -> low s x = low snap x)) /\
                      low s u <= low snap u).
      - eapply Hoare_conseq_pre.
        2: apply (UpdateLowKeepsVisitedCandidate_proof u lv snap).
        intros s [Heq_s _]. exact Heq_s.
      - apply Hoare_conj
          with (Q1 := fun _ s =>
                        (forall x, dfn s x = dfn snap x) /\
                        (forall x, fa s x = fa snap x) /\
                        (forall x, Active x s <-> Active x snap) /\
                        (forall x, x <> u -> low s x = low snap x))
               (Q2 := fun _ s => low s u <= low snap u).
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowKeepsSnapshotFieldsCandidate_proof u lv snap).
          intros s [Heq_s _]. exact Heq_s.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowBoundedByOldCandidate_proof u lv (low snap u)).
          intros s [Heq_s _]. subst s. reflexivity. }
    intros _ s [Hvisited [Hsnapshot Hlow_old]].
    destruct Hsnapshot as [Hdfn [Hfa [Hactive Hlow_other]]].
    split; [exact Hvisited |].
    split; [exact Hdfn |].
    split; [exact Hfa |].
    split; [exact Hactive |].
    split; [exact Hlow_other | exact Hlow_old].
  Qed.

  Lemma GetDfnUpdateLowKeepsTraversalSnapshotCandidate_proof:
    forall u a snap,
      Hoare
        (fun s : St => s = snap)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s =>
           (forall x, Visited x s <-> Visited x snap) /\
           (forall x, dfn s x = dfn snap x) /\
           (forall x, fa s x = fa snap x) /\
           (forall x, Active x s <-> Active x snap) /\
           (forall x, x <> u -> low s x = low snap x) /\
           low s u <= dfn snap a).
  Proof.
    intros u a snap.
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => forall x, Visited x s <-> Visited x snap)
             (Q2 := fun _ s =>
                      ((forall x, dfn s x = dfn snap x) /\
                       (forall x, fa s x = fa snap x) /\
                       (forall x, Active x s <-> Active x snap) /\
                       (forall x, x <> u -> low s x = low snap x)) /\
                      (dv = dfn snap a /\ low s u <= dv)).
      - eapply Hoare_conseq_pre.
        2: apply (UpdateLowKeepsVisitedCandidate_proof u dv snap).
        intros s [Heq_s _]. exact Heq_s.
      - apply Hoare_conj
          with (Q1 := fun _ s =>
                        (forall x, dfn s x = dfn snap x) /\
                        (forall x, fa s x = fa snap x) /\
                        (forall x, Active x s <-> Active x snap) /\
                        (forall x, x <> u -> low s x = low snap x))
               (Q2 := fun _ s => dv = dfn snap a /\ low s u <= dv).
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowKeepsSnapshotFieldsCandidate_proof u dv snap).
          intros s [Heq_s _]. exact Heq_s.
        + apply Hoare_conj
            with (Q1 := fun _ _ => dv = dfn snap a)
                 (Q2 := fun _ s => low s u <= dv).
	          * unfold Hoare.
	            intros s1 r s2 [Heq_s Hdv] _Hrun.
            subst s1. exact Hdv.
          * eapply Hoare_conseq_pre.
            2: apply (UpdateLowBoundedByIncomingCandidate_proof u dv).
            intros s _Hget. exact I.
    }
    intros _ s [Hvisited [Hsnapshot [Hdv Hlow_incoming]]].
    destruct Hsnapshot as [Hdfn [Hfa [Hactive Hlow_other]]].
    split; [exact Hvisited |].
    split; [exact Hdfn |].
    split; [exact Hfa |].
    split; [exact Hactive |].
    split; [exact Hlow_other |].
    rewrite <- Hdv.
    exact Hlow_incoming.
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

  Lemma GetLowUpdateLowProducesParentLowBelowChildCandidate_proof:
    GetLowUpdateLowProducesParentLowBelowChildCandidate_statement.
  Proof.
    unfold GetLowUpdateLowProducesParentLowBelowChildCandidate_statement,
      ParentLowBelowChildCandidate.
    intros u child.
    apply Hoare_normalize.
    intros snap _.
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => low s u <= lv)
             (Q2 := fun _ s =>
                      lv = low snap child /\
                      (forall x, dfn s x = dfn snap x) /\
                      (forall x, fa s x = fa snap x) /\
                      (forall x, Active x s <-> Active x snap) /\
                      (forall x, x <> u -> low s x = low snap x)).
      - eapply Hoare_conseq_pre.
        2: apply (UpdateLowBoundedByIncomingCandidate_proof u lv).
        intros s _. exact I.
      - apply Hoare_conj.
        + unfold Hoare. intros s1 _ s2 [_ Hlv] _. exact Hlv.
        + eapply Hoare_conseq_pre.
          2: apply (UpdateLowKeepsSnapshotFieldsCandidate_proof u lv snap).
          intros s [Heq_s _]. exact Heq_s. }
    intros _ s [Hlow_u_lv
                 [Hlv [_Hdfn_keep [_Hfa_keep [_Hactive_keep Hlow_other]]]]].
    destruct (equiv_dec child u) as [Hchild_u | Hchild_not_u].
    - rewrite Hchild_u. lia.
    - rewrite (Hlow_other child Hchild_not_u).
      rewrite <- Hlv.
      exact Hlow_u_lv.
  Qed.

  Lemma GetLowUpdateLowPreservesGlobalShapeCandidate_proof:
    GetLowUpdateLowPreservesGlobalShapeCandidate_statement.
  Proof.
    unfold GetLowUpdateLowPreservesGlobalShapeCandidate_statement,
      GlobalShapeCandidate,
      Visited.
    intros u child.
    apply Hoare_normalize.
    intros snap [Hshape Hvis_u].
    eapply Hoare_bind.
    { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: { apply (update_low_preserves_wf_scc_state g root u lv). }
    intros s [Heq_s _].
    subst s.
    split; [exact Hshape | exact Hvis_u].
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
  (* Phase-6 consumer audit proofs                                    *)
  (* ================================================================ *)

  Lemma DoneClosednessCandidate_empty_proof:
    DoneClosednessCandidate_empty_statement.
  Proof.
    unfold DoneClosednessCandidate_empty_statement,
      DoneClosednessCandidate,
      done_reachable_closed,
      done_tree_reachable_closed.
    intros u s.
    split; intros v; intros; sets_unfold in H; destruct H.
  Qed.

  Lemma DoneClosednessCandidate_step_child_proof:
    DoneClosednessCandidate_step_child_statement.
  Proof.
    unfold DoneClosednessCandidate_step_child_statement,
      DoneClosednessCandidate,
      ChildClosednessContributionCandidate,
      ParentResumeShapeCandidate,
      done_reachable_closed,
      done_tree_reachable_closed,
      done_after.
    intros u done child s [Hdone_closed Htree_closed]
           [Hedge_child [Hnot_done_child [Hfa_child Hfa_child_neq]]]
           Hchild_closed.
    split.
    - intros v w Hdone_after Hnot_active Hreach.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_v | Hv_child].
      + eapply Hdone_closed; eauto.
      + subst v. apply Hchild_closed; auto.
    - intros v w Hdone_after Hnot_active Hfa_v Hfa_v_neq Hreach.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_v | Hv_child].
      + eapply Htree_closed; eauto.
      + subst v. apply Hchild_closed; auto.
  Qed.

  Lemma ProcessedTreeChildrenCorrectCandidate_empty_proof:
    ProcessedTreeChildrenCorrectCandidate_empty_statement.
  Proof.
    unfold ProcessedTreeChildrenCorrectCandidate_empty_statement,
      ProcessedTreeChildrenCorrectCandidate,
      ProcessedTreeChildrenLowValidCandidate,
      ProcessedTreeChildrenIsLowCandidate,
      ProcessedTreeChildrenInactiveSelfLowCandidate.
    intros u s.
    split.
    - intros child Hempty. sets_unfold in Hempty. destruct Hempty.
    - split; intros child Hempty; sets_unfold in Hempty; destruct Hempty.
  Qed.

  Lemma ProcessedTreeChildrenCorrectCandidate_step_child_proof:
    ProcessedTreeChildrenCorrectCandidate_step_child_statement.
  Proof.
    unfold ProcessedTreeChildrenCorrectCandidate_step_child_statement,
      ProcessedTreeChildrenCorrectCandidate,
      ProcessedTreeChildrenLowValidCandidate,
      ProcessedTreeChildrenIsLowCandidate,
      ProcessedTreeChildrenInactiveSelfLowCandidate,
      ParentResumeShapeCandidate,
      ChildRootCorrectForParentCandidate,
      ChildInactiveSelfLowForParentCandidate,
      done_after.
    intros u done child s [Hlow_valid [His_low Hinactive]]
           [Hedge_child [Hnot_done_child [Hfa_child Hfa_child_neq]]]
           [Hchild_valid Hchild_is_low]
           Hchild_inactive.
    split.
    - intros x Hdone_after Hedge_x Hfa_x Hfa_neq_x.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_x | Hx_child].
      + apply Hlow_valid; assumption.
      + subst x. exact Hchild_valid.
    - split.
      + intros x Hdone_after Hedge_x Hfa_x Hfa_neq_x.
        sets_unfold in Hdone_after.
        destruct Hdone_after as [Hdone_x | Hx_child].
        * apply His_low; assumption.
        * subst x. exact Hchild_is_low.
      + intros x Hdone_after Hedge_x Hfa_x Hfa_neq_x.
        sets_unfold in Hdone_after.
        destruct Hdone_after as [Hdone_x | Hx_child].
        * apply Hinactive; assumption.
        * subst x. exact Hchild_inactive.
  Qed.

  Lemma dfs_tree_step_transport_from_stable_fields:
    forall snap s x y,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, fa s z = fa snap z) ->
      dg_step (state_to_dfs_tree g snap root) x y ->
      dg_step (state_to_dfs_tree g s root) x y.
  Proof.
    unfold Visited.
    intros snap s x y Hvisited Hfa Hstep.
    unfold dg_step in Hstep |- *.
    destruct Hstep as [e [Hedge [Hfst Hsnd]]].
    exists e.
    split; [| split; [exact Hfst | exact Hsnd]].
    unfold state_to_dfs_tree in Hedge |- *.
    simpl in *.
    destruct Hedge as [v [Hvis [Hfa_neq [Hfst_fa Hsnd_v]]]].
    exists v.
    split.
    - apply (proj2 (Hvisited v)). exact Hvis.
    - split.
      + intro Hbad.
        apply Hfa_neq.
        rewrite Hfa in Hbad.
        exact Hbad.
      + split.
        * rewrite Hfa. exact Hfst_fa.
        * exact Hsnd_v.
  Qed.

  Lemma dfs_tree_reachable_transport_from_stable_fields:
    forall snap s x y,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, fa s z = fa snap z) ->
      dg_reachable (state_to_dfs_tree g snap root) x y ->
      dg_reachable (state_to_dfs_tree g s root) x y.
  Proof.
    intros snap s x y Hvisited Hfa Hreach.
    unfold dg_reachable in *.
    induction Hreach as [x0 y0 Hstep | x0 | x0 y0 z0 Hxy IHxy Hyz IHyz].
    - apply Coq.Relations.Relation_Operators.rt_step.
      eapply dfs_tree_step_transport_from_stable_fields; eauto.
    - apply Coq.Relations.Relation_Operators.rt_refl.
    - eapply Coq.Relations.Relation_Operators.rt_trans; eauto.
  Qed.

  Lemma dfs_tree_step_transport_from_monotone_fields:
    forall snap s x y,
      (forall z, Visited z snap -> Visited z s) ->
      (forall z, Visited z snap -> fa s z = fa snap z) ->
      dg_step (state_to_dfs_tree g snap root) x y ->
      dg_step (state_to_dfs_tree g s root) x y.
  Proof.
    unfold Visited.
    intros snap s x y Hvisited Hfa Hstep.
    unfold dg_step in Hstep |- *.
    destruct Hstep as [e [Hedge [Hfst Hsnd]]].
    exists e.
    split; [| split; [exact Hfst | exact Hsnd]].
    unfold state_to_dfs_tree in Hedge |- *.
    simpl in *.
    destruct Hedge as [v [Hvis [Hfa_neq [Hfst_fa Hsnd_v]]]].
    exists v.
    split.
    - apply Hvisited. exact Hvis.
    - split.
      + intro Hbad.
        apply Hfa_neq.
        rewrite <- (Hfa v Hvis).
        exact Hbad.
      + split.
        * rewrite (Hfa v Hvis). exact Hfst_fa.
        * exact Hsnd_v.
  Qed.

  Lemma dfs_tree_reachable_transport_from_monotone_fields:
    forall snap s x y,
      (forall z, Visited z snap -> Visited z s) ->
      (forall z, Visited z snap -> fa s z = fa snap z) ->
      dg_reachable (state_to_dfs_tree g snap root) x y ->
      dg_reachable (state_to_dfs_tree g s root) x y.
  Proof.
    intros snap s x y Hvisited Hfa Hreach.
    unfold dg_reachable in *.
    induction Hreach as [x0 y0 Hstep | x0 | x0 y0 z0 Hxy IHxy Hyz IHyz].
    - apply Coq.Relations.Relation_Operators.rt_step.
      eapply dfs_tree_step_transport_from_monotone_fields; eauto.
    - apply Coq.Relations.Relation_Operators.rt_refl.
    - eapply Coq.Relations.Relation_Operators.rt_trans; eauto.
  Qed.

  Lemma dfs_tree_reachable_unvisited_endpoint_eq:
    forall s x y,
      dg_reachable (state_to_dfs_tree g s root) x y ->
      ~ Visited y s ->
      x = y.
  Proof.
    intros s x y Hreach.
    unfold dg_reachable in Hreach.
    induction Hreach as [x0 y0 Hstep | x0 | x0 y0 z0 Hxy IHxy Hyz IHyz].
    - intro Hnot_vis.
      apply tree_step_char in Hstep as [_ [_ Hvis_y]].
      exfalso. apply Hnot_vis. exact Hvis_y.
    - intros _Hnot_vis. reflexivity.
    - intro Hnot_vis_z.
      assert (Hy_eq_z: y0 = z0).
      { apply IHyz. exact Hnot_vis_z. }
      subst z0.
      apply IHxy. exact Hnot_vis_z.
  Qed.

  Lemma dfs_tree_reachable_dfn_le:
    forall s x y,
      GlobalShapeCandidate s ->
      dg_reachable (state_to_dfs_tree g s root) x y ->
      dfn s x <= dfn s y.
  Proof.
    unfold GlobalShapeCandidate, wf_scc_state.
    intros s x y [_Hstack [_Hdfn_inv [Hdfn_valid _Hfa]]] Hreach.
    induction Hreach as [x0 y0 Hstep | x0 | x0 y0 z0 _ IHxy _ IHyz].
    - pose proof (Hdfn_valid x0 y0 Hstep). lia.
    - lia.
    - lia.
  Qed.

  Lemma dfs_tree_reachable_endpoint_visited:
    forall s x y,
      Visited x s ->
      dg_reachable (state_to_dfs_tree g s root) x y ->
      Visited y s.
  Proof.
    intros s x y Hvis_x Hreach.
    induction Hreach as [x0 y0 Hstep | x0 | x0 y0 z0 _ IHxy _ IHyz].
    - apply tree_step_char in Hstep as [_ [_ Hvis_y]].
      exact Hvis_y.
    - exact Hvis_x.
    - apply IHyz. apply IHxy. exact Hvis_x.
  Qed.

  Lemma dg_reachable_last_step_candidate
        (T: OriginalGraphType V E) (x y: V):
    x <> y ->
    dg_reachable T x y ->
    exists p, dg_reachable T x p /\ dg_step T p y.
  Proof.
    intros Hneq Hreach.
    unfold dg_reachable in Hreach.
    induction Hreach as
      [x0 y0 Hstep | x0 | x0 y0 z0 Hxy IHxy Hyz IHyz].
    - exists x0.
      split.
      + apply Coq.Relations.Relation_Operators.rt_refl.
      + exact Hstep.
    - exfalso. apply Hneq. reflexivity.
    - destruct (classic (y0 = z0)) as [Hy_z | Hy_z].
      + subst z0. apply IHxy. exact Hneq.
      + destruct (IHyz Hy_z) as [p [Hyp Hpz]].
        exists p.
        split.
        * eapply Coq.Relations.Relation_Operators.rt_trans; eauto.
        * exact Hpz.
  Qed.

  Lemma dfs_tree_direct_child_subtrees_disjoint:
    forall s parent left right x,
      GlobalShapeCandidate s ->
      Edge parent left ->
      fa s left = parent ->
      fa s left <> left ->
      Visited left s ->
      Edge parent right ->
      fa s right = parent ->
      fa s right <> right ->
      Visited right s ->
      dg_reachable (state_to_dfs_tree g s root) left x ->
      dg_reachable (state_to_dfs_tree g s root) right x ->
      left = right.
  Proof.
    intros s parent left right.
    intros x Hshape Hedge_left Hfa_left Hfa_neq_left Hvis_left
           Hedge_right Hfa_right Hfa_neq_right Hvis_right
           Hreach_left Hreach_right.
    pose proof Hshape as Hshape_unfold.
    unfold GlobalShapeCandidate, wf_scc_state in Hshape_unfold.
    destruct Hshape_unfold as [_Hstack [_Hdfn_inv [Hdfn_valid _Hfa]]].
    assert (Htree_parent_left:
              dg_step (state_to_dfs_tree g s root) parent left).
    { apply tree_step_char_backward; assumption. }
    assert (Htree_parent_right:
              dg_step (state_to_dfs_tree g s root) parent right).
    { apply tree_step_char_backward; assumption. }
    assert (Hdfn_parent_left: dfn s parent < dfn s left).
    { apply Hdfn_valid. exact Htree_parent_left. }
    assert (Hdfn_parent_right: dfn s parent < dfn s right).
    { apply Hdfn_valid. exact Htree_parent_right. }
    remember (dfn s x) as n eqn:Hn.
    revert x Hreach_left Hreach_right Hn.
    induction n as [n IH] using Wf_nat.lt_wf_ind.
    intros x Hreach_left Hreach_right Hn.
    destruct (equiv_dec x left) as [Hx_left | Hx_not_left].
    - rewrite Hx_left in Hreach_right.
      destruct (equiv_dec right left) as [Hright_left | Hright_not_left].
      + symmetry. exact Hright_left.
      + destruct
          (dg_reachable_last_step_candidate
             (state_to_dfs_tree g s root) right left
             Hright_not_left Hreach_right)
        as [p [Hreach_right_p Hstep_p_left]].
        apply tree_step_char in Hstep_p_left as [Hfa_left_p _].
        assert (Hp_parent: p = parent).
        { rewrite Hfa_left in Hfa_left_p.
          symmetry. exact Hfa_left_p. }
        subst p.
        rewrite Hfa_left in Hreach_right_p.
        pose proof
          (dfs_tree_reachable_dfn_le
             s right parent Hshape Hreach_right_p) as Hle.
          lia.
    - destruct (equiv_dec x right) as [Hx_right | Hx_not_right].
      + rewrite Hx_right in Hreach_left.
        destruct (equiv_dec left right) as [Hleft_right | Hleft_not_right].
        * exact Hleft_right.
        * destruct
            (dg_reachable_last_step_candidate
               (state_to_dfs_tree g s root) left right
               Hleft_not_right Hreach_left)
          as [p [Hreach_left_p Hstep_p_right]].
          apply tree_step_char in Hstep_p_right as [Hfa_right_p _].
          assert (Hp_parent: p = parent).
          { rewrite Hfa_right in Hfa_right_p.
            symmetry. exact Hfa_right_p. }
          subst p.
          rewrite Hfa_right in Hreach_left_p.
          pose proof
            (dfs_tree_reachable_dfn_le
               s left parent Hshape Hreach_left_p) as Hle.
          lia.
      + destruct
          (dg_reachable_last_step_candidate
             (state_to_dfs_tree g s root) left x
             (fun Hleft_x => Hx_not_left (eq_sym Hleft_x))
             Hreach_left)
          as [p_left [Hreach_left_p Hstep_p_left]].
        destruct
          (dg_reachable_last_step_candidate
             (state_to_dfs_tree g s root) right x
             (fun Hright_x => Hx_not_right (eq_sym Hright_x))
             Hreach_right)
          as [p_right [Hreach_right_p Hstep_p_right]].
        pose proof Hstep_p_left as Hstep_p_left_orig.
        apply tree_step_char in Hstep_p_left as [Hfa_x_left _].
        apply tree_step_char in Hstep_p_right as [Hfa_x_right _].
        assert (Hp_eq: p_left = p_right).
        { rewrite Hfa_x_left in Hfa_x_right.
          exact Hfa_x_right. }
        subst p_right.
        assert (Hdfn_p_lt: dfn s p_left < n).
        { subst n.
          pose proof (Hdfn_valid p_left x Hstep_p_left_orig). lia. }
        subst p_left.
        eapply (IH (dfn s (fa s x))); eauto.
  Qed.

  Lemma set_fa_unvisited_preserves_tree_reachable:
    forall child parent s x y,
      Unvisited child s ->
      (dg_reachable
         (state_to_dfs_tree g
            (RecordSet.set fa
               (fun fa0 z => if equiv_decb z child then parent else fa0 z) s)
            root) x y <->
       dg_reachable (state_to_dfs_tree g s root) x y).
  Proof.
    unfold Unvisited, Visited, dg_reachable.
    intros child parent s x y Hunvis.
    split; intro Hreach.
    - induction Hreach as [x0 y0 Hstep | x0 | x0 y0 z0 _ IHxy _ IHyz].
      + apply Coq.Relations.Relation_Operators.rt_step.
        apply (proj1
                 (set_fa_unvisited_preserves_tree_step
                    g root child parent x0 y0 s Hunvis)).
        exact Hstep.
      + apply Coq.Relations.Relation_Operators.rt_refl.
      + eapply Coq.Relations.Relation_Operators.rt_trans;
          [exact IHxy | exact IHyz].
    - induction Hreach as [x0 y0 Hstep | x0 | x0 y0 z0 _ IHxy _ IHyz].
      + apply Coq.Relations.Relation_Operators.rt_step.
        apply (proj2
                 (set_fa_unvisited_preserves_tree_step
                    g root child parent x0 y0 s Hunvis)).
        exact Hstep.
      + apply Coq.Relations.Relation_Operators.rt_refl.
      + eapply Coq.Relations.Relation_Operators.rt_trans;
          [exact IHxy | exact IHyz].
  Qed.

  Lemma set_fa_unvisited_preserves_scc_is_low_v:
    forall target child parent s,
      Unvisited child s ->
      scc_is_low_v g root s target ->
      scc_is_low_v g root
        (RecordSet.set fa
           (fun fa0 x => if equiv_decb x child then parent else fa0 x) s)
        target.
  Proof.
    unfold Unvisited, Visited, scc_is_low_v, scc_is_low_v_val.
    intros target child parent s Hunvis His_low.
    simpl.
    eapply (@min_eq_forward' _ le NatLe_TotalOrder).
    - exact His_low.
    - intros x Hx.
      exists x.
      split; [| reflexivity].
      unfold scc_low_tree, scc_low_reachable in Hx |- *.
      destruct Hx as [z [Hreach Hcase]].
      exists z.
      split.
      + apply (proj2
                 (set_fa_unvisited_preserves_tree_reachable
                    child parent s target z Hunvis)).
        exact Hreach.
      + destruct Hcase as [Hz_x | Hback].
        * left. exact Hz_x.
        * right.
          unfold scc_back_edge in Hback |- *.
          destruct Hback as [Hedge [Hactive Hnot_tree]].
          split; [exact Hedge |].
          split; [exact Hactive |].
          intro Htree_new.
          apply Hnot_tree.
          apply (proj1
                   (set_fa_unvisited_preserves_tree_step
                      g root child parent z x s Hunvis)).
          exact Htree_new.
    - intros x Hx.
      exists x.
      split; [| reflexivity].
      unfold scc_low_tree, scc_low_reachable in Hx |- *.
      destruct Hx as [z [Hreach Hcase]].
      exists z.
      split.
      + apply (proj1
                 (set_fa_unvisited_preserves_tree_reachable
                    child parent s target z Hunvis)).
        exact Hreach.
      + destruct Hcase as [Hz_x | Hback].
        * left. exact Hz_x.
        * right.
          unfold scc_back_edge in Hback |- *.
          destruct Hback as [Hedge [Hactive Hnot_tree]].
          split; [exact Hedge |].
          split; [exact Hactive |].
          intro Htree_old.
          apply Hnot_tree.
          apply (proj2
                   (set_fa_unvisited_preserves_tree_step
                      g root child parent z x s Hunvis)).
          exact Htree_old.
  Qed.

  Lemma set_low_other_preserves_scc_is_low_v:
    forall target changed n s,
      target <> changed ->
      scc_is_low_v g root s target ->
      scc_is_low_v g root
        (RecordSet.set low
           (fun low0 x => if equiv_decb x changed then n else low0 x) s)
        target.
  Proof.
    unfold scc_is_low_v, scc_is_low_v_val.
    intros target changed n s Hneq His_low.
    simpl.
    unfold equiv_decb.
    destruct (equiv_dec target changed) as [Heq | _].
    - exfalso. apply Hneq. exact Heq.
    - exact His_low.
  Qed.

  Lemma update_low_other_preserves_scc_is_low_v:
    forall target changed n,
      target <> changed ->
      Hoare
        (fun s => scc_is_low_v g root s target)
        (update_low changed n)
        (fun _ s => scc_is_low_v g root s target).
  Proof.
    intros target changed n Hneq.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst. simpl.
      apply set_low_other_preserves_scc_is_low_v; assumption.
    - destruct H1 as [Heq _]. subst. exact H.
  Qed.

  Lemma scc_back_edge_transport_post_to_snapshot:
    forall snap s x y,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, fa s z = fa snap z) ->
      (forall z, Active z s -> Active z snap) ->
      scc_back_edge g root s x y ->
      scc_back_edge g root snap x y.
  Proof.
    unfold scc_back_edge.
    intros snap s x y Hvisited Hfa Hactive_subset
           [Hedge [Hactive_y Hnot_tree]].
    split; [exact Hedge |].
    split; [apply Hactive_subset; exact Hactive_y |].
    intro Htree_snap.
    apply Hnot_tree.
    eapply dfs_tree_step_transport_from_stable_fields; eauto.
  Qed.

  Lemma scc_back_edge_transport_snapshot_to_post_for_lower_anchor:
    forall child snap s x y,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, fa s z = fa snap z) ->
      ChildLowerStackAnchorsPreservedCandidate child snap s ->
      dfn snap y < dfn snap child ->
      scc_back_edge g root snap x y ->
      scc_back_edge g root s x y.
  Proof.
    unfold scc_back_edge, ChildLowerStackAnchorsPreservedCandidate.
    intros child snap s x y Hvisited Hfa Hlower Hdfn_lt
           [Hedge [Hactive_y Hnot_tree]].
    split; [exact Hedge |].
    split; [eapply Hlower; eauto |].
    intro Htree_post.
    apply Hnot_tree.
    eapply dfs_tree_step_transport_from_stable_fields
      with (snap := s) (s := snap).
    - intros z. symmetry. apply Hvisited.
    - intros z. symmetry. apply Hfa.
    - exact Htree_post.
  Qed.

  Lemma scc_low_tree_transport_post_to_snapshot:
    forall child snap s x,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, fa s z = fa snap z) ->
      (forall z, Active z s -> Active z snap) ->
      scc_low_tree g root s child x ->
      scc_low_tree g root snap child x.
  Proof.
    unfold scc_low_tree, scc_low_reachable.
    intros child snap s x Hvisited Hfa Hactive_subset
           [z [Hreach Hcase]].
    exists z.
    split.
    - eapply dfs_tree_reachable_transport_from_stable_fields
        with (snap := s) (s := snap).
      + intros a. symmetry. apply Hvisited.
      + intros a. symmetry. apply Hfa.
      + exact Hreach.
    - destruct Hcase as [Hz_eq | Hback].
      + left. exact Hz_eq.
      + right.
        eapply scc_back_edge_transport_post_to_snapshot; eauto.
  Qed.

  Lemma scc_low_tree_snapshot_to_post_min_relation:
    forall child snap s x,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, dfn s z = dfn snap z) ->
      (forall z, fa s z = fa snap z) ->
      ChildLowerStackAnchorsPreservedCandidate child snap s ->
      scc_low_tree g root snap child x ->
      exists y,
        scc_low_tree g root s child y /\
        dfn s y <= dfn snap x.
  Proof.
    unfold scc_low_tree, scc_low_reachable.
    intros child snap s x Hvisited Hdfn Hfa Hlower
           [z [Hreach Hcase]].
    destruct Hcase as [Hz_eq | Hback].
    - exists x.
      split.
      + exists z.
        split.
        * eapply dfs_tree_reachable_transport_from_stable_fields; eauto.
        * left. exact Hz_eq.
      + rewrite Hdfn. lia.
    - destruct (le_gt_dec (dfn snap child) (dfn snap x))
        as [Hge | Hlt].
      + exists child.
        split.
        * exists child.
          split.
          -- apply Coq.Relations.Relation_Operators.rt_refl.
          -- left. reflexivity.
        * rewrite Hdfn. lia.
      + exists x.
        split.
        * exists z.
          split.
          -- eapply dfs_tree_reachable_transport_from_stable_fields; eauto.
          -- right.
             eapply scc_back_edge_transport_snapshot_to_post_for_lower_anchor;
               eauto.
        * rewrite Hdfn. lia.
  Qed.

  Lemma scc_low_tree_post_to_snapshot_min_relation:
    forall child snap s x,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, dfn s z = dfn snap z) ->
      (forall z, fa s z = fa snap z) ->
      (forall z, Active z s -> Active z snap) ->
      scc_low_tree g root s child x ->
      exists y,
        scc_low_tree g root snap child y /\
        dfn snap y <= dfn s x.
  Proof.
    intros child snap s x Hvisited Hdfn Hfa Hactive_subset Hlow_tree.
    exists x.
    split.
    - eapply scc_low_tree_transport_post_to_snapshot; eauto.
    - rewrite Hdfn. lia.
  Qed.

  Lemma scc_back_edge_union_snapshot_to_post_min_relation:
    forall child snap s x,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, dfn s z = dfn snap z) ->
      (forall z, fa s z = fa snap z) ->
      ChildLowerStackAnchorsPreservedCandidate child snap s ->
      x ∈ scc_back_edge g root snap child ∪ [child] ->
      exists y,
        y ∈ scc_back_edge g root s child ∪ [child] /\
        dfn s y <= dfn snap x.
  Proof.
    intros child snap s x Hvisited Hdfn Hfa Hlower Hx.
    sets_unfold in Hx.
    destruct Hx as [Hback | Hx_child].
    - destruct (le_gt_dec (dfn snap child) (dfn snap x))
        as [Hge | Hlt].
      + exists child.
        split; [sets_unfold; right; reflexivity |].
        rewrite Hdfn. lia.
      + exists x.
        split.
        * sets_unfold. left.
          eapply scc_back_edge_transport_snapshot_to_post_for_lower_anchor;
            eauto.
        * rewrite Hdfn. lia.
    - subst x.
      exists child.
      split; [sets_unfold; right; reflexivity |].
      rewrite Hdfn. lia.
  Qed.

  Lemma scc_back_edge_union_post_to_snapshot_min_relation:
    forall child snap s x,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, dfn s z = dfn snap z) ->
      (forall z, fa s z = fa snap z) ->
      (forall z, Active z s -> Active z snap) ->
      x ∈ scc_back_edge g root s child ∪ [child] ->
      exists y,
        y ∈ scc_back_edge g root snap child ∪ [child] /\
        dfn snap y <= dfn s x.
  Proof.
    intros child snap s x Hvisited Hdfn Hfa Hactive_subset Hx.
    exists x.
    split.
    - sets_unfold in Hx. sets_unfold.
      destruct Hx as [Hback | Hx_child].
      + left.
        eapply scc_back_edge_transport_post_to_snapshot; eauto.
      + right. exact Hx_child.
    - rewrite Hdfn. lia.
  Qed.

  Lemma ChildRootCorrectTransportFromStackShrinkCandidate_proof:
    ChildRootCorrectTransportFromStackShrinkCandidate_statement.
  Proof.
    unfold
      ChildRootCorrectTransportFromStackShrinkCandidate_statement,
      ChildRootCorrectTransportCandidate,
      ChildRootCorrectForParentCandidate,
      ChildLowValidForParentCandidate,
      ChildIsLowForParentCandidate.
    intros child snap s Hvisited Hdfn Hlow Hfa Hactive_subset Hlower
           [Hvalid His_low].
    split.
    - unfold scc_low_valid_v in Hvalid |- *.
      replace (low s child) with (low snap child) by (rewrite Hlow; reflexivity).
      eapply (@min_eq_forward' _ le NatLe_TotalOrder).
      + exact Hvalid.
      + intros n Hn.
        sets_unfold in Hn.
        destruct Hn as [Htree_min | Hback_min].
        * exists n.
          split; [left | lia].
          eapply (@min_eq_forward' _ le NatLe_TotalOrder).
          -- exact Htree_min.
          -- intros x Htree_x.
             exists x.
             split.
             ++ eapply dfs_tree_step_transport_from_stable_fields; eauto.
             ++ rewrite Hlow. lia.
          -- intros x Htree_x.
             exists x.
             split.
             ++ eapply dfs_tree_step_transport_from_stable_fields
                  with (snap := s) (s := snap).
                ** intros z. symmetry. apply Hvisited.
                ** intros z. symmetry. apply Hfa.
                ** exact Htree_x.
             ++ rewrite Hlow. lia.
        * exists n.
          split; [right | lia].
          eapply (@min_eq_forward' _ le NatLe_TotalOrder).
          -- exact Hback_min.
          -- intros x Hx.
             eapply scc_back_edge_union_snapshot_to_post_min_relation;
               eauto.
          -- intros x Hx.
             eapply scc_back_edge_union_post_to_snapshot_min_relation;
               eauto.
      + intros n Hn.
        sets_unfold in Hn.
        destruct Hn as [Htree_min | Hback_min].
        * exists n.
          split; [left | lia].
          eapply (@min_eq_forward' _ le NatLe_TotalOrder).
          -- exact Htree_min.
          -- intros x Htree_x.
             exists x.
             split.
             ++ eapply dfs_tree_step_transport_from_stable_fields
                  with (snap := s) (s := snap).
                ** intros z. symmetry. apply Hvisited.
                ** intros z. symmetry. apply Hfa.
                ** exact Htree_x.
             ++ rewrite Hlow. lia.
          -- intros x Htree_x.
             exists x.
             split.
             ++ eapply dfs_tree_step_transport_from_stable_fields; eauto.
             ++ rewrite Hlow. lia.
        * pose proof
            (min_nonempty_exists
               (dfn snap)
               (scc_back_edge g root snap child ∪ [child])) as Hpre_min.
          destruct Hpre_min as [m Hm].
          { exists child. sets_unfold. right. reflexivity. }
          exists m.
          split; [right; exact Hm |].
          unfold min_value_of_subset, min_object_of_subset in Hm.
          unfold min_value_of_subset, min_object_of_subset in Hback_min.
          destruct Hm as [pre_w [[Hpre_w Hpre_bound] Hm_eq]].
          destruct Hback_min as [post_w [[Hpost_w _Hpost_bound] Hn_eq]].
          subst m n.
          destruct
            (scc_back_edge_union_post_to_snapshot_min_relation
               child snap s post_w
               Hvisited Hdfn Hfa Hactive_subset Hpost_w)
            as [pre_y [Hpre_y Hle_y]].
          specialize (Hpre_bound pre_y Hpre_y).
          lia.
    - unfold scc_is_low_v, scc_is_low_v_val in His_low |- *.
      replace (low s child) with (low snap child) by (rewrite Hlow; reflexivity).
      eapply (@min_eq_forward' _ le NatLe_TotalOrder).
      + exact His_low.
      + intros x Hlow_tree.
        eapply scc_low_tree_snapshot_to_post_min_relation; eauto.
      + intros x Hlow_tree.
        eapply scc_low_tree_post_to_snapshot_min_relation; eauto.
  Qed.

  Lemma ChildRootCorrectTransportFromInactiveSelfLowCandidate_proof:
    ChildRootCorrectTransportFromInactiveSelfLowCandidate_statement.
  Proof.
    unfold
      ChildRootCorrectTransportFromInactiveSelfLowCandidate_statement,
      ChildRootCorrectTransportCandidate,
      ChildRootCorrectForParentCandidate,
      ChildLowValidForParentCandidate,
      ChildIsLowForParentCandidate,
      ChildInactiveSelfLowForParentCandidate.
    intros child snap s Hvisited Hdfn Hlow Hfa Hactive_subset
           Hinactive Hnot_active [Hvalid His_low].
    assert (Hself_snap: low snap child = dfn snap child).
    { apply Hinactive. exact Hnot_active. }
    assert (Hself_s: low s child = dfn s child).
    { rewrite Hlow. rewrite Hdfn. exact Hself_snap. }
    assert (Hback_bound_snap:
              forall y,
                y ∈ scc_back_edge g root snap child ∪ [child] ->
                dfn snap child <= dfn snap y).
    { intros y Hy.
      unfold scc_low_valid_v, min_value_of_subset,
        min_object_of_subset in Hvalid.
      destruct Hvalid as [n [[_ Houter_bound] Hn_eq]].
      pose proof
        (min_nonempty_exists
           (dfn snap)
           (scc_back_edge g root snap child ∪ [child])) as Hmin.
      destruct Hmin as [m Hm].
      { exists child. sets_unfold. right. reflexivity. }
      specialize (Houter_bound m (or_intror Hm)).
      destruct Hm as [w [[Hw Hm_bound] Hm_eq]].
      specialize (Hm_bound y Hy).
      rewrite <- Hself_snap.
      rewrite <- Hn_eq.
      eapply le_trans; [exact Houter_bound |].
      rewrite <- Hm_eq.
      exact Hm_bound. }
    assert (Htree_bound_snap:
              forall x,
                dg_step (state_to_dfs_tree g snap root) child x ->
                low snap child <= low snap x).
    { intros x Htree_x.
      unfold scc_low_valid_v, min_value_of_subset,
        min_object_of_subset in Hvalid.
      destruct Hvalid as [n [[_ Houter_bound] Hn_eq]].
      pose proof
        (min_nonempty_exists
           (low snap)
           (dg_step (state_to_dfs_tree g snap root) child)) as Hmin.
      destruct Hmin as [m Hm].
      { exists x. exact Htree_x. }
      specialize (Houter_bound m (or_introl Hm)).
      destruct Hm as [w [[Hw Hm_bound] Hm_eq]].
      specialize (Hm_bound x Htree_x).
      rewrite <- Hn_eq.
      eapply le_trans; [exact Houter_bound |].
      rewrite <- Hm_eq.
      exact Hm_bound. }
    split.
    - unfold scc_low_valid_v, min_value_of_subset, min_object_of_subset.
      exists (low s child).
      split.
      + split.
        * right.
          exists child.
          split.
          -- split.
             ++ sets_unfold. right. reflexivity.
             ++ intros y Hy.
                assert (Hy_snap:
                          y ∈ scc_back_edge g root snap child ∪ [child]).
                { sets_unfold in Hy. sets_unfold.
                  destruct Hy as [Hback | Hy_child].
                  - left.
                    eapply scc_back_edge_transport_post_to_snapshot; eauto.
                  - right. exact Hy_child. }
                specialize (Hback_bound_snap y Hy_snap).
                rewrite (Hdfn child). rewrite (Hdfn y).
                exact Hback_bound_snap.
          -- symmetry. exact Hself_s.
        * intros n Hn.
          destruct Hn as [Htree_min | Hback_min].
          -- unfold min_value_of_subset, min_object_of_subset in Htree_min.
             destruct Htree_min as [x [[Htree_x _Htree_bound] Hn_eq]].
             assert (Htree_snap:
                       dg_step (state_to_dfs_tree g snap root) child x).
             { eapply dfs_tree_step_transport_from_stable_fields
                 with (snap := s) (s := snap).
               - intros z. symmetry. apply Hvisited.
               - intros z. symmetry. apply Hfa.
               - exact Htree_x. }
             specialize (Htree_bound_snap x Htree_snap).
             rewrite Hlow.
             rewrite <- Hn_eq.
             rewrite Hlow.
             exact Htree_bound_snap.
          -- unfold min_value_of_subset, min_object_of_subset in Hback_min.
             destruct Hback_min as [x [[Hx _Hmin_x] Hn_eq]].
             assert (Hx_snap:
                       x ∈ scc_back_edge g root snap child ∪ [child]).
             { sets_unfold in Hx. sets_unfold.
               destruct Hx as [Hback | Hx_child].
               - left.
                 eapply scc_back_edge_transport_post_to_snapshot; eauto.
               - right. exact Hx_child. }
             specialize (Hback_bound_snap x Hx_snap).
             rewrite Hlow.
             rewrite Hself_snap.
             rewrite <- Hn_eq.
             rewrite (Hdfn x).
             exact Hback_bound_snap.
      + reflexivity.
    - unfold scc_is_low_v, scc_is_low_v_val,
        min_value_of_subset, min_object_of_subset.
      exists child.
      split.
      + split.
        * unfold scc_low_tree, scc_low_reachable.
          exists child.
          split.
          -- apply Coq.Relations.Relation_Operators.rt_refl.
          -- left. reflexivity.
        * intros x Hx.
          assert (Hx_snap: scc_low_tree g root snap child x).
          { eapply scc_low_tree_transport_post_to_snapshot; eauto. }
          pose proof
            (scc_low_bound g root snap child (low snap child) x
               His_low Hx_snap) as Hbound.
          rewrite Hself_snap in Hbound.
          rewrite (Hdfn child). rewrite (Hdfn x).
          exact Hbound.
      + symmetry. exact Hself_s.
  Qed.

  Lemma ProcessedTreeChildrenCorrectCandidate_transport_proof:
    ProcessedTreeChildrenCorrectCandidate_transport_statement.
  Proof.
    unfold ProcessedTreeChildrenCorrectCandidate_transport_statement,
      ProcessedTreeChildrenCorrectCandidate,
      ProcessedTreeChildrenLowValidCandidate,
      ProcessedTreeChildrenIsLowCandidate,
      ProcessedTreeChildrenInactiveSelfLowCandidate,
      ChildRootCorrectTransportCandidate,
      ChildRootCorrectForParentCandidate,
      ChildInactiveSelfLowForParentCandidate.
    intros u done snap s Hdfn Hlow
           [Hlow_valid [His_low Hinactive]] Htransport.
    split.
    - intros child Hdone_child Hedge_child Hfa_child Hfa_neq_child.
      specialize (Htransport child Hdone_child Hedge_child
                    Hfa_child Hfa_neq_child) as
        [Hfa_snap [Hfa_neq_snap [Hactive_surv Hroot_transport]]].
      specialize (Hroot_transport
                    (conj
                       (Hlow_valid child Hdone_child Hedge_child
                          Hfa_snap Hfa_neq_snap)
                       (His_low child Hdone_child Hedge_child
                          Hfa_snap Hfa_neq_snap))) as [Hvalid _].
      exact Hvalid.
    - split.
      + intros child Hdone_child Hedge_child Hfa_child Hfa_neq_child.
        specialize (Htransport child Hdone_child Hedge_child
                      Hfa_child Hfa_neq_child) as
          [Hfa_snap [Hfa_neq_snap [Hactive_surv Hroot_transport]]].
        specialize (Hroot_transport
                      (conj
                         (Hlow_valid child Hdone_child Hedge_child
                            Hfa_snap Hfa_neq_snap)
                         (His_low child Hdone_child Hedge_child
                            Hfa_snap Hfa_neq_snap))) as [_ His].
        exact His.
      + intros child Hdone_child Hedge_child Hfa_child Hfa_neq_child
               Hnot_active.
        specialize (Htransport child Hdone_child Hedge_child
                      Hfa_child Hfa_neq_child) as
          [Hfa_snap [Hfa_neq_snap [Hactive_surv _Hroot_transport]]].
        rewrite Hlow. rewrite Hdfn.
        apply Hinactive; try assumption.
        intro Hactive_snap.
        apply Hnot_active.
        exact (Hactive_surv Hactive_snap).
  Qed.

  Lemma ActiveProcessedChildSegmentSummaryCandidate_empty_proof:
    ActiveProcessedChildSegmentSummaryCandidate_empty_statement.
  Proof.
    unfold ActiveProcessedChildSegmentSummaryCandidate_empty_statement,
      ActiveProcessedChildSegmentSummaryCandidate.
    intros u s child Hempty.
    sets_unfold in Hempty. destruct Hempty.
  Qed.

  Lemma ActiveProcessedChildSegmentSummaryCandidate_step_child_proof:
    ActiveProcessedChildSegmentSummaryCandidate_step_child_statement.
  Proof.
    unfold ActiveProcessedChildSegmentSummaryCandidate_step_child_statement,
      ActiveProcessedChildSegmentSummaryCandidate,
      ParentResumeShapeCandidate,
      done_after.
    intros u done child s Hold
           [Hedge_child [Hnot_done_child [Hfa_child Hfa_child_neq]]]
           Hchild_segment.
    intros x Hdone_after Hedge_x Hfa_x Hfa_neq_x Hactive_x.
    sets_unfold in Hdone_after.
    destruct Hdone_after as [Hdone_x | Hx_child].
    - eapply Hold; eauto.
    - subst x.
      unfold ChildSelfSegmentEscapeSummaryCandidate,
        ChildSegmentSummaryCandidate,
        SegmentEscapeAccountingCandidate in Hchild_segment |- *.
      destruct (Hchild_segment Hactive_x) as [Hchild_escape _Hchild_cover].
      intros w Hchild_w Hnot_vis_w.
      specialize (Hchild_escape child w Hactive_x (le_n (dfn s child))
                    Hchild_w Hnot_vis_w) as [Hpending | Hanchor].
      + left. exact Hpending.
      + right. exact Hanchor.
  Qed.

  Lemma PreloopPreservesChildSelfSegmentEscapeSummaryCandidate_proof:
    PreloopPreservesChildSelfSegmentEscapeSummaryCandidate_statement.
  Proof.
    unfold PreloopPreservesChildSelfSegmentEscapeSummaryCandidate_statement,
      ChildSelfSegmentEscapeSummaryCandidate,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate,
      Active,
      GlobalShapeCandidate,
      Unvisited,
      Visited.
    intros child a.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s.
    destruct H as [Hshape [Ha_unvisited [Hactive_child Hself]]].
    simpl in *.
    assert (Hchild_neq_a: child <> a).
    { intro Hchild_a.
      apply Ha_unvisited.
      rewrite <- Hchild_a.
      unfold wf_scc_state in Hshape.
      destruct Hshape as [Hstack_vis _].
      apply Hstack_vis.
      exact Hactive_child. }
    match goal with
    | Hchild_z: dg_reachable g child ?z,
      Hnot_vis_z: ~ ?z ∈ _ |- _ =>
        assert (Hnot_vis_z_old: ~ z ∈ visited s0);
        [ intros Hvis_z_old;
          apply Hnot_vis_z;
          sets_unfold; left; exact Hvis_z_old
        | specialize (Hself z Hchild_z Hnot_vis_z_old) as
            [Hpending | Hanchor] ]
    end.
    - left.
      destruct Hpending as
        [next [Hchild_child [Hedge_next [Hnot_done_next Hreach_next_w]]]].
      exists next.
      split; [exact Hchild_child |].
      split; [exact Hedge_next |].
      split; [exact Hnot_done_next | exact Hreach_next_w].
    - right.
      destruct Hanchor as
        [anchor [Hactive_anchor [Hdfn_anchor_child
                  [Hlow_child_anchor [Hchild_anchor Hanchor_w]]]]].
      exists anchor.
      split.
      + simpl. right. exact Hactive_anchor.
      + split.
        * unfold equiv_decb.
          destruct (equiv_dec anchor a) as [Hanchor_a | Hanchor_neq_a].
          -- rewrite Hanchor_a in Hactive_anchor. exfalso.
             apply Ha_unvisited.
             unfold wf_scc_state in Hshape.
             destruct Hshape as [Hstack_vis _].
             apply Hstack_vis.
             exact Hactive_anchor.
          -- destruct (equiv_dec child a) as [Hchild_a | Hchild_neq_a'].
             ++ exfalso. apply Hchild_neq_a. exact Hchild_a.
             ++ exact Hdfn_anchor_child.
        * split.
          -- unfold equiv_decb.
             destruct (equiv_dec child a) as [Hchild_a | Hchild_neq_a'].
             ++ exfalso. apply Hchild_neq_a. exact Hchild_a.
             ++ destruct (equiv_dec anchor a) as
                  [Hanchor_a | Hanchor_neq_a].
                ** rewrite Hanchor_a in Hactive_anchor. exfalso.
                   apply Ha_unvisited.
                   unfold wf_scc_state in Hshape.
                   destruct Hshape as [Hstack_vis _].
                   apply Hstack_vis.
                   exact Hactive_anchor.
                ** exact Hlow_child_anchor.
          -- split; [exact Hchild_anchor | exact Hanchor_w].
  Qed.

  Lemma PreloopPreservesActiveProcessedChildSegmentSummaryCandidate_proof:
    PreloopPreservesActiveProcessedChildSegmentSummaryCandidate_statement.
  Proof.
    unfold PreloopPreservesActiveProcessedChildSegmentSummaryCandidate_statement.
    intros u done a.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s.
    destruct H as [Hshape [Hdone_vis [Hunvis_a Hactive_summaries]]].
    simpl in *.
    unfold ActiveProcessedChildSegmentSummaryCandidate in *.
    intros c Hdone_c Hedge_c Hfa_c Hfa_neq_c Hactive_c.
    assert (Hc_neq_a: c <> a).
    { intro Hc_a. subst c.
      apply Hunvis_a.
      apply (Hdone_vis a Hdone_c). }
    unfold Active in Hactive_c.
    simpl in Hactive_c.
    destruct Hactive_c as [Hc_eq_a | Hc_in_stack].
    - symmetry in Hc_eq_a. exfalso. apply Hc_neq_a. exact Hc_eq_a.
    - specialize (Hactive_summaries
                    c Hdone_c Hedge_c Hfa_c Hfa_neq_c Hc_in_stack).
      revert Hactive_summaries.
      unfold ChildSelfSegmentEscapeSummaryCandidate,
        PendingRootEscapeCandidate,
        OldStackEscapeAnchorCandidate.
      cbn [dfn low fa timer visited stack sccs].
      unfold equiv_decb.
      destruct (equiv_dec c a) as [Hc_a | _].
      { exfalso. apply Hc_neq_a. exact Hc_a. }
      intros Hactive_summaries.
      intros w Hc_w Hnot_vis_w_post.
      assert (Hnot_vis_w_pre: ~ w ∈ visited s0).
      { intros Hvis_w_pre.
        apply Hnot_vis_w_post.
        sets_unfold. left. exact Hvis_w_pre. }
      specialize (Hactive_summaries w Hc_w Hnot_vis_w_pre)
        as [Hpending | Hanchor].
      + left.
        destruct Hpending as
          [next [Hc_c [Hedge_next [Hnot_edge_next Hreach_next_w]]]].
        exists next.
        split; [exact Hc_c |].
        split; [exact Hedge_next |].
        split; [exact Hnot_edge_next | exact Hreach_next_w].
      + right.
        destruct Hanchor as
          [b0 [Hactive_b0 [Hdfn_b0_c [Hlow_c_b0 [Hc_b0 Hb0_w]]]]].
        destruct (equiv_dec b0 a) as [Hb0_a | Hb0_neq_a].
        * rewrite Hb0_a in Hactive_b0.
          exfalso.
          apply Hunvis_a.
          unfold GlobalShapeCandidate, wf_scc_state in Hshape.
          destruct Hshape as [Hstack_vis _].
          apply Hstack_vis. exact Hactive_b0.
        * exists b0.
          split.
          { unfold Active. simpl. right. exact Hactive_b0. }
	          split.
	          { simpl. unfold equiv_decb.
	            destruct (equiv_dec b0 a); try contradiction.
	            exact Hdfn_b0_c. }
	          split.
	          { simpl. unfold equiv_decb.
	            destruct (equiv_dec b0 a) as [Hb0_a' | _].
	            - exfalso. apply Hb0_neq_a. exact Hb0_a'.
	            - exact Hlow_c_b0. }
	          split; [exact Hc_b0 | exact Hb0_w].
  Qed.

  Lemma LoopEntryImpliesPhase6Candidate_proof:
    LoopEntryImpliesPhase6Candidate_statement.
  Proof.
    unfold LoopEntryImpliesPhase6Candidate_statement,
      LoopInvPhase6Candidate.
    intros u s Hlow Hframe Hclosed Hchildren Hsegments.
    split; [exact Hlow |].
    split; [exact Hframe |].
    split; [exact Hclosed |].
    split; [exact Hchildren | exact Hsegments].
  Qed.

  Lemma Phase6ChildPostExtendsLoopFieldsCandidate_proof:
    Phase6ChildPostExtendsLoopFieldsCandidate_statement.
  Proof.
    unfold Phase6ChildPostExtendsLoopFieldsCandidate_statement.
    intros u done child s Hclosed Hchildren Hsegments
           Hresume Hchild_root Hchild_inactive Hchild_closed Hchild_segment.
    split.
    - eapply DoneClosednessCandidate_step_child_proof; eauto.
    - split.
      + eapply ProcessedTreeChildrenCorrectCandidate_step_child_proof; eauto.
      + eapply ActiveProcessedChildSegmentSummaryCandidate_step_child_proof;
          eauto.
  Qed.

  Lemma ChildContractCandidate_from_field_statements_proof:
    ChildContractCandidate_from_field_statements_statement.
  Proof.
    unfold ChildContractCandidate_from_field_statements_statement,
      ProcessEdgeUnvisitedChildPostCandidate_statement,
      ChildReturnsVisitedCandidate_statement,
      ChildRootCorrectForParentCandidate_statement,
      ChildContractCandidate,
      ChildPostCandidate.
    intros Hfields W parent child done Hedge Hnot_done.
    destruct Hfields as [Hvisited Hfields].
    destruct Hfields as [Hroot Hfields].
    destruct Hfields as [Hinactive Hfields].
    destruct Hfields as [Hclosed Hfields].
    destruct Hfields as [Hsegment Hfields].
    destruct Hfields as [Hresume Hfields].
    destruct Hfields as [Hparent_pending Hactive_blocks].
    destruct Hroot as [Hlow_valid Hchild_is_low].
    unfold Hoare.
    intros s1 r s2 Hentry Hrun.
    pose proof
      (Hvisited W parent child done Hedge Hnot_done)
      as Hvisited_run.
    pose proof
      (Hlow_valid W parent child done Hedge Hnot_done)
      as Hlow_valid_run.
    pose proof
      (Hchild_is_low W parent child done Hedge Hnot_done)
      as Hchild_is_low_run.
    pose proof
      (Hinactive W parent child done Hedge Hnot_done)
      as Hinactive_run.
    pose proof
      (Hclosed W parent child done Hedge Hnot_done)
      as Hclosed_run.
    pose proof
      (Hsegment W parent child done Hedge Hnot_done)
      as Hsegment_run.
    pose proof
      (Hresume W parent child done Hedge Hnot_done)
      as Hresume_run.
    pose proof
      (Hparent_pending W parent child done Hedge Hnot_done)
      as Hparent_pending_run.
    pose proof
      (Hactive_blocks W parent child done Hedge Hnot_done)
      as Hactive_blocks_run.
    unfold Hoare in
      Hlow_valid_run,
      Hchild_is_low_run,
      Hinactive_run,
      Hclosed_run,
      Hsegment_run,
      Hresume_run,
      Hparent_pending_run,
      Hactive_blocks_run.
    split.
    - eapply Hvisited_run; eauto.
    - split.
      + eapply Hlow_valid_run; eauto.
      + split.
        * eapply Hchild_is_low_run; eauto.
        * split.
          -- eapply Hinactive_run; eauto.
          -- split.
             ++ eapply Hclosed_run; eauto.
             ++ split.
                ** intros Hactive.
                   exact (Hsegment_run s1 r s2 Hentry Hrun Hactive).
                ** split.
                   --- eapply Hresume_run; eauto.
                   --- split.
                       { eapply Hparent_pending_run; eauto. }
                       { eapply Hactive_blocks_run; eauto. }
  Qed.

  Lemma ChildContractCandidate_provides_returns_visited_proof:
    ChildContractCandidate_provides_returns_visited_statement.
  Proof.
    unfold ChildContractCandidate_provides_returns_visited_statement,
      ChildContractCandidate,
      ChildReturnsVisitedCandidate,
      ChildPostCandidate.
    intros W Hcontract parent child done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: { apply (Hcontract parent child done Hedge Hnot_done). }
    intros r s Hpost.
    exact (proj1 Hpost).
  Qed.

  Lemma ChildContractCandidate_provides_post_fields_proof:
    ChildContractCandidate_provides_post_fields_statement.
  Proof.
    unfold ChildContractCandidate_provides_post_fields_statement.
    intros W Hcontract.
    split.
    - eapply ChildContractCandidate_provides_returns_visited_proof.
      exact Hcontract.
    - split.
      + intros parent child done Hedge Hnot_done.
        eapply Hoare_conseq_post.
        2: { apply (Hcontract parent child done Hedge Hnot_done). }
        intros r s Hpost.
        unfold ChildPostCandidate in Hpost.
        destruct Hpost as [_ [Hlow_valid [Hchild_is_low _]]].
        unfold ChildRootCorrectForParentCandidate.
        split; assumption.
      + split.
        * intros parent child done Hedge Hnot_done.
          eapply Hoare_conseq_post.
          2: { apply (Hcontract parent child done Hedge Hnot_done). }
          intros r s Hpost.
          unfold ChildPostCandidate in Hpost.
          destruct Hpost as [_ [_ [_ [Hinactive _]]]].
          exact Hinactive.
        * split.
          -- intros parent child done Hedge Hnot_done.
             eapply Hoare_conseq_post.
             2: { apply (Hcontract parent child done Hedge Hnot_done). }
             intros r s Hpost.
             unfold ChildPostCandidate in Hpost.
             destruct Hpost as [_ [_ [_ [_ [Hclosed _]]]]].
             exact Hclosed.
          -- split.
             ++ intros parent child done Hedge Hnot_done.
                eapply Hoare_conseq_post.
                2: { apply (Hcontract parent child done Hedge Hnot_done). }
                intros r s Hpost.
                unfold ChildPostCandidate in Hpost.
                destruct Hpost as [_ [_ [_ [_ [_ [Hsegment _]]]]]].
                exact Hsegment.
             ++ intros parent child done Hedge Hnot_done.
                eapply Hoare_conseq_post.
                2: { apply (Hcontract parent child done Hedge Hnot_done). }
                intros r s Hpost.
                unfold ChildPostCandidate in Hpost.
                destruct Hpost as [_ [_ [_ [_ [_ [_ [Hresume _Htail]]]]]]].
                exact Hresume.
  Qed.

  (* ================================================================ *)
  (* Phase-7 root-bridge consumer audit proofs                        *)
  (* ================================================================ *)

  Lemma LoopDoneProvidesRootBridgeInputCandidate_proof:
    LoopDoneProvidesRootBridgeInputCandidate_statement.
  Proof.
    unfold LoopDoneProvidesRootBridgeInputCandidate_statement,
      LoopDonePhase6Candidate,
      RootBridgeInputCandidate,
      LoopInvPhase6Candidate,
      LoopInvLowCandidate,
      LoopInvDoneCandidate,
      RootLowEquationReadyCandidate,
      RootTreeChildrenLowValidReadyCandidate,
      RootTreeChildrenIsLowReadyCandidate,
      ProcessedTreeChildrenCorrectCandidate.
    intros u s Hloop.
    destruct Hloop as [Hlow [Hframe [Hclosed [Hchildren _]]]].
    destruct Hlow as [Hdone_loop Hpartial].
    destruct Hdone_loop as [Hlocal _].
    destruct Hchildren as [Hchildren_valid [Hchildren_is_low _Hchildren_inactive]].
    pose proof Hlocal as Hlocal_order.
    destruct Hlocal_order as [_ [_ [_ [_ Horder]]]].
    split; [exact Hlocal |].
    split; [exact Hclosed |].
    split; [exact Hframe |].
    split; [exact Hpartial |].
    split; [exact Hchildren_valid |].
    split; [exact Hchildren_is_low | exact Horder].
  Qed.

  Lemma RootBridgeInputProvidesLowValidInputCandidate_proof:
    RootBridgeInputProvidesLowValidInputCandidate_statement.
  Proof.
    unfold RootBridgeInputProvidesLowValidInputCandidate_statement,
      RootBridgeInputCandidate,
      RootBridgeLowValidInputCandidate.
    intros u s
      [Hlocal [Hclosed [Hframe [Hroot_eq [Hchildren_valid [_ Horder]]]]]].
    split; [exact Hlocal |].
    split; [exact Hclosed |].
    split; [exact Hframe |].
    split; [exact Hroot_eq |].
    split; [exact Hchildren_valid | exact Horder].
  Qed.

  Lemma RootBridgeInputProvidesIsLowInputCandidate_proof:
    RootBridgeInputProvidesIsLowInputCandidate_statement.
  Proof.
    unfold RootBridgeInputProvidesIsLowInputCandidate_statement,
      RootBridgeInputCandidate,
      RootBridgeIsLowInputCandidate,
      RootBridgeLowValidInputCandidate.
    intros u s
      [Hlocal [Hclosed [Hframe [Hroot_eq [Hchildren_valid [Hchildren_is_low Horder]]]]]].
    split.
    - split; [exact Hlocal |].
      split; [exact Hclosed |].
      split; [exact Hframe |].
      split; [exact Hroot_eq |].
      split; [exact Hchildren_valid | exact Horder].
    - exact Hchildren_is_low.
  Qed.

  Lemma RootBridgeLowValidInputBuildsLowIterationDoneCandidate_proof:
    RootBridgeLowValidInputBuildsLowIterationDoneCandidate_statement.
  Proof.
    unfold RootBridgeLowValidInputBuildsLowIterationDoneCandidate_statement,
      RootBridgeLowValidInputCandidate,
      LocalActiveRootCandidate,
      DoneClosednessCandidate,
      ParentFrameResumeCandidate,
      RootLowEquationReadyCandidate,
      PartialRootLowEquationCandidate,
      LowFrontierCandidate,
      LowSourceCandidate,
      RootTreeChildrenLowValidReadyCandidate,
      ProcessedTreeChildrenLowValidCandidate,
      OrderFactsCandidate,
      low_iteration_done,
      low_iteration_inv,
      done_visited,
      done_reachable_closed,
      done_tree_reachable_closed,
      low_frontier,
      low_src,
      children_low_valid,
      fa_child_of_u,
      fa_not_done_implies_eq_u.
    intros u s
      [[Hwf [Hsettled [Hvis [Hstack Horder]]]]
       [[Hclosed Htree_closed]
        [[Hdone_vis [Hfa_child Hfa_not]]
         [[Hfront Hsrc] [Hchildren_low_valid Horder_again]]]]].
    destruct Horder as [Horder_stack Horder_inj].
    split.
    - split; [exact Hwf |].
      split; [exact Hsettled |].
      split; [exact Hvis |].
      split; [exact Hstack |].
      split; [exact Hdone_vis |].
      split; [exact Hclosed |].
      split; [exact Htree_closed |].
      split; [exact Hfront |].
      split; [exact Hsrc |].
      split; [exact Hchildren_low_valid |].
      split; [exact Hfa_child | exact Hfa_not].
    - split; assumption.
  Qed.

  Lemma RootBridgeLowValidCandidate_proof:
    RootBridgeLowValidCandidate_statement.
  Proof.
    unfold RootBridgeLowValidCandidate_statement,
      RootLowValidPrePopCandidate.
    intros u s Hinput.
    apply low_frontier_and_src_imply_low_valid.
    apply RootBridgeLowValidInputBuildsLowIterationDoneCandidate_proof.
    exact Hinput.
  Qed.

  Lemma RootBridgeIsLowCandidate_proof:
    RootBridgeIsLowCandidate_statement.
  Proof.
    unfold RootBridgeIsLowCandidate_statement,
      RootBridgeIsLowInputCandidate,
      RootBridgeLowValidInputCandidate,
      LocalActiveRootCandidate,
      RootTreeChildrenIsLowReadyCandidate,
      ProcessedTreeChildrenIsLowCandidate,
      RootIsLowPrePopCandidate.
    intros u s
      [[[Hwf [Hsettled [Hvis [Hstack Horder]]]]
        [Hclosed [Hframe [Hroot_eq [Hchildren_valid Horder_again]]]]]
       Hchildren_is_low].
    apply scc_is_low_induction_is_low.
    - exact Hvis.
    - intros child Htree_child.
      pose proof Hframe as Hframe_child_edge.
      unfold ParentFrameResumeCandidate, fa_child_of_u in Hframe_child_edge.
      destruct Hframe_child_edge as [_ [Hfa_child_of_u _]].
      pose proof Htree_child as Htree_child_shape.
      apply tree_step_char in Htree_child_shape as
        [Hfa_child [Hfa_ne_child _]].
      assert (Hedge_child : edge_set u child).
      { apply Hfa_child_of_u. split; [exact Hfa_child | exact Hfa_ne_child]. }
      unfold ChildIsLowForParentCandidate in Hchildren_is_low.
      apply Hchildren_is_low.
      + exact Hedge_child.
      + exact Hedge_child.
      + exact Hfa_child.
      + exact Hfa_ne_child.
    - apply RootBridgeLowValidCandidate_proof.
      unfold RootBridgeLowValidInputCandidate,
        LocalActiveRootCandidate.
      split.
      + split; [exact Hwf |].
        split; [exact Hsettled |].
        split; [exact Hvis |].
        split; [exact Hstack | exact Horder].
      + split; [exact Hclosed |].
        split; [exact Hframe |].
        split; [exact Hroot_eq |].
        split; [exact Hchildren_valid | exact Horder_again].
  Qed.

  Lemma RootBridgePrePopCandidate_proof:
    RootBridgeLowValidCandidate_statement ->
    RootBridgeIsLowCandidate_statement ->
    RootBridgePrePopCandidate_statement.
  Proof.
    unfold RootBridgeLowValidCandidate_statement,
      RootBridgeIsLowCandidate_statement,
      RootBridgePrePopCandidate_statement,
      RootLowPrePopCandidate.
    intros Hvalid Hislow u s Hinput.
    split.
    - apply Hvalid.
      apply RootBridgeInputProvidesLowValidInputCandidate_proof.
      exact Hinput.
    - apply Hislow.
      apply RootBridgeInputProvidesIsLowInputCandidate_proof.
      exact Hinput.
  Qed.

  (* ================================================================ *)
  (* Phase-7 root-segment consumer audit proofs                       *)
  (* ================================================================ *)

  Lemma dg_reachable_first_nonself_step_candidate
        (T: OriginalGraphType V E) (u z: V):
    u <> z ->
    dg_reachable T u z ->
    exists v, dg_step T u v /\ v <> u /\ dg_reachable T v z.
  Proof.
    intros Hneq Hreach.
    remember u as start eqn:Hstart.
    revert u Hneq Hstart.
    induction Hreach as
      [x y Hstep | x | x y z Hxy IHxy Hyz IHyz];
      intros u Hneq Hstart; subst x.
    - exists y.
      split; [exact Hstep |].
      split.
      + intro Hy_u. subst y. apply Hneq. reflexivity.
      + apply Coq.Relations.Relation_Operators.rt_refl.
    - exfalso. apply Hneq. reflexivity.
    - destruct (classic (u = y)) as [Hu_y | Hu_not_y].
      + subst y.
        apply (IHyz u Hneq eq_refl).
      + destruct (IHxy u Hu_not_y eq_refl) as
          [v [Hstep_v [Hv_not_u Hreach_vy]]].
        exists v.
        split; [exact Hstep_v |].
        split; [exact Hv_not_u |].
        eapply Coq.Relations.Relation_Operators.rt_trans.
        * exact Hreach_vy.
        * exact Hyz.
  Qed.

  Lemma LoopEntryImpliesPhase7Candidate_proof:
    LoopEntryImpliesPhase7Candidate_statement.
  Proof.
    unfold LoopEntryImpliesPhase7Candidate_statement,
      LoopInvPhase7Candidate.
    intros u s Hphase6 Hescape Hcoverage Hblocks.
    split; [exact Hphase6 |].
    split; [exact Hescape |].
    split; [exact Hcoverage | exact Hblocks].
  Qed.

  Lemma PreloopProducesRootSegmentInitialCandidate_proof:
    PreloopProducesRootSegmentInitialCandidate_statement.
  Proof.
    unfold PreloopProducesRootSegmentInitialCandidate_statement,
      EntryPreCandidate,
      GlobalShapePreCandidate,
      RootSegmentInitialCandidate,
      Active.
    intro u.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [Hpre _].
    unfold wf_scc_state_pre, wf_scc_state in Hpre.
    destruct Hpre as [[Hstack_vis [Hdfn_inv _]] Hnot_vis_u].
    destruct Hdfn_inv as [Hdfn_lt _].
    simpl in H2, H3.
    destruct H2 as [Hx_u | Hx_stack].
    - symmetry. exact Hx_u.
    - assert (Hx_vis: x ∈ visited s0)
        by (apply Hstack_vis; exact Hx_stack).
      assert (Hx_lt: dfn s0 x < timer s0)
        by (apply Hdfn_lt; exact Hx_vis).
      assert (Hx_ne_u: x <> u)
        by (intro Hx_u; subst x; exact (Hnot_vis_u Hx_vis)).
      unfold equiv_decb in H3.
      destruct (equiv_dec u u) as [_ | Hu_neq].
      + destruct (equiv_dec x u) as [Hx_u_eq | _].
        * exfalso. apply Hx_ne_u. exact Hx_u_eq.
        * exfalso. lia.
      + exfalso. apply Hu_neq. reflexivity.
  Qed.

  Lemma PreloopFromChildEntryProducesRootSegmentInitialCandidate_proof:
    PreloopFromChildEntryProducesRootSegmentInitialCandidate_statement.
  Proof.
    unfold PreloopFromChildEntryProducesRootSegmentInitialCandidate_statement.
    intros parent child done.
    eapply Hoare_conseq_pre.
    2: { apply PreloopProducesRootSegmentInitialCandidate_proof. }
    intros s Hentry.
    eapply ChildEntryProvidesEntryPreCandidate_proof.
    exact Hentry.
  Qed.

  Lemma PreloopProducesParentFrameResumeEmptyCandidate_proof:
    PreloopProducesParentFrameResumeEmptyCandidate_statement.
  Proof.
    unfold PreloopProducesParentFrameResumeEmptyCandidate_statement,
      EntryPreCandidate,
      GlobalShapePreCandidate,
      ParentFrameResumeCandidate,
      done_visited,
      fa_child_of_u,
      fa_not_done_implies_eq_u.
    intro u.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [Hpre _].
    unfold wf_scc_state_pre, wf_scc_state in Hpre.
    destruct Hpre as [[_ [_ [_ Hfa_visited]]] Hnot_vis_u].
    split.
    - intros v Hempty. sets_unfold in Hempty. destruct Hempty.
    - split.
      + intros v [Hfa_v Hfa_neq].
        simpl in Hfa_v, Hfa_neq.
        apply Hfa_visited in Hfa_neq.
        rewrite Hfa_v in Hfa_neq.
        exfalso. apply Hnot_vis_u. exact Hfa_neq.
      + intros v _ Hfa_v.
        simpl in Hfa_v.
        destruct (equiv_dec v u) as [Hv_u | Hv_ne_u].
        * exact Hv_u.
        * exfalso.
          assert (Hfa_neq: fa s0 v <> v).
          { intro Hfa_self.
            apply Hv_ne_u.
            rewrite <- Hfa_self.
            exact Hfa_v. }
          apply Hfa_visited in Hfa_neq.
          rewrite Hfa_v in Hfa_neq.
          apply Hnot_vis_u. exact Hfa_neq.
  Qed.

  Lemma SegmentEscapeAccountingCandidate_empty_proof:
    SegmentEscapeAccountingCandidate_empty_statement.
  Proof.
    unfold SegmentEscapeAccountingCandidate_empty_statement,
      SegmentEscapeAccountingCandidate,
      RootSegmentInitialCandidate,
      LocalActiveRootCandidate,
      PendingRootEscapeCandidate.
    intros u s [_ [_ [Hvis_u _]]] Hinitial
           x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w.
    left.
    assert (Hx_eq_u: x = u) by (apply Hinitial; assumption).
    subst x.
    apply dg_reachable_first_step in Hreach_xw as
      [Hu_eq_w | [a [Hedge_ua Hreach_aw]]].
    - subst w. exfalso. apply Hnot_vis_w.
      exact Hvis_u.
    - exists a.
      split.
      + apply dg_reachable_refl'.
      + split; [exact Hedge_ua |].
        split.
        * intros Hempty. sets_unfold in Hempty. destruct Hempty.
        * exact Hreach_aw.
  Qed.

  Lemma SegmentTreeCoverageByDoneCandidate_empty_proof:
    SegmentTreeCoverageByDoneCandidate_empty_statement.
  Proof.
    unfold SegmentTreeCoverageByDoneCandidate_empty_statement,
      SegmentTreeCoverageByDoneCandidate,
      RootSegmentInitialCandidate,
      ProcessedTreeReachableFromCandidate.
    intros u s Hinitial x Hactive_x Hdfn_x.
    left. apply Hinitial; assumption.
  Qed.

  Lemma ActiveTargetSegmentEscapeAccountedCandidate_empty_proof:
    ActiveTargetSegmentEscapeAccountedCandidate_empty_statement.
  Proof.
    unfold ActiveTargetSegmentEscapeAccountedCandidate_empty_statement,
      ActiveTargetSegmentEscapeAccountedCandidate,
      LocalActiveRootCandidate,
      RootSegmentInitialCandidate,
      PendingRootEscapeCandidate,
      done_after.
    intros u s [_Hshape [_Hsettled [Hvis_u _Hactive_u]]]
           Hinitial a w Hactive_a Hdfn_a _Hcovered Hreach_aw Hnot_vis_w.
    assert (Ha_u: a = u) by (apply Hinitial; assumption).
    subst a.
    left.
    assert (Hu_not_w: u <> w).
    { intro Hu_w. subst w. apply Hnot_vis_w. exact Hvis_u. }
    destruct (dg_reachable_first_nonself_step_candidate g u w
                Hu_not_w Hreach_aw) as
      [next [Hedge_next [Hnext_not_u Hreach_next_w]]].
    exists next.
    split; [apply dg_reachable_refl' |].
    split; [exact Hedge_next |].
    split.
    - intros Hdone_next.
      sets_unfold in Hdone_next.
      destruct Hdone_next as [Hempty | Hnext_u].
      + destruct Hempty.
      + apply Hnext_not_u. symmetry. exact Hnext_u.
    - exact Hreach_next_w.
  Qed.

  Lemma ActiveTargetBlocksEscapeAccountedCandidate_empty_proof:
    forall u s,
      LocalActiveRootCandidate u s ->
      RootSegmentInitialCandidate u s ->
      ActiveTargetBlocksEscapeAccountedCandidate u ∅ s.
  Proof.
    unfold ActiveTargetBlocksEscapeAccountedCandidate,
      ActiveTargetBlockEscapeAccountedCandidate,
      LocalActiveRootCandidate,
      RootSegmentInitialCandidate,
      PendingRootEscapeCandidate.
    intros u s [_Hshape [_Hsettled [Hvis_u _Hactive_u]]] Hinitial
           block a w Hblock_a Hblock_valid Hreach_aw Hnot_vis_w.
    assert (Ha_u: a = u).
    { specialize (Hblock_valid a Hblock_a) as
        [_Hedge_a [_Hnot_done_a [Hactive_a Hdfn_a]]].
      apply Hinitial; assumption. }
    subst a.
    left.
    assert (Hu_not_w: u <> w).
    { intro Hu_w. subst w. apply Hnot_vis_w. exact Hvis_u. }
    destruct (dg_reachable_first_nonself_step_candidate g u w
                Hu_not_w Hreach_aw) as
      [next [Hedge_next [Hnext_not_u Hreach_next_w]]].
    exists next.
    split; [apply dg_reachable_refl' |].
    split; [exact Hedge_next |].
    split.
    - intros Hdone_next.
      sets_unfold in Hdone_next.
      destruct Hdone_next as [Hempty | Hblock_next].
      + destruct Hempty.
      + specialize (Hblock_valid next Hblock_next) as
          [_Hedge_next [_Hnot_done_next
           [Hactive_next Hdfn_next]]].
        assert (Hnext_u: next = u) by (apply Hinitial; assumption).
        apply Hnext_not_u. exact Hnext_u.
    - exact Hreach_next_w.
  Qed.

  Lemma ActiveTargetBlocksProvideActiveEdgeTargetCandidate_proof:
    forall u done s,
      ActiveTargetBlocksEscapeAccountedCandidate u done s ->
      ActiveEdgeTargetSegmentEscapeAccountedCandidate u done s.
  Proof.
    unfold ActiveTargetBlocksEscapeAccountedCandidate,
      ActiveTargetBlockEscapeAccountedCandidate,
      ActiveEdgeTargetSegmentEscapeAccountedCandidate,
      done_after.
    intros u done s Hblocks a w Hedge Hnot_done Hactive Hdfn
           Hreach Hnot_vis.
    specialize (Hblocks [a] a w).
    eapply Hblocks.
    - sets_unfold. reflexivity.
    - intros b Hb.
      sets_unfold in Hb.
      subst b.
      repeat split; assumption.
    - exact Hreach.
    - exact Hnot_vis.
  Qed.

  Lemma PreloopProducesLoopInvPhase7InitialCandidate_proof:
    PreloopProducesLoopInvPhase7InitialCandidate_statement.
  Proof.
    unfold PreloopProducesLoopInvPhase7InitialCandidate_statement.
    intro u.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s => LoopEntryBaseCandidate u s)
        (Q2 := fun _ s =>
                 ParentFrameResumeCandidate u ∅ s /\
                 RootSegmentInitialCandidate u s).
      - apply PreloopEntryBaseCandidate_proof.
      - apply Hoare_conj.
        + apply PreloopProducesParentFrameResumeEmptyCandidate_proof.
        + apply PreloopProducesRootSegmentInitialCandidate_proof. }
    intros _ s [Hentry [Hframe Hroot_segment]].
    apply LoopEntryImpliesPhase7Candidate_proof.
    - apply LoopEntryImpliesPhase6Candidate_proof.
      + apply LoopEntryImpliesLowCandidate_proof. exact Hentry.
      + exact Hframe.
      + apply DoneClosednessCandidate_empty_proof.
      + apply ProcessedTreeChildrenCorrectCandidate_empty_proof.
      + apply ActiveProcessedChildSegmentSummaryCandidate_empty_proof.
    - apply SegmentEscapeAccountingCandidate_empty_proof.
      + apply LoopEntryImpliesLocalActiveRootCandidate_proof. exact Hentry.
      + exact Hroot_segment.
    - apply SegmentTreeCoverageByDoneCandidate_empty_proof.
      exact Hroot_segment.
    - apply ActiveTargetBlocksEscapeAccountedCandidate_empty_proof.
      + apply LoopEntryImpliesLocalActiveRootCandidate_proof. exact Hentry.
      + exact Hroot_segment.
  Qed.

  Lemma PreloopFromChildEntryProducesLoopInvPhase7InitialCandidate_proof:
    PreloopFromChildEntryProducesLoopInvPhase7InitialCandidate_statement.
  Proof.
    unfold PreloopFromChildEntryProducesLoopInvPhase7InitialCandidate_statement.
    intros parent child done.
    eapply Hoare_conseq_pre.
    2: { apply PreloopProducesLoopInvPhase7InitialCandidate_proof. }
    intros s Hentry.
    eapply ChildEntryProvidesEntryPreCandidate_proof.
    exact Hentry.
  Qed.

  Lemma Phase7ChildPostExtendsLoopFieldsCandidate_proof:
    SegmentEscapeAccountingCandidate_step_child_statement ->
    Phase7ChildPostExtendsLoopFieldsCandidate_statement.
  Proof.
    unfold SegmentEscapeAccountingCandidate_step_child_statement,
      Phase7ChildPostExtendsLoopFieldsCandidate_statement.
    intros Hstep u done child s Hescape Hpending_child.
    eapply Hstep; eauto.
  Qed.

  Lemma SegmentEscapeAccountingCandidate_step_child_from_lift_proof:
    ChildSegmentEscapeLiftsToParentCandidate_statement ->
    SegmentEscapeAccountingCandidate_step_child_statement.
  Proof.
    unfold ChildSegmentEscapeLiftsToParentCandidate_statement,
      SegmentEscapeAccountingCandidate_step_child_statement.
    intros Hlift u done child s Hescape Hpending_child.
    eapply Hlift; eauto.
  Qed.

  Lemma ChildSegmentEscapeLiftsToParentCandidate_proof:
    ChildSegmentEscapeLiftsToParentCandidate_statement.
  Proof.
    unfold ChildSegmentEscapeLiftsToParentCandidate_statement,
      SegmentEscapeAccountingCandidate,
      ParentPendingChildEscapeAccountedCandidate,
      PendingRootEscapeCandidate,
      done_after.
    intros u done child s Hpending_child Hescape
           x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w.
    specialize (Hescape x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w)
      as [Hpending | Hanchor].
    - destruct Hpending as
        [a [Hxu [Hedge_a [Hnot_done_a Hreach_aw]]]].
      destruct (equiv_dec a child) as [Ha_eq_child | Ha_neq_child].
      + rewrite Ha_eq_child in Hedge_a, Hreach_aw.
        apply Hpending_child; assumption.
      + left. exists a.
        split; [exact Hxu |].
        split; [exact Hedge_a |].
        split; [| exact Hreach_aw].
        intros Hdone_after.
        apply Hnot_done_a.
        sets_unfold in Hdone_after.
        destruct Hdone_after as [Hdone_a | Ha_eq_child].
        * exact Hdone_a.
        * exfalso. apply Ha_neq_child. symmetry. exact Ha_eq_child.
    - right. exact Hanchor.
  Qed.

  Lemma SegmentEscapeAccountingCandidate_step_child_proof:
    SegmentEscapeAccountingCandidate_step_child_statement.
  Proof.
    apply SegmentEscapeAccountingCandidate_step_child_from_lift_proof.
    apply ChildSegmentEscapeLiftsToParentCandidate_proof.
  Qed.

  Lemma SegmentEscapeAccountingSuspendsCandidate_proof:
    SegmentEscapeAccountingSuspendsCandidate_statement.
  Proof.
    unfold SegmentEscapeAccountingSuspendsCandidate_statement,
      SuspendedSegmentEscapeAccountingCandidate,
      SegmentEscapeAccountingCandidate.
    intros u done child s Hsegment x w Hactive_x Hdfn_x
           _Houtside Hreach_xw Hnot_vis_w.
    eapply Hsegment; eauto.
  Qed.

  Lemma SegmentTreeCoverageSuspendsCandidate_proof:
    SegmentTreeCoverageSuspendsCandidate_statement.
  Proof.
    unfold SegmentTreeCoverageSuspendsCandidate_statement,
      SuspendedSegmentTreeCoverageByDoneCandidate,
      SegmentTreeCoverageByDoneCandidate.
    intros u done child s Hcoverage x Hactive_x Hdfn_x _Houtside.
    eapply Hcoverage; eauto.
  Qed.

  Lemma SegmentTreeCoverageClosesAfterChildCandidate_proof:
    SegmentTreeCoverageClosesAfterChildCandidate_statement.
  Proof.
    unfold SegmentTreeCoverageClosesAfterChildCandidate_statement,
      SegmentTreeCoverageByDoneCandidate,
      SuspendedSegmentTreeCoverageByDoneCandidate,
      ChildSegmentSummaryCandidate,
      SegmentCoverageByDoneCandidate,
      ProcessedReachableFromCandidate,
      ProcessedTreeReachableFromCandidate,
      PendingChildSegmentCandidate,
      done_after,
      edge_set.
    intros u done child s Hshape Hedge Hfa Hfa_neq Hchild_segment
           Hsuspended x Hactive_x Hdfn_u_x.
    destruct (classic (Visited child s /\ Active child s /\
                       dg_reachable (state_to_dfs_tree g s root) child x))
      as [Hin_child_segment | Houtside_child_segment].
    - destruct Hin_child_segment as [Hvis_child [Hactive_child Htree_child_x]].
      assert (Hdfn_child_x: dfn s child <= dfn s x).
      { unfold GlobalShapeCandidate, wf_scc_state in Hshape.
        destruct Hshape as [_ [_ [Hdfn_valid _]]].
        assert (Hreach_dfn:
                  forall y z,
                    dg_reachable (state_to_dfs_tree g s root) y z ->
                    dfn s y <= dfn s z).
        { intros y z Hreach.
          induction Hreach.
          - pose proof (Hdfn_valid x0 y H). lia.
          - apply le_n.
          - lia. }
        eapply Hreach_dfn. exact Htree_child_x. }
      specialize (Hchild_segment Hactive_child) as [_ Hchild_coverage].
      specialize (Hchild_coverage x Hactive_x Hdfn_child_x) as
        [Hx_child | [next [_Hdone_next [Hedge_child_next Hreach_next_x]]]].
      + right. exists child.
        split.
        * sets_unfold. right. reflexivity.
        * split; [exact Hedge |].
          split; [exact Hfa |].
          split; [exact Hfa_neq |].
          subst x.
          split; apply dg_reachable_refl'.
      + right. exists child.
        split.
        * sets_unfold. right. reflexivity.
        * split; [exact Hedge |].
          split; [exact Hfa |].
          split; [exact Hfa_neq |].
          split; [exact Htree_child_x |].
          eapply dg_reachable_trans.
          -- apply dg_reachable_step. exact Hedge_child_next.
          -- exact Hreach_next_x.
    - specialize (Hsuspended x Hactive_x Hdfn_u_x Houtside_child_segment)
        as [Hx_u | [v [Hdone_v [Hedge_v
          [Hfa_v [Hfa_neq_v [Htree_vx Hreach_vx]]]]]]].
      + left. exact Hx_u.
      + right. exists v.
        split.
        * sets_unfold. left. exact Hdone_v.
        * split; [exact Hedge_v |].
          split; [exact Hfa_v |].
          split; [exact Hfa_neq_v |].
          split; [exact Htree_vx | exact Hreach_vx].
  Qed.

  Lemma SuspendedSegmentEscapeAccountingClosesAfterChildCandidate_proof:
    SuspendedSegmentEscapeAccountingClosesAfterChildCandidate_statement.
  Proof.
    unfold SuspendedSegmentEscapeAccountingClosesAfterChildCandidate_statement,
      SuspendedSegmentEscapeAccountingCandidate,
      PendingChildSegmentEscapeAccountedCandidate,
      ParentPendingChildEscapeAccountedCandidate,
      SegmentEscapeAccountingCandidate,
      PendingRootEscapeCandidate,
      done_after.
    intros u done child s Hsuspended Hparent_pending Hchild_segment
           x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w.
    destruct (classic (PendingChildSegmentCandidate child s x)) as
      [Hin_child_segment | Houtside_child_segment].
    - eapply Hchild_segment; eauto.
    - specialize (Hsuspended x w Hactive_x Hdfn_x Houtside_child_segment
                    Hreach_xw Hnot_vis_w) as [Hpending | Hanchor].
      + destruct Hpending as
          [a [Hxu [Hedge_a [Hnot_done_a Hreach_aw]]]].
        destruct (equiv_dec a child) as [Ha_child | Ha_not_child].
        * rewrite Ha_child in Hedge_a, Hreach_aw.
          eapply Hparent_pending; eauto.
        * left. exists a.
          split; [exact Hxu |].
          split; [exact Hedge_a |].
          split.
          -- intros Hdone_after.
             apply Hnot_done_a.
             sets_unfold in Hdone_after.
             destruct Hdone_after as [Hdone_a | Ha_child].
             ++ exact Hdone_a.
             ++ exfalso. apply Ha_not_child. symmetry. exact Ha_child.
          -- exact Hreach_aw.
      + right. exact Hanchor.
  Qed.

  Lemma ParentPendingChildEscapeAccountedCandidate_from_closed_proof:
    ParentPendingChildEscapeAccountedCandidate_from_closed_statement.
  Proof.
    unfold ParentPendingChildEscapeAccountedCandidate_from_closed_statement,
      ParentPendingChildEscapeAccountedCandidate,
      ChildClosednessContributionCandidate.
    intros u done child s Hclosed Hnot_active
           x w _Hactive_x _Hdfn_x _Hxu Hchild_w Hnot_vis_w.
    exfalso.
    apply Hnot_vis_w.
    apply Hclosed; assumption.
  Qed.

  Lemma ParentPendingChildEscapeAccountedCandidate_from_old_anchor_proof:
    ParentPendingChildEscapeAccountedCandidate_from_old_anchor_statement.
  Proof.
    unfold ParentPendingChildEscapeAccountedCandidate_from_old_anchor_statement,
      ParentPendingChildEscapeAccountedCandidate,
      OldStackEscapeAnchorCandidate.
    intros u done child s Hedge Hactive_child Hdfn_lt Hlow_le
           x w _Hactive_x _Hdfn_x Hxu Hchild_w _Hnot_vis_w.
    right. exists child.
    split; [exact Hactive_child |].
    split; [exact Hdfn_lt |].
    split; [exact Hlow_le |].
    split.
    - eapply dg_reachable_trans.
      + exact Hxu.
      + apply dg_reachable_step. exact Hedge.
    - exact Hchild_w.
  Qed.

  Lemma ParentPendingChildEscapeAccountedCandidate_from_active_descendant_proof:
    ParentPendingChildEscapeAccountedCandidate_from_active_descendant_statement.
  Proof.
    unfold ParentPendingChildEscapeAccountedCandidate_from_active_descendant_statement,
      ParentPendingChildEscapeAccountedCandidate,
      ChildSelfPendingEscapeAccountedCandidate,
      SegmentEscapeAccountingCandidate,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate.
    intros u done child s Hedge Hescape Hactive_child Hdfn_child Hself
           x w Hactive_x Hdfn_x Hxu Hchild_w Hnot_vis_w.
    assert (Hreach_x_child: dg_reachable g x child).
    { eapply dg_reachable_trans.
      - exact Hxu.
      - apply dg_reachable_step. exact Hedge. }
    specialize (Hescape child w Hactive_child Hdfn_child Hchild_w Hnot_vis_w)
      as [Hpending_child | Hanchor_child].
    - destruct Hpending_child as
        [a [Hchild_u [Hedge_a [Hnot_done_a Hreach_aw]]]].
      destruct (equiv_dec a child) as [Ha_eq_child | Ha_neq_child].
      + rewrite Ha_eq_child in Hedge_a, Hreach_aw.
        specialize (Hself w Hchild_u Hchild_w Hnot_vis_w)
          as [Hpending_new | Hanchor_new].
        * left.
          destruct Hpending_new as
            [b [_Hchild_u_b [Hedge_b [Hnot_done_b Hreach_bw]]]].
          exists b.
          split; [exact Hxu |].
          split; [exact Hedge_b |].
          split; [exact Hnot_done_b | exact Hreach_bw].
        * right.
          destruct Hanchor_new as
            [b [Hactive_b [Hdfn_lt_b [Hlow_le_b [Hchild_b Hbw]]]]].
          exists b.
          split; [exact Hactive_b |].
          split; [exact Hdfn_lt_b |].
          split; [exact Hlow_le_b |].
          split.
          -- eapply dg_reachable_trans; [exact Hreach_x_child | exact Hchild_b].
          -- exact Hbw.
      + left. exists a.
        split; [exact Hxu |].
        split; [exact Hedge_a |].
        split.
        * intros Hdone_after.
          apply Hnot_done_a.
          sets_unfold in Hdone_after.
          destruct Hdone_after as [Hdone_a | Ha_eq_child].
          -- exact Hdone_a.
          -- exfalso. apply Ha_neq_child. symmetry. exact Ha_eq_child.
        * exact Hreach_aw.
    - right.
      destruct Hanchor_child as
        [b [Hactive_b [Hdfn_lt_b [Hlow_le_b [Hchild_b Hbw]]]]].
      exists b.
      split; [exact Hactive_b |].
      split; [exact Hdfn_lt_b |].
      split; [exact Hlow_le_b |].
      split.
      + eapply dg_reachable_trans; [exact Hreach_x_child | exact Hchild_b].
      + exact Hbw.
  Qed.

  Lemma ChildSelfPendingEscapeAccountedCandidate_from_child_summary_proof:
    ChildSelfPendingEscapeAccountedCandidate_from_child_summary_statement.
  Proof.
    unfold ChildSelfPendingEscapeAccountedCandidate_from_child_summary_statement,
      ChildSelfPendingEscapeAccountedCandidate,
      ChildSegmentSummaryCandidate,
      ChildOldAnchorLiftsToParentCandidate,
      SegmentEscapeAccountingCandidate,
      Edge,
      edge_set,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate.
    intros u done child s Hactive_child [Hchild_escape _Hchild_cover]
           Hanchor_lift w Hchild_u Hchild_w Hnot_vis_w.
    specialize (Hchild_escape child w Hactive_child (le_n (dfn s child))
                  Hchild_w Hnot_vis_w)
      as [Hpending_child | Hanchor_child].
    - destruct Hpending_child as
        [a [Hchild_child [Hedge_a [Hnot_done_a Hreach_aw]]]].
      exfalso. apply Hnot_done_a. exact Hedge_a.
    - destruct Hanchor_child as
        [b [Hactive_b [Hdfn_lt_b [Hlow_le_b [Hchild_b Hbw]]]]].
      eapply Hanchor_lift; eauto.
  Qed.

  Lemma ChildSelfSegmentEscapeSummaryCandidate_from_child_summary_proof:
    ChildSelfSegmentEscapeSummaryCandidate_from_child_summary_statement.
  Proof.
    unfold ChildSelfSegmentEscapeSummaryCandidate_from_child_summary_statement,
      ChildSelfSegmentEscapeSummaryCandidate,
      ChildSegmentSummaryCandidate,
      SegmentEscapeAccountingCandidate.
    intros child s Hactive_child [Hchild_escape _Hchild_cover]
           w Hchild_w Hnot_vis_w.
    exact (Hchild_escape child w Hactive_child (le_n (dfn s child))
             Hchild_w Hnot_vis_w).
  Qed.

  Lemma ChildSelfPendingEscapeAccountedCandidate_from_self_summary_proof:
    ChildSelfPendingEscapeAccountedCandidate_from_self_summary_statement.
  Proof.
    unfold ChildSelfPendingEscapeAccountedCandidate_from_self_summary_statement,
      ChildSelfPendingEscapeAccountedCandidate,
      ChildSelfSegmentEscapeSummaryCandidate,
      ChildOldAnchorLiftsToParentCandidate,
      Edge,
      edge_set,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate.
    intros u done child s Hself_summary Hanchor_lift
           w Hchild_u Hchild_w Hnot_vis_w.
    specialize (Hself_summary w Hchild_w Hnot_vis_w)
      as [Hpending_child | Hanchor_child].
    - destruct Hpending_child as
        [a [Hchild_child [Hedge_a [Hnot_done_a Hreach_aw]]]].
      exfalso. apply Hnot_done_a. exact Hedge_a.
    - destruct Hanchor_child as
        [b [Hactive_b [Hdfn_lt_b [Hlow_le_b [Hchild_b Hbw]]]]].
      eapply Hanchor_lift; eauto.
  Qed.

  Lemma PendingChildSegmentEscapeAccountedCandidate_from_child_summary_proof:
    PendingChildSegmentEscapeAccountedCandidate_from_child_summary_statement.
  Proof.
    unfold PendingChildSegmentEscapeAccountedCandidate_from_child_summary_statement,
      PendingChildSegmentEscapeAccountedCandidate,
      PendingChildSegmentOrderCandidate,
      PendingChildSegmentOldAnchorLiftsToParentCandidate,
      ChildSegmentSummaryCandidate,
      SegmentEscapeAccountingCandidate,
      PendingRootEscapeCandidate,
      edge_set,
      Edge.
    intros u done child s [Hchild_escape _Hchild_cover]
           Hsegment_order Hanchor_lift
           x w Hpending_child_x Hactive_x Hdfn_u_x Hreach_xw Hnot_vis_w.
    specialize (Hsegment_order x Hpending_child_x Hactive_x) as
      Hdfn_child_x.
    specialize (Hchild_escape x w Hactive_x Hdfn_child_x
                  Hreach_xw Hnot_vis_w) as [Hpending_child | Hanchor_child].
    - destruct Hpending_child as
        [a [_Hxu [Hedge_a [Hnot_edge_a _Hreach_aw]]]].
      exfalso. apply Hnot_edge_a. exact Hedge_a.
    - destruct Hanchor_child as
        [b [Hactive_b [Hdfn_b_child [Hlow_child_b [Hx_b Hb_w]]]]].
      eapply Hanchor_lift; eauto.
  Qed.

  Lemma PendingChildSegmentOrderCandidate_from_global_shape_proof:
    PendingChildSegmentOrderCandidate_from_global_shape_statement.
  Proof.
    unfold PendingChildSegmentOrderCandidate_from_global_shape_statement,
      PendingChildSegmentOrderCandidate,
      PendingChildSegmentCandidate,
      GlobalShapeCandidate,
      wf_scc_state.
    intros child s [_ [_ [Hdfn_valid _]]]
           x [_ [_ Htree_reach]] _Hactive_x.
    assert (Hreach_dfn:
              forall y z,
                dg_reachable (state_to_dfs_tree g s root) y z ->
                dfn s y <= dfn s z).
    { intros y z Hreach.
      induction Hreach.
      - pose proof (Hdfn_valid x0 y H).
        lia.
      - apply le_n.
      - lia. }
    eapply Hreach_dfn. exact Htree_reach.
  Qed.

  Lemma PendingChildSegmentOldAnchorLiftsToParentCandidate_from_all_older_segment_proof:
    PendingChildSegmentOldAnchorLiftsToParentCandidate_from_all_older_segment_statement.
  Proof.
    unfold
      PendingChildSegmentOldAnchorLiftsToParentCandidate_from_all_older_segment_statement,
      PendingChildSegmentOldAnchorLiftsToParentCandidate,
      PendingChildSegmentOldAnchorsBelowParentCandidate,
      OldStackEscapeAnchorCandidate.
    intros u done child s Hlow_u_child Hall_older
           x b w Hsegment_x Hactive_x Hactive_b Hdfn_b_child
           Hlow_child_b Hxb Hbw _Hnot_vis_w _Hdfn_u_x.
    right.
    exists b.
    split; [exact Hactive_b |].
    split.
    - eapply Hall_older; eauto.
    - split.
      + lia.
      + split; [exact Hxb | exact Hbw].
  Qed.

  Lemma PendingChildSegmentOldAnchorLiftsToParentCandidate_from_anchor_split_proof:
    PendingChildSegmentOldAnchorLiftsToParentCandidate_from_anchor_split_statement.
  Proof.
    unfold
      PendingChildSegmentOldAnchorLiftsToParentCandidate_from_anchor_split_statement,
      ParentLowBelowChildCandidate,
      PendingChildSegmentNonOlderAnchorAccountedByParentCandidate,
      PendingChildSegmentOldAnchorLiftsToParentCandidate,
      OldStackEscapeAnchorCandidate.
    intros u done child s Hlow_u_child Hnon_older_escape
           x b w Hsegment_x Hactive_x Hactive_b Hdfn_b_child
           Hlow_child_b Hxb Hbw Hnot_vis_w Hdfn_u_x.
    destruct (classic (dfn s b < dfn s u)) as
      [Hb_older_parent | Hb_not_older_parent].
    - right. exists b.
      split; [exact Hactive_b |].
      split; [exact Hb_older_parent |].
      split; [lia |].
      split; [exact Hxb | exact Hbw].
    - eapply Hnon_older_escape; eauto.
      lia.
  Qed.

  Lemma PendingChildSegmentNonOlderAnchorAccountedBySuspendedParent_proof:
    PendingChildSegmentNonOlderAnchorAccountedBySuspendedParent_statement.
  Proof.
    unfold
      PendingChildSegmentNonOlderAnchorAccountedBySuspendedParent_statement,
      PendingChildSegmentNonOlderAnchorAccountedByParentCandidate,
      PendingChildSegmentOrderCandidate,
      SuspendedSegmentEscapeAccountingCandidate,
      ParentPendingChildEscapeAccountedCandidate,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate,
      done_after.
    intros u done child s Horder Hsuspended Hparent_pending
           x b w Hsegment_x Hactive_x Hactive_b Hdfn_b_child
           Hlow_child_b Hxb Hbw Hnot_vis_w Hdfn_u_x Hdfn_u_b.
    assert (Houtside_b: ~ PendingChildSegmentCandidate child s b).
    { intros Hsegment_b.
      specialize (Horder b Hsegment_b Hactive_b).
      lia. }
    specialize (Hsuspended b w Hactive_b Hdfn_u_b Houtside_b Hbw Hnot_vis_w)
      as [Hpending_b | Hanchor_b].
    - destruct Hpending_b as
        [a [Hbu [Hedge_a [Hnot_done_a Haw]]]].
      destruct (equiv_dec a child) as [Ha_child | Ha_not_child].
      + assert (Hchild_w: dg_reachable g child w).
        { rewrite <- Ha_child. exact Haw. }
        assert (Hxu: dg_reachable g x u).
        { eapply dg_reachable_trans; [exact Hxb | exact Hbu]. }
        eapply Hparent_pending; eauto.
      + left. exists a.
        split.
        * eapply dg_reachable_trans; [exact Hxb | exact Hbu].
        * split; [exact Hedge_a |].
          split.
          -- intros Hdone_after.
             apply Hnot_done_a.
             sets_unfold in Hdone_after.
             destruct Hdone_after as [Hdone_a | Ha_child].
             ++ exact Hdone_a.
             ++ exfalso. apply Ha_not_child. symmetry. exact Ha_child.
          -- exact Haw.
    - right.
      destruct Hanchor_b as
        [c [Hactive_c [Hdfn_c_u [Hlow_u_c [Hbc Hcw]]]]].
      exists c.
      split; [exact Hactive_c |].
      split; [exact Hdfn_c_u |].
      split; [exact Hlow_u_c |].
      split.
      + eapply dg_reachable_trans; [exact Hxb | exact Hbc].
      + exact Hcw.
  Qed.

  Lemma PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_segment_producers_proof:
    PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_segment_producers_statement.
  Proof.
    unfold
      PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_segment_producers_statement.
    intros u done child s Hshape Hsummary Hlow_u_child Hall_older.
    eapply PendingChildSegmentEscapeAccountedCandidate_from_child_summary_proof.
    - exact Hsummary.
    - eapply PendingChildSegmentOrderCandidate_from_global_shape_proof.
      exact Hshape.
    - eapply
        PendingChildSegmentOldAnchorLiftsToParentCandidate_from_all_older_segment_proof;
        eauto.
  Qed.

  Lemma PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_anchor_split_proof:
    PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_anchor_split_statement.
  Proof.
    unfold
      PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_anchor_split_statement.
    intros u done child s Hshape Hsummary Hlow_u_child Hnon_older_escape.
    eapply PendingChildSegmentEscapeAccountedCandidate_from_child_summary_proof.
    - exact Hsummary.
    - eapply PendingChildSegmentOrderCandidate_from_global_shape_proof.
      exact Hshape.
    - eapply PendingChildSegmentOldAnchorLiftsToParentCandidate_from_anchor_split_proof;
        eauto.
  Qed.

  Lemma PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_suspended_parent_proof:
    PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_suspended_parent_statement.
  Proof.
    unfold
      PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_suspended_parent_statement.
    intros u done child s Hshape Hsummary Hlow_u_child
           Hsuspended Hparent_pending.
    eapply
      PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_anchor_split_proof;
      eauto.
    eapply PendingChildSegmentNonOlderAnchorAccountedBySuspendedParent_proof;
      eauto.
    eapply PendingChildSegmentOrderCandidate_from_global_shape_proof.
    exact Hshape.
  Qed.

  Lemma GetLowUpdateLowPreservesChildSegmentSummaryCandidate_proof:
    GetLowUpdateLowPreservesChildSegmentSummaryCandidate_statement.
  Proof.
    unfold GetLowUpdateLowPreservesChildSegmentSummaryCandidate_statement.
    intros u child Hchild_neq_u.
    apply Hoare_normalize.
    intros snap Hsummary.
    eapply Hoare_conseq_post.
    2: { apply (GetLowUpdateLowKeepsTraversalSnapshotCandidate_proof
                  u child snap). }
    intros _ s [Hvisited [Hdfn [Hfa [Hactive [Hlow_other _Hlow_u]]]]].
    unfold ChildSegmentSummaryCandidate in Hsummary |- *.
    destruct Hsummary as [Hescape Hcoverage].
    split.
    - unfold SegmentEscapeAccountingCandidate in Hescape |- *.
      intros x w Hactive_x Hdfn_child_x Hreach_xw Hnot_vis_w.
      assert (Hactive_x_snap: Active x snap).
      { apply Hactive. exact Hactive_x. }
      assert (Hdfn_child_x_snap: dfn snap child <= dfn snap x).
      { pose proof (Hdfn child). pose proof (Hdfn x). lia. }
      assert (Hnot_vis_w_snap: ~ Visited w snap).
      { intros Hvis_w_snap. apply Hnot_vis_w.
        apply Hvisited. exact Hvis_w_snap. }
      specialize (Hescape x w Hactive_x_snap Hdfn_child_x_snap
                    Hreach_xw Hnot_vis_w_snap) as [Hpending | Hanchor].
      + left. exact Hpending.
      + right.
        unfold OldStackEscapeAnchorCandidate in Hanchor |- *.
        destruct Hanchor as
          [b [Hactive_b [Hdfn_b_child [Hlow_child_b [Hxb Hbw]]]]].
        exists b.
        split.
        * apply Hactive. exact Hactive_b.
        * split.
          -- pose proof (Hdfn b). pose proof (Hdfn child). lia.
          -- split.
             ++ assert (Hchild_neq_u': child <> u).
                { exact Hchild_neq_u. }
                rewrite (Hlow_other child Hchild_neq_u').
                pose proof (Hdfn b). lia.
             ++ split; [exact Hxb | exact Hbw].
    - unfold SegmentCoverageByDoneCandidate in Hcoverage |- *.
      intros x Hactive_x Hdfn_child_x.
      assert (Hactive_x_snap: Active x snap).
      { apply Hactive. exact Hactive_x. }
      assert (Hdfn_child_x_snap: dfn snap child <= dfn snap x).
      { pose proof (Hdfn child). pose proof (Hdfn x). lia. }
      exact (Hcoverage x Hactive_x_snap Hdfn_child_x_snap).
  Qed.

  Lemma GetLowUpdateLowProducesNonOlderAnchorAccountedByParentCandidate_proof:
    GetLowUpdateLowProducesNonOlderAnchorAccountedByParentCandidate_statement.
  Proof.
    unfold
      GetLowUpdateLowProducesNonOlderAnchorAccountedByParentCandidate_statement.
    intros u done child Hchild_neq_u.
    apply Hoare_normalize.
    intros snap [Hshape [Hsuspended Hparent_pending]].
    pose proof (PendingChildSegmentOrderCandidate_from_global_shape_proof
                  child snap Hshape) as Horder_snap.
    eapply Hoare_conseq_post.
    2: { apply (GetLowUpdateLowKeepsTraversalSnapshotCandidate_proof
                  u child snap). }
    intros _ s [Hvisited [Hdfn [Hfa [Hactive [Hlow_other Hlow_u_old]]]]].
    unfold PendingChildSegmentNonOlderAnchorAccountedByParentCandidate.
    intros x b w _Hsegment_x Hactive_x Hactive_b Hdfn_b_child
           Hlow_child_b Hxb Hbw Hnot_vis_w Hdfn_u_x Hdfn_u_b.
    assert (Hactive_b_snap: Active b snap).
    { apply Hactive. exact Hactive_b. }
    assert (Hdfn_b_child_snap: dfn snap b < dfn snap child).
    { pose proof (Hdfn b). pose proof (Hdfn child). lia. }
    assert (Hdfn_u_b_snap: dfn snap u <= dfn snap b).
    { pose proof (Hdfn u). pose proof (Hdfn b). lia. }
    assert (Hnot_vis_w_snap: ~ Visited w snap).
    { intros Hvis_w_snap. apply Hnot_vis_w.
      apply Hvisited. exact Hvis_w_snap. }
    assert (Houtside_b_snap: ~ PendingChildSegmentCandidate child snap b).
    { intros Hsegment_b_snap.
      unfold PendingChildSegmentOrderCandidate in Horder_snap.
      specialize (Horder_snap b Hsegment_b_snap Hactive_b_snap).
      lia. }
    specialize (Hsuspended b w Hactive_b_snap Hdfn_u_b_snap
                  Houtside_b_snap Hbw Hnot_vis_w_snap)
      as [Hpending_b | Hanchor_b].
    - unfold PendingRootEscapeCandidate in Hpending_b.
      destruct Hpending_b as
        [a [Hbu [Hedge_a [Hnot_done_a Haw]]]].
      destruct (equiv_dec a child) as [Ha_child | Ha_not_child].
      + assert (Hchild_w: dg_reachable g child w).
        { rewrite <- Ha_child. exact Haw. }
        assert (Hactive_x_snap: Active x snap).
        { apply Hactive. exact Hactive_x. }
        assert (Hdfn_u_x_snap: dfn snap u <= dfn snap x).
        { pose proof (Hdfn u). pose proof (Hdfn x). lia. }
        assert (Hxu: dg_reachable g x u).
        { eapply dg_reachable_trans; [exact Hxb | exact Hbu]. }
        specialize (Hparent_pending x w Hactive_x_snap Hdfn_u_x_snap
                      Hxu Hchild_w Hnot_vis_w_snap) as
          [Hpending_parent | Hanchor_parent].
        * left. exact Hpending_parent.
        * right.
          unfold OldStackEscapeAnchorCandidate in Hanchor_parent |- *.
          destruct Hanchor_parent as
            [c [Hactive_c [Hdfn_c_u [Hlow_u_c [Hxc Hcw]]]]].
          exists c.
          split.
          -- apply Hactive. exact Hactive_c.
          -- split.
             ++ pose proof (Hdfn c). pose proof (Hdfn u). lia.
             ++ split.
                ** pose proof (Hdfn c). lia.
                ** split; [exact Hxc | exact Hcw].
      + left.
        unfold PendingRootEscapeCandidate.
        exists a.
        split.
        * eapply dg_reachable_trans; [exact Hxb | exact Hbu].
        * split; [exact Hedge_a |].
          split.
          -- intros Hdone_after.
             apply Hnot_done_a.
             sets_unfold in Hdone_after.
             destruct Hdone_after as [Hdone_a | Ha_child].
             ++ exact Hdone_a.
             ++ exfalso. apply Ha_not_child. symmetry. exact Ha_child.
          -- exact Haw.
    - right.
      unfold OldStackEscapeAnchorCandidate in Hanchor_b |- *.
      destruct Hanchor_b as
        [c [Hactive_c [Hdfn_c_u [Hlow_u_c [Hbc Hcw]]]]].
      exists c.
      split.
      + apply Hactive. exact Hactive_c.
      + split.
        * pose proof (Hdfn c). pose proof (Hdfn u). lia.
        * split.
          -- pose proof (Hdfn c). lia.
          -- split.
             ++ eapply dg_reachable_trans; [exact Hxb | exact Hbc].
             ++ exact Hcw.
  Qed.

  Lemma GetLowUpdateLowPreservesChildSegmentSummaryFromParentResumeCandidate_proof:
    GetLowUpdateLowPreservesChildSegmentSummaryFromParentResumeCandidate_statement.
  Proof.
    unfold
      GetLowUpdateLowPreservesChildSegmentSummaryFromParentResumeCandidate_statement.
    intros u done child.
    apply Hoare_normalize.
    intros snap [Hresume Hsummary].
    destruct Hresume as [_Hedge [_Hnot_done [Hfa Hfa_neq]]].
    assert (Hchild_neq_u: child <> u).
    { intro Hchild_u.
      apply Hfa_neq.
      rewrite <- Hchild_u in Hfa.
      exact Hfa. }
    eapply Hoare_conseq_pre.
    2: {
      apply
        (GetLowUpdateLowPreservesChildSegmentSummaryCandidate_proof
           u child Hchild_neq_u).
    }
    intros s Heq_s.
    subst s.
    exact Hsummary.
  Qed.

  Lemma GetLowUpdateLowProducesNonOlderAnchorAccountedByParentFromParentResumeCandidate_proof:
    GetLowUpdateLowProducesNonOlderAnchorAccountedByParentFromParentResumeCandidate_statement.
  Proof.
    unfold
      GetLowUpdateLowProducesNonOlderAnchorAccountedByParentFromParentResumeCandidate_statement.
    intros u done child.
    apply Hoare_normalize.
    intros snap [Hresume [Hshape [Hsuspended Hparent_pending]]].
    destruct Hresume as [_Hedge [_Hnot_done [Hfa Hfa_neq]]].
    assert (Hchild_neq_u: child <> u).
    { intro Hchild_u.
      apply Hfa_neq.
      rewrite <- Hchild_u in Hfa.
      exact Hfa. }
    eapply Hoare_conseq_pre.
    2: {
      apply
        (GetLowUpdateLowProducesNonOlderAnchorAccountedByParentCandidate_proof
           u done child Hchild_neq_u).
    }
    intros s Heq_s.
    subst s.
    split; [exact Hshape |].
    split; [exact Hsuspended | exact Hparent_pending].
  Qed.

  Lemma GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_proof:
    GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_statement.
  Proof.
    unfold
      GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_statement.
    intros u done child.
    apply Hoare_normalize.
    intros snap
           [Hshape [Hvis_u [Hresume [Hsummary
            [Hsuspended Hparent_pending]]]]].
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => GlobalShapeCandidate s)
             (Q2 := fun _ s =>
                      ChildSegmentSummaryCandidate child s /\
                      ParentLowBelowChildCandidate u child s /\
                      PendingChildSegmentNonOlderAnchorAccountedByParentCandidate
                        u done child s).
      - eapply Hoare_conseq_pre.
        2: {
          apply (GetLowUpdateLowPreservesGlobalShapeCandidate_proof u child).
        }
        intros s Heq_s.
        subst s.
        split; [exact Hshape | exact Hvis_u].
      - apply Hoare_conj
          with (Q1 := fun _ s => ChildSegmentSummaryCandidate child s)
               (Q2 := fun _ s =>
                        ParentLowBelowChildCandidate u child s /\
                        PendingChildSegmentNonOlderAnchorAccountedByParentCandidate
                          u done child s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (GetLowUpdateLowPreservesChildSegmentSummaryFromParentResumeCandidate_proof
                 u done child).
          }
          intros s Heq_s.
          subst s.
          split; [exact Hresume | exact Hsummary].
        + apply Hoare_conj
            with (Q1 := fun _ s => ParentLowBelowChildCandidate u child s)
                 (Q2 := fun _ s =>
                          PendingChildSegmentNonOlderAnchorAccountedByParentCandidate
                            u done child s).
          * eapply Hoare_conseq_pre.
            2: {
              apply (GetLowUpdateLowProducesParentLowBelowChildCandidate_proof
                       u child).
            }
            intros s _.
            exact I.
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (GetLowUpdateLowProducesNonOlderAnchorAccountedByParentFromParentResumeCandidate_proof
                   u done child).
            }
            intros s Heq_s.
            subst s.
            split; [exact Hresume |].
            split; [exact Hshape |].
            split; [exact Hsuspended | exact Hparent_pending].
    }
    intros _ s [Hshape_after
                 [Hsummary_after [Hlow_after Haccounted_after]]].
    eapply
      PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_anchor_split_proof;
      eauto.
  Qed.

  Lemma GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedConditionalCandidate_proof:
    forall u done child,
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           Visited u s /\
           ParentResumeShapeCandidate u child done s /\
           (Active child s -> ChildSegmentSummaryCandidate child s) /\
           SuspendedSegmentEscapeAccountingCandidate u child done s /\
           ParentPendingChildEscapeAccountedCandidate u done child s)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s => PendingChildSegmentEscapeAccountedCandidate u done child s).
  Proof.
    intros u done child.
    apply Hoare_normalize.
    intros snap [Hshape [Hvis_u [Hresume [Hsummary_if
      [Hsuspended Hparent_pending]]]]].
    destruct (classic (Active child snap)) as [Hactive_child | Hnot_active_child].
    - eapply Hoare_conseq_pre.
      2: {
        apply
          (GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_proof
             u done child).
      }
      intros s Heq_s.
      subst s.
      split; [exact Hshape |].
      split; [exact Hvis_u |].
      split; [exact Hresume |].
      split; [apply Hsummary_if; exact Hactive_child |].
      split; [exact Hsuspended | exact Hparent_pending].
    - eapply Hoare_conseq_post.
      2: {
        apply
          (GetLowUpdateLowKeepsTraversalSnapshotCandidate_proof u child snap).
      }
      intros _ s [Hvisited [_Hdfn [_Hfa [Hactive _Hlow]]]].
      unfold PendingChildSegmentEscapeAccountedCandidate,
        PendingChildSegmentCandidate.
      intros x w [_Hvis_child [Hactive_child_after _Htree_child_x]]
             _Hactive_x _Hdfn_u_x _Hreach_xw _Hnot_vis_w.
      exfalso.
      apply Hnot_active_child.
      apply Hactive. exact Hactive_child_after.
  Qed.

  Lemma ChildOldAnchorLiftsToParentCandidate_from_all_older_proof:
    ChildOldAnchorLiftsToParentCandidate_from_all_older_statement.
  Proof.
    unfold ChildOldAnchorLiftsToParentCandidate_from_all_older_statement,
      ChildOldAnchorLiftsToParentCandidate,
      OldStackEscapeAnchorCandidate.
    intros u done child s Hlow_u_child Hall_older
           b w Hactive_b Hdfn_lt_b Hlow_child_b Hchild_b Hbw _Hnot_vis_w.
    right. exists b.
    split; [exact Hactive_b |].
    split.
    - eapply Hall_older; eauto.
    - split.
      + lia.
      + split; [exact Hchild_b | exact Hbw].
  Qed.

  (* ================================================================ *)
  (* Phase-8 frame consumer audit proofs                              *)
  (* ================================================================ *)

  Lemma FrameCompatibleWithOwnCallCandidate_proof:
    FrameCompatibleWithOwnCallCandidate_statement.
  Proof.
    unfold FrameCompatibleWithOwnCallCandidate_statement,
      FrameCompatibleWithCallCandidate,
      FrameOfCallCandidate.
    intros parent child done s.
    simpl. left. split; reflexivity.
  Qed.

  Lemma FrameCompatibleWithPendingParentCandidate_proof:
    FrameCompatibleWithPendingParentCandidate_statement.
  Proof.
    unfold FrameCompatibleWithPendingParentCandidate_statement,
      FrameCompatibleWithCallCandidate.
    intros F direct_parent direct_child s Hpending.
    right. exact Hpending.
  Qed.

  Lemma update_low_preserves_frame_progress_candidate:
    forall F parent changed n,
      Hoare
        (FrameProgressCandidate F parent)
        (update_low changed n)
        (fun _ s => FrameProgressCandidate F parent s).
  Proof.
    intros F parent changed n.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst. simpl. exact H.
    - destruct H1 as [Heq _]. subst. exact H.
  Qed.

  Lemma get_low_update_low_preserves_frame_progress_candidate:
    forall F parent source changed,
      Hoare
        (FrameProgressCandidate F parent)
        (lv <- get' (fun s => low s source);; update_low changed lv)
        (fun _ s => FrameProgressCandidate F parent s).
  Proof.
    intros F parent source changed.
    apply Hoare_normalize. intros snap Hprogress.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: { apply update_low_preserves_frame_progress_candidate. }
    intros s [Heq_s _]. subst s. exact Hprogress.
  Qed.

  Lemma get_dfn_update_low_preserves_frame_progress_candidate:
    forall F parent source changed,
      Hoare
        (FrameProgressCandidate F parent)
        (dv <- get' (fun s => dfn s source);; update_low changed dv)
        (fun _ s => FrameProgressCandidate F parent s).
  Proof.
    intros F parent source changed.
    apply Hoare_normalize. intros snap Hprogress.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: { apply update_low_preserves_frame_progress_candidate. }
    intros s [Heq_s _]. subst s. exact Hprogress.
  Qed.

  Lemma set_fa_unvisited_preserves_frame_progress_candidate:
    forall F parent child,
      Hoare
        (fun s =>
           FrameProgressCandidate F parent s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s => FrameProgressCandidate F parent s).
  Proof.
    intros F parent child.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [[Hpending [Hparent_older Hdone_older]] Hunvis].
    unfold PendingChildSegmentCandidate in Hpending |- *.
    destruct Hpending as
      [Hvisited_frame_child [Hactive_frame_child Htree_frame_parent]].
    split.
    - split; [exact Hvisited_frame_child |].
      split; [exact Hactive_frame_child |].
      eapply dfs_tree_reachable_transport_from_monotone_fields
        with (snap := s0).
      + intros z Hvis_z. exact Hvis_z.
      + intros z Hvis_z.
        destruct (equiv_decb z child) eqn:Hz_child; simpl.
        * unfold equiv_decb in Hz_child.
          destruct (equiv_dec z child) as [Hz_eq | Hz_neq].
          -- exfalso. apply Hunvis. rewrite <- Hz_eq. exact Hvis_z.
          -- discriminate Hz_child.
        * rewrite Hz_child. reflexivity.
      + exact Htree_frame_parent.
    - split; [exact Hparent_older |].
      intros v Hdone_v Hactive_v.
      apply Hdone_older; assumption.
  Qed.

  Lemma ProcessEdgeVisitedActivePreservesFrameProgressCandidate_proof:
    forall W F child (done: V -> Prop) a,
      Hoare
        (fun s =>
           FrameProgressCandidate F child s /\
           Visited a s /\
           Active a s)
        (process_edge child W a)
        (fun _ s => FrameProgressCandidate F child s).
  Proof.
    intros W F child done a.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hunvis Heq_s]. subst s1.
      destruct H as [_ [Hvis _Hactive]].
      exfalso. apply Hunvis. exact Hvis.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_Hnot_unvis Heq_s]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: {
          apply
            (get_dfn_update_low_preserves_frame_progress_candidate
               F child a child).
        }
        intros s [Hactive_guard Heq_s]. subst s.
        exact (proj1 H).
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s Hnot_active].
        subst s.
        destruct H as [_ [_ Hactive]].
        exfalso. apply Hnot_active. exact Hactive.
  Qed.

  Lemma ProcessEdgeVisitedNonStackPreservesFrameProgressCandidate_proof:
    forall W F child (done: V -> Prop) a,
      Hoare
        (fun s =>
           FrameProgressCandidate F child s /\
           Visited a s /\
           ~ Active a s)
        (process_edge child W a)
        (fun _ s => FrameProgressCandidate F child s).
  Proof.
    intros W F child done a.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hunvis Heq_s]. subst s1.
      destruct H as [_ [Hvis _Hnot_active]].
      exfalso. apply Hunvis. exact Hvis.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_Hnot_unvis Heq_s]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        intro_state.
        destruct H1 as [Hactive_guard Heq_s]. subst s1.
        destruct H as [_ [_ Hnot_active]].
        exfalso. apply Hnot_active. exact Hactive_guard.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _Hnot_active_guard].
        subst s.
        exact (proj1 H).
  Qed.

  Lemma ProcessEdgeTreeBranchPreservesFrameProgressCandidate_proof:
    forall W F child done a,
      FrameProgressContractCandidate W ->
      Edge child a ->
      ~ done a ->
      Hoare
        (fun s =>
           FrameProgressCandidate F child s /\
           LoopInvPhase7Candidate child done s /\
           Unvisited a s)
        (set_fa a child;; W a;;
         lv <- get' (fun s => low s a);; update_low child lv)
        (fun _ s => FrameProgressCandidate F child s).
  Proof.
    intros W F child done a Hprogress_contract Hedge Hnot_done.
    eapply Hoare_bind.
    - apply Hoare_conj
        with
          (Q1 := fun _ s => ChildEntryCandidate child a done s)
          (Q2 := fun _ s => FrameProgressCandidate F child s).
      + eapply Hoare_conseq_pre.
        2: {
          apply
            (SetFaCreatesPendingChildCandidate_proof
               child a done Hedge Hnot_done).
        }
        intros s [_Hprogress [Hloop Hunvis]].
        unfold LoopInvPhase7Candidate,
          LoopInvPhase6Candidate,
          LoopInvLowCandidate,
          LoopInvDoneCandidate in Hloop.
        destruct Hloop as [Hphase6 _Htail].
        destruct Hphase6 as [Hlow _Hphase6_tail].
        destruct Hlow as [Hdone_loop _Hpartial].
        destruct Hdone_loop as [Hlocal _Hdiscipline].
        split.
        * exact Hlocal.
        * split; [exact Hunvis |].
          unfold LocalActiveRootCandidate in Hlocal.
          exact (proj2 (proj2 (proj2 (proj2 Hlocal)))).
      + eapply Hoare_conseq_pre.
        2: {
          apply
            (set_fa_unvisited_preserves_frame_progress_candidate
               F child a).
        }
        intros s [Hprogress [_Hloop Hunvis]].
        split; [exact Hprogress | exact Hunvis].
    - simpl. intros _.
      eapply Hoare_bind.
      + eapply Hoare_conseq_pre.
        2: {
          apply
            (Hprogress_contract F child a done Hedge Hnot_done).
        }
        intros s [Hentry Hprogress].
        split; [exact Hprogress | exact Hentry].
      + simpl. intros _.
        apply get_low_update_low_preserves_frame_progress_candidate.
  Qed.

  Lemma ProcessEdgePreservesFrameProgressCandidate_proof:
    forall W F child done a,
      FrameProgressContractCandidate W ->
      Edge child a ->
      ~ done a ->
      Hoare
        (fun s =>
           FrameProgressCandidate F child s /\
           LoopInvPhase7Candidate child done s)
        (process_edge child W a)
        (fun _ s => FrameProgressCandidate F child s).
  Proof.
    intros W F child done a Hprogress_contract Hedge Hnot_done.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: {
        apply
          (ProcessEdgeTreeBranchPreservesFrameProgressCandidate_proof
             W F child done a Hprogress_contract Hedge Hnot_done).
      }
      intros s [Hunvis Heq_s]. subst s.
      destruct H as [Hprogress Hloop].
      split; [exact Hprogress |].
      split; [exact Hloop | exact Hunvis].
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hnot_unvis Heq_s]. subst s1.
      assert (Hvis: Visited a s0).
      { unfold Unvisited in Hnot_unvis.
        unfold Visited. apply NNPP. exact Hnot_unvis. }
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: {
          apply
            (get_dfn_update_low_preserves_frame_progress_candidate
               F child a child).
        }
        intros s [Hactive_guard Heq_s]. subst s.
        exact (proj1 H).
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _Hnot_active].
        subst s.
        exact (proj1 H).
  Qed.

  Lemma SuspendedLoopInvPhase7ProvidesFrameInvCandidate_proof:
    SuspendedLoopInvPhase7ProvidesFrameInvCandidate_statement.
  Proof.
    unfold SuspendedLoopInvPhase7ProvidesFrameInvCandidate_statement,
      SuspendedLoopInvPhase7Candidate,
      SuspendedLoopInvPhase6Candidate,
      FrameInvCandidate,
      FrameOfCallCandidate.
    intros u done child s [Hsuspended Hsegment] Hresume.
    destruct Hsuspended as
      [Hlow [Hframe [Hclosed [Hchildren Hactive_segments]]]].
    destruct Hsegment as [Hsegment Hcoverage].
    simpl.
    split; [exact Hresume |].
    split; [exact Hlow |].
    split; [exact Hframe |].
    split; [exact Hclosed |].
    split; [exact Hchildren |].
    split; [exact Hactive_segments |].
    split; [exact Hsegment | exact Hcoverage].
  Qed.

  Lemma SetFaCreatesSuspendedParentFrameCandidate_proof:
    SetFaCreatesSuspendedParentFrameCandidate_statement.
  Proof.
    unfold SetFaCreatesSuspendedParentFrameCandidate_statement,
      LocalActiveRootCandidate,
      ParentFrameResumeCandidate,
      SuspendedParentFrameResumeCandidate,
      ParentResumeShapeCandidate,
      fa_child_of_u,
      fa_not_done_implies_eq_u.
    intros parent child done Hedge Hnot_done.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [Hlocal [Hframe Hunvis]].
    destruct Hlocal as [_ [_ [Hvis_parent _]]].
    destruct Hframe as [Hdone_vis [Hfa_child Hfa_not_done]].
    assert (Hchild_neq_parent: child <> parent).
    { intro Hchild_parent. apply Hunvis.
      rewrite Hchild_parent. exact Hvis_parent. }
    split.
    - split.
      + intros v Hdone_v.
        exact (Hdone_vis v Hdone_v).
      + split.
        * intros v [Hfa_v Hfa_neq_v].
          simpl in Hfa_v, Hfa_neq_v.
          unfold equiv_decb in Hfa_v, Hfa_neq_v.
          destruct (equiv_dec v child) as [Hv_child | Hv_not_child].
          -- rewrite Hv_child. exact Hedge.
          -- apply Hfa_child. split; assumption.
        * intros v Hnot_done_v Hv_not_child Hfa_v.
          simpl in Hfa_v.
          unfold equiv_decb in Hfa_v.
          destruct (equiv_dec v child) as [Hv_child | Hv_not_child'].
          -- exfalso. apply Hv_not_child. exact Hv_child.
          -- eapply Hfa_not_done; eauto.
    - split; [exact Hedge |].
      split; [exact Hnot_done |].
      split.
      + unfold equiv_decb.
        destruct (equiv_dec child child) as [_ | Hneq].
        * reflexivity.
        * exfalso. apply Hneq. reflexivity.
      + unfold equiv_decb.
        destruct (equiv_dec child child) as [_ | Hneq].
        * intro Hparent_child. apply Hchild_neq_parent.
          symmetry. exact Hparent_child.
        * exfalso. apply Hneq. reflexivity.
  Qed.

  Lemma SetFaPreservesProcessedTreeChildrenCorrectCandidate_proof:
    SetFaPreservesProcessedTreeChildrenCorrectCandidate_statement.
  Proof.
    unfold SetFaPreservesProcessedTreeChildrenCorrectCandidate_statement,
      ProcessedTreeChildrenCorrectCandidate,
      ProcessedTreeChildrenLowValidCandidate,
      ProcessedTreeChildrenIsLowCandidate,
      ProcessedTreeChildrenInactiveSelfLowCandidate,
      ChildLowValidForParentCandidate,
      ChildIsLowForParentCandidate,
      Unvisited,
      Visited.
    intros parent child done Hnot_done.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [[Hlow_valid [His_low Hinactive]] Hunvis].
    split.
    - intros x Hdone_x Hedge_x Hfa_x Hfa_neq_x.
      simpl in Hfa_x, Hfa_neq_x.
      unfold equiv_decb in Hfa_x, Hfa_neq_x.
      destruct (equiv_dec x child) as [Hx_child | Hx_not_child].
      + exfalso. apply Hnot_done. rewrite <- Hx_child. exact Hdone_x.
      + match goal with
        | |- scc_low_valid_v _ _ (RecordSet.set _ _ ?st) _ =>
            apply
              (set_fa_preserves_scc_low_valid_v_when_unvisited
                 g root x child parent st Hunvis)
        end.
        apply Hlow_valid; assumption.
    - split.
      + intros x Hdone_x Hedge_x Hfa_x Hfa_neq_x.
        simpl in Hfa_x, Hfa_neq_x.
        unfold equiv_decb in Hfa_x, Hfa_neq_x.
        destruct (equiv_dec x child) as [Hx_child | Hx_not_child].
        * exfalso. apply Hnot_done. rewrite <- Hx_child. exact Hdone_x.
        * match goal with
          | |- scc_is_low_v _ _ (RecordSet.set _ _ ?st) _ =>
              apply
                (set_fa_unvisited_preserves_scc_is_low_v
                   x child parent st Hunvis)
          end.
          apply His_low; assumption.
      + intros x Hdone_x Hedge_x Hfa_x Hfa_neq_x Hnot_active.
        simpl in Hfa_x, Hfa_neq_x, Hnot_active |- *.
        unfold equiv_decb in Hfa_x, Hfa_neq_x.
        destruct (equiv_dec x child) as [Hx_child | Hx_not_child].
        * exfalso. apply Hnot_done. rewrite <- Hx_child. exact Hdone_x.
	    * apply Hinactive; try assumption.
  Qed.

  Lemma set_fa_unvisited_preserves_done_closedness_candidate:
    forall parent child u done,
      ~ done child ->
      Hoare
        (fun s =>
           DoneClosednessCandidate u done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s => DoneClosednessCandidate u done s).
  Proof.
    intros parent child u done Hnot_done_child.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [[Hdone_closed Htree_closed] Hunvis].
    unfold DoneClosednessCandidate,
      done_reachable_closed,
      done_tree_reachable_closed in Hdone_closed, Htree_closed |- *.
    split.
    - intros v w Hdone_v Hnot_active Hreach.
      simpl in Hnot_active.
      eapply Hdone_closed; eauto.
    - intros v w Hdone_v Hnot_active Hfa_v Hfa_neq_v Hreach.
      simpl in Hnot_active, Hfa_v, Hfa_neq_v.
      unfold equiv_decb in Hfa_v, Hfa_neq_v.
      destruct (equiv_dec v child) as [Hv_child | Hv_not_child].
      + rewrite Hv_child in Hdone_v.
        exfalso. apply Hnot_done_child. exact Hdone_v.
      + eapply Htree_closed; eauto.
  Qed.

  Lemma set_fa_unvisited_preserves_active_processed_child_segment_summary:
    forall parent child u done,
      ~ done child ->
      Hoare
        (fun s =>
           ActiveProcessedChildSegmentSummaryCandidate u done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s =>
           ActiveProcessedChildSegmentSummaryCandidate u done s).
  Proof.
    intros parent child u done Hnot_done_child.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [Hsummary Hunvis].
    unfold ActiveProcessedChildSegmentSummaryCandidate,
      ChildSelfSegmentEscapeSummaryCandidate,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate in Hsummary |- *.
    intros c Hdone_c Hedge_c Hfa_c Hfa_neq_c Hactive_c.
    simpl in Hfa_c, Hfa_neq_c, Hactive_c.
    unfold equiv_decb in Hfa_c, Hfa_neq_c.
    destruct (equiv_dec c child) as [Hc_child | Hc_not_child].
    - rewrite Hc_child in Hdone_c.
      exfalso. apply Hnot_done_child. exact Hdone_c.
    - specialize (Hsummary c Hdone_c Hedge_c Hfa_c Hfa_neq_c Hactive_c).
      intros w Hreach Hnot_vis.
      specialize (Hsummary w Hreach Hnot_vis) as [Hpending | Hanchor].
      + left. exact Hpending.
      + right. exact Hanchor.
  Qed.

  Lemma set_fa_unvisited_preserves_segment_escape_accounting_candidate:
    forall parent child u done,
      Hoare
        (fun s =>
           SegmentEscapeAccountingCandidate u done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s => SegmentEscapeAccountingCandidate u done s).
  Proof.
    intros parent child u done.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [Hsegment _Hunvis].
    unfold SegmentEscapeAccountingCandidate,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate in Hsegment |- *.
    intros x w Hactive_x Hdfn_x Hreach Hnot_vis.
    specialize (Hsegment x w Hactive_x Hdfn_x Hreach Hnot_vis)
      as [Hpending | Hanchor].
    - left. exact Hpending.
    - right. exact Hanchor.
  Qed.

  Lemma set_fa_unvisited_preserves_segment_tree_coverage_candidate:
    forall parent child u done,
      ~ done child ->
      Hoare
        (fun s =>
           SegmentTreeCoverageByDoneCandidate u done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s => SegmentTreeCoverageByDoneCandidate u done s).
  Proof.
    intros parent child u done Hnot_done_child.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [Hcoverage _Hunvis].
    unfold SegmentTreeCoverageByDoneCandidate,
      ProcessedTreeReachableFromCandidate in Hcoverage |- *.
    intros x Hactive_x Hdfn_x.
    specialize (Hcoverage x Hactive_x Hdfn_x) as
      [Hx_u | [v [Hdone_v [Hedge_v
        [Hfa_v [Hfa_neq_v [Htree_vx Hreach_vx]]]]]]].
    - left. exact Hx_u.
    - right. exists v.
      split; [exact Hdone_v |].
      split; [exact Hedge_v |].
      assert (Hv_not_child: v <> child).
      { intro Hv_child. subst v. apply Hnot_done_child. exact Hdone_v. }
      simpl in Hactive_x, Hdfn_x.
      unfold equiv_decb.
      destruct (equiv_dec v child) as [Hv_child | _].
      + exfalso. apply Hv_not_child. exact Hv_child.
      + simpl.
        unfold equiv_decb.
        destruct (equiv_dec v child) as [Hv_child | _].
        * exfalso. apply Hv_not_child. exact Hv_child.
        * split; [exact Hfa_v |].
          split; [exact Hfa_neq_v |].
          split.
          -- apply
               (proj2
                  (set_fa_unvisited_preserves_tree_reachable
                     child parent s0 v x _Hunvis)).
             exact Htree_vx.
          -- exact Hreach_vx.
  Qed.

  Lemma set_fa_unvisited_preserves_loop_inv_low_candidate:
    forall parent child done,
      ~ done child ->
      Hoare
        (fun s =>
           LoopInvLowCandidate parent done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s => LoopInvLowCandidate parent done s).
  Proof.
    intros parent child done Hnot_done_child.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => LoopInvDoneCandidate parent done s)
             (Q2 := fun _ s => PartialRootLowEquationCandidate parent done s).
      - eapply Hoare_conseq_post.
        2: {
          apply Hoare_conj
            with (Q1 := fun _ s => LocalActiveRootCandidate parent s)
                 (Q2 := fun _ s => DoneDisciplineCandidate parent done s).
          + eapply Hoare_conseq_pre.
            2: {
              apply (SetFaParentActiveCandidate_proof parent child).
            }
            intros s [[Hdone_loop _Hpartial] Hunvis].
            destruct Hdone_loop as [Hlocal _Hdone_disc].
            split; [exact Hlocal | exact Hunvis].
	        + apply Hoare_conj.
	            * unfold Hoare. intros s1 _ s2 Hpre _.
	              destruct Hpre as [[[_ [Hsubset _Hdone_vis]] _Hpartial] _Hunvis].
	              exact Hsubset.
	            * eapply Hoare_conseq_pre.
	              2: { apply (set_fa_keep_visited_forall child parent done). }
	              intros s [[[_ [_ Hdone_vis]] _Hpartial] _Hunvis].
	              exact Hdone_vis.
        }
        intros _ s [Hlocal Hdone_disc].
        split; [exact Hlocal | exact Hdone_disc].
      - eapply Hoare_conseq_pre.
        2: {
          apply (SetFaPreservesPartialLowCandidate_proof
                   parent child done Hnot_done_child).
        }
        intros s [[_ Hpartial] _Hunvis].
        exact Hpartial.
    }
    intros _ s [Hdone Hpartial].
    split; [exact Hdone | exact Hpartial].
  Qed.

  Lemma set_fa_unvisited_creates_frame_inv_candidate:
    forall parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           LoopInvPhase7Candidate parent done s /\
           Unvisited child s)
        (set_fa child parent)
        (fun _ s =>
           FrameInvCandidate (FrameOfCallCandidate parent child done) s /\
           ChildEntryCandidate parent child done s /\
           ParentResumeShapeCandidate parent child done s).
  Proof.
    intros parent child done Hedge Hnot_done_child.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => ChildEntryCandidate parent child done s)
	     (Q2 := fun _ s =>
	              (SuspendedParentFrameResumeCandidate parent child done s /\
	               ParentResumeShapeCandidate parent child done s) /\
	              LoopInvLowCandidate parent done s /\
	              DoneClosednessCandidate parent done s /\
	              ProcessedTreeChildrenCorrectCandidate parent done s /\
                      ActiveProcessedChildSegmentSummaryCandidate parent done s /\
                      SegmentEscapeAccountingCandidate parent done s /\
                      SegmentTreeCoverageByDoneCandidate parent done s).
      - eapply Hoare_conseq_pre.
        2: {
          apply (LoopInvDoneConsumesUnvisitedSetFaCandidate_proof
                   parent child done Hedge Hnot_done_child).
        }
        intros s [[Hphase6 _Hsegment] Hunvis].
        destruct Hphase6 as [Hlow _Htail].
        destruct Hlow as [Hdone_loop _Hpartial].
        split; [exact Hdone_loop | exact Hunvis].
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               SuspendedParentFrameResumeCandidate parent child done s /\
               ParentResumeShapeCandidate parent child done s)
            (Q2 := fun _ s =>
               LoopInvLowCandidate parent done s /\
               DoneClosednessCandidate parent done s /\
               ProcessedTreeChildrenCorrectCandidate parent done s /\
               ActiveProcessedChildSegmentSummaryCandidate parent done s /\
               SegmentEscapeAccountingCandidate parent done s /\
               SegmentTreeCoverageByDoneCandidate parent done s).
        + eapply Hoare_conseq_pre.
          2: {
            apply (SetFaCreatesSuspendedParentFrameCandidate_proof
                     parent child done Hedge Hnot_done_child).
          }
          intros s [[Hphase6 _Hsegment] Hunvis].
          destruct Hphase6 as [Hlow [Hframe _Htail]].
          destruct Hlow as [Hdone_loop _Hpartial].
          destruct Hdone_loop as [Hlocal _Hdone_disc].
          split; [exact Hlocal |].
          split; [exact Hframe | exact Hunvis].
        + apply Hoare_conj
            with
              (Q1 := fun _ s => LoopInvLowCandidate parent done s)
              (Q2 := fun _ s =>
                 DoneClosednessCandidate parent done s /\
                 ProcessedTreeChildrenCorrectCandidate parent done s /\
                 ActiveProcessedChildSegmentSummaryCandidate parent done s /\
                 SegmentEscapeAccountingCandidate parent done s /\
                 SegmentTreeCoverageByDoneCandidate parent done s).
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (set_fa_unvisited_preserves_loop_inv_low_candidate
                   parent child done Hnot_done_child).
            }
            intros s [[Hphase6 _Hsegment] Hunvis].
            destruct Hphase6 as [Hlow _Htail].
            split; [exact Hlow | exact Hunvis].
          * apply Hoare_conj
              with
                (Q1 := fun _ s => DoneClosednessCandidate parent done s)
                (Q2 := fun _ s =>
                   ProcessedTreeChildrenCorrectCandidate parent done s /\
                   ActiveProcessedChildSegmentSummaryCandidate parent done s /\
                   SegmentEscapeAccountingCandidate parent done s /\
                   SegmentTreeCoverageByDoneCandidate parent done s).
            -- eapply Hoare_conseq_pre.
               2: {
                 apply
                   (set_fa_unvisited_preserves_done_closedness_candidate
                      parent child parent done Hnot_done_child).
               }
               intros s [[Hphase6 _Hsegment] Hunvis].
               destruct Hphase6 as [_Hlow [_Hframe [Hclosed _Htail]]].
               split; [exact Hclosed | exact Hunvis].
            -- apply Hoare_conj
                with
                  (Q1 := fun _ s =>
                     ProcessedTreeChildrenCorrectCandidate parent done s)
                  (Q2 := fun _ s =>
                     ActiveProcessedChildSegmentSummaryCandidate parent done s /\
                     SegmentEscapeAccountingCandidate parent done s /\
                     SegmentTreeCoverageByDoneCandidate parent done s).
               ++ eapply Hoare_conseq_pre.
                  2: {
                    apply
                      (SetFaPreservesProcessedTreeChildrenCorrectCandidate_proof
                         parent child done Hnot_done_child).
                  }
                  intros s [[Hphase6 _Hsegment] Hunvis].
                  destruct Hphase6 as
                    [_Hlow [_Hframe [_Hclosed [Hchildren _Hactive]]]].
                  split; [exact Hchildren | exact Hunvis].
               ++ apply Hoare_conj
                    with
                      (Q1 := fun _ s =>
                         ActiveProcessedChildSegmentSummaryCandidate
                           parent done s)
                      (Q2 := fun _ s =>
                         SegmentEscapeAccountingCandidate parent done s /\
                         SegmentTreeCoverageByDoneCandidate parent done s).
                  ** eapply Hoare_conseq_pre.
                     2: {
                       apply
                         (set_fa_unvisited_preserves_active_processed_child_segment_summary
                            parent child parent done Hnot_done_child).
                     }
                     intros s [[Hphase6 _Hsegment] Hunvis].
                     destruct Hphase6 as
                       [_Hlow [_Hframe [_Hclosed [_Hchildren Hactive]]]].
                     split; [exact Hactive | exact Hunvis].
                  ** apply Hoare_conj.
                     --- eapply Hoare_conseq_pre.
                         2: {
                           apply
                             (set_fa_unvisited_preserves_segment_escape_accounting_candidate
                                parent child parent done).
                         }
                         intros s [[_Hphase6 [Hsegment _Hcoverage]] Hunvis].
                         split; [exact Hsegment | exact Hunvis].
                     --- eapply Hoare_conseq_pre.
                         2: {
                           apply
                             (set_fa_unvisited_preserves_segment_tree_coverage_candidate
                                parent child parent done Hnot_done_child).
                         }
                         intros s [[_Hphase6 [_Hsegment [Hcoverage _Hblocks]]] Hunvis].
                         split; [exact Hcoverage | exact Hunvis].
    }
    intros _ s
      [Hentry
       [[Hsuspended_frame Hresume]
        [Hlow [Hclosed [Hchildren [Hactive_segments [Hsegment Hcoverage]]]]]]].
    split.
    - unfold FrameInvCandidate, FrameOfCallCandidate. simpl.
      split; [exact Hresume |].
      split; [exact Hlow |].
      split; [exact Hsuspended_frame |].
      split; [exact Hclosed |].
      split; [exact Hchildren |].
      split; [exact Hactive_segments |].
      split.
      + apply SegmentEscapeAccountingSuspendsCandidate_proof.
        exact Hsegment.
      + apply SegmentTreeCoverageSuspendsCandidate_proof.
        exact Hcoverage.
    - split; [exact Hentry | exact Hresume].
  Qed.

  Lemma processed_direct_child_not_parent_tree_child:
    forall u done child s,
      GlobalShapeCandidate s ->
      DoneVisitedCandidate done s ->
      done child ->
      Edge u child ->
      fa s child = u ->
      fa s child <> child ->
      ~ dg_step (state_to_dfs_tree g s root) child u.
  Proof.
    unfold GlobalShapeCandidate, DoneVisitedCandidate, done_visited,
      Visited, Edge.
    intros u done child s Hglobal Hdone_vis Hdone_child Hedge Hfa Hfa_neq
           Htree_child_u.
    unfold wf_scc_state in Hglobal.
    destruct Hglobal as [_ [_ [Hdfn_valid _]]].
    pose proof (Hdfn_valid child u Htree_child_u) as Hdfn_child_u.
    assert (Htree_u_child: dg_step (state_to_dfs_tree g s root) u child).
    { apply tree_step_char_backward.
      - exact Hedge.
      - exact Hfa.
      - exact Hfa_neq.
      - apply Hdone_vis. exact Hdone_child. }
    pose proof (Hdfn_valid u child Htree_u_child) as Hdfn_u_child.
    lia.
  Qed.

  Lemma update_low_preserves_processed_tree_children_correct_parent:
    forall u done n,
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           DoneVisitedCandidate done s /\
           ProcessedTreeChildrenCorrectCandidate u done s)
        (update_low u n)
        (fun _ s => ProcessedTreeChildrenCorrectCandidate u done s).
  Proof.
    intros u done n.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst. simpl.
      destruct H as [Hglobal [Hdone_vis [Hlow_valid [His_low Hinactive]]]].
      split.
      + intros child Hdone_child Hedge Hfa Hfa_neq.
        simpl in Hfa, Hfa_neq.
        assert (Hchild_ne_u: child <> u).
        { intro Hchild_u. subst child. apply Hfa_neq. exact Hfa. }
        apply (set_low_preserves_scc_low_valid_v_when_not_child
                 g root child u n s0).
        * exact Hchild_ne_u.
        * eapply processed_direct_child_not_parent_tree_child; eauto.
        * apply Hlow_valid; assumption.
      + split.
        * intros child Hdone_child Hedge Hfa Hfa_neq.
          simpl in Hfa, Hfa_neq.
          assert (Hchild_ne_u: child <> u).
          { intro Hchild_u. subst child. apply Hfa_neq. exact Hfa. }
          apply set_low_other_preserves_scc_is_low_v.
          -- exact Hchild_ne_u.
          -- apply His_low; assumption.
        * intros child Hdone_child Hedge Hfa Hfa_neq Hnot_active.
          simpl in Hfa, Hfa_neq, Hnot_active |- *.
          assert (Hchild_ne_u: child <> u).
          { intro Hchild_u. subst child. apply Hfa_neq. exact Hfa. }
          unfold equiv_decb.
          destruct (equiv_dec child u) as [Hchild_u | _].
          -- exfalso. apply Hchild_ne_u. exact Hchild_u.
          -- apply Hinactive; try assumption.
    - destruct H1 as [Heq _]. subst.
      destruct H as [_ [_ Hchildren]].
      exact Hchildren.
  Qed.

  Lemma update_low_preserves_parent_frame_resume_candidate:
    forall changed n parent done,
      Hoare
        (ParentFrameResumeCandidate parent done)
        (update_low changed n)
        (fun _ s => ParentFrameResumeCandidate parent done s).
  Proof.
    intros changed n parent done.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst. simpl. exact H.
    - destruct H1 as [Heq _]. subst. exact H.
  Qed.

  Lemma update_low_preserves_local_active_root_candidate:
    forall changed n u,
      Hoare
        (LocalActiveRootCandidate u)
        (update_low changed n)
        (fun _ s => LocalActiveRootCandidate u s).
  Proof.
    intros changed n u.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst. simpl. exact H.
    - destruct H1 as [Heq _]. subst. exact H.
  Qed.

  Lemma update_low_preserves_done_discipline_candidate:
    forall changed n u done,
      Hoare
        (DoneDisciplineCandidate u done)
        (update_low changed n)
        (fun _ s => DoneDisciplineCandidate u done s).
  Proof.
    intros changed n u done.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst. simpl. exact H.
    - destruct H1 as [Heq _]. subst. exact H.
  Qed.

  Lemma update_low_preserves_loop_inv_done_candidate:
    forall changed n u done,
      Hoare
        (LoopInvDoneCandidate u done)
        (update_low changed n)
        (fun _ s => LoopInvDoneCandidate u done s).
  Proof.
    intros changed n u done.
    apply Hoare_conj.
    - eapply Hoare_conseq_pre.
      2: { apply (update_low_preserves_local_active_root_candidate changed n u). }
      intros s [Hlocal _]. exact Hlocal.
    - eapply Hoare_conseq_pre.
      2: {
        apply (update_low_preserves_done_discipline_candidate changed n u done).
      }
      intros s [_ Hdone]. exact Hdone.
  Qed.

  Lemma ParentFrameResumeCandidate_step_visited_proof:
    forall parent done child s,
      ParentFrameResumeCandidate parent done s ->
      Visited child s ->
      ParentFrameResumeCandidate parent (done_after done child) s.
  Proof.
    unfold ParentFrameResumeCandidate,
      done_visited,
      fa_not_done_implies_eq_u,
      done_after.
    intros parent done child s [Hdone_vis [Hfa_child Hfa_not_done]]
           Hvis_child.
    split.
    - intros v Hdone_after.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_v | Hv_child].
      + apply Hdone_vis. exact Hdone_v.
      + subst v. exact Hvis_child.
    - split; [exact Hfa_child |].
      intros v Hnot_done_after Hfa_v.
      apply Hfa_not_done.
      + intros Hdone_v.
        apply Hnot_done_after.
        sets_unfold. left. exact Hdone_v.
      + exact Hfa_v.
  Qed.

  Lemma update_low_preserves_done_closedness_candidate:
    forall changed n parent done,
      Hoare
        (DoneClosednessCandidate parent done)
        (update_low changed n)
        (fun _ s => DoneClosednessCandidate parent done s).
  Proof.
    intros changed n parent done.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst. simpl. exact H.
    - destruct H1 as [Heq _]. subst. exact H.
  Qed.

  Lemma update_low_preserves_segment_escape_accounting_candidate:
    forall u done n,
      Hoare
        (SegmentEscapeAccountingCandidate u done)
        (update_low u n)
        (fun _ s => SegmentEscapeAccountingCandidate u done s).
  Proof.
    intros u done n.
    unfold update_low.
    apply Hoare_normalize. intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lu.
    unfold If. intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold set_low. intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H1 as [Hlt Heq_s1]. subst s1. subst s.
      unfold SegmentEscapeAccountingCandidate,
        PendingRootEscapeCandidate,
        OldStackEscapeAnchorCandidate in Haccount |- *.
      intros x w Hactive_x Hdfn_x Hreach Hnot_vis.
      simpl in Hactive_x, Hdfn_x, Hnot_vis.
      specialize (Haccount x w Hactive_x Hdfn_x Hreach Hnot_vis)
        as [Hpending | Hanchor].
      + left. exact Hpending.
      + right.
        destruct Hanchor as
          [anchor [Hactive_anchor [Hdfn_anchor [Hlow_anchor [Hx_anchor Hanchor_w]]]]].
        exists anchor.
        simpl.
        split; [exact Hactive_anchor |].
        split; [exact Hdfn_anchor |].
        split.
        * unfold equiv_decb.
          destruct (equiv_dec u u) as [_ | Hneq].
          -- lia.
          -- exfalso. apply Hneq. reflexivity.
        * split; [exact Hx_anchor | exact Hanchor_w].
    - intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H2 as [Heq_s1 _]. subst s1. subst s.
      exact Haccount.
  Qed.

  Lemma update_low_preserves_segment_tree_coverage_candidate:
    forall u done n,
      Hoare
        (SegmentTreeCoverageByDoneCandidate u done)
        (update_low u n)
        (fun _ s => SegmentTreeCoverageByDoneCandidate u done s).
  Proof.
    intros u done n.
    unfold update_low.
    apply Hoare_normalize. intros snap Hcoverage.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lu.
    unfold If. intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold set_low. intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H1 as [_Hlt Heq_s1]. subst s1. subst s.
      unfold SegmentTreeCoverageByDoneCandidate,
        ProcessedTreeReachableFromCandidate in Hcoverage |- *.
      intros x Hactive_x Hdfn_x.
      simpl in Hactive_x, Hdfn_x.
      specialize (Hcoverage x Hactive_x Hdfn_x) as
        [Hx_u | [v [Hdone_v [Hedge_v [Hfa_v [Hfa_neq_v Hreach_vx]]]]]].
      + left. exact Hx_u.
      + right. exists v.
        split; [exact Hdone_v |].
        split; [exact Hedge_v |].
        simpl.
        split; [exact Hfa_v |].
        split; [exact Hfa_neq_v | exact Hreach_vx].
    - intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H2 as [Heq_s1 _]. subst s1. subst s.
      exact Hcoverage.
  Qed.

  Lemma get_dfn_update_low_preserves_segment_tree_coverage_candidate:
    forall u a done,
      Hoare
        (SegmentTreeCoverageByDoneCandidate u done)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s => SegmentTreeCoverageByDoneCandidate u done s).
  Proof.
    intros u a done.
    apply Hoare_normalize. intros snap Hcoverage.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_segment_tree_coverage_candidate
               u done dv).
    }
    intros s [Heq _]. subst s. exact Hcoverage.
  Qed.

  Lemma get_low_update_low_preserves_segment_tree_coverage_candidate:
    forall u a done,
      Hoare
        (SegmentTreeCoverageByDoneCandidate u done)
        (lv <- get' (fun s => low s a);; update_low u lv)
        (fun _ s => SegmentTreeCoverageByDoneCandidate u done s).
  Proof.
    intros u a done.
    apply Hoare_normalize. intros snap Hcoverage.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_segment_tree_coverage_candidate
               u done lv).
    }
    intros s [Heq _]. subst s. exact Hcoverage.
  Qed.

  Lemma SegmentTreeCoverageByDoneCandidate_mono_proof:
    forall u done1 done2 s,
      (forall x, done1 x -> done2 x) ->
      SegmentTreeCoverageByDoneCandidate u done1 s ->
      SegmentTreeCoverageByDoneCandidate u done2 s.
  Proof.
    unfold SegmentTreeCoverageByDoneCandidate,
      ProcessedTreeReachableFromCandidate.
    intros u done1 done2 s Hmono Hcoverage x Hactive_x Hdfn_x.
    specialize (Hcoverage x Hactive_x Hdfn_x) as
      [Hx_u | [child [Hdone_child [Hedge_child
        [Hfa_child [Hfa_neq_child [Htree_child_x Hreach_child_x]]]]]]].
    - left. exact Hx_u.
    - right. exists child.
      split; [apply Hmono; exact Hdone_child |].
      split; [exact Hedge_child |].
      split; [exact Hfa_child |].
      split; [exact Hfa_neq_child |].
      split; [exact Htree_child_x | exact Hreach_child_x].
  Qed.

  Lemma SegmentTreeCoverageByDoneCandidate_step_proof:
    forall u done a s,
      SegmentTreeCoverageByDoneCandidate u done s ->
      SegmentTreeCoverageByDoneCandidate u (done_after done a) s.
  Proof.
    intros u done a s Hcoverage.
    eapply SegmentTreeCoverageByDoneCandidate_mono_proof.
    - intros x Hdone_x. unfold done_after. sets_unfold. left. exact Hdone_x.
    - exact Hcoverage.
  Qed.

  Lemma SegmentTreeCoverageProvidesSegmentCoverageCandidate_proof:
    forall u done s,
      SegmentTreeCoverageByDoneCandidate u done s ->
      SegmentCoverageByDoneCandidate u done s.
  Proof.
    unfold SegmentTreeCoverageByDoneCandidate,
      SegmentCoverageByDoneCandidate,
      ProcessedTreeReachableFromCandidate,
      ProcessedReachableFromCandidate.
    intros u done s Hcoverage x Hactive_x Hdfn_x.
    specialize (Hcoverage x Hactive_x Hdfn_x) as
      [Hx_u | [child [Hdone_child [Hedge_child
       [_Hfa_child [_Hfa_neq_child [_Htree_child Hreach_child]]]]]]].
    - left. exact Hx_u.
    - right. exists child.
      split; [exact Hdone_child |].
      split; [exact Hedge_child | exact Hreach_child].
  Qed.

  Lemma LoopDonePhase7ProvidesChildSegmentSummaryCandidate_proof:
    forall child s,
      LoopDonePhase7Candidate child s ->
      ChildSegmentSummaryCandidate child s.
  Proof.
    unfold LoopDonePhase7Candidate,
      LoopInvPhase7Candidate,
      ChildSegmentSummaryCandidate.
    intros child s [_Hphase6 [Hsegment [Hcoverage _Hblocks]]].
    split; [exact Hsegment |].
    eapply SegmentTreeCoverageProvidesSegmentCoverageCandidate_proof.
    exact Hcoverage.
  Qed.

  Lemma ProcessEdgeVisitedNonStackExtendsSegmentTreeCoverageCandidate_proof:
    forall W u a done,
      Hoare
        (fun s =>
           SegmentTreeCoverageByDoneCandidate u done s /\
           Visited a s /\
           ~ Active a s)
        (process_edge u W a)
        (fun _ s =>
           SegmentTreeCoverageByDoneCandidate u (done_after done a) s).
  Proof.
    intros W u a done.
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
        destruct H as [_ [_ Hnot_active]].
        exfalso. apply Hnot_active. exact Hactive_guard.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _Hnot_active_guard].
        subst s.
        destruct H as [Hcoverage _].
        apply SegmentTreeCoverageByDoneCandidate_step_proof.
        exact Hcoverage.
  Qed.

  Lemma ProcessEdgeVisitedActiveExtendsSegmentTreeCoverageCandidate_proof:
    forall W u a done,
      Hoare
        (fun s =>
           SegmentTreeCoverageByDoneCandidate u done s /\
           Visited a s /\
           Active a s)
        (process_edge u W a)
        (fun _ s =>
           SegmentTreeCoverageByDoneCandidate u (done_after done a) s).
  Proof.
    intros W u a done.
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
        eapply Hoare_conseq_post.
        2: {
          eapply Hoare_conseq_pre.
          2: {
            apply
              (get_dfn_update_low_preserves_segment_tree_coverage_candidate
                 u a done).
          }
          intros s [Hactive_guard Heq_s]. subst s.
          destruct H as [Hcoverage _].
          exact Hcoverage.
        }
        intros ret st_after Hcoverage_after.
        apply SegmentTreeCoverageByDoneCandidate_step_proof.
        exact Hcoverage_after.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s Hnot_active].
        subst s.
        destruct H as [_ [_ Hactive]].
        exfalso. apply Hnot_active. exact Hactive.
  Qed.

  Lemma update_low_preserves_suspended_segment_escape_accounting_candidate:
    forall u child done n,
      Hoare
        (SuspendedSegmentEscapeAccountingCandidate u child done)
        (update_low u n)
        (fun _ s =>
           SuspendedSegmentEscapeAccountingCandidate u child done s).
  Proof.
    intros u child done n.
    unfold update_low.
    apply Hoare_normalize. intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lu.
    unfold If. intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold set_low. intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H1 as [Hlt Heq_s1]. subst s1. subst s.
      unfold SuspendedSegmentEscapeAccountingCandidate,
        PendingRootEscapeCandidate,
        OldStackEscapeAnchorCandidate in Haccount |- *.
      intros x w Hactive_x Hdfn_x Houtside Hreach Hnot_vis.
      simpl in Hactive_x, Hdfn_x, Houtside, Hnot_vis.
      specialize (Haccount x w Hactive_x Hdfn_x Houtside Hreach Hnot_vis)
        as [Hpending | Hanchor].
      + left. exact Hpending.
      + right.
        destruct Hanchor as
          [anchor [Hactive_anchor [Hdfn_anchor [Hlow_anchor [Hx_anchor Hanchor_w]]]]].
        exists anchor.
        simpl.
        split; [exact Hactive_anchor |].
        split; [exact Hdfn_anchor |].
        split.
        * unfold equiv_decb.
          destruct (equiv_dec u u) as [_ | Hneq].
          -- lia.
          -- exfalso. apply Hneq. reflexivity.
        * split; [exact Hx_anchor | exact Hanchor_w].
    - intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H2 as [Heq_s1 _]. subst s1. subst s.
      exact Haccount.
  Qed.

  Lemma update_low_preserves_parent_pending_child_escape_accounted_candidate:
    forall u done child n,
      Hoare
        (ParentPendingChildEscapeAccountedCandidate u done child)
        (update_low u n)
        (fun _ s =>
           ParentPendingChildEscapeAccountedCandidate u done child s).
  Proof.
    intros u done child n.
    unfold update_low.
    apply Hoare_normalize. intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lu.
    unfold If. intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold set_low. intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H1 as [Hlt Heq_s1]. subst s1. subst s.
      unfold ParentPendingChildEscapeAccountedCandidate,
        PendingRootEscapeCandidate,
        OldStackEscapeAnchorCandidate in Haccount |- *.
      intros x w Hactive_x Hdfn_x Hxu Hchild_w Hnot_vis.
      simpl in Hactive_x, Hdfn_x, Hnot_vis.
      specialize (Haccount x w Hactive_x Hdfn_x Hxu Hchild_w Hnot_vis)
        as [Hpending | Hanchor].
      + left. exact Hpending.
      + right.
        destruct Hanchor as
          [anchor [Hactive_anchor [Hdfn_anchor [Hlow_anchor [Hx_anchor Hanchor_w]]]]].
        exists anchor.
        simpl.
        split; [exact Hactive_anchor |].
        split; [exact Hdfn_anchor |].
        split.
        * unfold equiv_decb.
          destruct (equiv_dec u u) as [_ | Hneq].
          -- lia.
          -- exfalso. apply Hneq. reflexivity.
        * split; [exact Hx_anchor | exact Hanchor_w].
    - intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H2 as [Heq_s1 _]. subst s1. subst s.
      exact Haccount.
  Qed.

  Lemma get_low_update_low_preserves_suspended_segment_escape_accounting_candidate:
    forall u done child,
      Hoare
        (SuspendedSegmentEscapeAccountingCandidate u child done)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s =>
           SuspendedSegmentEscapeAccountingCandidate u child done s).
  Proof.
    intros u done child.
    apply Hoare_normalize.
    intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (update_low_preserves_suspended_segment_escape_accounting_candidate
           u child done lv).
    }
    intros s [Heq_s _]. subst s. exact Haccount.
  Qed.

  Lemma get_low_update_low_preserves_parent_pending_child_escape_accounted_candidate:
    forall u done child,
      Hoare
        (ParentPendingChildEscapeAccountedCandidate u done child)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s =>
           ParentPendingChildEscapeAccountedCandidate u done child s).
  Proof.
    intros u done child.
    apply Hoare_normalize.
    intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (update_low_preserves_parent_pending_child_escape_accounted_candidate
           u done child lv).
    }
    intros s [Heq_s _]. subst s. exact Haccount.
  Qed.

  Lemma update_low_preserves_active_target_blocks_escape_accounted_candidate:
    forall u done n,
      Hoare
        (ActiveTargetBlocksEscapeAccountedCandidate u done)
        (update_low u n)
        (fun _ s => ActiveTargetBlocksEscapeAccountedCandidate u done s).
  Proof.
    intros u done n.
    unfold update_low.
    apply Hoare_normalize. intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lu.
    unfold If. intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold set_low. intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H1 as [Hlt Heq_s1]. subst s1. subst s.
      unfold ActiveTargetBlocksEscapeAccountedCandidate,
        ActiveTargetBlockEscapeAccountedCandidate,
        PendingRootEscapeCandidate,
        OldStackEscapeAnchorCandidate in Haccount |- *.
      intros block a w Hblock_a Hblock_valid Hreach Hnot_vis.
      simpl in Hnot_vis.
      specialize (Haccount block a w Hblock_a) as Hblock_account.
      specialize
        (Hblock_account
           (fun b Hb =>
              let Hb_valid := Hblock_valid b Hb in
              match Hb_valid with
              | conj Hedge_b
                  (conj Hnot_done_b (conj Hactive_b Hdfn_b)) =>
                  conj Hedge_b
                    (conj Hnot_done_b (conj Hactive_b Hdfn_b))
              end)
           Hreach Hnot_vis) as [Hpending | Hanchor].
      + left. exact Hpending.
      + right.
        destruct Hanchor as
          [anchor [Hactive_anchor [Hdfn_anchor
           [Hlow_anchor [Ha_anchor Hanchor_w]]]]].
        exists anchor.
        simpl.
        split; [exact Hactive_anchor |].
        split; [exact Hdfn_anchor |].
        split.
        * unfold equiv_decb.
          destruct (equiv_dec u u) as [_ | Hneq].
          -- lia.
          -- exfalso. apply Hneq. reflexivity.
        * split; [exact Ha_anchor | exact Hanchor_w].
    - intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H2 as [Heq_s1 _]. subst s1. subst s.
      exact Haccount.
  Qed.

  Lemma get_dfn_update_low_preserves_active_target_blocks_escape_accounted_candidate:
    forall u done a,
      Hoare
        (ActiveTargetBlocksEscapeAccountedCandidate u done)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s => ActiveTargetBlocksEscapeAccountedCandidate u done s).
  Proof.
    intros u done a.
    apply Hoare_normalize.
    intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (update_low_preserves_active_target_blocks_escape_accounted_candidate
           u done dv).
    }
    intros s [Heq_s _]. subst s. exact Haccount.
  Qed.

  Lemma get_low_update_low_preserves_active_target_blocks_escape_accounted_candidate:
    forall u done child,
      Hoare
        (ActiveTargetBlocksEscapeAccountedCandidate u done)
        (lv <- get' (fun s => low s child);; update_low u lv)
        (fun _ s => ActiveTargetBlocksEscapeAccountedCandidate u done s).
  Proof.
    intros u done child.
    apply Hoare_normalize.
    intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (update_low_preserves_active_target_blocks_escape_accounted_candidate
           u done lv).
    }
    intros s [Heq_s _]. subst s. exact Haccount.
  Qed.

  Lemma SegmentEscapeAccountingCandidate_step_nonactive_visited_proof:
    forall u done a s,
      SegmentEscapeAccountingCandidate u done s ->
      SettledClosedCandidate s ->
      Visited a s ->
      ~ Active a s ->
      SegmentEscapeAccountingCandidate u (done_after done a) s.
  Proof.
    unfold SegmentEscapeAccountingCandidate,
      SettledClosedCandidate,
      PendingRootEscapeCandidate,
      done_after.
    intros u done a s Hsegment Hsettled Hvis_a Hnot_active_a
           x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w.
    specialize (Hsegment x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w)
      as [Hpending | Hanchor].
    - destruct Hpending as
        [b [Hxu [Hedge_b [Hnot_done_b Hreach_bw]]]].
	      destruct (equiv_dec b a) as [Hb_a | Hb_not_a].
	      + rewrite Hb_a in Hreach_bw.
	        exfalso.
	        apply Hnot_vis_w.
	        eapply Hsettled; eauto.
      + left. exists b.
        split; [exact Hxu |].
        split; [exact Hedge_b |].
        split.
        * intros Hdone_after.
          apply Hnot_done_b.
          sets_unfold in Hdone_after.
          destruct Hdone_after as [Hdone_b | Hb_a].
          -- exact Hdone_b.
          -- exfalso. apply Hb_not_a. symmetry. exact Hb_a.
        * exact Hreach_bw.
    - right. exact Hanchor.
  Qed.

  Lemma ActiveTargetBlocksEscapeAccountedCandidate_step_nonactive_visited_proof:
    forall u done a s,
      ActiveTargetBlocksEscapeAccountedCandidate u done s ->
      SettledClosedCandidate s ->
      Visited a s ->
      ~ Active a s ->
      ActiveTargetBlocksEscapeAccountedCandidate
        u (done_after done a) s.
  Proof.
    unfold ActiveTargetBlocksEscapeAccountedCandidate,
      ActiveTargetBlockEscapeAccountedCandidate,
      SettledClosedCandidate,
      PendingRootEscapeCandidate,
      done_after.
    intros u done a s Hblocks Hsettled Hvis_a Hnot_active_a
           block target w Hblock_target Hblock_valid Hreach Hnot_vis.
    specialize (Hblocks block target w Hblock_target) as Haccount.
    assert (Hblock_valid_old:
              forall b,
                block b ->
                Edge u b /\ ~ done b /\ Active b s /\
                dfn s u <= dfn s b).
    { intros b Hb.
      specialize (Hblock_valid b Hb) as
        [Hedge_b [Hnot_done_after_b [Hactive_b Hdfn_b]]].
      split; [exact Hedge_b |].
      split.
      - intros Hdone_b.
        apply Hnot_done_after_b.
        sets_unfold. left. exact Hdone_b.
      - split; [exact Hactive_b | exact Hdfn_b]. }
    specialize (Haccount Hblock_valid_old Hreach Hnot_vis)
      as [Hpending | Hanchor].
    - destruct Hpending as
        [next [Htarget_u [Hedge_next [Hnot_done_block Hnext_w]]]].
      destruct (equiv_dec next a) as [Hnext_a | Hnext_not_a].
      + rewrite Hnext_a in Hnext_w.
        exfalso.
        apply Hnot_vis.
        eapply Hsettled; eauto.
      + left.
        exists next.
        split; [exact Htarget_u |].
        split; [exact Hedge_next |].
        split.
        * intros Hbad.
          apply Hnot_done_block.
          sets_unfold in Hbad. sets_unfold.
          destruct Hbad as [[Hdone_next | Hnext_a] | Hblock_next].
          -- left. exact Hdone_next.
          -- exfalso. apply Hnext_not_a. symmetry. exact Hnext_a.
          -- right. exact Hblock_next.
        * exact Hnext_w.
    - right. exact Hanchor.
  Qed.

  Lemma SegmentEscapeAccountingCandidate_step_active_target_proof:
    forall u done a s,
      SegmentEscapeAccountingCandidate u done s ->
      SegmentTreeCoverageByDoneCandidate u done s ->
      ActiveTargetSegmentEscapeAccountedCandidate u done s ->
      Edge u a ->
      Active a s ->
      dfn s u <= dfn s a ->
      SegmentEscapeAccountingCandidate u (done_after done a) s.
  Proof.
    unfold SegmentEscapeAccountingCandidate,
      SegmentTreeCoverageByDoneCandidate,
      ActiveTargetSegmentEscapeAccountedCandidate,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate,
      done_after.
    intros u done a s Hsegment Hcoverage Htarget Hedge_a Hactive_a Hdfn_a
           x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w.
    specialize (Hsegment x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w)
      as [Hpending | Hanchor].
    - destruct Hpending as
        [b [Hxu [Hedge_b [Hnot_done_b Hreach_bw]]]].
      destruct (equiv_dec b a) as [Hb_a | Hb_not_a].
      + rewrite Hb_a in Hreach_bw.
        specialize (Hcoverage a Hactive_a Hdfn_a) as Hcovered_a.
        specialize (Htarget a w Hactive_a Hdfn_a Hcovered_a
                      Hreach_bw Hnot_vis_w) as [Hpending_a | Hanchor_a].
        * left.
          destruct Hpending_a as
            [c [_Ha_u [Hedge_c [Hnot_done_after_c Hreach_cw]]]].
          exists c.
          split; [exact Hxu |].
          split; [exact Hedge_c |].
          split; [exact Hnot_done_after_c | exact Hreach_cw].
        * right.
          destruct Hanchor_a as
            [c [Hactive_c [Hdfn_c [Hlow_c [Ha_c Hc_w]]]]].
          exists c.
          split; [exact Hactive_c |].
          split; [exact Hdfn_c |].
          split; [exact Hlow_c |].
          split.
          -- eapply dg_reachable_trans.
             ++ eapply dg_reachable_trans.
                ** exact Hxu.
                ** apply dg_reachable_step. exact Hedge_a.
             ++ exact Ha_c.
          -- exact Hc_w.
      + left. exists b.
        split; [exact Hxu |].
        split; [exact Hedge_b |].
        split.
        * intros Hdone_after.
          apply Hnot_done_b.
          sets_unfold in Hdone_after.
          destruct Hdone_after as [Hdone_b | Hb_a].
          -- exact Hdone_b.
          -- exfalso. apply Hb_not_a. symmetry. exact Hb_a.
        * exact Hreach_bw.
    - right. exact Hanchor.
  Qed.

  Lemma SegmentEscapeAccountingCandidate_step_active_edge_target_proof:
    forall u done a s,
      SegmentEscapeAccountingCandidate u done s ->
      SegmentTreeCoverageByDoneCandidate u done s ->
      ActiveEdgeTargetSegmentEscapeAccountedCandidate u done s ->
      Edge u a ->
      ~ done a ->
      Active a s ->
      dfn s u <= dfn s a ->
      SegmentEscapeAccountingCandidate u (done_after done a) s.
  Proof.
    unfold SegmentEscapeAccountingCandidate,
      SegmentTreeCoverageByDoneCandidate,
      ActiveEdgeTargetSegmentEscapeAccountedCandidate,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate,
      done_after.
    intros u done a s Hsegment Hcoverage Htarget Hedge_a Hnot_done_a
           Hactive_a Hdfn_a
           x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w.
    specialize (Hsegment x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w)
      as [Hpending | Hanchor].
    - destruct Hpending as
        [b [Hxu [Hedge_b [Hnot_done_b Hreach_bw]]]].
      destruct (equiv_dec b a) as [Hb_a | Hb_not_a].
      + rewrite Hb_a in Hreach_bw.
        specialize (Htarget a w Hedge_a Hnot_done_a Hactive_a Hdfn_a
                      Hreach_bw Hnot_vis_w) as
          [Hpending_a | Hanchor_a].
        * left.
          destruct Hpending_a as
            [c [_Ha_u [Hedge_c [Hnot_done_after_c Hreach_cw]]]].
          exists c.
          split; [exact Hxu |].
          split; [exact Hedge_c |].
          split; [exact Hnot_done_after_c | exact Hreach_cw].
        * right.
          destruct Hanchor_a as
            [c [Hactive_c [Hdfn_c [Hlow_c [Ha_c Hc_w]]]]].
          exists c.
          split; [exact Hactive_c |].
          split; [exact Hdfn_c |].
          split; [exact Hlow_c |].
          split.
          -- eapply dg_reachable_trans.
             ++ eapply dg_reachable_trans.
                ** exact Hxu.
                ** apply dg_reachable_step. exact Hedge_a.
             ++ exact Ha_c.
          -- exact Hc_w.
      + left. exists b.
        split; [exact Hxu |].
        split; [exact Hedge_b |].
        split.
        * intros Hdone_after.
          apply Hnot_done_b.
          sets_unfold in Hdone_after.
          destruct Hdone_after as [Hdone_b | Hb_a].
          -- exact Hdone_b.
          -- exfalso. apply Hb_not_a. symmetry. exact Hb_a.
        * exact Hreach_bw.
    - right. exact Hanchor.
  Qed.

  Lemma GetDfnUpdateLowExtendsSegmentEscapeAccountingActiveEdgeTargetCandidate_proof:
    forall u done a,
      Hoare
        (fun s =>
           SegmentEscapeAccountingCandidate u done s /\
           SegmentTreeCoverageByDoneCandidate u done s /\
           ActiveEdgeTargetSegmentEscapeAccountedCandidate u done s /\
           Edge u a /\
           ~ done a /\
           Active a s /\
           dfn s u <= dfn s a)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s =>
           SegmentEscapeAccountingCandidate u (done_after done a) s).
  Proof.
    intros u done a.
    apply Hoare_normalize.
    intros snap [Hsegment [Hcoverage [Htarget [Hedge
      [Hnot_done [Hactive Hdfn]]]]]].
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_segment_escape_accounting_candidate
               u (done_after done a) dv).
    }
    intros s [Heq _]. subst s.
    eapply SegmentEscapeAccountingCandidate_step_active_edge_target_proof;
      eauto.
  Qed.

  Lemma GetDfnUpdateLowExtendsSegmentEscapeAccountingActiveTargetCandidate_proof:
    forall u done a,
      Hoare
        (fun s =>
           SegmentEscapeAccountingCandidate u done s /\
           SegmentTreeCoverageByDoneCandidate u done s /\
           ActiveTargetSegmentEscapeAccountedCandidate u done s /\
           Edge u a /\
           Active a s /\
           dfn s u <= dfn s a)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s =>
           SegmentEscapeAccountingCandidate u (done_after done a) s).
  Proof.
    intros u done a.
    apply Hoare_normalize.
    intros snap [Hsegment [Hcoverage [Htarget [Hedge [Hactive Hdfn]]]]].
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_segment_escape_accounting_candidate
               u (done_after done a) dv).
    }
    intros s [Heq _]. subst s.
    eapply SegmentEscapeAccountingCandidate_step_active_target_proof;
      eauto.
  Qed.

  Lemma ProcessEdgeVisitedNonStackExtendsSegmentEscapeAccountingCandidate_proof:
    forall W u a done,
      Hoare
        (fun s =>
           SegmentEscapeAccountingCandidate u done s /\
           SettledClosedCandidate s /\
           Visited a s /\
           ~ Active a s)
        (process_edge u W a)
        (fun _ s =>
           SegmentEscapeAccountingCandidate u (done_after done a) s).
  Proof.
    intros W u a done.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hunvis Heq]. subst s1.
      destruct H as [_ [_ [Hvis _]]].
      exfalso. apply Hunvis. exact Hvis.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_ Heq0]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        intro_state.
        destruct H1 as [Hactive_guard Heq1]. subst s1.
        destruct H as [_ [_ [_ Hnot_active]]].
        exfalso. apply Hnot_active. exact Hactive_guard.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _Hnot_stack_guard].
        subst s.
        destruct H as [Hsegment [Hsettled [Hvis Hnot_active]]].
        eapply SegmentEscapeAccountingCandidate_step_nonactive_visited_proof;
          eauto.
  Qed.

  Lemma get_dfn_update_low_preserves_segment_escape_accounting_candidate:
    forall u a done,
      Hoare
        (SegmentEscapeAccountingCandidate u done)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s => SegmentEscapeAccountingCandidate u done s).
  Proof.
    intros u a done.
    apply Hoare_normalize. intros snap Hsegment.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_segment_escape_accounting_candidate
               u done dv).
    }
    intros s [Heq _]. subst s. exact Hsegment.
  Qed.

  Lemma GetDfnUpdateLowExtendsSegmentEscapeAccountingActiveOlderCandidate_proof:
    forall u done a,
      Hoare
        (fun s =>
           SegmentEscapeAccountingCandidate u done s /\
           Edge u a /\
           Active a s /\
           dfn s a < dfn s u)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s =>
           SegmentEscapeAccountingCandidate u (done_after done a) s).
  Proof.
    intros u done a.
    apply Hoare_normalize.
    intros snap [Hsegment [Hedge [Hactive_a Hdfn_lt]]].
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s => SegmentEscapeAccountingCandidate u done s)
          (Q2 := fun _ s =>
             (forall x, Visited x s <-> Visited x snap) /\
             (forall x, dfn s x = dfn snap x) /\
             (forall x, fa s x = fa snap x) /\
             (forall x, Active x s <-> Active x snap) /\
             (forall x, x <> u -> low s x = low snap x) /\
             low s u <= dfn snap a).
      - eapply Hoare_conseq_pre.
        2: {
          apply
            (get_dfn_update_low_preserves_segment_escape_accounting_candidate
               u a done).
        }
        intros s Heq_s. subst s. exact Hsegment.
      - eapply Hoare_conseq_pre.
        2: {
          apply (GetDfnUpdateLowKeepsTraversalSnapshotCandidate_proof
                   u a snap).
        }
        intros s Heq_s. exact Heq_s.
    }
    intros _ s [Hsegment_after [Hvisited [Hdfn [Hfa [Hactive
      [Hlow_other Hlow_u_a]]]]]].
    unfold SegmentEscapeAccountingCandidate,
      PendingRootEscapeCandidate,
      OldStackEscapeAnchorCandidate in Hsegment_after |- *.
    intros x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w.
    specialize (Hsegment_after x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w)
      as [Hpending | Hanchor].
    - destruct Hpending as
        [b [Hxu [Hedge_b [Hnot_done_b Hreach_bw]]]].
      destruct (equiv_dec b a) as [Hb_a | Hb_not_a].
      + right.
        exists a.
        split.
        * apply Hactive. exact Hactive_a.
        * split.
          -- pose proof (Hdfn a). pose proof (Hdfn u). lia.
          -- split.
             ++ pose proof (Hdfn a). lia.
             ++ split.
                ** eapply dg_reachable_trans.
                   --- exact Hxu.
                   --- apply dg_reachable_step.
                       rewrite Hb_a in Hedge_b. exact Hedge_b.
                ** rewrite Hb_a in Hreach_bw. exact Hreach_bw.
      + left.
        exists b.
        split; [exact Hxu |].
        split; [exact Hedge_b |].
        split.
        * intros Hdone_after.
          apply Hnot_done_b.
          sets_unfold in Hdone_after.
          destruct Hdone_after as [Hdone_b | Hb_a].
          -- exact Hdone_b.
          -- exfalso. apply Hb_not_a. symmetry. exact Hb_a.
        * exact Hreach_bw.
    - right. exact Hanchor.
  Qed.

  Lemma ProcessEdgeVisitedActiveOlderExtendsSegmentEscapeAccountingCandidate_proof:
    forall W u a done,
      Hoare
        (fun s =>
           SegmentEscapeAccountingCandidate u done s /\
           Edge u a /\
           Visited a s /\
           Active a s /\
           dfn s a < dfn s u)
        (process_edge u W a)
        (fun _ s =>
           SegmentEscapeAccountingCandidate u (done_after done a) s).
  Proof.
    intros W u a done.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hunvis Heq]. subst s1.
      destruct H as [_ [_ [Hvis _]]].
      exfalso. apply Hunvis. exact Hvis.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_ Heq0]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        eapply Hoare_conseq_pre.
        2: {
          apply
            (GetDfnUpdateLowExtendsSegmentEscapeAccountingActiveOlderCandidate_proof
               u done a).
        }
        intros s [Hactive_guard Heq_s]. subst s.
        destruct H as [Hsegment [Hedge [_Hvis [_Hactive Hdfn_lt]]]].
        split; [exact Hsegment |].
        split; [exact Hedge |].
        split; [exact Hactive_guard | exact Hdfn_lt].
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s Hnot_active].
        subst s.
        destruct H as [_ [_ [_ [Hactive _]]]].
        exfalso. apply Hnot_active. exact Hactive.
  Qed.

  Lemma ProcessEdgeVisitedActiveExtendsSegmentEscapeAccountingWithTargetCandidate_proof:
    ProcessEdgeVisitedActiveExtendsSegmentEscapeAccountingWithTargetCandidate_statement.
  Proof.
    unfold
      ProcessEdgeVisitedActiveExtendsSegmentEscapeAccountingWithTargetCandidate_statement.
    intros W u a done.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hunvis Heq]. subst s1.
      destruct H as [_ [_ [_ [_ [Hvis _]]]]].
      exfalso. apply Hunvis. exact Hvis.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_ Heq0]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        destruct (lt_dec (dfn s0 a) (dfn s0 u)) as
          [Holder | Hnot_older].
        * eapply Hoare_conseq_pre.
          2: {
            apply
              (GetDfnUpdateLowExtendsSegmentEscapeAccountingActiveOlderCandidate_proof
                 u done a).
          }
          intros s [Hactive_guard Heq_s]. subst s.
          destruct H as [Hsegment [_Hcoverage [_Htarget
            [Hedge [_Hvis _Hactive]]]]].
          split; [exact Hsegment |].
          split; [exact Hedge |].
          split; [exact Hactive_guard | exact Holder].
        * eapply Hoare_conseq_pre.
          2: {
            apply
              (GetDfnUpdateLowExtendsSegmentEscapeAccountingActiveTargetCandidate_proof
                 u done a).
          }
          intros s [Hactive_guard Heq_s]. subst s.
          destruct H as [Hsegment [Hcoverage [Htarget
            [Hedge [_Hvis _Hactive]]]]].
          split; [exact Hsegment |].
          split; [exact Hcoverage |].
          split; [exact Htarget |].
          split; [exact Hedge |].
          split; [exact Hactive_guard |].
          lia.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s Hnot_active].
        subst s.
        destruct H as [_ [_ [_ [_ [_ Hactive]]]]].
        exfalso. apply Hnot_active. exact Hactive.
  Qed.

  Lemma ProcessEdgeVisitedActiveExtendsSegmentEscapeAccountingWithBlockTargetCandidate_proof:
    forall W u a done,
      Hoare
        (fun s =>
           SegmentEscapeAccountingCandidate u done s /\
           SegmentTreeCoverageByDoneCandidate u done s /\
           ActiveTargetBlocksEscapeAccountedCandidate u done s /\
           Edge u a /\
           ~ done a /\
           Visited a s /\
           Active a s)
        (process_edge u W a)
        (fun _ s =>
           SegmentEscapeAccountingCandidate u (done_after done a) s).
  Proof.
    intros W u a done.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hunvis Heq]. subst s1.
      destruct H as [_ [_ [_ [_ [_ [Hvis _]]]]]].
      exfalso. apply Hunvis. exact Hvis.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_ Heq0]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        destruct (lt_dec (dfn s0 a) (dfn s0 u)) as
          [Holder | Hnot_older].
        * eapply Hoare_conseq_pre.
          2: {
            apply
              (GetDfnUpdateLowExtendsSegmentEscapeAccountingActiveOlderCandidate_proof
                 u done a).
          }
          intros s [Hactive_guard Heq_s]. subst s.
          destruct H as [Hsegment [_Hcoverage [_Hblocks
            [Hedge [_Hnot_done [_Hvis _Hactive]]]]]].
          split; [exact Hsegment |].
          split; [exact Hedge |].
          split; [exact Hactive_guard | exact Holder].
        * eapply Hoare_conseq_pre.
          2: {
            apply
              (GetDfnUpdateLowExtendsSegmentEscapeAccountingActiveEdgeTargetCandidate_proof
                 u done a).
          }
          intros s [Hactive_guard Heq_s]. subst s.
          destruct H as [Hsegment [Hcoverage [Hblocks
            [Hedge [Hnot_done [_Hvis _Hactive]]]]]].
          split; [exact Hsegment |].
          split; [exact Hcoverage |].
          split.
          -- eapply ActiveTargetBlocksProvideActiveEdgeTargetCandidate_proof.
             exact Hblocks.
          -- split; [exact Hedge |].
             split; [exact Hnot_done |].
             split; [exact Hactive_guard |].
             lia.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s Hnot_active].
        subst s.
        destruct H as [_ [_ [_ [_ [_ [_ Hactive]]]]]].
        exfalso. apply Hnot_active. exact Hactive.
  Qed.

  Lemma update_low_parent_preserves_active_processed_child_segment_summary:
    forall parent done n,
      Hoare
        (ActiveProcessedChildSegmentSummaryCandidate parent done)
        (update_low parent n)
        (fun _ s =>
           ActiveProcessedChildSegmentSummaryCandidate parent done s).
  Proof.
    intros parent done n.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - subst. simpl.
      unfold ActiveProcessedChildSegmentSummaryCandidate,
        ChildSelfSegmentEscapeSummaryCandidate,
        PendingRootEscapeCandidate,
        OldStackEscapeAnchorCandidate in H |- *.
      intros child Hdone_child Hedge Hfa Hfa_neq Hactive_child.
      simpl in Hfa, Hfa_neq, Hactive_child.
      assert (Hchild_ne_parent: child <> parent).
      { intro Hchild_parent. subst child. apply Hfa_neq. exact Hfa. }
      specialize (H child Hdone_child Hedge Hfa Hfa_neq Hactive_child).
      intros w Hreach Hnot_vis.
      specialize (H w Hreach Hnot_vis) as [Hpending | Hanchor].
      + left. exact Hpending.
      + right.
        destruct Hanchor as
          [anchor [Hactive_anchor [Hdfn_anchor [Hlow_anchor [Hchild_anchor Hanchor_w]]]]].
        exists anchor.
        simpl.
        split; [exact Hactive_anchor |].
        split; [exact Hdfn_anchor |].
        split.
        * unfold equiv_decb.
          destruct (equiv_dec child parent) as [Hchild_parent | _].
          -- exfalso. apply Hchild_ne_parent. exact Hchild_parent.
          -- exact Hlow_anchor.
        * split; [exact Hchild_anchor | exact Hanchor_w].
	    - destruct H1 as [Heq _]. subst. exact H.
  Qed.

  Lemma get_low_update_low_preserves_loop_inv_done_candidate:
    forall parent child done,
      Hoare
        (LoopInvDoneCandidate parent done)
        (lv <- get' (fun s => low s child);; update_low parent lv)
        (fun _ s => LoopInvDoneCandidate parent done s).
  Proof.
    intros parent child done.
    apply Hoare_normalize. intros snap Hdone.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_loop_inv_done_candidate
               parent lv parent done).
    }
    intros s [Heq _]. subst s. exact Hdone.
  Qed.

  Lemma get_low_update_low_preserves_parent_frame_resume_candidate:
    forall parent child done,
      Hoare
        (ParentFrameResumeCandidate parent done)
        (lv <- get' (fun s => low s child);; update_low parent lv)
        (fun _ s => ParentFrameResumeCandidate parent done s).
  Proof.
    intros parent child done.
    apply Hoare_normalize. intros snap Hframe.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_parent_frame_resume_candidate
               parent lv parent done).
    }
    intros s [Heq _]. subst s. exact Hframe.
  Qed.

  Lemma get_low_update_low_preserves_done_closedness_candidate:
    forall parent child done,
      Hoare
        (DoneClosednessCandidate parent done)
        (lv <- get' (fun s => low s child);; update_low parent lv)
        (fun _ s => DoneClosednessCandidate parent done s).
  Proof.
    intros parent child done.
    apply Hoare_normalize. intros snap Hclosed.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_done_closedness_candidate
               parent lv parent done).
    }
    intros s [Heq _]. subst s. exact Hclosed.
  Qed.

  Lemma get_low_update_low_preserves_processed_tree_children_correct_parent:
    forall parent child done,
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           DoneVisitedCandidate done s /\
           ProcessedTreeChildrenCorrectCandidate parent done s)
        (lv <- get' (fun s => low s child);; update_low parent lv)
        (fun _ s =>
           ProcessedTreeChildrenCorrectCandidate parent done s).
  Proof.
    intros parent child done.
    apply Hoare_normalize. intros snap Hpre.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (update_low_preserves_processed_tree_children_correct_parent
           parent done lv).
    }
    intros s [Heq _]. subst s. exact Hpre.
  Qed.

  Lemma get_low_update_low_preserves_active_processed_child_segment_summary:
    forall parent child done,
      Hoare
        (ActiveProcessedChildSegmentSummaryCandidate parent done)
        (lv <- get' (fun s => low s child);; update_low parent lv)
        (fun _ s =>
           ActiveProcessedChildSegmentSummaryCandidate parent done s).
  Proof.
    intros parent child done.
    apply Hoare_normalize. intros snap Hsummary.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lv.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (update_low_parent_preserves_active_processed_child_segment_summary
           parent done lv).
    }
    intros s [Heq _]. subst s. exact Hsummary.
  Qed.

  Lemma DoneClosednessCandidate_step_active_proof:
    forall u done a s,
      DoneClosednessCandidate u done s ->
      Active a s ->
      DoneClosednessCandidate u (done_after done a) s.
  Proof.
    unfold DoneClosednessCandidate,
      done_reachable_closed,
      done_tree_reachable_closed,
      done_after.
    intros u done a s [Hdone_closed Htree_closed] Hactive_a.
    split.
    - intros v w Hdone_after Hnot_active_v Hreach.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_v | Hv_a].
      + eapply Hdone_closed; eauto.
      + subst v. exfalso. apply Hnot_active_v. exact Hactive_a.
    - intros v w Hdone_after Hnot_active_v Hfa_v Hfa_neq_v Hreach.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_v | Hv_a].
      + eapply Htree_closed; eauto.
      + subst v. exfalso. apply Hnot_active_v. exact Hactive_a.
  Qed.

  Lemma DoneClosednessCandidate_step_settled_proof:
    forall u done a s,
      DoneClosednessCandidate u done s ->
      SettledClosedCandidate s ->
      Visited a s ->
      ~ Active a s ->
      DoneClosednessCandidate u (done_after done a) s.
  Proof.
    unfold DoneClosednessCandidate,
      SettledClosedCandidate,
      done_reachable_closed,
      done_tree_reachable_closed,
      done_after.
    intros u done a s [Hdone_closed Htree_closed] Hsettled _Hvis_a Hnot_active_a.
    split.
    - intros v w Hdone_after Hnot_active_v Hreach.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_v | Hv_a].
      + eapply Hdone_closed; eauto.
      + subst v. eapply Hsettled; eauto.
    - intros v w Hdone_after Hnot_active_v Hfa_v Hfa_neq_v Hreach.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_v | Hv_a].
      + eapply Htree_closed; eauto.
      + subst v. eapply Hsettled; eauto.
  Qed.

  Lemma ProcessedTreeChildrenCorrectCandidate_step_not_tree_proof:
    forall u done a s,
      ProcessedTreeChildrenCorrectCandidate u done s ->
      (fa s a = u -> fa s a <> a -> False) ->
      ProcessedTreeChildrenCorrectCandidate u (done_after done a) s.
  Proof.
    unfold ProcessedTreeChildrenCorrectCandidate,
      ProcessedTreeChildrenLowValidCandidate,
      ProcessedTreeChildrenIsLowCandidate,
      ProcessedTreeChildrenInactiveSelfLowCandidate,
      done_after.
    intros u done a s [Hvalid [His_low Hinactive]] Hnot_tree.
    split.
    - intros child Hdone_after Hedge_child Hfa_child Hfa_neq_child.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_child | Hchild_a].
      + eapply Hvalid; eauto.
      + subst child. exfalso. eapply Hnot_tree; eauto.
    - split.
      + intros child Hdone_after Hedge_child Hfa_child Hfa_neq_child.
        sets_unfold in Hdone_after.
        destruct Hdone_after as [Hdone_child | Hchild_a].
        * eapply His_low; eauto.
        * subst child. exfalso. eapply Hnot_tree; eauto.
      + intros child Hdone_after Hedge_child Hfa_child Hfa_neq_child Hnot_active.
        sets_unfold in Hdone_after.
        destruct Hdone_after as [Hdone_child | Hchild_a].
        * eapply Hinactive; eauto.
        * subst child. exfalso. eapply Hnot_tree; eauto.
  Qed.

  Lemma ActiveProcessedChildSegmentSummaryCandidate_step_not_active_proof:
    forall u done a s,
      ActiveProcessedChildSegmentSummaryCandidate u done s ->
      ~ Active a s ->
      ActiveProcessedChildSegmentSummaryCandidate u (done_after done a) s.
  Proof.
    unfold ActiveProcessedChildSegmentSummaryCandidate,
      done_after.
    intros u done a s Hsummary Hnot_active_a
           child Hdone_after Hedge_child Hfa_child Hfa_neq_child Hactive_child.
    sets_unfold in Hdone_after.
    destruct Hdone_after as [Hdone_child | Hchild_a].
    - eapply Hsummary; eauto.
    - subst child. exfalso. apply Hnot_active_a. exact Hactive_child.
  Qed.

  Lemma ActiveProcessedChildSegmentSummaryCandidate_step_not_tree_proof:
    forall u done a s,
      ActiveProcessedChildSegmentSummaryCandidate u done s ->
      (fa s a = u -> False) ->
      ActiveProcessedChildSegmentSummaryCandidate u (done_after done a) s.
  Proof.
    unfold ActiveProcessedChildSegmentSummaryCandidate,
      done_after.
    intros u done a s Hsummary Hnot_tree
           child Hdone_after Hedge_child Hfa_child Hfa_neq_child Hactive_child.
    sets_unfold in Hdone_after.
    destruct Hdone_after as [Hdone_child | Hchild_a].
    - eapply Hsummary; eauto.
    - subst child. exfalso. apply Hnot_tree. exact Hfa_child.
  Qed.

  Lemma ActiveProcessedChildSegmentSummaryCandidate_step_not_tree_child_proof:
    forall u done a s,
      ActiveProcessedChildSegmentSummaryCandidate u done s ->
      (fa s a = u -> fa s a <> a -> False) ->
      ActiveProcessedChildSegmentSummaryCandidate u (done_after done a) s.
  Proof.
    unfold ActiveProcessedChildSegmentSummaryCandidate,
      done_after.
    intros u done a s Hsummary Hnot_tree_child
           child Hdone_after Hedge_child Hfa_child Hfa_neq_child Hactive_child.
    sets_unfold in Hdone_after.
    destruct Hdone_after as [Hdone_child | Hchild_a].
    - eapply Hsummary; eauto.
    - subst child. exfalso. eapply Hnot_tree_child; eauto.
  Qed.

  Lemma get_dfn_update_low_preserves_loop_inv_done_candidate:
    forall parent a done,
      Hoare
        (LoopInvDoneCandidate parent done)
        (dv <- get' (fun s => dfn s a);; update_low parent dv)
        (fun _ s => LoopInvDoneCandidate parent done s).
  Proof.
    intros parent a done.
    apply Hoare_normalize. intros snap Hdone.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_loop_inv_done_candidate
               parent dv parent done).
    }
    intros s [Heq _]. subst s. exact Hdone.
  Qed.

  Lemma get_dfn_update_low_preserves_parent_frame_resume_candidate:
    forall parent a done,
      Hoare
        (ParentFrameResumeCandidate parent done)
        (dv <- get' (fun s => dfn s a);; update_low parent dv)
        (fun _ s => ParentFrameResumeCandidate parent done s).
  Proof.
    intros parent a done.
    apply Hoare_normalize. intros snap Hframe.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_parent_frame_resume_candidate
               parent dv parent done).
    }
    intros s [Heq _]. subst s. exact Hframe.
  Qed.

  Lemma get_dfn_update_low_preserves_done_closedness_candidate:
    forall parent a done,
      Hoare
        (DoneClosednessCandidate parent done)
        (dv <- get' (fun s => dfn s a);; update_low parent dv)
        (fun _ s => DoneClosednessCandidate parent done s).
  Proof.
    intros parent a done.
    apply Hoare_normalize. intros snap Hclosed.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply (update_low_preserves_done_closedness_candidate
               parent dv parent done).
    }
    intros s [Heq _]. subst s. exact Hclosed.
  Qed.

  Lemma get_dfn_update_low_preserves_processed_tree_children_correct_parent:
    forall parent a done,
      Hoare
        (fun s =>
           GlobalShapeCandidate s /\
           DoneVisitedCandidate done s /\
           ProcessedTreeChildrenCorrectCandidate parent done s)
        (dv <- get' (fun s => dfn s a);; update_low parent dv)
        (fun _ s =>
           ProcessedTreeChildrenCorrectCandidate parent done s).
  Proof.
    intros parent a done.
    apply Hoare_normalize. intros snap Hpre.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (update_low_preserves_processed_tree_children_correct_parent
           parent done dv).
    }
    intros s [Heq _]. subst s. exact Hpre.
  Qed.

  Lemma get_dfn_update_low_preserves_active_processed_child_segment_summary:
    forall parent a done,
      Hoare
        (ActiveProcessedChildSegmentSummaryCandidate parent done)
        (dv <- get' (fun s => dfn s a);; update_low parent dv)
        (fun _ s =>
           ActiveProcessedChildSegmentSummaryCandidate parent done s).
  Proof.
    intros parent a done.
    apply Hoare_normalize. intros snap Hsummary.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (update_low_parent_preserves_active_processed_child_segment_summary
           parent done dv).
    }
    intros s [Heq _]. subst s. exact Hsummary.
  Qed.

  Lemma get_dfn_update_low_extends_loop_inv_phase6_active_candidate:
    forall u a done,
      Edge u a ->
      Hoare
        (fun s =>
           LoopInvPhase6Candidate u done s /\
           Visited a s /\
           Active a s /\
           fa s a <> u)
        (dv <- get' (fun s => dfn s a);; update_low u dv)
        (fun _ s => LoopInvPhase6Candidate u (done_after done a) s).
  Proof.
    intros u a done Hedge.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s => LoopInvLowCandidate u (done_after done a) s)
          (Q2 := fun _ s =>
             ParentFrameResumeCandidate u (done_after done a) s /\
             DoneClosednessCandidate u (done_after done a) s /\
             ProcessedTreeChildrenCorrectCandidate u (done_after done a) s /\
             ActiveProcessedChildSegmentSummaryCandidate
               u (done_after done a) s).
      - apply Hoare_conj
          with
            (Q1 := fun _ s => LoopInvDoneCandidate u (done_after done a) s)
            (Q2 := fun _ s =>
               PartialRootLowEquationCandidate u (done_after done a) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (get_dfn_update_low_preserves_loop_inv_done_candidate
                 u a (done_after done a)).
          }
          intros s [Hphase6 [Hvis_a [_Hactive_a _Hfa_not]]].
          destruct Hphase6 as [Hlow _].
          destruct Hlow as [Hdone_loop _Hpartial].
          destruct Hdone_loop as [Hlocal Hdisc].
          split; [exact Hlocal |].
          eapply DoneDisciplineCandidate_step_proof; eauto.
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (GetDfnUpdateLowExtendsPartialLowStackCandidate_proof
                 u done a Hedge).
          }
          intros s [Hphase6 [_Hvis_a [Hactive_a Hfa_not_u]]].
          destruct Hphase6 as [Hlow _].
          destruct Hlow as [_Hdone_loop Hpartial].
          split; [exact Hpartial |].
          split; [exact Hactive_a | exact Hfa_not_u].
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               ParentFrameResumeCandidate u (done_after done a) s)
            (Q2 := fun _ s =>
               DoneClosednessCandidate u (done_after done a) s /\
               ProcessedTreeChildrenCorrectCandidate u (done_after done a) s /\
               ActiveProcessedChildSegmentSummaryCandidate
                 u (done_after done a) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (get_dfn_update_low_preserves_parent_frame_resume_candidate
                 u a (done_after done a)).
          }
          intros s [Hphase6 [Hvis_a _]].
          destruct Hphase6 as [_Hlow [Hframe _]].
          eapply ParentFrameResumeCandidate_step_visited_proof; eauto.
        + apply Hoare_conj
            with
              (Q1 := fun _ s =>
                 DoneClosednessCandidate u (done_after done a) s)
              (Q2 := fun _ s =>
                 ProcessedTreeChildrenCorrectCandidate
                   u (done_after done a) s /\
                 ActiveProcessedChildSegmentSummaryCandidate
                   u (done_after done a) s).
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (get_dfn_update_low_preserves_done_closedness_candidate
                   u a (done_after done a)).
            }
            intros s [Hphase6 [_Hvis_a [Hactive_a _Hfa_not]]].
            destruct Hphase6 as [_Hlow [_Hframe [Hclosed _]]].
            eapply DoneClosednessCandidate_step_active_proof; eauto.
          * apply Hoare_conj
              with
                (Q1 := fun _ s =>
                   ProcessedTreeChildrenCorrectCandidate
                     u (done_after done a) s)
                (Q2 := fun _ s =>
                   ActiveProcessedChildSegmentSummaryCandidate
                     u (done_after done a) s).
            -- eapply Hoare_conseq_pre.
               2: {
                 apply
                   (get_dfn_update_low_preserves_processed_tree_children_correct_parent
                      u a (done_after done a)).
               }
               intros s [Hphase6 [Hvis_a [Hactive_a Hfa_not_u]]].
               destruct Hphase6 as [Hlow [_Hframe [_Hclosed [Hchildren _]]]].
               destruct Hlow as [Hdone_loop _Hpartial].
               destruct Hdone_loop as [Hlocal Hdisc].
               destruct Hlocal as [Hglobal _].
               assert (Hdisc_after:
                         DoneDisciplineCandidate u (done_after done a) s).
               { eapply DoneDisciplineCandidate_step_proof; eauto. }
               destruct Hdisc_after as [_Hsubset_after Hdone_vis_after].
               split; [exact Hglobal |].
               split; [exact Hdone_vis_after |].
               eapply ProcessedTreeChildrenCorrectCandidate_step_not_tree_proof.
               ++ exact Hchildren.
               ++ intros Hfa_a _Hfa_neq_a.
                  apply Hfa_not_u. exact Hfa_a.
            -- eapply Hoare_conseq_pre.
               2: {
                 apply
                   (get_dfn_update_low_preserves_active_processed_child_segment_summary
                      u a (done_after done a)).
               }
               intros s [Hphase6 [_Hvis_a [_Hactive_a Hfa_not_u]]].
               destruct Hphase6 as [_Hlow [_Hframe [_Hclosed [_Hchildren Hactive_segments]]]].
               eapply ActiveProcessedChildSegmentSummaryCandidate_step_not_tree_proof.
               ++ exact Hactive_segments.
               ++ intros Hfa_a. apply Hfa_not_u. exact Hfa_a.
    }
    intros _ s [Hlow [Hframe [Hclosed [Hchildren Hactive_segments]]]].
    unfold LoopInvPhase6Candidate.
    split; [exact Hlow |].
    split; [exact Hframe |].
    split; [exact Hclosed |].
    split; [exact Hchildren | exact Hactive_segments].
  Qed.

  Lemma GetDfnUpdateLowExtendsPartialLowSelfCandidate_proof:
    forall u done,
      Edge u u ->
      Hoare
        (PartialRootLowEquationCandidate u done)
        (dv <- get' (fun s => dfn s u);; update_low u dv)
        (fun _ s =>
           PartialRootLowEquationCandidate u (done_after done u) s).
  Proof.
    intros u done Hedge.
    unfold PartialRootLowEquationCandidate.
    apply Hoare_conj.
    - apply Hoare_normalize. intros snap [Hfront _Hsrc].
      eapply Hoare_bind. { apply Hoare_get'. }
      simpl. intros dv.
      eapply Hoare_conseq_post.
      2: {
        eapply Hoare_conseq_pre.
        2: { apply (UpdateLowPreservesFrontierCandidate_proof u done dv). }
        intros s [Heq_s _]. subst s. exact Hfront.
      }
      intros ret st_after Hfront_after.
      eapply LowFrontierCandidate_step_proof.
      + exact Hfront_after.
      + exact Hedge.
      + intros _Hfa. lia.
      + intros _Hactive. exact (proj1 Hfront_after).
    - apply Hoare_normalize. intros snap [_Hfront Hsrc].
      eapply Hoare_bind. { apply Hoare_get'. }
      simpl. intros dv.
      eapply Hoare_conseq_post.
      2: {
        apply Hoare_conj
          with (Q1 := fun _ s =>
                        LowSourceCandidate u done s \/ low s u = dv)
               (Q2 := fun _ s =>
                        dv = dfn snap u /\
                        forall x, dfn s x = dfn snap x).
        + eapply Hoare_conseq_pre.
          2: { apply (UpdateLowSourceOrIncomingCandidate_proof u done dv). }
          intros s [Heq_s _]. subst s. exact Hsrc.
        + apply Hoare_conj.
          * unfold Hoare.
            intros st1 ret_get st2 Hpre Hrun.
            destruct Hpre as [_ Hdv].
            exact Hdv.
          * eapply Hoare_conseq_post.
            2: {
              eapply Hoare_conseq_pre.
              2: { apply (UpdateLowKeepsSnapshotFieldsCandidate_proof u dv snap). }
              intros s [Heq_s _]. subst s. reflexivity.
            }
            intros ret_update st_update [Hdfn_keep _].
            exact Hdfn_keep.
      }
      intros ret st_after [[Hsrc_after | Hlow_incoming] [Hdv Hdfn_keep]].
      + apply LowSourceCandidate_step_keep_proof.
        exact Hsrc_after.
      + left.
        rewrite Hlow_incoming.
        rewrite Hdv.
        rewrite <- Hdfn_keep.
        reflexivity.
  Qed.

  Lemma get_dfn_update_low_extends_loop_inv_phase6_active_self_candidate:
    forall u done,
      Edge u u ->
      Hoare
        (LoopInvPhase6Candidate u done)
        (dv <- get' (fun s => dfn s u);; update_low u dv)
        (fun _ s => LoopInvPhase6Candidate u (done_after done u) s).
  Proof.
    intros u done Hedge.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s => LoopInvLowCandidate u (done_after done u) s)
          (Q2 := fun _ s =>
             ParentFrameResumeCandidate u (done_after done u) s /\
             DoneClosednessCandidate u (done_after done u) s /\
             ProcessedTreeChildrenCorrectCandidate u (done_after done u) s /\
             ActiveProcessedChildSegmentSummaryCandidate
               u (done_after done u) s).
      - apply Hoare_conj
          with
            (Q1 := fun _ s => LoopInvDoneCandidate u (done_after done u) s)
            (Q2 := fun _ s =>
               PartialRootLowEquationCandidate u (done_after done u) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (get_dfn_update_low_preserves_loop_inv_done_candidate
                 u u (done_after done u)).
          }
          intros s Hphase6.
          destruct Hphase6 as [Hlow _].
          destruct Hlow as [Hdone_loop _Hpartial].
          destruct Hdone_loop as [Hlocal Hdisc].
          pose proof Hlocal as Hlocal_keep.
          destruct Hlocal as [_Hshape [_Hsettled [Hvis_u _]]].
          split; [exact Hlocal_keep |].
          eapply DoneDisciplineCandidate_step_proof; eauto.
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (GetDfnUpdateLowExtendsPartialLowSelfCandidate_proof
                 u done Hedge).
          }
          intros s Hphase6.
          destruct Hphase6 as [Hlow _].
          exact (proj2 Hlow).
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               ParentFrameResumeCandidate u (done_after done u) s)
            (Q2 := fun _ s =>
               DoneClosednessCandidate u (done_after done u) s /\
               ProcessedTreeChildrenCorrectCandidate
                 u (done_after done u) s /\
               ActiveProcessedChildSegmentSummaryCandidate
                 u (done_after done u) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (get_dfn_update_low_preserves_parent_frame_resume_candidate
                 u u (done_after done u)).
          }
          intros s Hphase6.
          destruct Hphase6 as [Hlow [Hframe _]].
          destruct Hlow as [Hdone_loop _].
          destruct Hdone_loop as [Hlocal _].
          destruct Hlocal as [_Hshape [_Hsettled [Hvis_u _]]].
          eapply ParentFrameResumeCandidate_step_visited_proof; eauto.
        + apply Hoare_conj
            with
              (Q1 := fun _ s =>
                 DoneClosednessCandidate u (done_after done u) s)
              (Q2 := fun _ s =>
                 ProcessedTreeChildrenCorrectCandidate
                   u (done_after done u) s /\
                 ActiveProcessedChildSegmentSummaryCandidate
                   u (done_after done u) s).
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (get_dfn_update_low_preserves_done_closedness_candidate
                   u u (done_after done u)).
            }
            intros s Hphase6.
            destruct Hphase6 as [Hlow [_Hframe [Hclosed _]]].
            destruct Hlow as [Hdone_loop _].
            destruct Hdone_loop as [Hlocal _].
            destruct Hlocal as [_Hshape [_Hsettled [_Hvis_u [Hactive_u _]]]].
            eapply DoneClosednessCandidate_step_active_proof; eauto.
          * apply Hoare_conj
              with
                (Q1 := fun _ s =>
                   ProcessedTreeChildrenCorrectCandidate
                     u (done_after done u) s)
                (Q2 := fun _ s =>
                   ActiveProcessedChildSegmentSummaryCandidate
                     u (done_after done u) s).
            -- eapply Hoare_conseq_pre.
               2: {
                 apply
                   (get_dfn_update_low_preserves_processed_tree_children_correct_parent
                      u u (done_after done u)).
               }
               intros s Hphase6.
               destruct Hphase6 as [Hlow [_Hframe [_Hclosed [Hchildren _]]]].
               destruct Hlow as [Hdone_loop _Hpartial].
               destruct Hdone_loop as [Hlocal Hdisc].
               destruct Hlocal as [Hglobal [_Hsettled [Hvis_u _]]].
               assert (Hdisc_after:
                         DoneDisciplineCandidate u (done_after done u) s).
               { eapply DoneDisciplineCandidate_step_proof; eauto. }
               destruct Hdisc_after as [_Hsubset_after Hdone_vis_after].
               split; [exact Hglobal |].
               split; [exact Hdone_vis_after |].
               eapply ProcessedTreeChildrenCorrectCandidate_step_not_tree_proof.
               ++ exact Hchildren.
               ++ intros Hfa_u Hfa_neq_u.
                  apply Hfa_neq_u. exact Hfa_u.
            -- eapply Hoare_conseq_pre.
               2: {
                 apply
                   (get_dfn_update_low_preserves_active_processed_child_segment_summary
                      u u (done_after done u)).
               }
               intros s Hphase6.
               destruct Hphase6 as
                 [_Hlow [_Hframe [_Hclosed [_Hchildren Hactive_segments]]]].
               eapply
                 ActiveProcessedChildSegmentSummaryCandidate_step_not_tree_child_proof.
               ++ exact Hactive_segments.
               ++ intros Hfa_u Hfa_neq_u.
                  apply Hfa_neq_u. exact Hfa_u.
    }
    intros _ s [Hlow [Hframe [Hclosed [Hchildren Hactive_segments]]]].
    unfold LoopInvPhase6Candidate.
    split; [exact Hlow |].
    split; [exact Hframe |].
    split; [exact Hclosed |].
    split; [exact Hchildren | exact Hactive_segments].
  Qed.

  Lemma ProcessEdgeVisitedActiveExtendsLoopInvPhase6Candidate_proof:
    forall W u a done,
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvPhase6Candidate u done s /\
           Visited a s /\
           Active a s)
        (process_edge u W a)
        (fun _ s => LoopInvPhase6Candidate u (done_after done a) s).
  Proof.
    intros W u a done Hedge Hnot_done.
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
        destruct (equiv_dec a u) as [Ha_u | Ha_not_u].
        * rewrite Ha_u in Hedge.
          rewrite Ha_u.
          eapply Hoare_conseq_pre.
          2: {
            apply
              (get_dfn_update_low_extends_loop_inv_phase6_active_self_candidate
                 u done Hedge).
          }
          intros s [_Hactive_guard Heq_s]. subst s.
          exact (proj1 H).
        * eapply Hoare_conseq_pre.
          2: {
            apply
              (get_dfn_update_low_extends_loop_inv_phase6_active_candidate
                 u a done Hedge).
          }
          intros s [Hactive_guard Heq_s]. subst s.
          destruct H as [Hphase6 [Hvis_a _Hactive_a]].
          assert (Hfa_not_u: fa s0 a <> u).
          { intro Hfa_a.
            destruct Hphase6 as [_Hlow [Hframe _Htail]].
            destruct Hframe as [_Hdone_vis [_Hfa_child Hfa_not_done]].
            apply Ha_not_u.
            eapply Hfa_not_done; eauto. }
          split; [exact Hphase6 |].
          split; [exact Hvis_a |].
          split; [exact Hactive_guard | exact Hfa_not_u].
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s Hnot_active].
        subst s.
        destruct H as [_ [_ Hactive_a]].
        exfalso. apply Hnot_active. exact Hactive_a.
  Qed.

  Lemma ProcessEdgeVisitedActivePreservesActiveTargetBlocksCandidate_proof:
    forall W u a done,
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           ActiveTargetBlocksEscapeAccountedCandidate u done s /\
           Visited a s /\
           Active a s)
        (process_edge u W a)
        (fun _ s =>
           ActiveTargetBlocksEscapeAccountedCandidate u (done_after done a) s).
  Proof.
    intros W u a done Hedge Hnot_done.
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
        destruct (lt_dec (dfn s0 a) (dfn s0 u)) as
          [Holder | Hnot_older].
        * eapply Hoare_conseq_post.
          2: {
            apply Hoare_conj
              with
                (Q1 := fun _ s =>
                   ActiveTargetBlocksEscapeAccountedCandidate u done s)
                (Q2 := fun _ s =>
                   (forall x, dfn s x = dfn s0 x) /\
                   (forall x, Active x s <-> Active x s0) /\
                   low s u <= dfn s0 a).
            - eapply Hoare_conseq_pre.
              2: {
                apply
                  (get_dfn_update_low_preserves_active_target_blocks_escape_accounted_candidate
                     u done a).
              }
              intros s [Hactive_guard Heq_s]. subst s.
              exact (proj1 H).
            - eapply Hoare_conseq_post.
              2: {
                eapply Hoare_conseq_pre.
                2: {
                  apply (GetDfnUpdateLowKeepsTraversalSnapshotCandidate_proof
                           u a s0).
                }
                intros s [Hactive_guard Heq_s]. subst s.
                reflexivity.
              }
              intros _ s [_Hvisited [Hdfn [_Hfa [Hactive [_Hlow_other Hlow_u_a]]]]].
              split; [exact Hdfn |].
              split; [exact Hactive | exact Hlow_u_a].
          }
          intros _ s [Hblocks [Hdfn [Hactive_keep Hlow_u_a]]].
          unfold ActiveTargetBlocksEscapeAccountedCandidate,
            ActiveTargetBlockEscapeAccountedCandidate,
            PendingRootEscapeCandidate,
            OldStackEscapeAnchorCandidate,
            done_after in Hblocks |- *.
          intros block target w Hblock_target Hblock_valid Hreach Hnot_vis.
          specialize (Hblocks block target w Hblock_target) as Haccount.
          assert (Hblock_valid_old:
                    forall b,
                      block b ->
                      Edge u b /\ ~ done b /\ Active b s /\
                      dfn s u <= dfn s b).
          { intros b Hb.
            specialize (Hblock_valid b Hb) as
              [Hedge_b [Hnot_done_after_b [Hactive_b Hdfn_b]]].
            split; [exact Hedge_b |].
            split.
            - intros Hdone_b.
              apply Hnot_done_after_b.
              sets_unfold. left. exact Hdone_b.
            - split; [exact Hactive_b | exact Hdfn_b]. }
          specialize (Haccount Hblock_valid_old Hreach Hnot_vis)
            as [Hpending | Hanchor].
          -- destruct Hpending as
               [next [Htarget_u [Hedge_next [Hnot_done_block Hnext_w]]]].
             destruct (equiv_dec next a) as [Hnext_a | Hnext_not_a].
             ++ right.
                exists a.
                split.
                ** destruct H as [_ [_ Hactive_a_pre]].
                   simpl in Hactive_a_pre.
                   apply (proj2 (Hactive_keep a)).
                   exact Hactive_a_pre.
                ** split.
                   --- pose proof (Hdfn a). pose proof (Hdfn u). lia.
                   --- split.
                       +++ pose proof (Hdfn a). lia.
                       +++ split.
                           *** eapply dg_reachable_trans.
                               ---- exact Htarget_u.
                               ---- apply dg_reachable_step.
                                    rewrite Hnext_a in Hedge_next.
                                    exact Hedge_next.
                           *** rewrite Hnext_a in Hnext_w. exact Hnext_w.
             ++ left.
                exists next.
                split; [exact Htarget_u |].
                split; [exact Hedge_next |].
                split.
                ** intros Hbad.
                   apply Hnot_done_block.
                   sets_unfold in Hbad. sets_unfold.
                   destruct Hbad as [[Hdone_next | Hnext_a'] | Hblock_next].
                   --- left. exact Hdone_next.
                   --- exfalso. apply Hnext_not_a. symmetry. exact Hnext_a'.
                   --- right. exact Hblock_next.
                ** exact Hnext_w.
          -- right. exact Hanchor.
        * eapply Hoare_conseq_post.
          2: {
            apply Hoare_conj
              with
                (Q1 := fun _ s =>
                   ActiveTargetBlocksEscapeAccountedCandidate u done s)
                (Q2 := fun _ s =>
                   (forall x, dfn s x = dfn s0 x) /\
                   (forall x, Active x s <-> Active x s0)).
            - eapply Hoare_conseq_pre.
              2: {
                apply
                  (get_dfn_update_low_preserves_active_target_blocks_escape_accounted_candidate
                     u done a).
              }
              intros s [Hactive_guard Heq_s]. subst s.
              exact (proj1 H).
            - eapply Hoare_conseq_post.
              2: {
                eapply Hoare_conseq_pre.
                2: {
                  apply (GetDfnUpdateLowKeepsTraversalSnapshotCandidate_proof
                           u a s0).
                }
                intros s [Hactive_guard Heq_s]. subst s.
                reflexivity.
              }
              intros _ s [_Hvisited [Hdfn [_Hfa [Hactive [_Hlow_other _Hlow_u_a]]]]].
              split; [exact Hdfn | exact Hactive].
          }
          intros _ s [Hblocks [Hdfn Hactive_keep]].
          unfold ActiveTargetBlocksEscapeAccountedCandidate,
            ActiveTargetBlockEscapeAccountedCandidate,
            PendingRootEscapeCandidate,
            OldStackEscapeAnchorCandidate,
            done_after in Hblocks |- *.
          intros block target w Hblock_target Hblock_valid Hreach Hnot_vis.
          pose (block_with_a := [a] ∪ block).
          assert (Hblock_with_a_target: block_with_a target).
          { unfold block_with_a. sets_unfold. right. exact Hblock_target. }
          assert (Hblock_with_a_valid:
                    forall b,
                      block_with_a b ->
                      Edge u b /\ ~ done b /\ Active b s /\
                      dfn s u <= dfn s b).
          { intros b Hb.
            unfold block_with_a in Hb.
            sets_unfold in Hb.
            destruct Hb as [Ha_b | Hblock_b].
            - subst b.
              destruct H as [_ [_ Hactive_a_pre]].
              split; [exact Hedge |].
              split; [exact Hnot_done |].
              split.
              + simpl in Hactive_a_pre.
                apply (proj2 (Hactive_keep a)).
                exact Hactive_a_pre.
              + pose proof (Hdfn a).
                pose proof (Hdfn u).
                lia.
            - specialize (Hblock_valid b Hblock_b) as
                [Hedge_b [Hnot_done_after_b [Hactive_b Hdfn_b]]].
              split; [exact Hedge_b |].
              split.
              + intros Hdone_b.
                apply Hnot_done_after_b.
                sets_unfold. left. exact Hdone_b.
              + split; [exact Hactive_b | exact Hdfn_b]. }
          specialize (Hblocks block_with_a target w Hblock_with_a_target
                        Hblock_with_a_valid Hreach Hnot_vis)
            as [Hpending | Hanchor].
          -- left.
             destruct Hpending as
               [next [Htarget_u [Hedge_next [Hnot_done_block Hnext_w]]]].
             exists next.
             split; [exact Htarget_u |].
             split; [exact Hedge_next |].
             split.
             ++ intros Hbad.
                apply Hnot_done_block.
                unfold block_with_a.
                sets_unfold in Hbad. sets_unfold.
                destruct Hbad as [[Hdone_next | Hnext_a] | Hblock_next].
                ** left. exact Hdone_next.
                ** right. left. exact Hnext_a.
                ** right. right. exact Hblock_next.
             ++ exact Hnext_w.
          -- right. exact Hanchor.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s Hnot_active].
        subst s.
        destruct H as [_ [_ Hactive_a]].
        exfalso. apply Hnot_active. exact Hactive_a.
  Qed.

  Lemma ProcessEdgeVisitedNonStackPreservesActiveTargetBlocksCandidate_proof:
    forall W u a done,
      Hoare
        (fun s =>
           ActiveTargetBlocksEscapeAccountedCandidate u done s /\
           SettledClosedCandidate s /\
           Visited a s /\
           ~ Active a s)
        (process_edge u W a)
        (fun _ s =>
           ActiveTargetBlocksEscapeAccountedCandidate
             u (done_after done a) s).
  Proof.
    intros W u a done.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hunvis Heq]. subst s1.
      destruct H as [_ [_ [Hvis _]]].
      exfalso. apply Hunvis. exact Hvis.
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [_ Heq0]. subst s1.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        intro_state.
        destruct H1 as [Hactive_guard Heq1]. subst s1.
        destruct H as [_ [_ [_ Hnot_active]]].
        exfalso. apply Hnot_active. exact Hactive_guard.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _Hnot_stack_guard].
        subst s.
        destruct H as [Hblocks [Hsettled [Hvis Hnot_active]]].
        eapply ActiveTargetBlocksEscapeAccountedCandidate_step_nonactive_visited_proof;
          eauto.
  Qed.

  Lemma ProcessEdgeVisitedNonStackExtendsLoopInvPhase6Candidate_proof:
    forall W u a done,
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvPhase6Candidate u done s /\
           Visited a s /\
           ~ Active a s)
        (process_edge u W a)
        (fun _ s => LoopInvPhase6Candidate u (done_after done a) s).
  Proof.
    intros W u a done Hedge Hnot_done.
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
        destruct H as [_ [_ Hnot_active]].
        exfalso. apply Hnot_active. exact Hactive_guard.
      + eapply Hoare_conseq_post.
        2: { apply Hoare_assume_s. }
        intros _ s [Heq_s _Hnot_active_guard].
        subst s.
        destruct H as [Hphase6 [Hvis_a Hnot_active_a]].
        destruct Hphase6 as
          [Hlow [Hframe [Hclosed [Hchildren Hactive_segments]]]].
        destruct Hlow as [Hdone_loop Hpartial].
        destruct Hdone_loop as [Hlocal Hdisc].
        pose proof Hlocal as Hlocal_keep.
        destruct Hlocal as [Hglobal [Hsettled [_Hvis_u [_Hactive_u _Horder]]]].
        assert (Hfa_tree_false:
                  fa s0 a = u -> fa s0 a <> a -> False).
        { intros Hfa_a Hfa_neq_a.
          destruct Hframe as [_Hdone_vis [_Hfa_child Hfa_not_done]].
          assert (Ha_u: a = u) by (eapply Hfa_not_done; eauto).
          subst a. apply Hfa_neq_a. exact Hfa_a. }
        unfold LoopInvPhase6Candidate.
        split.
        * split.
          -- split; [exact Hlocal_keep |].
             eapply DoneDisciplineCandidate_step_proof; eauto.
          -- eapply PartialRootLowEquationCandidate_step_keep_proof.
	             ++ exact Hpartial.
	             ++ exact Hedge.
	             ++ intros Hfa_a.
	                destruct Hframe as [_Hdone_vis [_Hfa_child Hfa_not_done]].
	                assert (Ha_u: a = u) by (eapply Hfa_not_done; eauto).
	                subst a. lia.
	             ++ intros Hactive_a.
	                exfalso. apply Hnot_active_a. exact Hactive_a.
        * split.
          -- eapply ParentFrameResumeCandidate_step_visited_proof; eauto.
          -- split.
             ++ eapply DoneClosednessCandidate_step_settled_proof; eauto.
             ++ split.
                ** eapply ProcessedTreeChildrenCorrectCandidate_step_not_tree_proof;
                     eauto.
                ** eapply ActiveProcessedChildSegmentSummaryCandidate_step_not_active_proof;
                     eauto.
  Qed.

  Lemma ProcessEdgeVisitedActiveExtendsLoopInvPhase7WithTargetCandidate_proof:
    forall W u a done,
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvPhase7Candidate u done s /\
           ActiveTargetSegmentEscapeAccountedCandidate u done s /\
           ActiveTargetBlocksEscapeAccountedCandidate u done s /\
           Visited a s /\
           Active a s)
        (process_edge u W a)
        (fun _ s => LoopInvPhase7Candidate u (done_after done a) s).
  Proof.
    intros W u a done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s => LoopInvPhase6Candidate u (done_after done a) s)
          (Q2 := fun _ s =>
             SegmentEscapeAccountingCandidate u (done_after done a) s /\
             SegmentTreeCoverageByDoneCandidate u (done_after done a) s /\
             ActiveTargetBlocksEscapeAccountedCandidate
               u (done_after done a) s).
      - eapply Hoare_conseq_pre.
        2: {
          apply
            (ProcessEdgeVisitedActiveExtendsLoopInvPhase6Candidate_proof
               W u a done Hedge Hnot_done).
        }
        intros s [Hloop7 [_Htarget [_Hblocks [Hvis Hactive]]]].
        destruct Hloop7 as [Hphase6 _].
        split; [exact Hphase6 |].
        split; [exact Hvis | exact Hactive].
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               SegmentEscapeAccountingCandidate u (done_after done a) s)
            (Q2 := fun _ s =>
               SegmentTreeCoverageByDoneCandidate u (done_after done a) s /\
               ActiveTargetBlocksEscapeAccountedCandidate
                 u (done_after done a) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (ProcessEdgeVisitedActiveExtendsSegmentEscapeAccountingWithTargetCandidate_proof
                 W u a done).
          }
          intros s [Hloop7 [Htarget [_Hblocks [Hvis Hactive]]]].
          destruct Hloop7 as [_Hphase6 [Hsegment [Hcoverage _Hloop_blocks]]].
          split; [exact Hsegment |].
          split; [exact Hcoverage |].
          split; [exact Htarget |].
          split; [exact Hedge |].
          split; [exact Hvis | exact Hactive].
        + apply Hoare_conj.
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (ProcessEdgeVisitedActiveExtendsSegmentTreeCoverageCandidate_proof
                   W u a done).
            }
            intros s [Hloop7 [_Htarget [_Hblocks [Hvis Hactive]]]].
            destruct Hloop7 as [_Hphase6 [_Hsegment [Hcoverage _Hloop_blocks]]].
            split; [exact Hcoverage |].
            split; [exact Hvis | exact Hactive].
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (ProcessEdgeVisitedActivePreservesActiveTargetBlocksCandidate_proof
                   W u a done Hedge Hnot_done).
            }
            intros s [_Hloop7 [_Htarget [Hblocks [Hvis Hactive]]]].
            split; [exact Hblocks |].
            split; [exact Hvis | exact Hactive].
    }
    intros _ s [Hphase6 [Hsegment [Hcoverage Hblocks]]].
    unfold LoopInvPhase7Candidate.
    split; [exact Hphase6 |].
    split; [exact Hsegment |].
    split; [exact Hcoverage | exact Hblocks].
  Qed.

  Lemma ProcessEdgeVisitedActiveExtendsLoopInvPhase7WithBlockTargetCandidate_proof:
    forall W u a done,
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvPhase7Candidate u done s /\
           ActiveTargetBlocksEscapeAccountedCandidate u done s /\
           Visited a s /\
           Active a s)
        (process_edge u W a)
        (fun _ s => LoopInvPhase7Candidate u (done_after done a) s).
  Proof.
    intros W u a done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s => LoopInvPhase6Candidate u (done_after done a) s)
          (Q2 := fun _ s =>
             SegmentEscapeAccountingCandidate u (done_after done a) s /\
             SegmentTreeCoverageByDoneCandidate u (done_after done a) s /\
             ActiveTargetBlocksEscapeAccountedCandidate
               u (done_after done a) s).
      - eapply Hoare_conseq_pre.
        2: {
          apply
            (ProcessEdgeVisitedActiveExtendsLoopInvPhase6Candidate_proof
               W u a done Hedge Hnot_done).
        }
        intros s [Hloop7 [_Hblocks [Hvis Hactive]]].
        destruct Hloop7 as [Hphase6 _].
        split; [exact Hphase6 |].
        split; [exact Hvis | exact Hactive].
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               SegmentEscapeAccountingCandidate u (done_after done a) s)
            (Q2 := fun _ s =>
               SegmentTreeCoverageByDoneCandidate u (done_after done a) s /\
               ActiveTargetBlocksEscapeAccountedCandidate
                 u (done_after done a) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (ProcessEdgeVisitedActiveExtendsSegmentEscapeAccountingWithBlockTargetCandidate_proof
                 W u a done).
          }
          intros s [Hloop7 [Hblocks [Hvis Hactive]]].
          destruct Hloop7 as [_Hphase6 [Hsegment [Hcoverage _Hloop_blocks]]].
          split; [exact Hsegment |].
          split; [exact Hcoverage |].
          split; [exact Hblocks |].
          split; [exact Hedge |].
          split; [exact Hnot_done |].
          split; [exact Hvis | exact Hactive].
        + apply Hoare_conj.
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (ProcessEdgeVisitedActiveExtendsSegmentTreeCoverageCandidate_proof
                   W u a done).
            }
            intros s [Hloop7 [_Hblocks [Hvis Hactive]]].
            destruct Hloop7 as [_Hphase6 [_Hsegment [Hcoverage _Hloop_blocks]]].
            split; [exact Hcoverage |].
            split; [exact Hvis | exact Hactive].
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (ProcessEdgeVisitedActivePreservesActiveTargetBlocksCandidate_proof
                   W u a done Hedge Hnot_done).
            }
            intros s [_Hloop7 [Hblocks [Hvis Hactive]]].
            split; [exact Hblocks |].
            split; [exact Hvis | exact Hactive].
    }
    intros _ s [Hphase6 [Hsegment [Hcoverage Hblocks]]].
    unfold LoopInvPhase7Candidate.
    split; [exact Hphase6 |].
    split; [exact Hsegment |].
    split; [exact Hcoverage | exact Hblocks].
  Qed.

  Lemma ProcessEdgeVisitedNonStackExtendsLoopInvPhase7Candidate_proof:
    forall W u a done,
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvPhase7Candidate u done s /\
           Visited a s /\
           ~ Active a s)
        (process_edge u W a)
        (fun _ s => LoopInvPhase7Candidate u (done_after done a) s).
  Proof.
    intros W u a done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s => LoopInvPhase6Candidate u (done_after done a) s)
          (Q2 := fun _ s =>
             SegmentEscapeAccountingCandidate u (done_after done a) s /\
             SegmentTreeCoverageByDoneCandidate u (done_after done a) s /\
             ActiveTargetBlocksEscapeAccountedCandidate
               u (done_after done a) s).
      - eapply Hoare_conseq_pre.
        2: {
          apply
            (ProcessEdgeVisitedNonStackExtendsLoopInvPhase6Candidate_proof
               W u a done Hedge Hnot_done).
        }
        intros s [Hloop7 [Hvis Hnot_active]].
        destruct Hloop7 as [Hphase6 _].
        split; [exact Hphase6 |].
        split; [exact Hvis | exact Hnot_active].
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               SegmentEscapeAccountingCandidate u (done_after done a) s)
            (Q2 := fun _ s =>
               SegmentTreeCoverageByDoneCandidate u (done_after done a) s /\
               ActiveTargetBlocksEscapeAccountedCandidate
                 u (done_after done a) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (ProcessEdgeVisitedNonStackExtendsSegmentEscapeAccountingCandidate_proof
                 W u a done).
          }
          intros s [Hloop7 [Hvis Hnot_active]].
          destruct Hloop7 as [Hphase6 [Hsegment [_Hcoverage _Hblocks]]].
          destruct Hphase6 as [Hlow _].
          destruct Hlow as [Hdone_loop _Hpartial].
          destruct Hdone_loop as [Hlocal _Hdisc].
          destruct Hlocal as [_Hshape [Hsettled _]].
          split; [exact Hsegment |].
          split; [exact Hsettled |].
          split; [exact Hvis | exact Hnot_active].
        + apply Hoare_conj.
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (ProcessEdgeVisitedNonStackExtendsSegmentTreeCoverageCandidate_proof
                   W u a done).
            }
            intros s [Hloop7 [Hvis Hnot_active]].
            destruct Hloop7 as [_Hphase6 [_Hsegment [Hcoverage _Hblocks]]].
            split; [exact Hcoverage |].
            split; [exact Hvis | exact Hnot_active].
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (ProcessEdgeVisitedNonStackPreservesActiveTargetBlocksCandidate_proof
                   W u a done).
            }
            intros s [Hloop7 [Hvis Hnot_active]].
            destruct Hloop7 as [Hphase6 [_Hsegment [_Hcoverage Hblocks]]].
            destruct Hphase6 as [Hlow _].
            destruct Hlow as [Hdone_loop _Hpartial].
            destruct Hdone_loop as [Hlocal _Hdisc].
            destruct Hlocal as [_Hshape [Hsettled _Htail]].
            split; [exact Hblocks |].
            split; [exact Hsettled |].
            split; [exact Hvis | exact Hnot_active].
    }
    intros _ s [Hphase6 [Hsegment [Hcoverage Hblocks]]].
    unfold LoopInvPhase7Candidate.
    split; [exact Hphase6 |].
    split; [exact Hsegment |].
    split; [exact Hcoverage | exact Hblocks].
  Qed.

  Lemma get_low_update_low_extends_loop_inv_phase6_after_child_candidate:
    forall parent child done,
      Edge parent child ->
      Hoare
        (fun s =>
           LoopInvLowCandidate parent done s /\
           SuspendedParentFrameResumeCandidate parent child done s /\
           Visited child s /\
           DoneClosednessCandidate parent done s /\
           ProcessedTreeChildrenCorrectCandidate parent done s /\
           ActiveProcessedChildSegmentSummaryCandidate parent done s /\
           ParentResumeShapeCandidate parent child done s /\
           ChildRootCorrectForParentCandidate child s /\
           ChildInactiveSelfLowForParentCandidate child s /\
           ChildClosednessContributionCandidate child s /\
           (Active child s -> ChildSegmentSummaryCandidate child s) /\
           fa s child = parent /\
           fa s child <> child /\
           low s child <= dfn s child)
        (lv <- get' (fun s => low s child);; update_low parent lv)
        (fun _ s =>
           LoopInvPhase6Candidate parent (done_after done child) s).
  Proof.
    intros parent child done Hedge.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s =>
             LoopInvLowCandidate parent (done_after done child) s)
          (Q2 := fun _ s =>
             ParentFrameResumeCandidate parent (done_after done child) s /\
             DoneClosednessCandidate parent (done_after done child) s /\
             ProcessedTreeChildrenCorrectCandidate
               parent (done_after done child) s /\
             ActiveProcessedChildSegmentSummaryCandidate
               parent (done_after done child) s).
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               LoopInvDoneCandidate parent (done_after done child) s)
            (Q2 := fun _ s =>
               PartialRootLowEquationCandidate
                 parent (done_after done child) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (get_low_update_low_preserves_loop_inv_done_candidate
                 parent child (done_after done child)).
          }
          intros s Hpre.
          destruct Hpre as
            [Hlow [_Hsuspended [Hvis_child _Htail]]].
          destruct Hlow as [Hdone_loop _Hpartial].
          destruct Hdone_loop as [Hlocal Hdone_disc].
          split; [exact Hlocal |].
          eapply DoneDisciplineCandidate_step_proof; eauto.
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (GetLowUpdateLowExtendsPartialLowTreeCandidate_proof
                 parent done child Hedge).
	          }
	          intros s Hpre.
	          destruct Hpre as [Hlow Hpre].
	          destruct Hpre as [_Hsuspended Hpre].
	          destruct Hpre as [_Hvis_child Hpre].
	          destruct Hpre as [_Hclosed Hpre].
	          destruct Hpre as [_Hchildren Hpre].
	          destruct Hpre as [_Hactive_segments Hpre].
	          destruct Hpre as [_Hresume Hpre].
	          destruct Hpre as [_Hroot Hpre].
	          destruct Hpre as [_Hinactive Hpre].
	          destruct Hpre as [_Hchild_closed Hpre].
	          destruct Hpre as [_Hchild_segment Hpre].
	          destruct Hpre as [Hfa [Hfa_neq Hlow_child]].
          destruct Hlow as [_Hdone_loop Hpartial].
          split; [exact Hpartial |].
          split; [exact Hfa |].
          split; [exact Hfa_neq | exact Hlow_child].
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               ParentFrameResumeCandidate
                 parent (done_after done child) s)
            (Q2 := fun _ s =>
               DoneClosednessCandidate parent (done_after done child) s /\
               ProcessedTreeChildrenCorrectCandidate
                 parent (done_after done child) s /\
               ActiveProcessedChildSegmentSummaryCandidate
                 parent (done_after done child) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (get_low_update_low_preserves_parent_frame_resume_candidate
                 parent child (done_after done child)).
	          }
	          intros s Hpre.
	          destruct Hpre as
	            [_Hlow [Hsuspended [Hvis_child _Htail]]].
	          unfold SuspendedParentFrameResumeCandidate,
	            ParentFrameResumeCandidate,
	            done_visited,
	            fa_not_done_implies_eq_u,
	            done_after in Hsuspended |- *.
	          destruct Hsuspended as [Hdone_vis [Hfa_child Hfa_not_child]].
	          split.
	          * intros v Hdone_after.
	            sets_unfold in Hdone_after.
	            destruct Hdone_after as [Hdone_v | Hv_child].
	            -- apply Hdone_vis. exact Hdone_v.
	            -- subst v. exact Hvis_child.
	          * split; [exact Hfa_child |].
	            intros v Hnot_done_after Hfa_v.
	            apply Hfa_not_child.
	            -- intros Hdone_v.
	               apply Hnot_done_after.
	               sets_unfold. left. exact Hdone_v.
	            -- intros Hv_child.
	               apply Hnot_done_after.
	               sets_unfold. right. symmetry. exact Hv_child.
	            -- exact Hfa_v.
        + apply Hoare_conj
            with
              (Q1 := fun _ s =>
                 DoneClosednessCandidate parent (done_after done child) s)
              (Q2 := fun _ s =>
                 ProcessedTreeChildrenCorrectCandidate
                   parent (done_after done child) s /\
                 ActiveProcessedChildSegmentSummaryCandidate
                   parent (done_after done child) s).
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (get_low_update_low_preserves_done_closedness_candidate
                   parent child (done_after done child)).
	            }
	            intros s Hpre.
	            destruct Hpre as [_Hlow Hpre].
	            destruct Hpre as [_Hsuspended Hpre].
	            destruct Hpre as [_Hvis_child Hpre].
	            destruct Hpre as [Hclosed Hpre].
	            destruct Hpre as [_Hchildren Hpre].
	            destruct Hpre as [_Hactive_segments Hpre].
	            destruct Hpre as [Hresume Hpre].
	            destruct Hpre as [_Hroot Hpre].
	            destruct Hpre as [_Hinactive Hpre].
	            destruct Hpre as [Hchild_closed _Htail].
            eapply DoneClosednessCandidate_step_child_proof; eauto.
          * apply Hoare_conj
              with
                (Q1 := fun _ s =>
                   ProcessedTreeChildrenCorrectCandidate
                     parent (done_after done child) s)
                (Q2 := fun _ s =>
                   ActiveProcessedChildSegmentSummaryCandidate
                     parent (done_after done child) s).
            -- eapply Hoare_conseq_pre.
               2: {
                 apply
                   (get_low_update_low_preserves_processed_tree_children_correct_parent
                      parent child (done_after done child)).
	               }
	               intros s Hpre.
	               destruct Hpre as [Hlow Hpre].
	               destruct Hpre as [Hsuspended Hpre].
	               destruct Hpre as [Hvis_child Hpre].
	               destruct Hpre as [_Hclosed Hpre].
	               destruct Hpre as [Hchildren Hpre].
	               destruct Hpre as [_Hactive_segments Hpre].
	               destruct Hpre as [Hresume Hpre].
	               destruct Hpre as [Hchild_root Hpre].
	               destruct Hpre as [Hchild_inactive _Htail].
               destruct Hlow as [Hdone_loop _Hpartial].
               destruct Hdone_loop as [Hlocal _Hdone_disc].
               destruct Hlocal as [Hglobal _Hlocal_tail].
               split; [exact Hglobal |].
               split.
               ++ unfold DoneVisitedCandidate, done_after.
                  intros v Hdone_after.
                  sets_unfold in Hdone_after.
                  destruct Hdone_after as [Hdone_v | Hv_child].
                  ** destruct Hsuspended as [Hdone_vis _].
                     apply Hdone_vis. exact Hdone_v.
                  ** subst v. exact Hvis_child.
               ++ eapply ProcessedTreeChildrenCorrectCandidate_step_child_proof;
                    eauto.
            -- eapply Hoare_conseq_pre.
               2: {
                 apply
                   (get_low_update_low_preserves_active_processed_child_segment_summary
                      parent child (done_after done child)).
	               }
	               intros s Hpre.
	               destruct Hpre as [_Hlow Hpre].
	               destruct Hpre as [_Hsuspended Hpre].
	               destruct Hpre as [_Hvis_child Hpre].
	               destruct Hpre as [_Hclosed Hpre].
	               destruct Hpre as [_Hchildren Hpre].
	               destruct Hpre as [Hactive_segments Hpre].
	               destruct Hpre as [Hresume Hpre].
	               destruct Hpre as [_Hroot Hpre].
	               destruct Hpre as [_Hinactive Hpre].
	               destruct Hpre as [_Hchild_closed Hpre].
	               destruct Hpre as [Hchild_segment _Htail].
               eapply ActiveProcessedChildSegmentSummaryCandidate_step_child_proof;
                 eauto.
    }
    intros _ s [Hlow [Hframe [Hclosed [Hchildren Hactive_segments]]]].
    unfold LoopInvPhase6Candidate.
    split; [exact Hlow |].
    split; [exact Hframe |].
    split; [exact Hclosed |].
    split; [exact Hchildren | exact Hactive_segments].
  Qed.

  Lemma FrameInvProvidesParentResumeShapeCandidate_proof:
    FrameInvProvidesParentResumeShapeCandidate_statement.
  Proof.
    unfold FrameInvProvidesParentResumeShapeCandidate_statement,
      FrameInvCandidate.
    intros F s [Hresume _].
    exact Hresume.
  Qed.

  Lemma FrameInvProvidesLoopInvLowCandidate_proof:
    FrameInvProvidesLoopInvLowCandidate_statement.
  Proof.
    unfold FrameInvProvidesLoopInvLowCandidate_statement,
      FrameInvCandidate.
    intros F s [_ [Hlow _]].
    exact Hlow.
  Qed.

  Lemma FrameInvProvidesSuspendedParentFrameResumeCandidate_proof:
    FrameInvProvidesSuspendedParentFrameResumeCandidate_statement.
  Proof.
    unfold FrameInvProvidesSuspendedParentFrameResumeCandidate_statement,
      FrameInvCandidate.
    intros F s [_ [_ [Hframe _]]].
    exact Hframe.
  Qed.

  Lemma FrameInvProvidesDoneClosednessCandidate_proof:
    FrameInvProvidesDoneClosednessCandidate_statement.
  Proof.
    unfold FrameInvProvidesDoneClosednessCandidate_statement,
      FrameInvCandidate.
    intros F s [_ [_ [_ [Hclosed _]]]].
    exact Hclosed.
  Qed.

  Lemma FrameInvProvidesProcessedTreeChildrenCorrectCandidate_proof:
    FrameInvProvidesProcessedTreeChildrenCorrectCandidate_statement.
  Proof.
    unfold FrameInvProvidesProcessedTreeChildrenCorrectCandidate_statement,
      FrameInvCandidate.
    intros F s [_ [_ [_ [_ [Hchildren _]]]]].
    exact Hchildren.
  Qed.

  Lemma FrameInvProvidesActiveProcessedChildSegmentSummaryCandidate_proof:
    FrameInvProvidesActiveProcessedChildSegmentSummaryCandidate_statement.
  Proof.
    unfold FrameInvProvidesActiveProcessedChildSegmentSummaryCandidate_statement,
      FrameInvCandidate.
    intros F s [_ [_ [_ [_ [_ [Hactive_segments _]]]]]].
    exact Hactive_segments.
  Qed.

  Lemma FrameInvProvidesSuspendedSegmentEscapeAccountingCandidate_proof:
    FrameInvProvidesSuspendedSegmentEscapeAccountingCandidate_statement.
  Proof.
    unfold FrameInvProvidesSuspendedSegmentEscapeAccountingCandidate_statement,
      FrameInvCandidate.
    intros F s [_ [_ [_ [_ [_ [_ [Hsegment _Hcoverage]]]]]]].
    exact Hsegment.
  Qed.

  Lemma FrameInvProvidesSuspendedSegmentTreeCoverageCandidate_proof:
    FrameInvProvidesSuspendedSegmentTreeCoverageCandidate_statement.
  Proof.
    unfold FrameInvProvidesSuspendedSegmentTreeCoverageCandidate_statement,
      FrameInvCandidate.
    intros F s [_ [_ [_ [_ [_ [_ [_Hsegment Hcoverage]]]]]]].
    exact Hcoverage.
  Qed.

  Lemma FrameInvForgetsSuspendedLoopInvPhase6Candidate_proof:
    FrameInvForgetsSuspendedLoopInvPhase6Candidate_statement.
  Proof.
    unfold FrameInvForgetsSuspendedLoopInvPhase6Candidate_statement,
      FrameInvCandidate,
      SuspendedLoopInvPhase6Candidate.
    intros F s
      [_Hresume [Hlow [Hframe [Hclosed [Hchildren [Hactive_segments _Hsegment]]]]]].
    split; [exact Hlow |].
    split; [exact Hframe |].
    split; [exact Hclosed |].
    split; [exact Hchildren | exact Hactive_segments].
  Qed.

  Lemma SuspendedParentFrameResumeClosesAfterChildCandidate_proof:
    SuspendedParentFrameResumeClosesAfterChildCandidate_statement.
  Proof.
    unfold SuspendedParentFrameResumeClosesAfterChildCandidate_statement,
      SuspendedParentFrameResumeCandidate,
      ParentFrameResumeCandidate,
      Visited,
      done_after,
      done_visited,
      fa_not_done_implies_eq_u.
    intros parent child done s [Hdone_vis [Hfa_child Hfa_not_child]]
           Hvis_child.
    split.
    - intros v Hdone_after.
      sets_unfold in Hdone_after.
      destruct Hdone_after as [Hdone_v | Hv_child].
      + apply Hdone_vis. exact Hdone_v.
      + subst v. exact Hvis_child.
    - split; [exact Hfa_child |].
      intros v Hnot_done_after Hfa_v.
      apply Hfa_not_child.
      + intros Hdone_v.
        apply Hnot_done_after.
        sets_unfold. left. exact Hdone_v.
      + intros Hv_child.
        apply Hnot_done_after.
        sets_unfold. right. symmetry. exact Hv_child.
      + exact Hfa_v.
  Qed.

  Lemma SuspendedLoopInvPhase7ClosesAfterChildCandidate_proof:
    SuspendedLoopInvPhase7ClosesAfterChildCandidate_statement.
  Proof.
    unfold SuspendedLoopInvPhase7ClosesAfterChildCandidate_statement,
      LoopInvPhase7Candidate,
      LoopInvPhase6Candidate.
    intros parent child done s Hlow Hsuspended_frame Hvis_child
           Hclosed Hchildren Hactive_segments Hsegment Hcoverage Hblocks.
    split.
    - split; [exact Hlow |].
      split.
      + eapply SuspendedParentFrameResumeClosesAfterChildCandidate_proof;
          eauto.
      + split; [exact Hclosed |].
        split; [exact Hchildren | exact Hactive_segments].
    - split; [exact Hsegment |].
      split; [exact Hcoverage | exact Hblocks].
  Qed.

  Lemma FrameContractCandidate_from_field_preservation_proof:
    FrameContractCandidate_from_field_preservation_statement.
  Proof.
    unfold FrameContractCandidate_from_field_preservation_statement,
      FramePreservationBundleCandidate,
      FramePreservesParentResumeShapeCandidate,
      FramePreservesLoopInvLowCandidate,
      FramePreservesSuspendedParentFrameResumeCandidate,
      FramePreservesDoneClosednessCandidate,
      FramePreservesProcessedTreeChildrenCorrectCandidate,
      FramePreservesActiveProcessedChildSegmentSummaryCandidate,
      FramePreservesSuspendedSegmentEscapeAccountingCandidate,
      FramePreservesSuspendedSegmentTreeCoverageCandidate,
      FrameFieldPreservationCandidate,
      FrameContractCandidate,
      FrameInvCandidate.
    intros W
      [Hresume [Hlow [Hsuspended_frame [Hclosed
       [Hchildren [Hactive_segments [Hsegment Hcoverage]]]]]]]
      F parent child done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s =>
          ParentResumeShapeCandidate
            (frame_parent F) (frame_child F) (frame_done F) s)
        (Q2 := fun _ s =>
          LoopInvLowCandidate (frame_parent F) (frame_done F) s /\
          SuspendedParentFrameResumeCandidate
            (frame_parent F) (frame_child F) (frame_done F) s /\
          DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
          ProcessedTreeChildrenCorrectCandidate
            (frame_parent F) (frame_done F) s /\
          ActiveProcessedChildSegmentSummaryCandidate
            (frame_parent F) (frame_done F) s /\
          SuspendedSegmentEscapeAccountingCandidate
            (frame_parent F) (frame_child F) (frame_done F) s /\
          SuspendedSegmentTreeCoverageByDoneCandidate
            (frame_parent F) (frame_child F) (frame_done F) s).
      - eapply Hoare_conseq_pre.
        2: { exact (Hresume F parent child done Hedge Hnot_done). }
        intros s [Hframe [Hcompat Hchild_entry]].
        split; [exact Hframe |].
        split; [exact Hcompat | exact Hchild_entry].
      - apply Hoare_conj with
          (Q1 := fun _ s =>
            LoopInvLowCandidate (frame_parent F) (frame_done F) s)
          (Q2 := fun _ s =>
            SuspendedParentFrameResumeCandidate
              (frame_parent F) (frame_child F) (frame_done F) s /\
            DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
            ProcessedTreeChildrenCorrectCandidate
              (frame_parent F) (frame_done F) s /\
            ActiveProcessedChildSegmentSummaryCandidate
              (frame_parent F) (frame_done F) s /\
            SuspendedSegmentEscapeAccountingCandidate
              (frame_parent F) (frame_child F) (frame_done F) s /\
            SuspendedSegmentTreeCoverageByDoneCandidate
              (frame_parent F) (frame_child F) (frame_done F) s).
        + eapply Hoare_conseq_pre.
          2: { exact (Hlow F parent child done Hedge Hnot_done). }
          intros s [Hframe [Hcompat Hchild_entry]].
          split; [exact Hframe |].
          split; [exact Hcompat | exact Hchild_entry].
        + apply Hoare_conj with
            (Q1 := fun _ s =>
              SuspendedParentFrameResumeCandidate
                (frame_parent F) (frame_child F) (frame_done F) s)
            (Q2 := fun _ s =>
              DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
              ProcessedTreeChildrenCorrectCandidate
                (frame_parent F) (frame_done F) s /\
              ActiveProcessedChildSegmentSummaryCandidate
                (frame_parent F) (frame_done F) s /\
              SuspendedSegmentEscapeAccountingCandidate
                (frame_parent F) (frame_child F) (frame_done F) s /\
              SuspendedSegmentTreeCoverageByDoneCandidate
                (frame_parent F) (frame_child F) (frame_done F) s).
          * eapply Hoare_conseq_pre.
            2: {
              exact (Hsuspended_frame F parent child done Hedge Hnot_done).
            }
            intros s [Hframe [Hcompat Hchild_entry]].
            split; [exact Hframe |].
            split; [exact Hcompat | exact Hchild_entry].
          * apply Hoare_conj with
              (Q1 := fun _ s =>
                DoneClosednessCandidate (frame_parent F) (frame_done F) s)
              (Q2 := fun _ s =>
                ProcessedTreeChildrenCorrectCandidate
                  (frame_parent F) (frame_done F) s /\
                ActiveProcessedChildSegmentSummaryCandidate
                  (frame_parent F) (frame_done F) s /\
                SuspendedSegmentEscapeAccountingCandidate
                  (frame_parent F) (frame_child F) (frame_done F) s /\
                SuspendedSegmentTreeCoverageByDoneCandidate
                  (frame_parent F) (frame_child F) (frame_done F) s).
            -- eapply Hoare_conseq_pre.
               2: { exact (Hclosed F parent child done Hedge Hnot_done). }
               intros s [Hframe [Hcompat Hchild_entry]].
               split; [exact Hframe |].
               split; [exact Hcompat | exact Hchild_entry].
            -- apply Hoare_conj with
                (Q1 := fun _ s =>
                  ProcessedTreeChildrenCorrectCandidate
                    (frame_parent F) (frame_done F) s)
                (Q2 := fun _ s =>
                  ActiveProcessedChildSegmentSummaryCandidate
                    (frame_parent F) (frame_done F) s /\
                  SuspendedSegmentEscapeAccountingCandidate
                    (frame_parent F) (frame_child F) (frame_done F) s /\
                  SuspendedSegmentTreeCoverageByDoneCandidate
                    (frame_parent F) (frame_child F) (frame_done F) s).
               ++ eapply Hoare_conseq_pre.
                  2: { exact (Hchildren F parent child done Hedge Hnot_done). }
                  intros s [Hframe [Hcompat Hchild_entry]].
                  split; [exact Hframe |].
                  split; [exact Hcompat | exact Hchild_entry].
               ++ apply Hoare_conj with
                    (Q1 := fun _ s =>
                      ActiveProcessedChildSegmentSummaryCandidate
                        (frame_parent F) (frame_done F) s)
                    (Q2 := fun _ s =>
                      SuspendedSegmentEscapeAccountingCandidate
                        (frame_parent F) (frame_child F) (frame_done F) s /\
                      SuspendedSegmentTreeCoverageByDoneCandidate
                        (frame_parent F) (frame_child F) (frame_done F) s).
                  ** eapply Hoare_conseq_pre.
                     2: {
                       exact
                         (Hactive_segments F parent child done Hedge Hnot_done).
                     }
                     intros s [Hframe [Hcompat Hchild_entry]].
                     split; [exact Hframe |].
                     split; [exact Hcompat | exact Hchild_entry].
                  ** apply Hoare_conj.
                     --- eapply Hoare_conseq_pre.
                         2: { exact (Hsegment F parent child done Hedge Hnot_done). }
                         intros s [Hframe [Hcompat Hchild_entry]].
                         split; [exact Hframe |].
                         split; [exact Hcompat | exact Hchild_entry].
                     --- eapply Hoare_conseq_pre.
                         2: { exact (Hcoverage F parent child done Hedge Hnot_done). }
                         intros s [Hframe [Hcompat Hchild_entry]].
                         split; [exact Hframe |].
                         split; [exact Hcompat | exact Hchild_entry].
    }
    intros _ s [Hresume_field
      [Hlow_field [Hsuspended_field [Hclosed_field
       [Hchildren_field [Hactive_field [Hsegment_field Hcoverage_field]]]]]]].
    split; [exact Hresume_field |].
    split; [exact Hlow_field |].
    split; [exact Hsuspended_field |].
    split; [exact Hclosed_field |].
    split; [exact Hchildren_field |].
    split; [exact Hactive_field |].
    split; [exact Hsegment_field | exact Hcoverage_field].
  Qed.

  Lemma FrameContractCandidate_provides_field_preservation_proof:
    FrameContractCandidate_provides_field_preservation_statement.
  Proof.
    unfold FrameContractCandidate_provides_field_preservation_statement,
      FrameFieldPreservationCandidate,
      FrameContractCandidate.
    intros W Field Hproject Hcontract F parent child done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: { exact (Hcontract F parent child done Hedge Hnot_done). }
    intros r s Hframe.
    apply Hproject. exact Hframe.
  Qed.

  Lemma FrameContractCandidate_to_field_preservation_bundle_proof:
    FrameContractCandidate_to_field_preservation_bundle_statement.
  Proof.
    unfold FrameContractCandidate_to_field_preservation_bundle_statement.
    intros W Hcontract.
    unfold FramePreservationBundleCandidate,
      FramePreservesParentResumeShapeCandidate,
      FramePreservesLoopInvLowCandidate,
      FramePreservesSuspendedParentFrameResumeCandidate,
      FramePreservesDoneClosednessCandidate,
      FramePreservesProcessedTreeChildrenCorrectCandidate,
      FramePreservesActiveProcessedChildSegmentSummaryCandidate,
      FramePreservesSuspendedSegmentEscapeAccountingCandidate,
      FramePreservesSuspendedSegmentTreeCoverageCandidate,
      FrameFieldPreservationCandidate.
    split.
    - (* ParentResumeShape *)
      intros Fr p c d Hedge Hnot_done.
      eapply Hoare_conseq_post.
      2: { exact (Hcontract Fr p c d Hedge Hnot_done). }
      intros r s Hframe.
      destruct Hframe as [Hresume _].
      exact Hresume.
    - split.
      + (* LoopInvLow *)
        intros Fr p c d Hedge Hnot_done.
        eapply Hoare_conseq_post.
        2: { exact (Hcontract Fr p c d Hedge Hnot_done). }
        intros r s Hframe.
        destruct Hframe as [_ [Hlow _]].
        exact Hlow.
      + split.
        * (* SuspendedParentFrameResume *)
          intros Fr p c d Hedge Hnot_done.
          eapply Hoare_conseq_post.
          2: { exact (Hcontract Fr p c d Hedge Hnot_done). }
          intros r s Hframe.
          destruct Hframe as [_ [_ [Hfield _]]].
          exact Hfield.
        * split.
          -- (* DoneClosedness *)
             intros Fr p c d Hedge Hnot_done.
             eapply Hoare_conseq_post.
             2: { exact (Hcontract Fr p c d Hedge Hnot_done). }
             intros r s Hframe.
             destruct Hframe as [_ [_ [_ [Hfield _]]]].
             exact Hfield.
          -- split.
             ++ (* ProcessedTreeChildrenCorrect *)
                intros Fr p c d Hedge Hnot_done.
                eapply Hoare_conseq_post.
                2: { exact (Hcontract Fr p c d Hedge Hnot_done). }
                intros r s Hframe.
                destruct Hframe as [_ [_ [_ [_ [Hfield _]]]]].
                exact Hfield.
             ++ split.
                ** (* ActiveProcessedChildSegmentSummary *)
                   intros Fr p c d Hedge Hnot_done.
                   eapply Hoare_conseq_post.
                   2: { exact (Hcontract Fr p c d Hedge Hnot_done). }
                   intros r s Hframe.
                   destruct Hframe as [_ [_ [_ [_ [_ [Hfield _]]]]]].
                   exact Hfield.
                ** split.
                   --- (* SegmentEscapeAccounting *)
                       intros Fr p c d Hedge Hnot_done.
                       eapply Hoare_conseq_post.
                       2: { exact (Hcontract Fr p c d Hedge Hnot_done). }
                       intros r s Hframe.
                       destruct Hframe as [_ [_ [_ [_ [_ [_ [Hfield _]]]]]]].
                       exact Hfield.
                   --- (* SegmentTreeCoverage *)
                       intros Fr p c d Hedge Hnot_done.
                       eapply Hoare_conseq_post.
                       2: { exact (Hcontract Fr p c d Hedge Hnot_done). }
                       intros r s Hframe.
                       destruct Hframe as [_ [_ [_ [_ [_ [_ [_ Hfield]]]]]]].
                       exact Hfield.
  Qed.

  Lemma ProcessEdgeTreeBranchExtendsLoopInvPhase6Candidate_proof:
    forall W u a done,
      RecursiveCallContractsCandidate W ->
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvPhase7Candidate u done s /\
           Unvisited a s)
        (set_fa a u;; W a;;
         lv <- get' (fun s => low s a);; update_low u lv)
        (fun _ s =>
           LoopInvPhase6Candidate u (done_after done a) s).
  Proof.
    intros W u a done Hcontracts Hedge Hnot_done.
    destruct Hcontracts as [Hchild [Hlow_contribution Hframe]].
    eapply Hoare_bind.
    - apply (set_fa_unvisited_creates_frame_inv_candidate
               u a done Hedge Hnot_done).
    - simpl. intros _.
	      eapply Hoare_bind with
	        (Q := fun (_: unit) s =>
	           FrameInvCandidate (FrameOfCallCandidate u a done) s /\
	           ChildPostCandidate u a done s /\
	           (PartialRootLowEquationCandidate u done s /\
            fa s a = u /\
            fa s a <> a /\
            low s a <= dfn s a)).
      + eapply Hoare_conseq_post.
        2: {
          apply Hoare_conj
            with
              (Q1 := fun _ s =>
                 FrameInvCandidate (FrameOfCallCandidate u a done) s)
              (Q2 := fun _ s =>
                 ChildPostCandidate u a done s /\
                 (PartialRootLowEquationCandidate u done s /\
                  fa s a = u /\
                  fa s a <> a /\
                  low s a <= dfn s a)).
          - eapply Hoare_conseq_pre.
            2: {
              apply
                (Hframe (FrameOfCallCandidate u a done)
                   u a done Hedge Hnot_done).
            }
            intros s [Hframe_inv [Hentry _Hresume]].
            split; [exact Hframe_inv |].
            split.
            + apply FrameCompatibleWithOwnCallCandidate_proof.
            + exact Hentry.
          - apply Hoare_conj
              with
                (Q1 := fun _ s => ChildPostCandidate u a done s)
                (Q2 := fun _ s =>
                   PartialRootLowEquationCandidate u done s /\
                   fa s a = u /\
                   fa s a <> a /\
                   low s a <= dfn s a).
            + eapply Hoare_conseq_pre.
              2: { apply (Hchild u a done Hedge Hnot_done). }
              intros s [_Hframe_inv [Hentry _Hresume]].
              exact Hentry.
            + eapply Hoare_conseq_pre.
              2: { apply (Hlow_contribution u a done Hedge Hnot_done). }
              intros s [Hframe_inv [Hentry _Hresume]].
              split; [exact Hframe_inv |].
              split; [exact Hentry |].
              pose proof
                (FrameInvProvidesLoopInvLowCandidate_proof
                   (FrameOfCallCandidate u a done) s Hframe_inv)
                as Hloop_low.
              simpl in Hloop_low.
              exact (proj2 Hloop_low).
        }
	        intros r s [Hframe_inv [Hchild_post Hlow_post]].
        split; [exact Hframe_inv | split; [exact Hchild_post | exact Hlow_post]].
      + simpl. intros _.
        eapply Hoare_conseq_pre.
        2: {
          apply
            (get_low_update_low_extends_loop_inv_phase6_after_child_candidate
               u a done Hedge).
        }
        intros s [Hframe_inv [Hchild_post Hlow_post]].
        destruct Hframe_inv as
          [Hresume_frame [Hloop_low [Hsuspended_frame [Hclosed
           [Hchildren [Hactive_segments _Hsuspended_segment]]]]]].
        destruct Hchild_post as
          [Hvis_child [Hchild_low_valid [Hchild_is_low
           [Hchild_inactive [Hchild_closed
           [Hchild_segment Hresume_pending]]]]]].
        destruct Hresume_pending as [Hresume_child Hresume_pending].
        destruct Hresume_pending as [Hparent_pending_unused Hactive_blocks_unused].
        destruct Hlow_post as [Hpartial [Hfa [Hfa_neq Hlow_child]]].
        split; [exact Hloop_low |].
        split; [exact Hsuspended_frame |].
        split; [exact Hvis_child |].
        split; [exact Hclosed |].
        split; [exact Hchildren |].
        split; [exact Hactive_segments |].
        split; [exact Hresume_child |].
        split.
        * split; [exact Hchild_low_valid | exact Hchild_is_low].
        * split; [exact Hchild_inactive |].
          split; [exact Hchild_closed |].
          split; [exact Hchild_segment |].
          split; [exact Hfa |].
          split; [exact Hfa_neq | exact Hlow_child].
  Qed.

  Lemma ProcessEdgeTreeBranchExtendsPhase7SegmentFieldsCandidate_proof:
    forall W u a done,
      RecursiveCallContractsCandidate W ->
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvPhase7Candidate u done s /\
           Unvisited a s)
        (set_fa a u;; W a;;
         lv <- get' (fun s => low s a);; update_low u lv)
        (fun _ s =>
           SegmentEscapeAccountingCandidate u (done_after done a) s /\
           SegmentTreeCoverageByDoneCandidate u (done_after done a) s /\
           ActiveTargetBlocksEscapeAccountedCandidate
             u (done_after done a) s).
  Proof.
    intros W u a done Hcontracts Hedge Hnot_done.
    destruct Hcontracts as [Hchild [_Hlow_contribution Hframe]].
    eapply Hoare_bind.
    - apply (set_fa_unvisited_creates_frame_inv_candidate
               u a done Hedge Hnot_done).
    - simpl. intros _.
      eapply Hoare_bind
        with
          (Q := fun (_: unit) s =>
             FrameInvCandidate (FrameOfCallCandidate u a done) s /\
             ChildPostCandidate u a done s).
      + apply Hoare_conj.
        * eapply Hoare_conseq_pre.
          2: {
            apply
              (Hframe (FrameOfCallCandidate u a done)
                 u a done Hedge Hnot_done).
          }
          intros s [Hframe_inv [Hentry _Hresume]].
          split; [exact Hframe_inv |].
          split.
          -- apply FrameCompatibleWithOwnCallCandidate_proof.
          -- exact Hentry.
        * eapply Hoare_conseq_pre.
          2: { apply (Hchild u a done Hedge Hnot_done). }
          intros s [_Hframe_inv [Hentry _Hresume]].
          exact Hentry.
      + simpl. intros _.
        eapply Hoare_conseq_post.
        2: {
          apply Hoare_conj
            with
              (Q1 := fun _ s =>
                 SegmentEscapeAccountingCandidate u (done_after done a) s)
              (Q2 := fun _ s =>
                 SegmentTreeCoverageByDoneCandidate u (done_after done a) s /\
                 ActiveTargetBlocksEscapeAccountedCandidate
                   u (done_after done a) s).
          - eapply Hoare_conseq_post.
            2: {
              apply Hoare_conj
                with
                  (Q1 := fun _ s =>
                     SuspendedSegmentEscapeAccountingCandidate u a done s)
                  (Q2 := fun _ s =>
                     ParentPendingChildEscapeAccountedCandidate u done a s /\
                     PendingChildSegmentEscapeAccountedCandidate u done a s).
              + eapply Hoare_conseq_pre.
                2: {
                  apply
                    (get_low_update_low_preserves_suspended_segment_escape_accounting_candidate
                       u done a).
                }
                intros s [Hframe_inv _Hchild_post].
                destruct Hframe_inv as
                  [_Hresume_frame [_Hloop_low [_Hsuspended_frame [_Hclosed
                   [_Hchildren [_Hactive_segments
                   [Hsuspended_escape _Hsuspended_coverage]]]]]]].
                exact Hsuspended_escape.
              + apply Hoare_conj.
                * eapply Hoare_conseq_pre.
                  2: {
                    apply
                      (get_low_update_low_preserves_parent_pending_child_escape_accounted_candidate
                         u done a).
                  }
                  intros s [_Hframe_inv Hchild_post].
                  destruct Hchild_post as
                    [_Hvis_child [_Hchild_low_valid [_Hchild_is_low
                     [_Hchild_inactive [_Hchild_closed
                     [_Hchild_segment Hresume_pending]]]]]].
                  destruct Hresume_pending as [_Hresume_child Hresume_pending].
                  destruct Hresume_pending as [Hparent_pending _Hactive_blocks].
                  exact Hparent_pending.
                * eapply Hoare_conseq_pre.
                  2: {
                    apply
                      (GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedConditionalCandidate_proof
                         u done a).
                  }
                  intros s [Hframe_inv Hchild_post].
                  destruct Hframe_inv as
                    [_Hresume_frame [Hloop_low [_Hsuspended_frame [_Hclosed
                     [_Hchildren [_Hactive_segments
                     [Hsuspended_escape _Hsuspended_coverage]]]]]]].
                  destruct Hloop_low as [Hdone_loop _Hpartial].
                  destruct Hdone_loop as [Hlocal _Hdiscipline].
                  destruct Hlocal as [Hshape [_Hsettled [Hvis_u _Horder]]].
                  destruct Hchild_post as
                    [_Hvis_child [_Hchild_low_valid [_Hchild_is_low
                     [_Hchild_inactive [_Hchild_closed
                     [Hchild_segment_if Hresume_pending]]]]]].
                  destruct Hresume_pending as [Hresume_child Hresume_pending].
                  destruct Hresume_pending as [Hparent_pending _Hactive_blocks].
                  split; [exact Hshape |].
                  split; [exact Hvis_u |].
                  split; [exact Hresume_child |].
                  split; [exact Hchild_segment_if |].
                  split; [exact Hsuspended_escape | exact Hparent_pending].
            }
            intros _ s [Hsuspended_escape
                         [Hparent_pending Hpending_child_segment]].
            eapply SuspendedSegmentEscapeAccountingClosesAfterChildCandidate_proof;
              eauto.
          - apply Hoare_conj.
            + eapply Hoare_conseq_pre.
              2: {
                apply
                  (get_low_update_low_preserves_segment_tree_coverage_candidate
                     u a (done_after done a)).
              }
              intros s [Hframe_inv Hchild_post].
              destruct Hframe_inv as
                [_Hresume_frame [Hloop_low [_Hsuspended_frame [_Hclosed
                 [_Hchildren [_Hactive_segments
                 [_Hsuspended_escape Hsuspended_coverage]]]]]]].
              destruct Hloop_low as [Hdone_loop _Hpartial].
              destruct Hdone_loop as [Hlocal _Hdiscipline].
              destruct Hlocal as [Hshape _Hlocal_tail].
              destruct Hchild_post as
                [_Hvis_child [_Hchild_low_valid [_Hchild_is_low
                 [_Hchild_inactive [_Hchild_closed
                 [Hchild_segment_if Hresume_pending]]]]]].
              destruct Hresume_pending as [Hresume_child Hresume_pending].
              destruct Hresume_pending as [_Hparent_pending _Hactive_blocks].
              destruct Hresume_child as [_Hedge_child Hresume_child].
              destruct Hresume_child as [_Hnot_done_child Hresume_child].
              destruct Hresume_child as [Hfa Hfa_neq].
              eapply SegmentTreeCoverageClosesAfterChildCandidate_proof;
                eauto.
            + eapply Hoare_conseq_pre.
              2: {
                apply
                  (get_low_update_low_preserves_active_target_blocks_escape_accounted_candidate
                     u (done_after done a) a).
              }
              intros s [_Hframe_inv Hchild_post].
              destruct Hchild_post as
                [_Hvis_child [_Hchild_low_valid [_Hchild_is_low
                 [_Hchild_inactive [_Hchild_closed
                 [_Hchild_segment Hresume_pending]]]]]].
              destruct Hresume_pending as [_Hresume_child Hresume_pending].
              destruct Hresume_pending as [_Hparent_pending Hactive_blocks].
              exact Hactive_blocks.
        }
        intros _ s [Hsegment [Hcoverage Hblocks]].
        split; [exact Hsegment |].
        split; [exact Hcoverage | exact Hblocks].
  Qed.

  Lemma ProcessEdgeTreeBranchExtendsLoopInvPhase7Candidate_proof:
    forall W u a done,
      RecursiveCallContractsCandidate W ->
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvPhase7Candidate u done s /\
           Unvisited a s)
        (set_fa a u;; W a;;
         lv <- get' (fun s => low s a);; update_low u lv)
        (fun _ s =>
           LoopInvPhase7Candidate u (done_after done a) s).
  Proof.
    intros W u a done Hcontracts Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s => LoopInvPhase6Candidate u (done_after done a) s)
          (Q2 := fun _ s =>
             SegmentEscapeAccountingCandidate u (done_after done a) s /\
             SegmentTreeCoverageByDoneCandidate u (done_after done a) s /\
             ActiveTargetBlocksEscapeAccountedCandidate
               u (done_after done a) s).
      - eapply Hoare_conseq_pre.
        2: {
          apply
            (ProcessEdgeTreeBranchExtendsLoopInvPhase6Candidate_proof
               W u a done Hcontracts Hedge Hnot_done).
        }
        intros s Hpre. exact Hpre.
      - eapply Hoare_conseq_pre.
        2: {
          apply
            (ProcessEdgeTreeBranchExtendsPhase7SegmentFieldsCandidate_proof
               W u a done Hcontracts Hedge Hnot_done).
        }
        intros s Hpre. exact Hpre.
    }
    intros _ s [Hphase6 [Hsegment [Hcoverage Hblocks]]].
    unfold LoopInvPhase7Candidate.
    split; [exact Hphase6 |].
    split; [exact Hsegment |].
    split; [exact Hcoverage | exact Hblocks].
  Qed.

  Lemma ProcessEdgeUnvisitedExtendsLoopInvPhase7Candidate_proof:
    forall W u a done,
      RecursiveCallContractsCandidate W ->
      Edge u a ->
      ~ done a ->
      Hoare
        (fun s =>
           LoopInvPhase7Candidate u done s /\
           Unvisited a s)
        (process_edge u W a)
        (fun _ s =>
           LoopInvPhase7Candidate u (done_after done a) s).
  Proof.
    intros W u a done Hcontracts Hedge Hnot_done.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_conseq_pre.
      2: {
        apply
          (ProcessEdgeTreeBranchExtendsLoopInvPhase7Candidate_proof
             W u a done Hcontracts Hedge Hnot_done).
      }
      intros s [Hunvis_guard Heq_s]. subst s.
      destruct H as [Hloop7 Hunvis].
      split; [exact Hloop7 | exact Hunvis_guard].
    - apply Hoare_assume_bind. simpl.
      intro_state.
      destruct H1 as [Hnot_unvis_guard Heq_s]. subst s1.
      destruct H as [_Hloop7 Hunvis].
      exfalso. apply Hnot_unvis_guard. exact Hunvis.
  Qed.

  Lemma BodyRecursiveCallContractsCandidate_from_parts_proof:
    BodyRecursiveCallContractsCandidate_from_parts_statement.
  Proof.
    unfold BodyRecursiveCallContractsCandidate_from_parts_statement,
      BodySatisfiesChildContractCandidate_statement,
      BodyProvidesLowContributionCandidate_statement,
      BodyPreservesFrameContractCandidate_statement,
      RecursiveCallContractsCandidate.
    intros Hchild Hlow Hframe W Hcontracts.
    split. apply Hchild. exact Hcontracts.
    split. apply Hlow. exact Hcontracts. apply Hframe. exact Hcontracts.
  Qed.

  Lemma FrameParentResumeShapeAfterPreloopCandidate_proof:
    FrameParentResumeShapeAfterPreloopCandidate_statement.
  Proof.
    unfold FrameParentResumeShapeAfterPreloopCandidate_statement,
      FrameInvCandidate,
      FrameCompatibleWithCallCandidate,
      ParentResumeShapeCandidate,
      Visited.
    intros F parent child done _Hedge _Hnot_done.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [[Hresume _Hframe_tail] [Hcompat _Hchild_entry]].
    destruct Hresume as
      [Hedge_frame [Hnot_done_frame [Hfa_frame Hfa_neq_frame]]].
    split.
    - split; [exact Hedge_frame |].
      split; [exact Hnot_done_frame |].
      split; [exact Hfa_frame | exact Hfa_neq_frame].
    - sets_unfold.
      destruct Hcompat as [[_Hown_parent Hown_child] | Hpending_parent].
      + right. symmetry. exact Hown_child.
      + destruct Hpending_parent as [Hvis_frame _Hpending_tail].
        left. exact Hvis_frame.
  Qed.

  Lemma FrameParentResumeShapePreservedByMaybePopCandidate_proof:
    FrameParentResumeShapePreservedByMaybePopCandidate_statement.
  Proof.
    unfold FrameParentResumeShapePreservedByMaybePopCandidate_statement,
      ParentResumeShapeCandidate,
      maybe_pop,
      root_pop_guard.
    intros F u.
    intro_state. hoare_auto_s.
    - destruct H as [Hedge [Hnot_done [Hfa Hfa_neq]]].
      eapply Hoare_conseq_post.
      2: {
        eapply Hoare_conseq_pre.
        2: { apply (pop_scc_keep_fa u (frame_child F) (frame_parent F)). }
        intros s Hs. subst s. exact Hfa.
      }
      intros r s Hfa_post.
      split; [exact Hedge |].
      split; [exact Hnot_done |].
      split; [exact Hfa_post |].
      intro Hbad.
      apply Hfa_neq.
      rewrite Hfa.
      rewrite <- Hfa_post.
      exact Hbad.
    - destruct H1 as [Hs _Hguard].
      subst s. exact H.
  Qed.

  Lemma FrameSuspendedParentFrameResumeAfterPreloopCandidate_proof:
    FrameSuspendedParentFrameResumeAfterPreloopCandidate_statement.
  Proof.
    unfold FrameSuspendedParentFrameResumeAfterPreloopCandidate_statement,
      FrameInvCandidate,
      SuspendedParentFrameResumeCandidate,
      done_visited,
      fa_child_of_u.
    intros F parent child done _Hedge _Hnot_done.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [[_Hresume [_Hlow [Hframe _Htail]]]
                   [_Hcompat _Hchild_entry]].
    destruct Hframe as [Hdone_vis [Hfa_child Hfa_not_child]].
    split.
    - intros v Hdone_v.
      sets_unfold. left.
      apply Hdone_vis. exact Hdone_v.
    - split.
      + intros v Hfa_v.
        apply Hfa_child. exact Hfa_v.
      + intros v Hnot_done_v Hneq_child Hfa_v.
        eapply Hfa_not_child; eauto.
  Qed.

  Lemma FrameSuspendedParentFrameResumePreservedByMaybePopCandidate_proof:
    FrameSuspendedParentFrameResumePreservedByMaybePopCandidate_statement.
  Proof.
    unfold FrameSuspendedParentFrameResumePreservedByMaybePopCandidate_statement,
      SuspendedParentFrameResumeCandidate,
      maybe_pop,
      root_pop_guard.
    intros F u.
    intro_state. hoare_auto_s.
    - unfold pop_scc. intro_state. hoare_auto_s.
      subst s1. subst s. unfold pop_scc_state.
      destruct (stack_split_at (stack s0) u) as [popped rest] eqn:_Hsplit.
      simpl. exact H.
    - destruct H1 as [Hs _Hguard].
      subst s. exact H.
  Qed.

  Lemma MaybePopProducesFramePopBoundarySnapshotCandidate_proof:
    MaybePopProducesFramePopBoundarySnapshotCandidate_statement.
  Proof.
    unfold MaybePopProducesFramePopBoundarySnapshotCandidate_statement,
      FramePopBoundarySnapshotCandidate,
      FramePopBoundaryCandidate,
      maybe_pop,
      pop_scc,
      root_pop_guard,
      Active.
    intros F u snap.
    intro_state. hoare_auto_s.
    - destruct H as [Heq_s [Hparent_active [Hparent_rest Hdone_rest]]].
      subst s0.
      subst s.
      unfold pop_scc_state.
      destruct (stack_split_at (stack snap) u) as [popped rest] eqn:Hsplit.
      simpl.
      split.
      + exact (Hparent_rest popped rest eq_refl).
      + split.
        * intros v Hdone_v Hactive_v.
          exact (Hdone_rest v Hdone_v Hactive_v popped rest eq_refl).
        * split.
          -- intros x. split; intro Hvisited; exact Hvisited.
          -- split.
             ++ intros x. reflexivity.
             ++ split.
                ** intros x. reflexivity.
                ** intros x. reflexivity.
    - destruct H1 as [Hs _Hguard].
      subst s.
      destruct H as [Heq_s [Hparent_active _Hboundary]].
      subst s0.
      split.
      + exact Hparent_active.
      + split.
        * intros v _Hdone_v Hactive_v. exact Hactive_v.
        * split.
          -- intros x. split; intro Hvisited; exact Hvisited.
          -- split.
             ++ intros x. reflexivity.
             ++ split.
                ** intros x. reflexivity.
                ** intros x. reflexivity.
  Qed.

  Lemma SegmentClosedAtRootCandidate_proof:
    SegmentClosedAtRootCandidate_statement.
  Proof.
    unfold SegmentClosedAtRootCandidate_statement,
      SegmentClosedAtRootInputCandidate,
      PoppedSegmentClosedCandidate,
      LoopDonePhase7Candidate,
      LoopInvPhase7Candidate,
      root_pop_guard.
    intros u s [Hloop Hguard] x w Hvis_x Hactive_x Hdfn_x Hreach.
    destruct Hloop as [_ [Hescape _Hcoverage]].
    destruct (classic (Visited w s)) as [Hvis_w | Hnot_vis_w].
    - exact Hvis_w.
    - specialize (Hescape x w Hactive_x Hdfn_x Hreach Hnot_vis_w) as
        [Hpending | Hold].
      + destruct Hpending as [a [_ [Hedge_a [Hnot_done_a _]]]].
        exfalso. apply Hnot_done_a. exact Hedge_a.
      + destruct Hold as
          [b [Hactive_b [Hdfn_lt_b [Hlow_le_b [_ _]]]]].
        exfalso.
        rewrite Hguard in Hlow_le_b.
        lia.
  Qed.

  Lemma stack_split_removed_vertex_dfn_ge_root:
    forall u x s popped rest,
      stack_split_at (stack s) u = (popped, rest) ->
      In u (stack s) ->
      stack_dfn_order s ->
      In x (stack s) ->
      ~ In x rest ->
      dfn s u <= dfn s x.
  Proof.
    intros u x s popped rest Hsplit Hu_stack Horder Hx_stack Hx_not_rest.
    destruct (stack_split_at_decomp (stack s) u Hu_stack popped rest Hsplit)
      as [prefix Hstack].
    pose proof Hx_stack as Hx_stack_old.
    rewrite Hstack in Hx_stack.
    rewrite List.in_app_iff in Hx_stack.
    destruct Hx_stack as [Hx_prefix | [Hx_eq_u | Hx_rest]].
    - destruct (in_split x prefix Hx_prefix) as [l1 [l2 Hprefix]].
      assert (Hafter:
                exists l1' l2',
                  stack s = l1' ++ x :: l2' /\ In u l2').
      { exists l1. exists (l2 ++ u :: rest). split.
        - rewrite Hstack. rewrite Hprefix. rewrite <- app_assoc.
          reflexivity.
        - rewrite List.in_app_iff. right. simpl. left. reflexivity. }
      exact (Horder x u Hx_stack_old Hu_stack Hafter).
    - subst x. apply le_n.
    - exfalso. apply Hx_not_rest. exact Hx_rest.
  Qed.

  Lemma stack_split_rest_in_original_stack:
    forall u x s popped rest,
      stack_split_at (stack s) u = (popped, rest) ->
      In u (stack s) ->
      In x rest ->
      In x (stack s).
  Proof.
    intros u x s popped rest Hsplit Hu_stack Hx_rest.
    destruct (stack_split_at_decomp (stack s) u Hu_stack popped rest Hsplit)
      as [prefix Hstack].
    rewrite Hstack, List.in_app_iff.
    right. simpl. right. exact Hx_rest.
  Qed.

  Lemma stack_split_older_active_vertex_in_rest:
    forall u x s popped rest,
      stack_split_at (stack s) u = (popped, rest) ->
      Active u s ->
      Active x s ->
      stack_dfn_order s ->
      dfn s x < dfn s u ->
      In x rest.
  Proof.
    intros u x s popped rest Hsplit Hu_active Hx_active Horder Hdfn_lt.
    destruct (classic (In x rest)) as [Hx_rest | Hx_not_rest];
      [exact Hx_rest |].
    exfalso.
    pose proof
      (stack_split_removed_vertex_dfn_ge_root
         u x s popped rest Hsplit Hu_active Horder Hx_active Hx_not_rest)
      as Hdfn_ge.
    lia.
  Qed.

  Lemma FramePopBoundaryCandidate_from_older_active_vertices_proof:
    forall F u s,
      Active u s ->
      LoopInvLowCandidate (frame_parent F) (frame_done F) s ->
      dfn s (frame_parent F) < dfn s u ->
      (forall v,
          frame_done F v ->
          Active v s ->
          dfn s v < dfn s u) ->
      FramePopBoundaryCandidate F u s.
  Proof.
    unfold FramePopBoundaryCandidate,
      LoopInvLowCandidate,
      LoopInvDoneCandidate,
      LocalActiveRootCandidate.
    intros F u s Hu_active
           [[[_Hshape [_Hsettled [_Hvis_parent
             [Hparent_active [Horder _Hinj]]]]] _Hdone_disc] _Hpartial]
           Hparent_older Hdone_older.
    split.
    - intros popped rest Hsplit.
      eapply stack_split_older_active_vertex_in_rest; eauto.
    - intros v Hdone_v Hactive_v popped rest Hsplit.
      eapply stack_split_older_active_vertex_in_rest; eauto.
  Qed.

  Lemma FramePopBoundaryCandidate_from_loop_done_older_vertices_proof:
    forall F u s,
      LoopDonePhase7Candidate u s ->
      FrameInvCandidate F s ->
      dfn s (frame_parent F) < dfn s u ->
      (forall v,
          frame_done F v ->
          Active v s ->
          dfn s v < dfn s u) ->
      FramePopBoundaryCandidate F u s.
  Proof.
    intros F u s Hloop_done Hframe Hparent_older Hdone_older.
    eapply FramePopBoundaryCandidate_from_older_active_vertices_proof.
    - unfold LoopDonePhase7Candidate,
        LoopInvPhase7Candidate,
        LoopInvPhase6Candidate,
        LoopInvLowCandidate,
        LoopInvDoneCandidate,
        LocalActiveRootCandidate in Hloop_done.
      destruct Hloop_done as [Hphase6 _Hphase7_tail].
      destruct Hphase6 as [Hlow _Hphase6_tail].
      destruct Hlow as [Hdone_loop _Hpartial].
      destruct Hdone_loop as [Hlocal _Hdone_disc].
      destruct Hlocal as [_Hshape [_Hsettled [_Hvis [Hactive _Horder]]]].
      exact Hactive.
    - eapply FrameInvProvidesLoopInvLowCandidate_proof.
      exact Hframe.
    - exact Hparent_older.
    - exact Hdone_older.
  Qed.

  Lemma MaybePopActivePostImpliesPreSnapshotCandidate_proof:
    MaybePopActivePostImpliesPreSnapshotCandidate_statement.
  Proof.
    unfold MaybePopActivePostImpliesPreSnapshotCandidate_statement,
      maybe_pop,
      pop_scc,
      root_pop_guard,
      Active.
    intros u snap.
    intro_state. hoare_auto_s.
    - destruct H as [Heq_s Hu_stack].
      subst s0.
      subst s.
      unfold pop_scc_state in *.
      destruct (stack_split_at (stack snap) u) as [popped rest] eqn:Hsplit.
      simpl in *.
      eapply stack_split_rest_in_original_stack
        with (popped := popped) (rest := rest);
        [exact Hsplit | exact Hu_stack | assumption].
    - destruct H1 as [Hs _Hguard].
      subst s.
      destruct H as [Heq_s _Hu_stack].
      subst s0.
      assumption.
  Qed.

  Lemma MaybePopProducesChildInactiveSelfLowCandidate_proof:
    forall u,
      Hoare
        (fun s => Active u s)
        (maybe_pop u)
        (fun _ s => ChildInactiveSelfLowForParentCandidate u s).
  Proof.
    unfold ChildInactiveSelfLowForParentCandidate,
      maybe_pop,
      root_pop_guard,
      Active.
    intros u.
    unfold If.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold pop_scc. intro_state. hoare_auto_s.
      subst s.
      destruct H as [Hguard _Hactive].
      unfold pop_scc_state.
      destruct (stack_split_at (stack s0) u) as [_popped _rest] eqn:_Hsplit.
      simpl. exact Hguard.
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume. }
      intros _ s [Hactive _Hnot_guard].
      intros Hnot_active.
      exfalso. apply Hnot_active. exact Hactive.
  Qed.

  Lemma PopSccKeepsDfnInjectiveCandidate_proof:
    PopSccKeepsDfnInjectiveCandidate_statement.
  Proof.
    unfold PopSccKeepsDfnInjectiveCandidate_statement.
    intros u.
    unfold pop_scc. intro_state. hoare_auto_s.
    subst s.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s0) u) as [popped rest] eqn:_Hsplit.
    simpl. exact H.
  Qed.

  Lemma MaybePopPreservesGlobalShapeCandidate_proof:
    MaybePopPreservesGlobalShapeCandidate_statement.
  Proof.
    unfold MaybePopPreservesGlobalShapeCandidate_statement,
      GlobalShapeCandidate,
      maybe_pop,
      root_pop_guard.
    intros u.
    intro_state. hoare_auto_s.
    - eapply Hoare_conseq_pre.
      2: {
        apply (@pop_scc_preserves_wf_scc_state
                 V E equiv0 H0 g root u).
      }
      intros s Hs. subst s. exact H.
    - destruct H1 as [Hs _Hguard].
      subst s. exact H.
  Qed.

  Lemma MaybePopPreservesOrderFactsCandidate_proof:
    MaybePopPreservesOrderFactsCandidate_statement.
  Proof.
    unfold MaybePopPreservesOrderFactsCandidate_statement,
      OrderFactsCandidate,
      Active,
      maybe_pop,
      root_pop_guard.
    intros u.
    intro_state. hoare_auto_s.
    - destruct H as [[Horder Hinj] Hu_stack].
      apply Hoare_conj with
        (Q1 := fun _ s => stack_dfn_order s)
        (Q2 := fun _ s => dfn_injective s).
      + eapply Hoare_conseq_pre.
        2: { apply (pop_scc_preserves_stack_dfn_order u). }
        intros s Hs.
        subst s.
        split; [exact Horder | exact Hu_stack].
      + eapply Hoare_conseq_pre.
        2: { apply (PopSccKeepsDfnInjectiveCandidate_proof u). }
        intros s Hs.
        subst s.
        exact Hinj.
    - destruct H1 as [Hs _Hguard].
      subst s.
      destruct H as [Horder _Hu_stack].
      exact Horder.
  Qed.

  Lemma MaybePopPreservesSettledClosedWithSegmentClosedCandidate_proof:
    MaybePopPreservesSettledClosedWithSegmentClosedCandidate_statement.
  Proof.
    unfold
      MaybePopPreservesSettledClosedWithSegmentClosedCandidate_statement,
      SettledClosedCandidate,
      Active,
      OrderFactsCandidate,
      PoppedSegmentClosedCandidate,
      maybe_pop,
      pop_scc,
      root_pop_guard.
    intros u.
    intro_state. hoare_auto_s.
    - destruct H as [Hsettled [Hu_stack [[Horder _Hinj] Hsegment_closed]]].
      subst s.
      unfold pop_scc_state in *.
      destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
      simpl in *.
      intros x w Hvis_x Hx_not_rest Hreach_xw.
      destruct (classic (In x (stack s0))) as [Hx_stack | Hx_not_stack].
      + eapply Hsegment_closed; eauto.
        eapply stack_split_removed_vertex_dfn_ge_root; eauto.
      + eapply Hsettled; eauto.
    - destruct H1 as [Hs _Hguard].
      subst s.
      destruct H as [Hsettled _].
      exact Hsettled.
  Qed.

  Lemma FramePopBoundarySnapshotPreservesDoneClosednessCandidate_proof:
    FramePopBoundarySnapshotPreservesDoneClosednessCandidate_statement.
  Proof.
    unfold
      FramePopBoundarySnapshotPreservesDoneClosednessCandidate_statement,
      FramePopBoundarySnapshotCandidate,
      DoneClosednessCandidate,
      done_reachable_closed,
      done_tree_reachable_closed,
      Active.
    intros F snap s
           [_Hparent_active [Hdone_active
            [Hvisited [_Hdfn [_Hlow Hfa]]]]]
           [Hclosed Htree_closed].
    split.
    - intros v w Hdone_v Hnot_stack_s Hreach_vw.
      apply Hvisited.
      destruct (classic (In v (stack snap))) as [Hactive_snap | Hnot_snap].
      + exfalso.
        apply Hnot_stack_s.
        exact (Hdone_active v Hdone_v Hactive_snap).
      + eapply Hclosed; eauto.
    - intros v w Hdone_v Hnot_stack_s Hfa_s_v Hfa_neq_s Hreach_vw.
      apply Hvisited.
      destruct (classic (In v (stack snap))) as [Hactive_snap | Hnot_snap].
      + exfalso.
        apply Hnot_stack_s.
        exact (Hdone_active v Hdone_v Hactive_snap).
	      + eapply Htree_closed; eauto.
	        * rewrite <- Hfa. exact Hfa_s_v.
	        * intros Hfa_snap_v.
	          apply Hfa_neq_s.
	          rewrite Hfa.
	          exact Hfa_snap_v.
	  Qed.

  Lemma FramePopBoundarySnapshotPreservesProcessedTreeChildrenCorrectWithTransportCandidate_proof:
    FramePopBoundarySnapshotPreservesProcessedTreeChildrenCorrectWithTransportCandidate_statement.
  Proof.
    unfold
      FramePopBoundarySnapshotPreservesProcessedTreeChildrenCorrectWithTransportCandidate_statement,
      FramePopBoundarySnapshotCandidate.
    intros F snap s
           [_Hparent_active [Hdone_active
            [_Hvisited [Hdfn [Hlow Hfa]]]]]
           Hchildren Hroot_transport.
    eapply ProcessedTreeChildrenCorrectCandidate_transport_proof.
    - exact Hdfn.
    - exact Hlow.
    - exact Hchildren.
    - intros child Hdone_child Hedge_child Hfa_s_child Hfa_neq_s_child.
      assert (Hfa_snap_child: fa snap child = frame_parent F).
      { rewrite <- Hfa. exact Hfa_s_child. }
      assert (Hfa_neq_snap_child: fa snap child <> child).
      { intro Hbad.
        apply Hfa_neq_s_child.
        rewrite Hfa. exact Hbad. }
      split; [exact Hfa_snap_child |].
      split; [exact Hfa_neq_snap_child |].
      split.
      + intros Hactive_snap_child.
        exact (Hdone_active child Hdone_child Hactive_snap_child).
      + apply Hroot_transport; assumption.
	  Qed.

  Lemma MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryAndTransportCandidate_proof:
    MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryAndTransportCandidate_statement.
  Proof.
    unfold
      MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryAndTransportCandidate_statement.
    intros F u.
    apply Hoare_normalize.
    intros snap [Hchildren [Hparent_active [Hboundary Hroot_transport]]].
    eapply Hoare_conseq_post.
    2: {
      eapply Hoare_conseq_pre.
      2: {
        apply
          (MaybePopProducesFramePopBoundarySnapshotCandidate_proof F u snap).
      }
      intros s Heq_s.
      subst s.
      split; [reflexivity |].
      split; [exact Hparent_active | exact Hboundary].
    }
    intros ret post Hsnapshot.
    eapply
      (FramePopBoundarySnapshotPreservesProcessedTreeChildrenCorrectWithTransportCandidate_proof
         F snap post).
    - exact Hsnapshot.
    - exact Hchildren.
    - intros child Hdone_child Hedge_child Hfa_child Hfa_neq_child.
      eapply Hroot_transport; eauto.
  Qed.

  Lemma MaybePopPreservesDoneClosednessWithFramePopBoundaryCandidate_proof:
    MaybePopPreservesDoneClosednessWithFramePopBoundaryCandidate_statement.
  Proof.
    unfold
      MaybePopPreservesDoneClosednessWithFramePopBoundaryCandidate_statement.
    intros F u.
    apply Hoare_normalize.
    intros snap [Hclosed [Hparent_active Hboundary]].
    eapply Hoare_conseq_post.
    2: {
      eapply Hoare_conseq_pre.
      2: {
        apply
          (MaybePopProducesFramePopBoundarySnapshotCandidate_proof
             F u snap).
      }
      intros s Heq_s.
      subst s.
      split; [reflexivity |].
      split; [exact Hparent_active | exact Hboundary].
    }
    intros r s Hsnapshot.
    eapply FramePopBoundarySnapshotPreservesDoneClosednessCandidate_proof.
    - exact Hsnapshot.
    - exact Hclosed.
  Qed.

  Lemma FramePopSnapshotsPreservePartialRootLowEquationCandidate_proof:
    FramePopSnapshotsPreservePartialRootLowEquationCandidate_statement.
  Proof.
    unfold
      FramePopSnapshotsPreservePartialRootLowEquationCandidate_statement,
      FramePopBoundarySnapshotCandidate,
      PartialRootLowEquationCandidate,
      LowFrontierCandidate,
      LowSourceCandidate,
      Active.
    intros F snap s
           [_Hparent_active [Hdone_active
            [_Hvisited [Hdfn [Hlow Hfa]]]]]
           Hactive_subset
           [Hfront Hsrc].
    destruct Hfront as [Hlow_parent_dfn Hfront].
    split.
    - split.
      + rewrite Hlow. rewrite Hdfn. exact Hlow_parent_dfn.
      + intros a Hdone_a Hedge_a.
        specialize (Hfront a Hdone_a Hedge_a) as [Htree Hstack].
        split.
        * intros Hfa_a.
          rewrite Hlow. rewrite (Hlow a).
          apply Htree.
          rewrite <- Hfa.
          exact Hfa_a.
        * intros Hactive_a.
          rewrite Hlow. rewrite Hdfn.
          apply Hstack.
          apply Hactive_subset.
          exact Hactive_a.
    - destruct Hsrc as [Hself | [Htree_src | Hstack_src]].
      + left.
        rewrite Hlow. rewrite Hdfn. exact Hself.
      + right. left.
        destruct Htree_src as
          [a [Hdone_a [Hedge_a [Hfa_a [Hfa_neq_a Hlow_eq]]]]].
        exists a.
        split; [exact Hdone_a |].
        split; [exact Hedge_a |].
        split.
        * rewrite Hfa. exact Hfa_a.
        * split.
          -- intros Hfa_post_a.
             apply Hfa_neq_a.
             rewrite <- Hfa.
             exact Hfa_post_a.
          -- rewrite Hlow. rewrite (Hlow a). exact Hlow_eq.
      + right. right.
        destruct Hstack_src as
          [a [Hdone_a [Hedge_a [Hactive_a [Hfa_neq_a Hlow_eq]]]]].
        exists a.
        split; [exact Hdone_a |].
        split; [exact Hedge_a |].
        split.
        * exact (Hdone_active a Hdone_a Hactive_a).
        * split.
          -- intros Hfa_post_a.
             apply Hfa_neq_a.
             rewrite <- Hfa.
             exact Hfa_post_a.
          -- rewrite Hlow. rewrite Hdfn. exact Hlow_eq.
  Qed.

  Lemma FramePopSnapshotsPreserveLoopInvLowCandidate_proof:
    FramePopSnapshotsPreserveLoopInvLowCandidate_statement.
  Proof.
    unfold FramePopSnapshotsPreserveLoopInvLowCandidate_statement,
      FramePopBoundarySnapshotCandidate,
      LoopInvLowCandidate,
      LoopInvDoneCandidate,
      LocalActiveRootCandidate,
      DoneDisciplineCandidate,
      DoneVisitedCandidate.
    intros F snap s
           [Hparent_active [Hdone_active
            [Hvisited [Hdfn [Hlow Hfa]]]]]
           Hactive_subset Hshape Hsettled Horder
           [Hdone_loop Hpartial].
    destruct Hdone_loop as [Hlocal Hdone_disc].
    destruct Hlocal as
      [_Hshape_snap [_Hsettled_snap
       [Hvisited_parent_snap [_Hactive_parent_snap _Horder_snap]]]].
    destruct Hdone_disc as [Hdone_subset Hdone_visited].
    split.
    - split.
      + split; [exact Hshape |].
        split; [exact Hsettled |].
        split.
        * apply Hvisited. exact Hvisited_parent_snap.
        * split; [exact Hparent_active | exact Horder].
      + split; [exact Hdone_subset |].
        intros a Hdone_a.
        apply Hvisited.
        exact (Hdone_visited a Hdone_a).
    - eapply FramePopSnapshotsPreservePartialRootLowEquationCandidate_proof.
      + unfold FramePopBoundarySnapshotCandidate.
        split; [exact Hparent_active |].
        split; [exact Hdone_active |].
        split; [exact Hvisited |].
        split; [exact Hdfn |].
        split; [exact Hlow | exact Hfa].
      + exact Hactive_subset.
      + exact Hpartial.
  Qed.

  Lemma MaybePopPreservesLoopInvLowWithFramePopBoundaryCandidate_proof:
    MaybePopPreservesLoopInvLowWithFramePopBoundaryCandidate_statement.
  Proof.
    unfold MaybePopPreservesLoopInvLowWithFramePopBoundaryCandidate_statement.
    intros F u.
    apply Hoare_normalize.
    intros snap [Hloop [Hu_active [Hboundary Hsegment_closed]]].
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with (Q1 := fun _ s => FramePopBoundarySnapshotCandidate F snap s)
             (Q2 := fun _ s =>
                      (forall x, Active x s -> Active x snap) /\
                      GlobalShapeCandidate s /\
                      SettledClosedCandidate s /\
                      OrderFactsCandidate s).
      - eapply Hoare_conseq_pre.
        2: {
          apply (MaybePopProducesFramePopBoundarySnapshotCandidate_proof
                   F u snap).
        }
        intros s Heq_s.
        subst s.
        split; [reflexivity |].
        destruct Hloop as [Hdone_loop _Hpartial].
        destruct Hdone_loop as [Hlocal _Hdone_disc].
        destruct Hlocal as [_Hshape [_Hsettled [_Hvisited
          [Hparent_active _Horder]]]].
        split; [exact Hparent_active | exact Hboundary].
      - apply Hoare_conj
          with (Q1 := fun _ s => forall x, Active x s -> Active x snap)
               (Q2 := fun _ s =>
                        GlobalShapeCandidate s /\
                        SettledClosedCandidate s /\
                        OrderFactsCandidate s).
        + eapply Hoare_conseq_pre.
          2: {
            apply (MaybePopActivePostImpliesPreSnapshotCandidate_proof
                     u snap).
          }
          intros s Heq_s.
          subst s.
          split; [reflexivity | exact Hu_active].
        + apply Hoare_conj
            with (Q1 := fun _ s => GlobalShapeCandidate s)
                 (Q2 := fun _ s =>
                          SettledClosedCandidate s /\
                          OrderFactsCandidate s).
          * eapply Hoare_conseq_pre.
            2: { apply (MaybePopPreservesGlobalShapeCandidate_proof u). }
            intros s Heq_s.
            subst s.
            destruct Hloop as [[Hlocal _Hdone_disc] _Hpartial].
            destruct Hlocal as [Hshape _].
            exact Hshape.
          * apply Hoare_conj
              with (Q1 := fun _ s => SettledClosedCandidate s)
                   (Q2 := fun _ s => OrderFactsCandidate s).
            -- eapply Hoare_conseq_pre.
               2: {
                 apply
                   (MaybePopPreservesSettledClosedWithSegmentClosedCandidate_proof
                      u).
               }
               intros s Heq_s.
               subst s.
               destruct Hloop as [[Hlocal _Hdone_disc] _Hpartial].
               destruct Hlocal as [_Hshape [Hsettled [_Hvisited
                 [_Hactive Horder]]]].
               split; [exact Hsettled |].
               split; [exact Hu_active |].
               split; [exact Horder | exact Hsegment_closed].
            -- eapply Hoare_conseq_pre.
               2: { apply (MaybePopPreservesOrderFactsCandidate_proof u). }
               intros s Heq_s.
               subst s.
               destruct Hloop as [[Hlocal _Hdone_disc] _Hpartial].
               destruct Hlocal as [_Hshape [_Hsettled [_Hvisited
                 [_Hactive Horder]]]].
               split; [exact Horder | exact Hu_active].
    }
    intros _ s [Hsnapshot [Hactive_subset
                 [Hshape [Hsettled Horder]]]].
    eapply FramePopSnapshotsPreserveLoopInvLowCandidate_proof; eauto.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Stack lemma: old-anchor stays in rest when child stays in rest    *)
  (* ---------------------------------------------------------------- *)

  Lemma old_anchor_in_rest_when_child_in_rest:
    forall u c b s popped rest,
      stack_split_at (stack s) u = (popped, rest) ->
      In u (stack s) ->
      In c rest ->
      In b (stack s) ->
      dfn s b < dfn s c ->
      stack_dfn_order s ->
      In b rest.
  Proof.
    intros u c b s popped rest Hsplit Hu_stack Hc_rest
           Hb_stack Hdfn_lt Horder.
    assert (Hc_stack: In c (stack s)).
    { eapply stack_split_rest_in_original_stack; eauto. }
    destruct (classic (In b rest)) as [Hin | Hnot_in]; [exact Hin |].
    exfalso.
    assert (Hdfn_c_le_b: dfn s c <= dfn s b).
    { destruct (stack_split_at_decomp (stack s) u Hu_stack popped rest Hsplit)
        as [prefix Hstack].
      assert (Hb_prefix_or_u: In b prefix \/ b = u).
      { rewrite Hstack in Hb_stack.
        rewrite List.in_app_iff in Hb_stack.
        destruct Hb_stack as [Hb_prefix | [Hb_u | Hb_rest]].
        - left. exact Hb_prefix.
        - right. symmetry. exact Hb_u.
        - exfalso. apply Hnot_in. exact Hb_rest. }
      destruct Hb_prefix_or_u as [Hb_prefix | Hb_u].
      - destruct (in_split b prefix Hb_prefix) as [l1 [l2 Hprefix]].
        apply (Horder b c Hb_stack Hc_stack).
        exists l1. exists (l2 ++ u :: rest). split.
        + rewrite Hstack. rewrite Hprefix. rewrite <- List.app_assoc.
          reflexivity.
        + rewrite List.in_app_iff. right. simpl. right. exact Hc_rest.
      - subst b.
        apply (Horder u c Hu_stack Hc_stack).
        exists prefix. exists rest. split; [exact Hstack | exact Hc_rest]. }
    lia.
  Qed.

  Lemma MaybePopProducesChildLowerStackAnchorsPreservedCandidate_proof:
    MaybePopProducesChildLowerStackAnchorsPreservedCandidate_statement.
  Proof.
    unfold
      MaybePopProducesChildLowerStackAnchorsPreservedCandidate_statement,
      ChildLowerStackAnchorsPreservedCandidate,
      OrderFactsCandidate,
      maybe_pop,
      pop_scc,
      root_pop_guard,
      Active.
    intros F u child snap.
    intro_state. hoare_auto_s.
    - destruct H as
        [Heq_s [Hu_active [[Horder _Hinj]
         [Hdone_child [Hchild_active [_Hparent_rest Hdone_rest]]]]]].
      subst s0.
      subst s.
      unfold pop_scc_state.
      destruct (stack_split_at (stack snap) u) as [popped rest] eqn:Hsplit.
      simpl.
      assert (Hchild_rest: In child rest).
      { exact (Hdone_rest child Hdone_child Hchild_active popped rest eq_refl). }
      match goal with
      | |- In ?anchor rest =>
          eapply old_anchor_in_rest_when_child_in_rest
            with (u := u) (c := child) (b := anchor)
                 (s := snap) (popped := popped) (rest := rest);
          eauto
      end.
    - destruct H1 as [Hs _Hguard].
      subst s.
      destruct H as
        [Heq_s [_Hu_active [_Horder
         [_Hdone_child [_Hchild_active _Hboundary]]]]].
      subst s0.
      match goal with
      | |- forall anchor, In anchor (stack snap) -> _ =>
          intros anchor Hb_active _Hdfn_lt; exact Hb_active
      | |- In ?anchor (stack snap) =>
          assumption
      end.
  Qed.

  Lemma MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryCandidate_proof:
    MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryCandidate_statement.
  Proof.
    unfold
      MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryCandidate_statement,
      maybe_pop,
      pop_scc,
      root_pop_guard,
      Active,
      OrderFactsCandidate.
    intros F u.
    intro_state. hoare_auto_s.
    - destruct H as
        [Hchildren [Hparent_active [Hu_active [Horderfacts Hboundary]]]].
      destruct Horderfacts as [Horder _Hinj].
      subst s.
      unfold pop_scc_state.
      destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
      simpl.
      eapply ProcessedTreeChildrenCorrectCandidate_transport_proof
        with (snap := s0).
      + intros x. reflexivity.
      + intros x. reflexivity.
      + exact Hchildren.
      + intros child Hdone_child Hedge_child Hfa_child Hfa_neq_child.
        assert (Hfa_snap_child: fa s0 child = frame_parent F).
        { exact Hfa_child. }
        assert (Hfa_neq_snap_child: fa s0 child <> child).
        { exact Hfa_neq_child. }
        split; [exact Hfa_snap_child |].
        split; [exact Hfa_neq_snap_child |].
        split.
        * intros Hactive_child.
          destruct Hboundary as [_Hparent_rest Hdone_rest].
          exact (Hdone_rest child Hdone_child Hactive_child popped rest Hsplit).
        * destruct (classic (In child (stack s0)))
            as [Hactive_child | Hnot_active_child].
          -- eapply ChildRootCorrectTransportFromStackShrinkCandidate_proof.
             ++ intros x. split; intro Hvisit; exact Hvisit.
             ++ intros x. reflexivity.
             ++ intros x. reflexivity.
             ++ intros x. reflexivity.
             ++ intros x Hactive_post.
                eapply stack_split_rest_in_original_stack
                  with (popped := popped) (rest := rest);
                  eauto.
             ++ unfold ChildLowerStackAnchorsPreservedCandidate, Active.
                intros anchor Hanchor_active Hanchor_lt.
                destruct Hboundary as [_Hparent_rest Hdone_rest].
                assert (Hchild_rest: In child rest).
                { exact (Hdone_rest child Hdone_child Hactive_child
                           popped rest Hsplit). }
                eapply old_anchor_in_rest_when_child_in_rest
                  with (u := u) (c := child) (b := anchor)
                       (s := s0) (popped := popped) (rest := rest);
                  eauto.
          -- eapply ChildRootCorrectTransportFromInactiveSelfLowCandidate_proof.
             ++ intros x. split; intro Hvisit; exact Hvisit.
             ++ intros x. reflexivity.
             ++ intros x. reflexivity.
             ++ intros x. reflexivity.
             ++ intros x Hactive_post.
                eapply stack_split_rest_in_original_stack
                  with (popped := popped) (rest := rest);
                  eauto.
             ++ destruct Hchildren as [_ [_ Hinactive]].
                apply Hinactive; assumption.
             ++ exact Hnot_active_child.
    - destruct H1 as [Hs _Hguard].
      subst s.
      destruct H as [Hchildren _].
      exact Hchildren.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* maybe_pop preserves ActiveProcessedChildSegmentSummaryCandidate   *)
  (* ---------------------------------------------------------------- *)

  Lemma MaybePopPreservesActiveProcessedChildSegmentSummaryCandidate_proof:
    MaybePopPreservesActiveProcessedChildSegmentSummaryCandidate_statement.
  Proof.
    unfold
      MaybePopPreservesActiveProcessedChildSegmentSummaryCandidate_statement.
    intros u done parent.
    unfold maybe_pop, root_pop_guard.
    intro_state. hoare_auto_s.
    - unfold pop_scc. intro_state. hoare_auto_s.
      subst s1 s.
      match goal with
      | Hpre:
          (ActiveProcessedChildSegmentSummaryCandidate parent done s0 /\
           LocalActiveRootCandidate parent s0 /\
           Active u s0) /\ _ |- _ =>
          destruct Hpre as [[Hsummaries [Hlocal Hu_stack]] _Hguard]
      | Hpre:
          ActiveProcessedChildSegmentSummaryCandidate parent done s0 /\
          LocalActiveRootCandidate parent s0 /\
          Active u s0 |- _ =>
          destruct Hpre as [Hsummaries [Hlocal Hu_stack]]
      end.
      unfold pop_scc_state in *.
      destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
      simpl in *.
      unfold ActiveProcessedChildSegmentSummaryCandidate in *.
      intros c Hdone_c Hedge_c Hfa_c Hfa_neq_c Hactive_c_post.
      unfold LocalActiveRootCandidate in Hlocal.
      destruct Hlocal as [Hshape [Hsettled [Hvis [_Hparent_stack Horder]]]].
      destruct Horder as [Horder_stack _].
      (* c was active before pop (since c ∈ rest ⊆ stack s0) *)
      assert (Hc_stack_s0: In c (stack s0)).
      { eapply stack_split_rest_in_original_stack
          with (popped := popped) (rest := rest);
          [exact Hsplit | exact Hu_stack | exact Hactive_c_post]. }
      (* Get the pre-state self-summary *)
      specialize (Hsummaries c Hdone_c Hedge_c Hfa_c Hfa_neq_c Hc_stack_s0).
      unfold ChildSelfSegmentEscapeSummaryCandidate in *.
      intros w Hc_w Hnot_vis_w_post.
      assert (Hnot_vis_w_pre: ~ Visited w s0).
      { unfold Visited. intro Hvis_w.
        apply Hnot_vis_w_post. exact Hvis_w. }
      specialize (Hsummaries w Hc_w Hnot_vis_w_pre)
        as [Hpending | Hanchor].
      + left.
        unfold PendingRootEscapeCandidate in *.
        destruct Hpending as
          [next [Hc_c [Hedge_next [Hnot_edge_next Hreach_next_w]]]].
        exists next.
        split; [exact Hc_c |].
        split; [exact Hedge_next |].
        split; [exact Hnot_edge_next | exact Hreach_next_w].
      + right.
        unfold OldStackEscapeAnchorCandidate in *.
        destruct Hanchor as
          [b0 [Hactive_b0 [Hdfn_b0_c [Hlow_c_b0 [Hc_b0 Hb0_w]]]]].
        exists b0.
        split.
        { simpl.
          eapply old_anchor_in_rest_when_child_in_rest
            with (u := u) (c := c) (b := b0)
                 (s := s0) (popped := popped) (rest := rest);
            eauto. }
        split.
        { simpl. unfold equiv_decb.
          exact Hdfn_b0_c. }
        split.
        { simpl. unfold equiv_decb.
          exact Hlow_c_b0. }
        split; [exact Hc_b0 | exact Hb0_w].
    - destruct H1 as [Hs _Hguard].
      subst s. destruct H as [Hsummaries _]. exact Hsummaries.
  Qed.

  Lemma stack_split_tree_ancestor_of_rest_active_in_rest:
    forall u child x s popped rest,
      stack_split_at (stack s) u = (popped, rest) ->
      Active u s ->
      Active child s ->
      In x rest ->
      GlobalShapeCandidate s ->
      OrderFactsCandidate s ->
      dg_reachable (state_to_dfs_tree g s root) child x ->
      In child rest.
  Proof.
    intros u child x s popped rest Hsplit Hu_active Hchild_active
           Hx_rest Hshape Horderfacts Htree_child_x.
    unfold Active in Hu_active, Hchild_active.
    destruct (classic (In child rest)) as [Hchild_rest | Hchild_not_rest];
      [exact Hchild_rest |].
    exfalso.
    unfold GlobalShapeCandidate, wf_scc_state in Hshape.
    destruct Hshape as [Hstack_visited [_Hdfn_inv [Hdfn_valid _Hfa_vis]]].
    destruct Horderfacts as [Hstack_order Hdfn_inj].
    assert (Hx_active: In x (stack s)).
    { eapply stack_split_rest_in_original_stack; eauto. }
    assert (Hdfn_x_child: dfn s x <= dfn s child).
    { destruct (stack_split_at_decomp (stack s) u Hu_active
                 popped rest Hsplit) as [prefix Hstack].
      assert (Hchild_prefix_or_u: In child prefix \/ child = u).
      { rewrite Hstack in Hchild_active.
        rewrite List.in_app_iff in Hchild_active.
        destruct Hchild_active as [Hchild_prefix | [Hchild_u | Hchild_rest]].
        - left. exact Hchild_prefix.
        - right. symmetry. exact Hchild_u.
        - exfalso. apply Hchild_not_rest. exact Hchild_rest. }
      destruct Hchild_prefix_or_u as [Hchild_prefix | Hchild_u].
      - destruct (in_split child prefix Hchild_prefix) as
          [l1 [l2 Hprefix]].
        apply (Hstack_order child x Hchild_active Hx_active).
        exists l1. exists (l2 ++ u :: rest).
        split.
        + rewrite Hstack. rewrite Hprefix. rewrite <- List.app_assoc.
          reflexivity.
        + rewrite List.in_app_iff. right. simpl. right. exact Hx_rest.
      - subst child.
        apply (Hstack_order u x Hu_active Hx_active).
        exists prefix. exists rest. split; [exact Hstack | exact Hx_rest]. }
    assert (Hdfn_child_x: dfn s child <= dfn s x).
    { assert (Hreach_dfn:
                forall y z,
                  dg_reachable (state_to_dfs_tree g s root) y z ->
                  dfn s y <= dfn s z).
      { intros y z Hreach.
        induction Hreach.
        - pose proof (Hdfn_valid x0 y H) as Hstep_dfn. lia.
        - apply le_n.
        - lia. }
      eapply Hreach_dfn. exact Htree_child_x. }
    assert (Hchild_neq_x: child <> x).
    { intro Hchild_x. apply Hchild_not_rest. subst child. exact Hx_rest. }
    assert (Hvisited_child: Visited child s).
    { unfold Visited. apply Hstack_visited. exact Hchild_active. }
    assert (Hvisited_x: Visited x s).
    { unfold Visited. apply Hstack_visited. exact Hx_active. }
    pose proof
      (Hdfn_inj child x Hchild_neq_x Hvisited_child Hvisited_x)
      as Hdfn_neq.
    apply Hdfn_neq. lia.
  Qed.

  Lemma PendingChildSegmentCandidate_snapshot_to_post_with_child_active:
    forall child snap s x,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, fa s z = fa snap z) ->
      Active child s ->
      PendingChildSegmentCandidate child snap x ->
      PendingChildSegmentCandidate child s x.
  Proof.
    unfold PendingChildSegmentCandidate.
    intros child snap s x Hvisited Hfa Hchild_active
           [Hvisited_child [_Hchild_active_snap Htree_child_x]].
    split.
    - apply (proj2 (Hvisited child)). exact Hvisited_child.
    - split; [exact Hchild_active |].
      eapply dfs_tree_reachable_transport_from_stable_fields; eauto.
  Qed.

  Lemma ProcessedTreeReachableFromCandidate_snapshot_to_post:
    forall u done snap s x,
      (forall z, Visited z s <-> Visited z snap) ->
      (forall z, fa s z = fa snap z) ->
      ProcessedTreeReachableFromCandidate u done snap x ->
      ProcessedTreeReachableFromCandidate u done s x.
  Proof.
    unfold ProcessedTreeReachableFromCandidate.
    intros u done snap s x Hvisited Hfa Hprocessed.
    destruct Hprocessed as [Hx_u | Hprocessed].
    - left. exact Hx_u.
    - right.
      destruct Hprocessed as
        [v [Hdone_v [Hedge_v [Hfa_v [Hfa_neq_v
          [Htree_vx Hreach_vx]]]]]].
      exists v.
      split; [exact Hdone_v |].
      split; [exact Hedge_v |].
      split.
      + rewrite Hfa. exact Hfa_v.
      + split.
        * intro Hbad.
          apply Hfa_neq_v.
          rewrite <- Hfa. exact Hbad.
        * split.
          -- eapply dfs_tree_reachable_transport_from_stable_fields; eauto.
          -- exact Hreach_vx.
  Qed.

  Lemma ProcessedTreeReachableFromCandidate_snapshot_to_post_monotone:
    forall u done snap s x,
      (forall z, Visited z snap -> Visited z s) ->
      (forall z, Visited z snap -> fa s z = fa snap z) ->
      DoneVisitedCandidate done snap ->
      ProcessedTreeReachableFromCandidate u done snap x ->
      ProcessedTreeReachableFromCandidate u done s x.
  Proof.
    unfold ProcessedTreeReachableFromCandidate,
      DoneVisitedCandidate.
    intros u done snap s x Hvisited Hfa Hdone_vis Hprocessed.
    destruct Hprocessed as [Hx_u | Hprocessed].
    - left. exact Hx_u.
    - right.
      destruct Hprocessed as
        [v [Hdone_v [Hedge_v [Hfa_v [Hfa_neq_v
          [Htree_vx Hreach_vx]]]]]].
      assert (Hvis_v: Visited v snap).
      { apply Hdone_vis. exact Hdone_v. }
      exists v.
      split; [exact Hdone_v |].
      split; [exact Hedge_v |].
      split.
      + rewrite (Hfa v Hvis_v). exact Hfa_v.
      + split.
        * intro Hbad.
          apply Hfa_neq_v.
          rewrite <- (Hfa v Hvis_v). exact Hbad.
        * split.
          -- eapply dfs_tree_reachable_transport_from_monotone_fields; eauto.
          -- exact Hreach_vx.
  Qed.

  Lemma MaybePopPreservesFrameSuspendedSegmentFieldsWithBoundaryCandidate_proof:
    forall F u,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           Active u s /\
           FramePopBoundaryCandidate F u s /\
           PoppedSegmentClosedCandidate u s)
        (maybe_pop u)
        (fun _ s =>
           SuspendedSegmentEscapeAccountingCandidate
             (frame_parent F) (frame_child F) (frame_done F) s /\
           SuspendedSegmentTreeCoverageByDoneCandidate
             (frame_parent F) (frame_child F) (frame_done F) s).
  Proof.
    intros F u.
    unfold maybe_pop, root_pop_guard.
    intro_state. hoare_auto_s.
    - unfold pop_scc. intro_state. hoare_auto_s.
      subst s1 s.
      destruct H as [Hframe [Hu_active [Hboundary _Hsegment_closed]]].
      pose proof
        (FrameInvProvidesLoopInvLowCandidate_proof F s0 Hframe) as Hlow.
      pose proof
        (FrameInvProvidesSuspendedSegmentEscapeAccountingCandidate_proof
           F s0 Hframe) as Hescape.
      pose proof
        (FrameInvProvidesSuspendedSegmentTreeCoverageCandidate_proof
           F s0 Hframe) as Hcoverage.
      unfold LoopInvLowCandidate, LoopInvDoneCandidate,
        LocalActiveRootCandidate in Hlow.
      destruct Hlow as [[Hlocal _Hdone_disc] _Hpartial].
      destruct Hlocal as
        [Hshape [_Hsettled [_Hvisited_parent
         [_Hparent_active Horderfacts]]]].
      unfold pop_scc_state.
      destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
      simpl.
      split.
      + unfold SuspendedSegmentEscapeAccountingCandidate.
        intros x w Hactive_x_post Hdfn_parent_x_post Houtside_post
               Hreach_xw Hnot_vis_w_post.
        assert (Hactive_x_snap: Active x s0).
        { eapply stack_split_rest_in_original_stack; eauto. }
        assert (Hdfn_parent_x_snap:
                  dfn s0 (frame_parent F) <= dfn s0 x).
        { exact Hdfn_parent_x_post. }
        assert (Houtside_snap:
                  ~ PendingChildSegmentCandidate (frame_child F) s0 x).
        { intro Hpending_snap.
          apply Houtside_post.
          destruct Hpending_snap as
            [Hvisited_child [Hactive_child_snap Htree_child_x]].
          unfold PendingChildSegmentCandidate.
          simpl.
          split; [exact Hvisited_child |].
          split.
          - eapply stack_split_tree_ancestor_of_rest_active_in_rest
              with (u := u) (x := x) (s := s0)
                   (popped := popped) (rest := rest); eauto.
          - exact Htree_child_x. }
        assert (Hnot_vis_w_snap: ~ Visited w s0).
        { intro Hvisited_w. apply Hnot_vis_w_post. exact Hvisited_w. }
        specialize (Hescape x w Hactive_x_snap Hdfn_parent_x_snap
                      Houtside_snap Hreach_xw Hnot_vis_w_snap) as
          [Hpending | Hanchor].
        * left. exact Hpending.
        * right.
          unfold OldStackEscapeAnchorCandidate in Hanchor |- *.
          destruct Hanchor as
            [anchor
             [Hactive_anchor [Hdfn_anchor_parent
              [Hlow_parent_anchor [Hx_anchor Hanchor_w]]]]].
          exists anchor.
          split.
          -- simpl.
             destruct Hboundary as [Hparent_rest _Hdone_rest].
             eapply old_anchor_in_rest_when_child_in_rest
               with (u := u) (c := frame_parent F) (b := anchor)
                    (s := s0) (popped := popped) (rest := rest).
             ++ exact Hsplit.
             ++ exact Hu_active.
             ++ exact (Hparent_rest popped rest Hsplit).
             ++ exact Hactive_anchor.
             ++ exact Hdfn_anchor_parent.
             ++ exact (proj1 Horderfacts).
          -- split; [exact Hdfn_anchor_parent |].
             split; [exact Hlow_parent_anchor |].
             split; [exact Hx_anchor | exact Hanchor_w].
      + unfold SuspendedSegmentTreeCoverageByDoneCandidate.
        intros x Hactive_x_post Hdfn_parent_x_post Houtside_post.
        assert (Hactive_x_snap: Active x s0).
        { eapply stack_split_rest_in_original_stack; eauto. }
        assert (Hdfn_parent_x_snap:
                  dfn s0 (frame_parent F) <= dfn s0 x).
        { exact Hdfn_parent_x_post. }
        assert (Houtside_snap:
                  ~ PendingChildSegmentCandidate (frame_child F) s0 x).
        { intro Hpending_snap.
          apply Houtside_post.
          destruct Hpending_snap as
            [Hvisited_child [Hactive_child_snap Htree_child_x]].
          unfold PendingChildSegmentCandidate.
          simpl.
          split; [exact Hvisited_child |].
          split.
          - eapply stack_split_tree_ancestor_of_rest_active_in_rest
              with (u := u) (x := x) (s := s0)
                   (popped := popped) (rest := rest); eauto.
          - exact Htree_child_x. }
        specialize (Hcoverage x Hactive_x_snap Hdfn_parent_x_snap
                      Houtside_snap) as Hprocessed.
        eapply ProcessedTreeReachableFromCandidate_snapshot_to_post.
        * intros z. split; intro Hz; exact Hz.
        * intros z. reflexivity.
        * exact Hprocessed.
    - destruct H1 as [Hs _Hguard].
      subst s.
      destruct H as [Hframe _Htail].
      split.
      + eapply FrameInvProvidesSuspendedSegmentEscapeAccountingCandidate_proof.
        exact Hframe.
      + eapply FrameInvProvidesSuspendedSegmentTreeCoverageCandidate_proof.
        exact Hframe.
  Qed.

  Lemma MaybePopPreservesFrameNonSegmentFieldsWithBoundaryCandidate_proof:
    forall F u,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           Active u s /\
           FramePopBoundaryCandidate F u s /\
           PoppedSegmentClosedCandidate u s)
        (maybe_pop u)
        (fun _ s =>
           ParentResumeShapeCandidate
             (frame_parent F) (frame_child F) (frame_done F) s /\
           LoopInvLowCandidate (frame_parent F) (frame_done F) s /\
           SuspendedParentFrameResumeCandidate
             (frame_parent F) (frame_child F) (frame_done F) s /\
           DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
           ProcessedTreeChildrenCorrectCandidate
             (frame_parent F) (frame_done F) s /\
           ActiveProcessedChildSegmentSummaryCandidate
             (frame_parent F) (frame_done F) s).
  Proof.
    intros F u.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s =>
             ParentResumeShapeCandidate
               (frame_parent F) (frame_child F) (frame_done F) s)
          (Q2 := fun _ s =>
             LoopInvLowCandidate (frame_parent F) (frame_done F) s /\
             SuspendedParentFrameResumeCandidate
               (frame_parent F) (frame_child F) (frame_done F) s /\
             DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
             ProcessedTreeChildrenCorrectCandidate
               (frame_parent F) (frame_done F) s /\
             ActiveProcessedChildSegmentSummaryCandidate
               (frame_parent F) (frame_done F) s).
      - eapply Hoare_conseq_pre.
        2: { apply FrameParentResumeShapePreservedByMaybePopCandidate_proof. }
        intros s [Hframe _Htail].
        eapply FrameInvProvidesParentResumeShapeCandidate_proof.
        exact Hframe.
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               LoopInvLowCandidate (frame_parent F) (frame_done F) s)
            (Q2 := fun _ s =>
               SuspendedParentFrameResumeCandidate
                 (frame_parent F) (frame_child F) (frame_done F) s /\
               DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
               ProcessedTreeChildrenCorrectCandidate
                 (frame_parent F) (frame_done F) s /\
               ActiveProcessedChildSegmentSummaryCandidate
                 (frame_parent F) (frame_done F) s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (MaybePopPreservesLoopInvLowWithFramePopBoundaryCandidate_proof
                 F u).
          }
          intros s [Hframe [Hu_active [Hboundary Hsegment_closed]]].
          split.
          * eapply FrameInvProvidesLoopInvLowCandidate_proof.
            exact Hframe.
          * split; [exact Hu_active |].
            split; [exact Hboundary | exact Hsegment_closed].
        + apply Hoare_conj
            with
              (Q1 := fun _ s =>
                 SuspendedParentFrameResumeCandidate
                   (frame_parent F) (frame_child F) (frame_done F) s)
              (Q2 := fun _ s =>
                 DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
                 ProcessedTreeChildrenCorrectCandidate
                   (frame_parent F) (frame_done F) s /\
                 ActiveProcessedChildSegmentSummaryCandidate
                   (frame_parent F) (frame_done F) s).
          * eapply Hoare_conseq_pre.
            2: {
              apply
                FrameSuspendedParentFrameResumePreservedByMaybePopCandidate_proof.
            }
            intros s [Hframe _Htail].
            eapply FrameInvProvidesSuspendedParentFrameResumeCandidate_proof.
            exact Hframe.
          * apply Hoare_conj
              with
                (Q1 := fun _ s =>
                   DoneClosednessCandidate
                     (frame_parent F) (frame_done F) s)
                (Q2 := fun _ s =>
                   ProcessedTreeChildrenCorrectCandidate
                     (frame_parent F) (frame_done F) s /\
                   ActiveProcessedChildSegmentSummaryCandidate
                     (frame_parent F) (frame_done F) s).
            -- eapply Hoare_conseq_pre.
               2: {
                 apply
                   (MaybePopPreservesDoneClosednessWithFramePopBoundaryCandidate_proof
                      F u).
               }
               intros s [Hframe [_Hu_active [Hboundary _Hsegment_closed]]].
               split.
               ++ eapply FrameInvProvidesDoneClosednessCandidate_proof.
                  exact Hframe.
               ++ split.
                  ** pose proof
                       (FrameInvProvidesLoopInvLowCandidate_proof F s Hframe)
                       as Hlow.
                     unfold LoopInvLowCandidate,
                       LoopInvDoneCandidate,
                       LocalActiveRootCandidate in Hlow.
                     destruct Hlow as [[Hlocal _Hdone_disc] _Hpartial].
                     destruct Hlocal as
                       [_Hshape [_Hsettled [_Hvis [Hactive _Horder]]]].
                     exact Hactive.
                  ** exact Hboundary.
            -- apply Hoare_conj.
               ++ eapply Hoare_conseq_pre.
                  2: {
                    apply
                      (MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryCandidate_proof
                         F u).
                  }
                  intros s [Hframe [Hu_active [Hboundary _Hsegment_closed]]].
                  pose proof
                    (FrameInvProvidesLoopInvLowCandidate_proof F s Hframe)
                    as Hlow.
                  unfold LoopInvLowCandidate,
                    LoopInvDoneCandidate,
                    LocalActiveRootCandidate in Hlow.
                  destruct Hlow as [[Hlocal _Hdone_disc] _Hpartial].
                  destruct Hlocal as
                    [_Hshape [_Hsettled [_Hvis [Hparent_active Horder]]]].
                  split.
                  ** eapply
                       FrameInvProvidesProcessedTreeChildrenCorrectCandidate_proof.
                     exact Hframe.
                  ** split; [exact Hparent_active |].
                     split; [exact Hu_active |].
                     split; [exact Horder | exact Hboundary].
               ++ eapply Hoare_conseq_pre.
                  2: {
                    apply
                      (MaybePopPreservesActiveProcessedChildSegmentSummaryCandidate_proof
                         u (frame_done F) (frame_parent F)).
                  }
                  intros s [Hframe [Hu_active _Htail]].
                  split.
                  ** eapply
                       FrameInvProvidesActiveProcessedChildSegmentSummaryCandidate_proof.
                     exact Hframe.
                  ** split.
                     --- pose proof
                           (FrameInvProvidesLoopInvLowCandidate_proof F s Hframe)
                           as Hlow.
                         unfold LoopInvLowCandidate,
                           LoopInvDoneCandidate in Hlow.
                         exact (proj1 (proj1 Hlow)).
                     --- exact Hu_active.
    }
    intros _ s
      [Hresume
       [Hlow [Hsuspended [Hclosed [Hchildren Hactive_segments]]]]].
    split; [exact Hresume |].
    split; [exact Hlow |].
    split; [exact Hsuspended |].
    split; [exact Hclosed |].
    split; [exact Hchildren | exact Hactive_segments].
  Qed.

  Lemma MaybePopPreservesFrameInvWithBoundaryCandidate_proof:
    forall F u,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           Active u s /\
           FramePopBoundaryCandidate F u s /\
           PoppedSegmentClosedCandidate u s)
        (maybe_pop u)
        (fun _ s => FrameInvCandidate F s).
  Proof.
    intros F u.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s =>
             ParentResumeShapeCandidate
               (frame_parent F) (frame_child F) (frame_done F) s /\
             LoopInvLowCandidate (frame_parent F) (frame_done F) s /\
             SuspendedParentFrameResumeCandidate
               (frame_parent F) (frame_child F) (frame_done F) s /\
             DoneClosednessCandidate (frame_parent F) (frame_done F) s /\
             ProcessedTreeChildrenCorrectCandidate
               (frame_parent F) (frame_done F) s /\
             ActiveProcessedChildSegmentSummaryCandidate
               (frame_parent F) (frame_done F) s)
          (Q2 := fun _ s =>
             SuspendedSegmentEscapeAccountingCandidate
               (frame_parent F) (frame_child F) (frame_done F) s /\
             SuspendedSegmentTreeCoverageByDoneCandidate
               (frame_parent F) (frame_child F) (frame_done F) s).
      - apply MaybePopPreservesFrameNonSegmentFieldsWithBoundaryCandidate_proof.
      - apply
          MaybePopPreservesFrameSuspendedSegmentFieldsWithBoundaryCandidate_proof.
    }
    intros _ s
      [[Hresume
        [Hlow [Hsuspended [Hclosed [Hchildren Hactive_segments]]]]]
       [Hescape Hcoverage]].
    unfold FrameInvCandidate.
    split; [exact Hresume |].
    split; [exact Hlow |].
    split; [exact Hsuspended |].
    split; [exact Hclosed |].
    split; [exact Hchildren |].
    split; [exact Hactive_segments |].
    split; [exact Hescape | exact Hcoverage].
  Qed.

  Lemma PreloopMakesFrameVerticesOlderThanChildCandidate_proof:
    forall F parent child done,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           dfn s (frame_parent F) < dfn s child /\
           forall v,
             frame_done F v ->
             dfn s v < dfn s child).
  Proof.
    unfold Hoare.
    intros F parent child done s1 r s2 [Hframe Hentry] Hrun.
    pose proof
      (FrameInvProvidesLoopInvLowCandidate_proof F s1 Hframe) as Hlow.
    unfold LoopInvLowCandidate, LoopInvDoneCandidate,
      LocalActiveRootCandidate, DoneDisciplineCandidate in Hlow.
    destruct Hlow as [[Hlocal [_Hdone_subset Hdone_visited]] _Hpartial].
    destruct Hlocal as
      [_Hshape_frame [_Hsettled_frame
       [Hvisited_parent_frame _Hactive_order_frame]]].
    unfold ChildEntryCandidate,
      ParentLoopSuspendedBaseCandidate,
      PendingChildShapeCandidate,
      GlobalShapePreCandidate,
      wf_scc_state_pre,
      GlobalShapeCandidate,
      wf_scc_state in Hentry.
    destruct Hentry as [_Hparent_base [Hglobal_pre _Hpending_tail]].
    destruct Hglobal_pre as [Hwf Hchild_unvisited].
    destruct Hwf as [_Hstack_visited [Hdfn_inv _Hwf_tail]].
    split.
    - pose proof
        (preloop_after_visited_dfn_lt (frame_parent F) child) as Hlt.
      unfold Hoare in Hlt.
      eapply Hlt; [| exact Hrun].
      split; [exact Hvisited_parent_frame |].
      split; [exact Hchild_unvisited | exact Hdfn_inv].
    - intros v Hdone_v.
      pose proof (preloop_after_visited_dfn_lt v child) as Hlt.
      unfold Hoare in Hlt.
      eapply Hlt; [| exact Hrun].
      split.
      + exact (Hdone_visited v Hdone_v).
      + split; [exact Hchild_unvisited | exact Hdfn_inv].
  Qed.

  Lemma PreloopProducesFrameBodyPrefixFactsCandidate_proof:
    forall F parent child done,
      Edge parent child ->
      ~ done child ->
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           FrameCompatibleWithCallCandidate F parent child s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           ParentResumeShapeCandidate
             (frame_parent F) (frame_child F) (frame_done F) s /\
           Visited (frame_child F) s /\
           SuspendedParentFrameResumeCandidate
             (frame_parent F) (frame_child F) (frame_done F) s /\
           dfn s (frame_parent F) < dfn s child /\
           forall v,
             frame_done F v ->
             dfn s v < dfn s child).
  Proof.
    intros F parent child done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s =>
             ParentResumeShapeCandidate
               (frame_parent F) (frame_child F) (frame_done F) s /\
             Visited (frame_child F) s)
          (Q2 := fun _ s =>
             SuspendedParentFrameResumeCandidate
               (frame_parent F) (frame_child F) (frame_done F) s /\
             dfn s (frame_parent F) < dfn s child /\
             forall v,
               frame_done F v ->
               dfn s v < dfn s child).
      - apply
          (FrameParentResumeShapeAfterPreloopCandidate_proof
             F parent child done Hedge Hnot_done).
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               SuspendedParentFrameResumeCandidate
                 (frame_parent F) (frame_child F) (frame_done F) s)
            (Q2 := fun _ s =>
               dfn s (frame_parent F) < dfn s child /\
               forall v,
                 frame_done F v ->
                 dfn s v < dfn s child).
        + apply
            (FrameSuspendedParentFrameResumeAfterPreloopCandidate_proof
               F parent child done Hedge Hnot_done).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (PreloopMakesFrameVerticesOlderThanChildCandidate_proof
                 F parent child done).
          }
          intros s [Hframe [_Hcompat Hentry]].
          split; [exact Hframe | exact Hentry].
    }
    intros _ s [[Hresume Hvis_child]
                [Hsuspended [Hparent_older Hdone_older]]].
    split; [exact Hresume |].
    split; [exact Hvis_child |].
    split; [exact Hsuspended |].
    split; [exact Hparent_older | exact Hdone_older].
  Qed.

  Lemma PreloopProducesPendingChildSegmentFromFrameCompatibilityCandidate_proof:
    forall F parent child done,
      Hoare
        (fun s =>
           FrameCompatibleWithCallCandidate F parent child s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           PendingChildSegmentCandidate (frame_child F) s child).
  Proof.
    unfold FrameCompatibleWithCallCandidate,
      PendingChildSegmentCandidate,
      ChildEntryCandidate,
      ParentLoopSuspendedBaseCandidate,
      PendingChildShapeCandidate,
      GlobalShapePreCandidate,
      Visited,
      Active.
    intros F parent child done.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s.
    destruct H as [Hcompat [_Hparent_base Hpending_shape]].
    destruct Hpending_shape as
      [Hglobal_pre [_Hsettled [_Hvis_parent [Hedge_parent_child
       [Hfa_child Horderfacts]]]]].
    destruct Hglobal_pre as [_Hwf Hchild_unvisited].
    assert (Hfa_neq_child: fa s0 child <> child).
    { intro Hfa_self.
      apply Hchild_unvisited.
      rewrite Hfa_child in Hfa_self.
      rewrite <- Hfa_self.
      exact _Hvis_parent. }
    simpl.
    destruct Hcompat as [[_Hown_parent Hown_child] | Hpending_parent].
    - rewrite Hown_child.
      split.
      + sets_unfold. right. reflexivity.
      + split.
        * left. reflexivity.
        * apply Coq.Relations.Relation_Operators.rt_refl.
    - destruct Hpending_parent as
        [Hvisited_frame_child [Hactive_frame_child Htree_frame_parent]].
      split.
      + sets_unfold. left. exact Hvisited_frame_child.
      + split.
        * right. exact Hactive_frame_child.
        * eapply dg_reachable_trans.
          -- eapply dfs_tree_reachable_transport_from_monotone_fields
               with (snap := s0).
             ++ intros z Hvis_z.
                sets_unfold. left. exact Hvis_z.
             ++ intros z _Hvis_z. reflexivity.
             ++ exact Htree_frame_parent.
          -- apply dg_reachable_step.
             apply tree_step_char_backward.
             ++ exact Hedge_parent_child.
             ++ simpl. exact Hfa_child.
             ++ simpl. exact Hfa_neq_child.
             ++ simpl. sets_unfold. right. reflexivity.
  Qed.

  Lemma PreloopPreservesFrameSuspendedSegmentFieldsFromCompatibilityCandidate_proof:
    forall F parent child done,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           FrameCompatibleWithCallCandidate F parent child s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           SuspendedSegmentEscapeAccountingCandidate
             (frame_parent F) (frame_child F) (frame_done F) s /\
           SuspendedSegmentTreeCoverageByDoneCandidate
             (frame_parent F) (frame_child F) (frame_done F) s).
  Proof.
    intros F parent child done.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s.
    destruct H as [Hframe [Hcompat Hentry]].
    set (sp :=
           RecordSet.set visited (fun vs => vs ∪ [child])
             (RecordSet.set stack (fun stk => child :: stk)
                (RecordSet.set timer S
                   (RecordSet.set low
                      (fun low0 x =>
                         if equiv_decb x child then timer s0 else low0 x)
                      (RecordSet.set dfn
                         (fun dfn0 x =>
                            if equiv_decb x child then timer s0 else dfn0 x)
                         s0))))).
    change
      (SuspendedSegmentEscapeAccountingCandidate
         (frame_parent F) (frame_child F) (frame_done F) sp /\
       SuspendedSegmentTreeCoverageByDoneCandidate
         (frame_parent F) (frame_child F) (frame_done F) sp).
    pose proof
      (FrameInvProvidesLoopInvLowCandidate_proof F s0 Hframe) as Hlow.
    pose proof
      (FrameInvProvidesSuspendedSegmentEscapeAccountingCandidate_proof
         F s0 Hframe) as Hescape.
    pose proof
      (FrameInvProvidesSuspendedSegmentTreeCoverageCandidate_proof
         F s0 Hframe) as Hcoverage.
    unfold LoopInvLowCandidate, LoopInvDoneCandidate,
      LocalActiveRootCandidate, DoneDisciplineCandidate in Hlow.
    destruct Hlow as [[Hlocal [_Hdone_subset Hdone_vis]] _Hpartial].
    destruct Hlocal as
      [Hshape [_Hsettled [_Hvis_parent
       [Hactive_parent _Horderfacts]]]].
    unfold ChildEntryCandidate,
      ParentLoopSuspendedBaseCandidate,
      PendingChildShapeCandidate,
      GlobalShapePreCandidate in Hentry.
    destruct Hentry as [_Hparent_base Hpending_shape].
    destruct Hpending_shape as
      [Hglobal_pre [_Hsettled_child [_Hvis_direct_parent
       [Hedge_parent_child [Hfa_child _Horder_child]]]]].
    destruct Hglobal_pre as [_Hwf Hchild_unvisited].
    assert (Hframe_parent_neq_child: frame_parent F <> child).
    { intro Hbad. apply Hchild_unvisited.
      rewrite <- Hbad. exact _Hvis_parent. }
    assert (Hfa_child_neq: fa s0 child <> child).
    { intro Hbad. apply Hchild_unvisited.
      rewrite Hfa_child in Hbad. rewrite <- Hbad.
      exact _Hvis_direct_parent. }
    assert (Hvisited_sp_mono:
              forall z, Visited z s0 -> Visited z sp).
    { intros z Hvis_z. subst sp. unfold Visited. simpl.
      sets_unfold. left. exact Hvis_z. }
    assert (Hactive_sp_cases:
              forall z, Active z sp -> z = child \/ Active z s0).
    { intros z Hactive_z. subst sp. unfold Active in *.
      simpl in Hactive_z. destruct Hactive_z as [Hz | Hz].
      - left. symmetry. exact Hz.
      - right. exact Hz. }
    assert (Hactive_sp_old:
              forall z, Active z s0 -> Active z sp).
    { intros z Hactive_z. subst sp. unfold Active in *. simpl.
      right. exact Hactive_z. }
    assert (Hvisited_child_sp: Visited child sp).
    { subst sp. unfold Visited. simpl. sets_unfold. right. reflexivity. }
    assert (Hactive_child_sp: Active child sp).
    { subst sp. unfold Active. simpl. left. reflexivity. }
    assert (Hfa_sp_keep:
              forall z, fa sp z = fa s0 z).
    { intro z. subst sp. reflexivity. }
    assert (Hdfn_sp_keep:
              forall z, z <> child -> dfn sp z = dfn s0 z).
    { intros z Hz. subst sp. simpl. unfold equiv_decb.
      destruct (equiv_dec z child) as [Hbad | _].
      - exfalso. apply Hz. exact Hbad.
      - reflexivity. }
    assert (Hlow_sp_keep:
              forall z, z <> child -> low sp z = low s0 z).
    { intros z Hz. subst sp. simpl. unfold equiv_decb.
      destruct (equiv_dec z child) as [Hbad | _].
      - exfalso. apply Hz. exact Hbad.
      - reflexivity. }
    assert (Hpending_child_post:
              PendingChildSegmentCandidate (frame_child F)
                sp child).
    { unfold FrameCompatibleWithCallCandidate in Hcompat.
      unfold PendingChildSegmentCandidate.
      destruct Hcompat as [[_Hown_parent Hown_child] | Hpending_parent].
      - rewrite Hown_child.
        split; [exact Hvisited_child_sp |].
        split; [exact Hactive_child_sp |].
        apply Coq.Relations.Relation_Operators.rt_refl.
      - destruct Hpending_parent as
          [Hvisited_frame_child [Hactive_frame_child Htree_frame_parent]].
        split; [apply Hvisited_sp_mono; exact Hvisited_frame_child |].
        split; [apply Hactive_sp_old; exact Hactive_frame_child |].
        eapply dg_reachable_trans.
        + eapply dfs_tree_reachable_transport_from_monotone_fields
             with (snap := s0).
          * exact Hvisited_sp_mono.
          * intros z _Hvis_z. apply Hfa_sp_keep.
          * exact Htree_frame_parent.
        + apply dg_reachable_step.
          apply tree_step_char_backward.
          * exact Hedge_parent_child.
          * rewrite Hfa_sp_keep. exact Hfa_child.
          * rewrite Hfa_sp_keep. exact Hfa_child_neq.
          * exact Hvisited_child_sp. }
    assert (Hpending_pre_to_post:
              forall x,
                PendingChildSegmentCandidate (frame_child F) s0 x ->
                PendingChildSegmentCandidate (frame_child F) sp x).
    { intros x [Hvisited_frame_child [Hactive_frame_child Htree_frame_x]].
      unfold PendingChildSegmentCandidate.
      split; [apply Hvisited_sp_mono; exact Hvisited_frame_child |].
      split; [apply Hactive_sp_old; exact Hactive_frame_child |].
      eapply dfs_tree_reachable_transport_from_monotone_fields
        with (snap := s0).
      - exact Hvisited_sp_mono.
      - intros z _Hvis_z. apply Hfa_sp_keep.
      - exact Htree_frame_x. }
    assert (Hdfn_parent_keep:
              dfn sp (frame_parent F) =
              dfn s0 (frame_parent F)).
    { apply Hdfn_sp_keep. exact Hframe_parent_neq_child. }
    assert (Hlow_parent_keep:
              low sp (frame_parent F) =
              low s0 (frame_parent F)).
    { apply Hlow_sp_keep. exact Hframe_parent_neq_child. }
    split.
    - unfold SuspendedSegmentEscapeAccountingCandidate.
      intros x w Hactive_x_post Hdfn_parent_x_post Houtside_post
             Hreach_xw Hnot_vis_w_post.
      destruct (Hactive_sp_cases x Hactive_x_post) as
        [Hx_child | Hactive_x_pre].
      + subst x.
        exfalso. apply Houtside_post. exact Hpending_child_post.
      + assert (Hx_neq_child: x <> child).
        { intro Hx_child. subst x.
          apply Hchild_unvisited.
          unfold GlobalShapeCandidate, wf_scc_state in Hshape.
          destruct Hshape as [Hstack_vis _].
          apply Hstack_vis. exact Hactive_x_pre. }
        assert (Hdfn_x_keep:
                  dfn sp x =
                  dfn s0 x).
        { apply Hdfn_sp_keep. exact Hx_neq_child. }
        assert (Hdfn_parent_x_pre:
                  dfn s0 (frame_parent F) <= dfn s0 x).
        { rewrite Hdfn_parent_keep in Hdfn_parent_x_post.
          rewrite Hdfn_x_keep in Hdfn_parent_x_post.
          exact Hdfn_parent_x_post. }
        assert (Houtside_pre:
                  ~ PendingChildSegmentCandidate (frame_child F) s0 x).
        { intro Hpending_pre.
          apply Houtside_post.
          exact (Hpending_pre_to_post x Hpending_pre). }
        assert (Hnot_vis_w_pre: ~ Visited w s0).
        { intro Hvisited_w_pre.
          apply Hnot_vis_w_post.
          apply Hvisited_sp_mono. exact Hvisited_w_pre. }
        specialize (Hescape x w Hactive_x_pre Hdfn_parent_x_pre
                      Houtside_pre Hreach_xw Hnot_vis_w_pre) as
          [Hpending | Hanchor].
        * left. exact Hpending.
        * right.
          unfold OldStackEscapeAnchorCandidate in Hanchor |- *.
          destruct Hanchor as
            [anchor
             [Hactive_anchor [Hdfn_anchor_parent
              [Hlow_parent_anchor [Hx_anchor Hanchor_w]]]]].
          assert (Hanchor_neq_child: anchor <> child).
          { intro Hanchor_child. subst anchor.
            apply Hchild_unvisited.
            unfold GlobalShapeCandidate, wf_scc_state in Hshape.
            destruct Hshape as [Hstack_vis _].
            apply Hstack_vis. exact Hactive_anchor. }
          exists anchor.
          split.
          -- apply Hactive_sp_old. exact Hactive_anchor.
          -- split.
             ++ rewrite Hdfn_sp_keep; [rewrite Hdfn_parent_keep |].
                ** exact Hdfn_anchor_parent.
                ** exact Hanchor_neq_child.
             ++ split.
                ** rewrite Hlow_parent_keep.
                   rewrite Hdfn_sp_keep; [exact Hlow_parent_anchor |].
                   exact Hanchor_neq_child.
                ** split; [exact Hx_anchor | exact Hanchor_w].
    - unfold SuspendedSegmentTreeCoverageByDoneCandidate.
      intros x Hactive_x_post Hdfn_parent_x_post Houtside_post.
      destruct (Hactive_sp_cases x Hactive_x_post) as
        [Hx_child | Hactive_x_pre].
      + subst x.
        exfalso. apply Houtside_post. exact Hpending_child_post.
      + assert (Hx_neq_child: x <> child).
        { intro Hx_child. subst x.
          apply Hchild_unvisited.
          unfold GlobalShapeCandidate, wf_scc_state in Hshape.
          destruct Hshape as [Hstack_vis _].
          apply Hstack_vis. exact Hactive_x_pre. }
        assert (Hdfn_x_keep:
                  dfn sp x =
                  dfn s0 x).
        { apply Hdfn_sp_keep. exact Hx_neq_child. }
        assert (Hdfn_parent_x_pre:
                  dfn s0 (frame_parent F) <= dfn s0 x).
        { rewrite Hdfn_parent_keep in Hdfn_parent_x_post.
          rewrite Hdfn_x_keep in Hdfn_parent_x_post.
          exact Hdfn_parent_x_post. }
        assert (Houtside_pre:
                  ~ PendingChildSegmentCandidate (frame_child F) s0 x).
        { intro Hpending_pre.
          apply Houtside_post.
          exact (Hpending_pre_to_post x Hpending_pre). }
        specialize (Hcoverage x Hactive_x_pre Hdfn_parent_x_pre
                      Houtside_pre) as Hprocessed.
        eapply ProcessedTreeReachableFromCandidate_snapshot_to_post_monotone.
        * exact Hvisited_sp_mono.
        * intros z _Hvisited_z. apply Hfa_sp_keep.
        * exact Hdone_vis.
        * exact Hprocessed.
  Qed.

  Lemma PreloopPreservesLocalActiveRootCandidate_proof:
    forall u child,
      Hoare
        (fun s => LocalActiveRootCandidate u s /\ Unvisited child s)
        (preloop child)
        (fun _ s => LocalActiveRootCandidate u s).
  Proof.
    intros u child.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s => GlobalShapeCandidate s)
        (Q2 := fun _ s =>
           SettledClosedCandidate s /\
           Visited u s /\
           Active u s /\
           OrderFactsCandidate s).
      - eapply Hoare_conseq_pre.
        2: { apply (PreloopGlobalShapeCandidate_proof child). }
        intros s [Hlocal Hunvis_child].
        unfold GlobalShapePreCandidate.
        split.
        + exact (proj1 Hlocal).
        + exact Hunvis_child.
      - apply Hoare_conj with
          (Q1 := fun _ s => SettledClosedCandidate s)
          (Q2 := fun _ s =>
             Visited u s /\ Active u s /\ OrderFactsCandidate s).
        + eapply Hoare_conseq_pre.
          2: { apply (PreloopSettledClosedCandidate_proof child). }
          intros s [Hlocal _Hunvis_child].
          exact (proj1 (proj2 Hlocal)).
        + apply Hoare_conj with
            (Q1 := fun _ s => Visited u s)
            (Q2 := fun _ s => Active u s /\ OrderFactsCandidate s).
          * eapply Hoare_conseq_pre.
            2: { apply (preloop_keep_visited child u). }
            intros s [Hlocal _Hunvis_child].
            exact (proj1 (proj2 (proj2 Hlocal))).
          * apply Hoare_conj with
              (Q1 := fun _ s => Active u s)
              (Q2 := fun _ s => OrderFactsCandidate s).
            -- eapply Hoare_conseq_pre.
               2: { apply (preloop_keep_stack_elements child u). }
               intros s [Hlocal _Hunvis_child].
               exact (proj1 (proj2 (proj2 (proj2 Hlocal)))).
            -- eapply Hoare_conseq_pre.
               2: { apply (PreloopOrderFactsCandidate_proof child). }
               intros s [Hlocal Hunvis_child].
               split.
               ++ exact (proj2 (proj2 (proj2 (proj2 Hlocal)))).
               ++ unfold GlobalShapePreCandidate.
                  split; [exact (proj1 Hlocal) | exact Hunvis_child].
    }
    intros _ s [Hshape [Hsettled [Hvis [Hactive Horder]]]].
    unfold LocalActiveRootCandidate.
    split; [exact Hshape |].
    split; [exact Hsettled |].
    split; [exact Hvis |].
    split; [exact Hactive | exact Horder].
  Qed.

  Lemma PreloopPreservesDoneDisciplineCandidate_proof:
    forall u done child,
      Hoare
        (fun s => DoneDisciplineCandidate u done s)
        (preloop child)
        (fun _ s => DoneDisciplineCandidate u done s).
  Proof.
    unfold DoneDisciplineCandidate,
      DoneVisitedCandidate.
    intros u done child.
    apply Hoare_conj.
    - unfold preloop. unfold_op. intro_state. hoare_auto_s.
    - eapply Hoare_conseq_pre.
      2: {
        apply
          (@preloop_keep_visited_forall
             V E equiv0 H0 g OriginalGraph_gvalid0 child done).
      }
      intros s [_Hsubset Hdone_vis].
      exact Hdone_vis.
  Qed.

  Lemma PreloopPreservesPartialRootLowEquationCandidate_proof:
    forall u done child,
      Hoare
        (fun s =>
           PartialRootLowEquationCandidate u done s /\
           DoneVisitedCandidate done s /\
           Visited u s /\
           Unvisited child s)
        (preloop child)
        (fun _ s => PartialRootLowEquationCandidate u done s).
  Proof.
    intros u done child.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s.
    set (sp :=
           RecordSet.set visited (fun vs => vs ∪ [child])
             (RecordSet.set stack (fun stk => child :: stk)
                (RecordSet.set timer S
                   (RecordSet.set low
                      (fun low0 x =>
                         if equiv_decb x child then timer s0 else low0 x)
                      (RecordSet.set dfn
                         (fun dfn0 x =>
                            if equiv_decb x child then timer s0 else dfn0 x)
                         s0))))).
    change (PartialRootLowEquationCandidate u done sp).
    destruct H as [Hpartial [Hdone_vis [Hvis_u Hunvis_child]]].
    destruct Hpartial as [Hfront Hsrc].
    assert (Hu_neq_child: u <> child).
    { intro Hu_child. apply Hunvis_child. rewrite <- Hu_child. exact Hvis_u. }
    assert (Hdone_neq_child:
              forall a, done a -> a <> child).
    { intros a Hdone_a Ha_child. apply Hunvis_child.
      rewrite <- Ha_child. apply Hdone_vis. exact Hdone_a. }
    assert (Hactive_sp_cases:
              forall a, Active a sp -> a = child \/ Active a s0).
    { intros a Hactive_a. subst sp. unfold Active in *.
      simpl in Hactive_a. destruct Hactive_a as [Ha | Ha].
      - left. symmetry. exact Ha.
      - right. exact Ha. }
    assert (Hactive_sp_old:
              forall a, Active a s0 -> Active a sp).
    { intros a Hactive_a. subst sp. unfold Active in *. simpl.
      right. exact Hactive_a. }
    assert (Hlow_keep:
              forall a, a <> child -> low sp a = low s0 a).
    { intros a Ha_neq. subst sp. simpl. unfold equiv_decb.
      destruct (equiv_dec a child) as [Ha_child | _].
      - exfalso. apply Ha_neq. exact Ha_child.
      - reflexivity. }
    assert (Hdfn_keep:
              forall a, a <> child -> dfn sp a = dfn s0 a).
    { intros a Ha_neq. subst sp. simpl. unfold equiv_decb.
      destruct (equiv_dec a child) as [Ha_child | _].
      - exfalso. apply Ha_neq. exact Ha_child.
      - reflexivity. }
    assert (Hfa_keep:
              forall a, fa sp a = fa s0 a).
    { intro a. subst sp. reflexivity. }
    assert (Hlow_u_keep: low sp u = low s0 u).
    { apply Hlow_keep. exact Hu_neq_child. }
    assert (Hdfn_u_keep: dfn sp u = dfn s0 u).
    { apply Hdfn_keep. exact Hu_neq_child. }
    split.
    - unfold LowFrontierCandidate in Hfront |- *.
      destruct Hfront as [Hself Hfront].
      split.
      + rewrite Hlow_u_keep. rewrite Hdfn_u_keep. exact Hself.
      + intros a Hdone_a Hedge_a.
        assert (Ha_neq_child: a <> child).
        { apply Hdone_neq_child. exact Hdone_a. }
        assert (Hlow_a_keep: low sp a = low s0 a).
        { apply Hlow_keep. exact Ha_neq_child. }
        assert (Hdfn_a_keep: dfn sp a = dfn s0 a).
        { apply Hdfn_keep. exact Ha_neq_child. }
        specialize (Hfront a Hdone_a Hedge_a) as [Htree Hstack].
        split.
        * intro Hfa_a.
          rewrite Hlow_u_keep. rewrite Hlow_a_keep.
          apply Htree.
          rewrite <- Hfa_keep. exact Hfa_a.
        * intro Hactive_a_post.
          destruct (Hactive_sp_cases a Hactive_a_post) as
            [Ha_child | Hactive_a_pre].
          -- exfalso. apply Ha_neq_child. exact Ha_child.
          -- rewrite Hlow_u_keep. rewrite Hdfn_a_keep.
             apply Hstack. exact Hactive_a_pre.
    - unfold LowSourceCandidate in Hsrc |- *.
      destruct Hsrc as [Hself | [Htree | Hstack]].
      + left. rewrite Hlow_u_keep. rewrite Hdfn_u_keep. exact Hself.
      + right. left.
        destruct Htree as
          [a [Hdone_a [Hedge_a [Hfa_a [Hfa_neq_a Hlow_a]]]]].
        assert (Ha_neq_child: a <> child).
        { apply Hdone_neq_child. exact Hdone_a. }
        exists a.
        split; [exact Hdone_a |].
        split; [exact Hedge_a |].
        split.
        * rewrite Hfa_keep. exact Hfa_a.
        * split.
          -- intro Hfa_sp_a.
             apply Hfa_neq_a.
             rewrite <- Hfa_keep. exact Hfa_sp_a.
          -- rewrite Hlow_u_keep.
             rewrite Hlow_keep; [exact Hlow_a | exact Ha_neq_child].
      + right. right.
        destruct Hstack as
          [a [Hdone_a [Hedge_a [Hactive_a [Hfa_neq_a Hlow_a]]]]].
        assert (Ha_neq_child: a <> child).
        { apply Hdone_neq_child. exact Hdone_a. }
        exists a.
        split; [exact Hdone_a |].
        split; [exact Hedge_a |].
        split.
        * apply Hactive_sp_old. exact Hactive_a.
        * split.
          -- intro Hfa_sp_a.
             apply Hfa_neq_a.
             rewrite <- Hfa_keep. exact Hfa_sp_a.
          -- rewrite Hlow_u_keep.
             rewrite Hdfn_keep; [exact Hlow_a | exact Ha_neq_child].
  Qed.

  Lemma PreloopPreservesLoopInvLowCandidate_proof:
    forall u done child,
      Hoare
        (fun s => LoopInvLowCandidate u done s /\ Unvisited child s)
        (preloop child)
        (fun _ s => LoopInvLowCandidate u done s).
  Proof.
    intros u done child.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s => LoopInvDoneCandidate u done s)
        (Q2 := fun _ s => PartialRootLowEquationCandidate u done s).
      - apply Hoare_conj with
          (Q1 := fun _ s => LocalActiveRootCandidate u s)
          (Q2 := fun _ s => DoneDisciplineCandidate u done s).
        + eapply Hoare_conseq_pre.
          2: { apply (PreloopPreservesLocalActiveRootCandidate_proof u child). }
          intros s [Hlow Hunvis_child].
          unfold LoopInvLowCandidate, LoopInvDoneCandidate in Hlow.
          split; [exact (proj1 (proj1 Hlow)) | exact Hunvis_child].
        + eapply Hoare_conseq_pre.
          2: { apply (PreloopPreservesDoneDisciplineCandidate_proof u done child). }
          intros s [Hlow _Hunvis_child].
          unfold LoopInvLowCandidate, LoopInvDoneCandidate in Hlow.
          exact (proj2 (proj1 Hlow)).
      - eapply Hoare_conseq_pre.
        2: {
          apply
            (PreloopPreservesPartialRootLowEquationCandidate_proof
               u done child).
        }
        intros s [Hlow Hunvis_child].
        unfold LoopInvLowCandidate, LoopInvDoneCandidate,
          LocalActiveRootCandidate, DoneDisciplineCandidate in Hlow.
        destruct Hlow as [[Hlocal [_Hdone_subset Hdone_vis]] Hpartial].
        destruct Hlocal as [_Hshape [_Hsettled [Hvis_u _Hactive_order]]].
        split; [exact Hpartial |].
        split; [exact Hdone_vis |].
        split; [exact Hvis_u | exact Hunvis_child].
    }
    intros _ s [Hdone_loop Hpartial].
    unfold LoopInvLowCandidate.
    split; [exact Hdone_loop | exact Hpartial].
  Qed.

  Lemma PreloopPreservesFrameLoopInvLowCandidate_proof:
    forall F parent child done,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           LoopInvLowCandidate (frame_parent F) (frame_done F) s).
  Proof.
    intros F parent child done.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (PreloopPreservesLoopInvLowCandidate_proof
           (frame_parent F) (frame_done F) child).
    }
    intros s [Hframe Hentry].
    split.
    - eapply FrameInvProvidesLoopInvLowCandidate_proof.
      exact Hframe.
    - unfold ChildEntryCandidate,
        ParentLoopSuspendedBaseCandidate,
        PendingChildShapeCandidate,
        GlobalShapePreCandidate in Hentry.
      destruct Hentry as [_Hparent_base [Hglobal_pre _Hpending_tail]].
      exact (proj2 Hglobal_pre).
  Qed.

  Lemma PreloopPreservesFrameActiveProcessedChildSegmentSummaryCandidate_proof:
    forall F parent child done,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           ActiveProcessedChildSegmentSummaryCandidate
             (frame_parent F) (frame_done F) s).
  Proof.
    intros F parent child done.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (PreloopPreservesActiveProcessedChildSegmentSummaryCandidate_proof
           (frame_parent F) (frame_done F) child).
    }
    intros s [Hframe Hentry].
    pose proof
      (FrameInvProvidesLoopInvLowCandidate_proof F s Hframe) as Hlow.
    unfold LoopInvLowCandidate, LoopInvDoneCandidate,
      LocalActiveRootCandidate, DoneDisciplineCandidate in Hlow.
    destruct Hlow as [[Hlocal [_Hdone_subset Hdone_vis]] _Hpartial].
    destruct Hlocal as [Hshape _Hlocal_tail].
    unfold ChildEntryCandidate,
      ParentLoopSuspendedBaseCandidate,
      PendingChildShapeCandidate,
      GlobalShapePreCandidate in Hentry.
    destruct Hentry as [_Hparent_base [Hglobal_pre _Hpending_tail]].
    split; [exact Hshape |].
    split; [exact Hdone_vis |].
    split; [exact (proj2 Hglobal_pre) |].
    eapply FrameInvProvidesActiveProcessedChildSegmentSummaryCandidate_proof.
    exact Hframe.
  Qed.

  Lemma PreloopPreservesDoneClosednessCandidate_proof:
    forall u done child,
      Hoare
        (fun s =>
           DoneClosednessCandidate u done s /\
           DoneVisitedCandidate done s /\
           Unvisited child s)
        (preloop child)
        (fun _ s => DoneClosednessCandidate u done s).
  Proof.
    intros u done child.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s.
    set (sp :=
           RecordSet.set visited (fun vs => vs ∪ [child])
             (RecordSet.set stack (fun stk => child :: stk)
                (RecordSet.set timer S
                   (RecordSet.set low
                      (fun low0 x =>
                         if equiv_decb x child then timer s0 else low0 x)
                      (RecordSet.set dfn
                         (fun dfn0 x =>
                            if equiv_decb x child then timer s0 else dfn0 x)
                         s0))))).
    change (DoneClosednessCandidate u done sp).
    destruct H as [[Hdone_closed Htree_closed] [Hdone_vis Hunvis_child]].
    assert (Hvisited_sp_mono:
              forall z, Visited z s0 -> Visited z sp).
    { intros z Hvis_z. subst sp. unfold Visited. simpl.
      sets_unfold. left. exact Hvis_z. }
    assert (Hactive_sp_old:
              forall z, Active z s0 -> Active z sp).
    { intros z Hactive_z. subst sp. unfold Active in *. simpl.
      right. exact Hactive_z. }
    assert (Hfa_keep:
              forall z, fa sp z = fa s0 z).
    { intro z. subst sp. reflexivity. }
    unfold DoneClosednessCandidate,
      done_reachable_closed,
      done_tree_reachable_closed.
    split.
    - intros v w Hdone_v Hnot_active_post Hreach_vw.
      apply Hvisited_sp_mono.
      eapply Hdone_closed; eauto.
      intro Hactive_pre.
      apply Hnot_active_post.
      apply Hactive_sp_old. exact Hactive_pre.
    - intros v w Hdone_v Hnot_active_post Hfa_post_v
             Hfa_post_neq Htree_vw.
      apply Hvisited_sp_mono.
      apply (Htree_closed v w Hdone_v).
      + intro Hactive_pre.
        apply Hnot_active_post.
        apply Hactive_sp_old. exact Hactive_pre.
      + rewrite <- Hfa_keep. exact Hfa_post_v.
      + intro Hfa_pre_v.
        apply Hfa_post_neq.
        rewrite Hfa_keep. exact Hfa_pre_v.
      + exact Htree_vw.
  Qed.

  Lemma PreloopPreservesFrameDoneClosednessCandidate_proof:
    forall F parent child done,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           ChildEntryCandidate parent child done s)
        (preloop child)
        (fun _ s =>
           DoneClosednessCandidate (frame_parent F) (frame_done F) s).
  Proof.
    intros F parent child done.
    eapply Hoare_conseq_pre.
    2: {
      apply
        (PreloopPreservesDoneClosednessCandidate_proof
           (frame_parent F) (frame_done F) child).
    }
    intros s [Hframe Hentry].
    pose proof
      (FrameInvProvidesLoopInvLowCandidate_proof F s Hframe) as Hlow.
    unfold LoopInvLowCandidate, LoopInvDoneCandidate,
      LocalActiveRootCandidate, DoneDisciplineCandidate in Hlow.
    destruct Hlow as [[_Hlocal [_Hdone_subset Hdone_vis]] _Hpartial].
    split.
    - eapply FrameInvProvidesDoneClosednessCandidate_proof.
      exact Hframe.
    - split; [exact Hdone_vis |].
      unfold ChildEntryCandidate,
        ParentLoopSuspendedBaseCandidate,
        PendingChildShapeCandidate,
        GlobalShapePreCandidate in Hentry.
      destruct Hentry as [_Hparent_base [Hglobal_pre _Hpending_tail]].
      exact (proj2 Hglobal_pre).
  Qed.

  Lemma BodyFrameAfterPreloopCandidate_from_processed_cut_proof:
    PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement ->
    BodyFrameAfterPreloopCandidate_statement.
  Proof.
    unfold
      PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement,
      BodyFrameAfterPreloopCandidate_statement.
    intros Hprocessed F parent child done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s =>
             FrameInvCandidate F s)
          (Q2 := fun _ s =>
             LoopInvPhase7Candidate child ∅ s /\
             PendingChildSegmentCandidate (frame_child F) s child /\
             dfn s (frame_parent F) < dfn s child /\
             forall v,
               frame_done F v ->
               dfn s v < dfn s child).
      - eapply Hoare_conseq_post.
        2: {
          apply Hoare_conj
            with
              (Q1 := fun _ s =>
                 ParentResumeShapeCandidate
                   (frame_parent F) (frame_child F) (frame_done F) s /\
                 Visited (frame_child F) s /\
                 SuspendedParentFrameResumeCandidate
                   (frame_parent F) (frame_child F) (frame_done F) s)
              (Q2 := fun _ s =>
                 LoopInvLowCandidate
                   (frame_parent F) (frame_done F) s /\
                 DoneClosednessCandidate
                   (frame_parent F) (frame_done F) s /\
                 ProcessedTreeChildrenCorrectCandidate
                   (frame_parent F) (frame_done F) s /\
                 ActiveProcessedChildSegmentSummaryCandidate
                   (frame_parent F) (frame_done F) s /\
                 SuspendedSegmentEscapeAccountingCandidate
                   (frame_parent F) (frame_child F) (frame_done F) s /\
                 SuspendedSegmentTreeCoverageByDoneCandidate
                   (frame_parent F) (frame_child F) (frame_done F) s).
          - eapply Hoare_conseq_post.
            2: {
              apply
                (PreloopProducesFrameBodyPrefixFactsCandidate_proof
                   F parent child done Hedge Hnot_done).
            }
            intros _ s [Hresume [Hvis_child [Hsuspended _Holder]]].
            split; [exact Hresume |].
            split; [exact Hvis_child | exact Hsuspended].
          - apply Hoare_conj
              with
                (Q1 := fun _ s =>
                   LoopInvLowCandidate
                     (frame_parent F) (frame_done F) s)
                (Q2 := fun _ s =>
                   DoneClosednessCandidate
                     (frame_parent F) (frame_done F) s /\
                   ProcessedTreeChildrenCorrectCandidate
                     (frame_parent F) (frame_done F) s /\
                   ActiveProcessedChildSegmentSummaryCandidate
                     (frame_parent F) (frame_done F) s /\
                   SuspendedSegmentEscapeAccountingCandidate
                     (frame_parent F) (frame_child F) (frame_done F) s /\
                   SuspendedSegmentTreeCoverageByDoneCandidate
                     (frame_parent F) (frame_child F) (frame_done F) s).
            + eapply Hoare_conseq_pre.
              2: {
                apply
                  (PreloopPreservesFrameLoopInvLowCandidate_proof
                     F parent child done).
              }
              intros s [Hframe [_Hcompat Hentry]].
              split; [exact Hframe | exact Hentry].
            + apply Hoare_conj
                with
                  (Q1 := fun _ s =>
                     DoneClosednessCandidate
                       (frame_parent F) (frame_done F) s)
                  (Q2 := fun _ s =>
                     ProcessedTreeChildrenCorrectCandidate
                       (frame_parent F) (frame_done F) s /\
                     ActiveProcessedChildSegmentSummaryCandidate
                       (frame_parent F) (frame_done F) s /\
                     SuspendedSegmentEscapeAccountingCandidate
                       (frame_parent F) (frame_child F) (frame_done F) s /\
                     SuspendedSegmentTreeCoverageByDoneCandidate
                       (frame_parent F) (frame_child F) (frame_done F) s).
              * eapply Hoare_conseq_pre.
                2: {
                  apply
                    (PreloopPreservesFrameDoneClosednessCandidate_proof
                       F parent child done).
                }
                intros s [Hframe [_Hcompat Hentry]].
                split; [exact Hframe | exact Hentry].
              * apply Hoare_conj
                  with
                    (Q1 := fun _ s =>
                       ProcessedTreeChildrenCorrectCandidate
                         (frame_parent F) (frame_done F) s)
                    (Q2 := fun _ s =>
                       ActiveProcessedChildSegmentSummaryCandidate
                         (frame_parent F) (frame_done F) s /\
                       SuspendedSegmentEscapeAccountingCandidate
                         (frame_parent F) (frame_child F) (frame_done F) s /\
                       SuspendedSegmentTreeCoverageByDoneCandidate
                         (frame_parent F) (frame_child F) (frame_done F) s).
                -- apply (Hprocessed F parent child done).
                -- apply Hoare_conj
                    with
                      (Q1 := fun _ s =>
                         ActiveProcessedChildSegmentSummaryCandidate
                           (frame_parent F) (frame_done F) s)
                      (Q2 := fun _ s =>
                         SuspendedSegmentEscapeAccountingCandidate
                           (frame_parent F) (frame_child F) (frame_done F) s /\
                         SuspendedSegmentTreeCoverageByDoneCandidate
                           (frame_parent F) (frame_child F) (frame_done F) s).
                   ++ eapply Hoare_conseq_pre.
                      2: {
                        apply
                          (PreloopPreservesFrameActiveProcessedChildSegmentSummaryCandidate_proof
                             F parent child done).
                      }
                      intros s [Hframe [_Hcompat Hentry]].
                      split; [exact Hframe | exact Hentry].
                   ++ apply
                        (PreloopPreservesFrameSuspendedSegmentFieldsFromCompatibilityCandidate_proof
                           F parent child done).
        }
        intros _ s
          [[Hresume [_Hvis_child Hsuspended]]
           [Hlow [Hclosed [Hchildren
            [Hactive_segments [Hsegment Hcoverage]]]]]].
        unfold FrameInvCandidate.
        split; [exact Hresume |].
        split; [exact Hlow |].
        split; [exact Hsuspended |].
        split; [exact Hclosed |].
        split; [exact Hchildren |].
        split; [exact Hactive_segments |].
        split; [exact Hsegment | exact Hcoverage].
      - apply Hoare_conj
          with
            (Q1 := fun _ s => LoopInvPhase7Candidate child ∅ s)
            (Q2 := fun _ s =>
               PendingChildSegmentCandidate (frame_child F) s child /\
               dfn s (frame_parent F) < dfn s child /\
               forall v,
                 frame_done F v ->
                 dfn s v < dfn s child).
        + eapply Hoare_conseq_pre.
          2: { apply PreloopFromChildEntryProducesLoopInvPhase7InitialCandidate_proof. }
          intros s [_Hframe [_Hcompat Hentry]].
          exact Hentry.
        + apply Hoare_conj
            with
              (Q1 := fun _ s =>
                 PendingChildSegmentCandidate (frame_child F) s child)
              (Q2 := fun _ s =>
                 dfn s (frame_parent F) < dfn s child /\
                 forall v,
                   frame_done F v ->
                   dfn s v < dfn s child).
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (PreloopProducesPendingChildSegmentFromFrameCompatibilityCandidate_proof
                   F parent child done).
            }
            intros s [_Hframe [Hcompat Hentry]].
            split; [exact Hcompat | exact Hentry].
          * eapply Hoare_conseq_pre.
            2: {
              apply
                (PreloopMakesFrameVerticesOlderThanChildCandidate_proof
                   F parent child done).
            }
            intros s [Hframe [_Hcompat Hentry]].
            split; [exact Hframe | exact Hentry].
    }
    intros _ s [Hframe [Hloop [Hpending [Hparent_older Hdone_older]]]].
    split; [exact Hframe |].
    split; [exact Hloop |].
    split; [exact Hpending |].
    split; [exact Hparent_older | exact Hdone_older].
  Qed.

  Lemma MaybePopPreservesFrameInvFromLoopDoneOlderVerticesCandidate_proof:
    forall F u,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           LoopDonePhase7Candidate u s /\
           dfn s (frame_parent F) < dfn s u /\
           (forall v,
               frame_done F v ->
               Active v s ->
               dfn s v < dfn s u) /\
           PoppedSegmentClosedCandidate u s)
        (maybe_pop u)
        (fun _ s => FrameInvCandidate F s).
  Proof.
    intros F u.
    eapply Hoare_conseq_pre.
    2: { apply MaybePopPreservesFrameInvWithBoundaryCandidate_proof. }
    intros s
      [Hframe [Hloop_done [Hparent_older [Hdone_older Hsegment_closed]]]].
    split; [exact Hframe |].
    split.
    - unfold LoopDonePhase7Candidate,
        LoopInvPhase7Candidate,
        LoopInvPhase6Candidate,
        LoopInvLowCandidate,
        LoopInvDoneCandidate,
        LocalActiveRootCandidate in Hloop_done.
      destruct Hloop_done as [Hphase6 _Hphase7_tail].
      destruct Hphase6 as [Hlow _Hphase6_tail].
      destruct Hlow as [Hdone_loop _Hpartial].
      destruct Hdone_loop as [Hlocal _Hdone_disc].
      destruct Hlocal as [_Hshape [_Hsettled [_Hvis [Hactive _Horder]]]].
      exact Hactive.
    - split.
      + eapply FramePopBoundaryCandidate_from_loop_done_older_vertices_proof;
          eauto.
      + exact Hsegment_closed.
  Qed.

  Lemma BodyMaybePopPreservesFrameInvFromLoopDoneOlderVerticesCandidate_proof:
    forall F u,
      Hoare
        (fun s =>
           FrameInvCandidate F s /\
           LoopDonePhase7Candidate u s /\
           dfn s (frame_parent F) < dfn s u /\
           (forall v,
               frame_done F v ->
               Active v s ->
               dfn s v < dfn s u))
        (maybe_pop u)
        (fun _ s => FrameInvCandidate F s).
  Proof.
    intros F u.
    unfold maybe_pop, If.
    apply Hoare_choice.
    - apply Hoare_assume_bind.
      unfold Hoare.
      intros s1 ret s2 [Hguard Hpre] Hrun.
      pose proof
        (MaybePopPreservesFrameInvFromLoopDoneOlderVerticesCandidate_proof
           F u) as Hstrong.
      unfold Hoare in Hstrong.
      eapply Hstrong.
      + destruct Hpre as
          [Hframe [Hloop_done [Hparent_older Hdone_older]]].
        split; [exact Hframe |].
        split; [exact Hloop_done |].
        split; [exact Hparent_older |].
        split; [exact Hdone_older |].
        apply SegmentClosedAtRootCandidate_proof.
        unfold SegmentClosedAtRootInputCandidate.
        split; [exact Hloop_done | exact Hguard].
      + unfold maybe_pop, If, choice.
        sets_unfold. left.
        unfold bind, StateRelMonad.bind.
        exists tt, s1.
        split.
        * unfold test. split; [exact Hguard | reflexivity].
        * exact Hrun.
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume. }
      intros _ s [Hpre _Hnot_guard].
      exact (proj1 Hpre).
  Qed.

  (* ================================================================ *)
  (* Phase-7c pop-bridge consumer audit proofs                        *)
  (* ================================================================ *)

  Lemma RootFinalFromPrePopCandidate_proof:
    RootFinalFromPrePopCandidate_statement.
  Proof.
    unfold RootFinalFromPrePopCandidate_statement,
      RootFinalFromPrePopCandidate,
      RootFinalCandidate,
      RootFinalCorrectCandidate,
      RootFinalLowValidCandidate,
      RootFinalIsLowCandidate,
      RootLowPrePopCandidate,
      RootLowValidPrePopCandidate,
      RootIsLowPrePopCandidate.
    intros u s [Hshape [Hsettled [Hvis [[Hlow_valid H_is_low] Horder]]]].
    split; [exact Hshape |].
    split; [exact Hsettled |].
    split; [exact Hvis |].
    split; [split; [exact Hlow_valid | exact H_is_low] | exact Horder].
  Qed.

  Lemma LoopDonePhase6ProvidesFinalFromPrePopCandidate_proof:
    forall u s,
      LoopDonePhase6Candidate u s ->
      RootLowPrePopCandidate u s ->
      RootFinalFromPrePopCandidate u s.
  Proof.
    unfold LoopDonePhase6Candidate,
      LoopInvPhase6Candidate,
      LoopInvLowCandidate,
      LoopInvDoneCandidate,
      LocalActiveRootCandidate,
      RootFinalFromPrePopCandidate.
    intros u s Hloop Hprepop.
    destruct Hloop as [Hlow _].
    destruct Hlow as [Hdone_loop _].
    destruct Hdone_loop as [Hlocal _].
    destruct Hlocal as [Hshape [Hsettled [Hvis [_ Horder]]]].
    split; [exact Hshape |].
    split; [exact Hsettled |].
    split; [exact Hvis |].
    split; [exact Hprepop | exact Horder].
  Qed.

  Lemma SkipBranchProducesRootFinalCandidate_proof:
    SkipBranchProducesRootFinalCandidate_statement.
  Proof.
    unfold SkipBranchProducesRootFinalCandidate_statement,
      SkipBranchInputCandidate,
      LoopDonePhase7Candidate,
      LoopInvPhase7Candidate.
    intros u s [[Hloop _Hsegment] [Hprepop _]].
    apply RootFinalFromPrePopCandidate_proof.
    eapply LoopDonePhase6ProvidesFinalFromPrePopCandidate_proof; eauto.
  Qed.

  Lemma RootPopLowValidStableFieldsCandidate_proof:
    RootPopLowValidStableFieldsCandidate_statement.
  Proof.
    unfold RootPopLowValidStableFieldsCandidate_statement,
      RootFinalLowValidStableFieldsCandidate,
      RootFinalLowValidCandidate,
      RootLowValidPrePopCandidate.
    intros u.
    eapply Hoare_conseq_post.
    2: {
      eapply Hoare_conseq_pre.
      2: {
        apply (@pop_scc_preserves_low_valid_post_when_root
                 V E equiv0 H0 g root u).
      }
      intros s [Hloop7 [Hlow_valid Hguard]].
      split.
      - apply RootBridgeLowValidInputBuildsLowIterationDoneCandidate_proof.
        apply RootBridgeInputProvidesLowValidInputCandidate_proof.
        apply LoopDoneProvidesRootBridgeInputCandidate_proof.
        unfold LoopDonePhase7Candidate,
          LoopInvPhase7Candidate in Hloop7.
        unfold LoopDonePhase6Candidate.
        exact (proj1 Hloop7).
      - split; [exact Hlow_valid | exact Hguard].
    }
    intros _ s [[Hshape Hlow_valid] [Hvis [Horder Hinj]]].
    split; [exact Hshape |].
    split; [exact Hvis |].
    split; [exact Hlow_valid |].
    split; [exact Horder | exact Hinj].
  Qed.

  Lemma RootPopSettledClosedCandidate_proof:
    RootPopSettledClosedCandidate_statement.
  Proof.
    unfold RootPopSettledClosedCandidate_statement,
      LoopDonePhase7Candidate,
      LoopInvPhase7Candidate,
      LoopInvPhase6Candidate,
      LoopInvLowCandidate,
      LoopInvDoneCandidate,
      LocalActiveRootCandidate,
      PoppedSegmentClosedCandidate,
      SettledClosedCandidate,
      Active.
    intros u.
    unfold pop_scc. intro_state. hoare_auto_s.
    subst s. unfold pop_scc_state.
    destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
    simpl.
    destruct H as [Hpre Hsegment_closed].
    destruct Hpre as [Hloop7 _Hsegment_account].
    destruct Hloop7 as [Hlow _Hphase6_tail].
    destruct Hlow as [Hdone_loop _Hpartial].
    destruct Hdone_loop as [Hlocal _Hdone_disc].
    destruct Hlocal as
      [Hshape [Hsettled [Hvis_u [Hu_stack [Horder Hinj]]]]].
    unfold settled_closed in Hsettled |- *.
    intros x w Hvis_x Hx_not_rest Hreach_xw.
    destruct (classic (In x (stack s0))) as [Hx_stack | Hx_not_stack].
    - eapply Hsegment_closed; eauto.
      eapply stack_split_removed_vertex_dfn_ge_root; eauto.
    - eapply Hsettled; eauto.
  Qed.

  Lemma RootPopIsLowCandidate_proof:
    RootPopIsLowCandidate_statement.
  Proof.
    unfold RootPopIsLowCandidate_statement,
      RootPopIsLowInputCandidate,
      RootFinalIsLowCandidate,
      RootIsLowPrePopCandidate,
      Active,
      root_pop_guard.
    intros u.
    unfold pop_scc. intro_state. hoare_auto_s.
    subst s.
    destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
    destruct H as [Hu_stack [Hpre_is_low Hguard]].
    assert (Hpost_tree_subset:
              forall x,
                scc_low_tree g root (pop_scc_state s0 u) u x ->
                scc_low_tree g root s0 u x).
    { intros x Hx.
      unfold pop_scc_state in Hx. rewrite Hsplit in Hx. simpl in Hx.
      unfold scc_low_tree, scc_low_reachable in Hx |- *.
      destruct Hx as [z [Hreach_post Hcase]].
      exists z. split.
      - unfold state_to_dfs_tree in Hreach_post |- *.
        simpl in Hreach_post |- *.
        exact Hreach_post.
      - destruct Hcase as [Hz_eq | Hback_post].
        + left. exact Hz_eq.
        + destruct Hback_post as [Hedge [Hstack_post Hnot_tree_post]].
          right.
          unfold scc_back_edge in *.
          split; [exact Hedge |].
          split.
          * eapply stack_split_rest_in_original_stack; eauto.
          * intros Htree_pre.
            apply Hnot_tree_post.
            unfold state_to_dfs_tree in Htree_pre |- *.
            simpl in Htree_pre |- *.
            exact Htree_pre. }
    unfold scc_is_low_v, scc_is_low_v_val,
      min_value_of_subset, min_object_of_subset in *.
    exists u.
    split.
    - split.
      + unfold scc_low_tree, scc_low_reachable.
        unfold pop_scc_state. rewrite Hsplit. simpl.
        exists u. split.
        * apply Coq.Relations.Relation_Operators.rt_refl.
        * left. reflexivity.
      + intros x Hx.
        specialize (Hpost_tree_subset x Hx) as Hx_pre.
        pose proof (scc_low_bound g root s0 u (low s0 u) x
                      Hpre_is_low Hx_pre) as Hbound.
        rewrite Hguard in Hbound.
        unfold pop_scc_state. rewrite Hsplit. simpl.
        exact Hbound.
    - unfold pop_scc_state. rewrite Hsplit. simpl.
      symmetry. exact Hguard.
  Qed.

  Lemma RootPopBridgeCandidate_from_parts_proof:
    RootPopLowValidStableFieldsCandidate_statement ->
    RootPopSettledClosedCandidate_statement ->
    RootPopIsLowCandidate_statement ->
    RootPopBridgeCandidate_statement.
  Proof.
    unfold RootPopLowValidStableFieldsCandidate_statement,
      RootPopSettledClosedCandidate_statement,
      RootPopIsLowCandidate_statement,
      RootPopBridgeCandidate_statement,
      RootFinalLowValidStableFieldsCandidate,
      RootFinalCandidate,
      RootFinalCorrectCandidate.
    intros Hlow_valid_bridge Hsettled_bridge His_low_bridge u.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s => GlobalShapeCandidate s /\
                          Visited u s /\
                          RootFinalLowValidCandidate u s /\
                          OrderFactsCandidate s)
        (Q2 := fun _ s => SettledClosedCandidate s /\
                          RootFinalIsLowCandidate u s).
      - eapply Hoare_conseq_pre.
        2: { apply Hlow_valid_bridge. }
        intros s [Hloop7 [Hprepop [Hguard _Hclosed]]].
        unfold RootLowPrePopCandidate in Hprepop.
        destruct Hprepop as [Hlow_valid_pre _His_low_pre].
        split; [exact Hloop7 |].
        split; [exact Hlow_valid_pre | exact Hguard].
      - apply Hoare_conj with
          (Q1 := fun _ s => SettledClosedCandidate s)
          (Q2 := fun _ s => RootFinalIsLowCandidate u s).
        + eapply Hoare_conseq_pre.
          2: { apply Hsettled_bridge. }
          intros s [Hloop7 [_Hprepop [_Hguard Hclosed]]].
          split; [exact Hloop7 | exact Hclosed].
        + eapply Hoare_conseq_pre.
          2: { apply His_low_bridge. }
          intros s [Hloop7 [Hprepop [Hguard _Hclosed]]].
          unfold RootLowPrePopCandidate in Hprepop.
          destruct Hprepop as [_Hlow_valid His_low_pre].
          unfold RootPopIsLowInputCandidate.
          split.
          * unfold LoopDonePhase7Candidate, LoopInvPhase7Candidate,
              LoopInvPhase6Candidate, LoopInvLowCandidate,
              LoopInvDoneCandidate, LocalActiveRootCandidate in Hloop7.
            destruct Hloop7 as [Hphase6 _Hsegment].
            destruct Hphase6 as [Hlow _Hphase6_tail].
            destruct Hlow as [Hdone_loop _Hpartial].
            destruct Hdone_loop as [Hlocal _Hdone_disc].
            destruct Hlocal as
              [_Hshape [_Hsettled [_Hvis_u [Hu_stack _Horder]]]].
            exact Hu_stack.
          * split; [exact His_low_pre | exact Hguard].
    }
    intros _ s [[Hshape [Hvis [Hlow_valid Horder]]] [Hsettled His_low]].
    split; [exact Hshape |].
    split; [exact Hsettled |].
    split; [exact Hvis |].
    split; [split; [exact Hlow_valid | exact His_low] | exact Horder].
  Qed.

  Lemma RootPopBridgeCandidate_proof:
    RootPopBridgeCandidate_statement.
  Proof.
    apply RootPopBridgeCandidate_from_parts_proof.
    - apply RootPopLowValidStableFieldsCandidate_proof.
    - apply RootPopSettledClosedCandidate_proof.
    - apply RootPopIsLowCandidate_proof.
  Qed.

  Lemma PopBranchProvidesSegmentClosedAtRootCandidate_proof:
    forall u s,
      PopBranchInputCandidate u s ->
      PoppedSegmentClosedCandidate u s.
  Proof.
    unfold PopBranchInputCandidate.
    intros u s [Hloop7 [_Hprepop Hguard]].
    apply SegmentClosedAtRootCandidate_proof.
    unfold SegmentClosedAtRootInputCandidate.
    split; [exact Hloop7 | exact Hguard].
  Qed.

  Lemma PopBranchProducesRootFinalCandidate_from_root_pop_bridge_proof:
    RootPopBridgeCandidate_statement ->
    PopBranchProducesRootFinalCandidate_statement.
  Proof.
    unfold RootPopBridgeCandidate_statement,
      PopBranchProducesRootFinalCandidate_statement,
      PopBranchInputCandidate.
    intros Hbridge u.
    eapply Hoare_conseq_pre.
    2: { apply Hbridge. }
    intros s [Hloop7 [Hprepop Hguard]].
    split; [exact Hloop7 |].
    split; [exact Hprepop |].
    split; [exact Hguard |].
    eapply PopBranchProvidesSegmentClosedAtRootCandidate_proof.
    unfold PopBranchInputCandidate.
    split; [exact Hloop7 | split; [exact Hprepop | exact Hguard]].
  Qed.

  Lemma PopBranchProducesRootFinalCandidate_proof:
    PopBranchProducesRootFinalCandidate_statement.
  Proof.
    apply PopBranchProducesRootFinalCandidate_from_root_pop_bridge_proof.
    apply RootPopBridgeCandidate_proof.
  Qed.

  Lemma MaybePopFinalCandidate_from_branches_proof:
    PopBranchProducesRootFinalCandidate_statement ->
    MaybePopFinalCandidate_statement.
  Proof.
    unfold PopBranchProducesRootFinalCandidate_statement,
      MaybePopFinalCandidate_statement,
      PopBranchInputCandidate,
      SkipBranchInputCandidate,
      maybe_pop, If.
    intros Hpop u.
    apply Hoare_choice.
    - apply Hoare_assume_bind.
      apply Hoare_conseq_pre
        with (P2 := PopBranchInputCandidate u).
      { intros s [Hguard [Hloop7 Hprepop]].
        split; [exact Hloop7 | split; [exact Hprepop | exact Hguard]]. }
      apply Hpop.
    - eapply Hoare_conseq_post.
      2: { apply Hoare_assume. }
      intros _ s [[Hloop7 Hprepop] Hnot_guard].
      apply SkipBranchProducesRootFinalCandidate_proof.
      split; [exact Hloop7 | split; [exact Hprepop | exact Hnot_guard]].
  Qed.

  Lemma MaybePopFinalCandidate_proof:
    MaybePopFinalCandidate_statement.
  Proof.
    apply MaybePopFinalCandidate_from_branches_proof.
    apply PopBranchProducesRootFinalCandidate_proof.
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
      Auxiliary recursive contract consumed by the tree-branch low update.
      Unlike [ChildPost], this contract depends on parent low-equation
      material present before the recursive call.
     *)
    LowContributionPre : V -> V -> (V -> Prop) -> St -> Prop;
    LowContributionPost : V -> V -> (V -> Prop) -> St -> Prop;

    (*
      Suspended outer parent frame.  This is the Hoare-logic counterpart of a
      continuation: an inner recursive call must preserve enough outer state
      for the parent loop to resume.
    *)
    Frame : Type;
    FrameInv : Frame -> St -> Prop;
    FrameCompatible : Frame -> V -> V -> St -> Prop;
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

  Definition LowContributionContract
             (I: LowProofInterface) (W: RecProgram): Prop :=
    forall parent child done,
      dg_step g parent child ->
      ~ done child ->
      Hoare
        (LowContributionPre I parent child done)
        (W child)
        (fun _ s => LowContributionPost I parent child done s).

  Definition FrameContract (I: LowProofInterface) (W: RecProgram): Prop :=
    forall (F: Frame I) direct_parent child direct_done,
      dg_step g direct_parent child ->
      ~ direct_done child ->
      Hoare
        (fun s =>
           FrameInv I F s /\
           FrameCompatible I F direct_parent child s /\
           ChildEntry I direct_parent child direct_done s)
        (W child)
        (fun _ s => FrameInv I F s).

  Definition LowCandidateInterface: LowProofInterface :=
    {|
      EntryPre := EntryPreCandidate;
      RootFinal := RootFinalCandidate;
      RootLowPrePop := RootLowPrePopCandidate;
      LoopInv := LoopInvPhase7Candidate;
      ChildEntry := ChildEntryCandidate;
      ChildPost := ChildPostCandidate;
      LowContributionPre :=
        fun parent child done s =>
          FrameInvCandidate (FrameOfCallCandidate parent child done) s /\
          ChildEntryCandidate parent child done s /\
          PartialRootLowEquationCandidate parent done s;
      LowContributionPost :=
        fun parent child done s =>
          PartialRootLowEquationCandidate parent done s /\
          fa s child = parent /\
          fa s child <> child /\
          low s child <= dfn s child;
      Frame := SuspendedFrameCandidate;
      FrameInv := FrameInvCandidate;
      FrameCompatible := FrameCompatibleWithCallCandidate;
    |}.

  Definition ChildContractCandidate_to_interface_statement: Prop :=
    forall W,
      ChildContractCandidate W ->
      ChildContract LowCandidateInterface W.

  Definition LowContributionCandidate_to_interface_statement: Prop :=
    forall W,
      FramedChildProvidesLowContributionCandidate W ->
      LowContributionContract LowCandidateInterface W.

  Definition FrameContractCandidate_to_interface_statement: Prop :=
    forall W,
      FrameContractCandidate W ->
      FrameContract LowCandidateInterface W.

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
      LowContributionContract I W ->
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
      LowContributionContract I W ->
      FrameContract I W ->
      Hoare
        (LoopEntry I u)
        (edge_loop u W)
        (fun _ s => LoopDone I u s).

  Definition LoopInvProper_statement (I: LowProofInterface): Prop :=
    forall u,
      Proper (Sets.equiv ==> eq ==> iff) (LoopInv I u).

  Definition EdgeLoopDone_from_process_edge_step_statement
             (I: LowProofInterface): Prop :=
    LoopInvProper_statement I ->
    ProcessEdgeStep_statement I ->
    EdgeLoopDone_statement I.

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

  Definition RootBridgeCandidate_to_interface_statement: Prop :=
    RootBridge_statement LowCandidateInterface.

  Definition MaybePopFinalCandidate_to_interface_statement: Prop :=
    MaybePopFinal_statement LowCandidateInterface.

  Definition PreloopEntryCandidate_to_interface_statement: Prop :=
    PreloopEntry_statement LowCandidateInterface.

  Definition ProcessEdgeStepCandidate_statement: Prop :=
    forall W u a done,
      RecursiveCallContractsCandidate W ->
      Edge u a ->
      ~ done a ->
      Hoare
        (LoopInvPhase7Candidate u done)
        (process_edge u W a)
        (fun _ s => LoopInvPhase7Candidate u (done_after done a) s).

  Definition ProcessEdgeStepCandidate_to_interface_statement: Prop :=
    ProcessEdgeStepCandidate_statement ->
    ProcessEdgeStep_statement LowCandidateInterface.

  Definition EdgeLoopDoneCandidate_from_process_edge_step_statement: Prop :=
    ProcessEdgeStep_statement LowCandidateInterface ->
    EdgeLoopDone_statement LowCandidateInterface.

  Lemma ProcessEdgeStepCandidate_proof:
    ProcessEdgeStepCandidate_statement.
  Proof.
    unfold ProcessEdgeStepCandidate_statement.
    intros W u a done Hcontracts Hedge Hnot_done.
    unfold Hoare.
    intros s1 r s2 Hloop7 Hrun.
    destruct (classic (Unvisited a s1)) as [Hunvis | Hnot_unvis].
    - pose proof
        (ProcessEdgeUnvisitedExtendsLoopInvPhase7Candidate_proof
           W u a done Hcontracts Hedge Hnot_done) as Hunvis_step.
      unfold Hoare in Hunvis_step.
      eapply Hunvis_step; [| exact Hrun].
      split; [exact Hloop7 | exact Hunvis].
    - assert (Hvis: Visited a s1).
      { unfold Unvisited in Hnot_unvis.
        unfold Visited. apply NNPP. exact Hnot_unvis. }
      destruct (classic (Active a s1)) as [Hactive | Hnot_active].
      + pose proof
          (ProcessEdgeVisitedActiveExtendsLoopInvPhase7WithBlockTargetCandidate_proof
             W u a done Hedge Hnot_done) as Hactive_step.
        unfold Hoare in Hactive_step.
        eapply Hactive_step; [| exact Hrun].
        pose proof Hloop7 as Hloop7_fields.
        destruct Hloop7_fields as [_Hphase6 [_Hsegment [_Hcoverage Hblocks]]].
        split; [exact Hloop7 |].
        split; [exact Hblocks |].
        split; [exact Hvis | exact Hactive].
      + pose proof
          (ProcessEdgeVisitedNonStackExtendsLoopInvPhase7Candidate_proof
             W u a done Hedge Hnot_done) as Hnonstack_step.
        unfold Hoare in Hnonstack_step.
        eapply Hnonstack_step; [| exact Hrun].
        split; [exact Hloop7 |].
        split; [exact Hvis | exact Hnot_active].
  Qed.

  (* ================================================================ *)
  (* Recursive-body theorem statements                                *)
  (* ================================================================ *)

  Definition BodySatisfiesChildContract_statement
             (I: LowProofInterface): Prop :=
    forall W,
      ChildContract I W ->
      LowContributionContract I W ->
      FrameContract I W ->
      ChildContract I (tarjan_scc_f g W).

  Definition BodyProvidesLowContributionContract_statement
             (I: LowProofInterface): Prop :=
    forall W,
      ChildContract I W ->
      LowContributionContract I W ->
      FrameContract I W ->
      LowContributionContract I (tarjan_scc_f g W).

  Definition BodyPreservesFrameContract_statement
             (I: LowProofInterface): Prop :=
    forall W,
      ChildContract I W ->
      LowContributionContract I W ->
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
    obligation_body_provides_low_contribution_contract :
      BodyProvidesLowContributionContract_statement I;
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
  | LowContributionMode (parent: V) (done: V -> Prop)
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
    | LowContributionMode _ parent done =>
        LowContributionPre I parent x done s /\
        dg_step g parent x /\
        ~ done x
    | LowFrameMode _ outer direct_parent direct_done =>
        FrameInv I outer s /\
        FrameCompatible I outer direct_parent x s /\
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
    | LowContributionMode _ parent done =>
        LowContributionPost I parent x done s
    | LowFrameMode _ outer _ _ =>
        FrameInv I outer s
    end.

  Definition FixIHProvidesChildContract_statement: Prop :=
    forall I W,
      (forall x mode,
          Hoare (FixPre I x mode) (W x) (FixPost I x mode)) ->
      ChildContract I W.

  Definition FixIHProvidesLowContributionContract_statement: Prop :=
    forall I W,
      (forall x mode,
          Hoare (FixPre I x mode) (W x) (FixPost I x mode)) ->
      LowContributionContract I W.

  Definition FixIHProvidesFrameContract_statement: Prop :=
    forall I W,
      (forall x mode,
          Hoare (FixPre I x mode) (W x) (FixPost I x mode)) ->
      FrameContract I W.

  Definition FixpointModeStep_statement (I: LowProofInterface): Prop :=
    LowProofObligations I ->
    forall W,
      (forall x mode,
          Hoare (FixPre I x mode) (W x) (FixPost I x mode)) ->
      forall x mode,
        Hoare
          (FixPre I x mode)
          (tarjan_scc_f g W x)
          (FixPost I x mode).

  Lemma ChildContractCandidate_to_interface_proof:
    ChildContractCandidate_to_interface_statement.
  Proof.
    unfold ChildContractCandidate_to_interface_statement,
      ChildContractCandidate,
      ChildContract,
      LowCandidateInterface.
    intros W Hchild parent child done Hedge Hnot_done.
    exact (Hchild parent child done Hedge Hnot_done).
  Qed.

  Lemma LowContributionCandidate_to_interface_proof:
    LowContributionCandidate_to_interface_statement.
  Proof.
    unfold LowContributionCandidate_to_interface_statement,
      FramedChildProvidesLowContributionCandidate,
      LowContributionContract,
      LowCandidateInterface.
    intros W Hlow parent child done Hedge Hnot_done.
    exact (Hlow parent child done Hedge Hnot_done).
  Qed.

  Lemma FrameContractCandidate_to_interface_proof:
    FrameContractCandidate_to_interface_statement.
  Proof.
    unfold FrameContractCandidate_to_interface_statement,
      FrameContractCandidate,
      FrameContract,
      LowCandidateInterface.
    intros W Hframe F parent child done Hedge Hnot_done.
    exact (Hframe F parent child done Hedge Hnot_done).
  Qed.

  Lemma RootBridgeCandidate_to_interface_proof:
    RootBridgeCandidate_to_interface_statement.
  Proof.
    unfold RootBridgeCandidate_to_interface_statement,
      RootBridge_statement,
      LoopDone,
      LowCandidateInterface.
    intros u s Hloop7.
    apply
      (RootBridgePrePopCandidate_proof
         RootBridgeLowValidCandidate_proof
         RootBridgeIsLowCandidate_proof).
    apply LoopDoneProvidesRootBridgeInputCandidate_proof.
    unfold LoopDonePhase7Candidate,
      LoopInvPhase7Candidate in Hloop7.
    exact (proj1 Hloop7).
  Qed.

  Lemma MaybePopFinalCandidate_to_interface_proof:
    MaybePopFinalCandidate_to_interface_statement.
  Proof.
    unfold MaybePopFinalCandidate_to_interface_statement,
      MaybePopFinal_statement,
      PrePopRootReady,
      LoopDone,
      LowCandidateInterface.
    exact MaybePopFinalCandidate_proof.
  Qed.

  Lemma PreloopEntryCandidate_to_interface_proof:
    PreloopEntryCandidate_to_interface_statement.
  Proof.
    unfold PreloopEntryCandidate_to_interface_statement,
      PreloopEntry_statement,
      LoopEntry,
      LowCandidateInterface.
    apply PreloopProducesLoopInvPhase7InitialCandidate_proof.
  Qed.

  Lemma ProcessEdgeStepCandidate_to_interface_proof:
    ProcessEdgeStepCandidate_to_interface_statement.
  Proof.
    unfold ProcessEdgeStepCandidate_to_interface_statement,
      ProcessEdgeStepCandidate_statement,
      ProcessEdgeStep_statement,
      RecursiveCallContractsCandidate,
      ChildContractCandidate,
      FramedChildProvidesLowContributionCandidate,
      FrameContractCandidate,
      ChildContract,
      LowContributionContract,
      FrameContract,
      LowCandidateInterface,
      Edge.
    intros Hstep W u a done Hchild Hlow Hframe Hedge Hnot_done.
    apply Hstep; try assumption.
    split; [exact Hchild | split; [exact Hlow | exact Hframe]].
  Qed.

  Lemma EdgeLoopDone_from_process_edge_step_proof:
    forall I,
      EdgeLoopDone_from_process_edge_step_statement I.
  Proof.
    unfold EdgeLoopDone_from_process_edge_step_statement,
      LoopInvProper_statement,
      ProcessEdgeStep_statement,
      EdgeLoopDone_statement,
      LoopEntry,
      LoopDone,
      edge_loop.
    intros I Hproper Hstep W u Hchild Hlow Hframe.
    eapply Hoare_forset
      with (P := fun done s => LoopInv I u done s).
    - apply Hproper.
    - intros done a _Hsubset Hedge Hnot_done.
      apply Hstep; assumption.
  Qed.

  Lemma LoopInvPhase7Candidate_done_proper_proof:
    forall u,
      Proper (Sets.equiv ==> eq ==> iff) (LoopInvPhase7Candidate u).
  Proof.
    unfold Proper, respectful.
    intros u done1 done2 Hdone s1 s2 Hstate.
    subst s2.
    sets_unfold in Hdone.
    unfold LoopInvPhase7Candidate,
      LoopInvPhase6Candidate,
      LoopInvLowCandidate,
      LoopInvDoneCandidate,
      DoneDisciplineCandidate,
      DoneSubsetOfOutgoingCandidate,
      DoneVisitedCandidate,
      PartialRootLowEquationCandidate,
      LowFrontierCandidate,
      LowSourceCandidate,
      ParentFrameResumeCandidate,
      DoneClosednessCandidate,
      ProcessedTreeChildrenCorrectCandidate,
      ProcessedTreeChildrenLowValidCandidate,
      ProcessedTreeChildrenIsLowCandidate,
      ProcessedTreeChildrenInactiveSelfLowCandidate,
      ActiveProcessedChildSegmentSummaryCandidate,
      SegmentEscapeAccountingCandidate,
      SegmentTreeCoverageByDoneCandidate,
      ActiveTargetBlocksEscapeAccountedCandidate,
      ActiveTargetBlockEscapeAccountedCandidate,
      ProcessedTreeReachableFromCandidate,
      ParentLowBelowChildCandidate,
      PendingRootEscapeCandidate,
      done_visited,
      done_reachable_closed,
      done_tree_reachable_closed,
      low_frontier,
      low_src,
      fa_not_done_implies_eq_u.
    assert
      (Htransport:
         forall src dst,
           (forall x, src x -> dst x) ->
           (forall x, dst x -> src x) ->
           LoopInvPhase7Candidate u src s1 ->
           LoopInvPhase7Candidate u dst s1).
    {
      intros src dst Hsrc_dst Hdst_src Hloop.
      assert (Hnot_src_dst: forall x, ~ src x -> ~ dst x).
      { intros x Hnot_src Hdst. apply Hnot_src. apply Hdst_src. exact Hdst. }
      assert (Hnot_dst_src: forall x, ~ dst x -> ~ src x).
      { intros x Hnot_dst Hsrc. apply Hnot_dst. apply Hsrc_dst. exact Hsrc. }
      unfold LoopInvPhase7Candidate,
        LoopInvPhase6Candidate,
        LoopInvLowCandidate,
        LoopInvDoneCandidate,
        DoneDisciplineCandidate,
        DoneSubsetOfOutgoingCandidate,
        DoneVisitedCandidate,
        PartialRootLowEquationCandidate,
        LowFrontierCandidate,
        LowSourceCandidate,
        ParentFrameResumeCandidate,
        DoneClosednessCandidate,
        ProcessedTreeChildrenCorrectCandidate,
        ProcessedTreeChildrenLowValidCandidate,
        ProcessedTreeChildrenIsLowCandidate,
        ProcessedTreeChildrenInactiveSelfLowCandidate,
        ActiveProcessedChildSegmentSummaryCandidate,
        SegmentEscapeAccountingCandidate,
        SegmentTreeCoverageByDoneCandidate,
        ActiveTargetBlocksEscapeAccountedCandidate,
        ActiveTargetBlockEscapeAccountedCandidate,
        ProcessedTreeReachableFromCandidate,
        PendingRootEscapeCandidate,
        done_visited,
        done_reachable_closed,
        done_tree_reachable_closed,
        fa_not_done_implies_eq_u
        in Hloop |- *.
      destruct Hloop as [Hphase6 [Hsegment [Hcoverage Hblocks]]].
      destruct Hphase6 as
        [Hlow [Hframe [Hclosed [Hchildren Hactive_segments]]]].
      destruct Hlow as [Hdone_loop [Hfront Hsource]].
      destruct Hdone_loop as [Hlocal [Hsubset Hdone_vis]].
      destruct Hframe as [Hframe_done_vis [Hfa_child Hfa_not_done]].
      destruct Hclosed as [Hdone_closed Htree_closed].
      destruct Hchildren as
        [Hchildren_valid [Hchildren_is_low Hchildren_inactive]].
      split.
      - split.
        + split.
          * split.
            { exact Hlocal. }
            { split.
              - intros a Hdst_a.
                apply Hsubset. apply Hdst_src. exact Hdst_a.
              - intros a Hdst_a.
                apply Hdone_vis. apply Hdst_src. exact Hdst_a. }
          * split.
            { split.
              - exact (proj1 Hfront).
              - intros a Hdst_a Hedge_a.
                apply Hfront; [apply Hdst_src; exact Hdst_a | exact Hedge_a]. }
            { destruct Hsource as [Hself | [Htree_source | Hstack_source]].
              - left. exact Hself.
              - destruct Htree_source as
                  [a [Hsrc_a [Hedge_a [Hfa_a [Hfa_neq_a Hlow_a]]]]].
                right. left. exists a.
                repeat split; try assumption.
                apply Hsrc_dst. exact Hsrc_a.
              - destruct Hstack_source as
                  [a [Hsrc_a [Hedge_a [Hactive_a [Hfa_neq_a Hlow_a]]]]].
                right. right. exists a.
                repeat split; try assumption.
                apply Hsrc_dst. exact Hsrc_a. }
        + split.
          * split.
            { intros a Hdst_a.
              apply Hframe_done_vis. apply Hdst_src. exact Hdst_a. }
            { split.
              - exact Hfa_child.
              - intros a Hnot_dst_a Hfa_a.
                apply Hfa_not_done; [apply Hnot_dst_src; exact Hnot_dst_a |].
                exact Hfa_a. }
          * split.
            { split.
              - intros a w Hdst_a Hnot_active Hreach.
                apply (Hdone_closed a w).
                + apply Hdst_src. exact Hdst_a.
                + exact Hnot_active.
                + exact Hreach.
              - intros a w Hdst_a Hnot_active Hfa_a Hfa_neq_a Hreach.
                apply (Htree_closed a w).
                + apply Hdst_src. exact Hdst_a.
                + exact Hnot_active.
                + exact Hfa_a.
                + exact Hfa_neq_a.
                + exact Hreach. }
            { split.
              - split.
                + intros child Hdst_child.
                  apply Hchildren_valid. apply Hdst_src. exact Hdst_child.
                + split.
                  * intros child Hdst_child.
                    apply Hchildren_is_low. apply Hdst_src. exact Hdst_child.
                  * intros child Hdst_child.
                    apply Hchildren_inactive.
                    apply Hdst_src. exact Hdst_child.
              - intros child Hdst_child.
                apply Hactive_segments. apply Hdst_src. exact Hdst_child. }
      - split.
        + intros x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w.
          specialize
            (Hsegment x w Hactive_x Hdfn_x Hreach_xw Hnot_vis_w)
            as [Hpending | Hanchor].
          * left.
            destruct Hpending as
              [a [Hx_a [Hedge_a [Hnot_src_a Hreach_aw]]]].
            exists a.
            split; [exact Hx_a |].
            split; [exact Hedge_a |].
            split; [| exact Hreach_aw].
            apply Hnot_src_dst. exact Hnot_src_a.
          * right. exact Hanchor.
        + split.
          * intros x Hactive_x Hdfn_x.
            specialize (Hcoverage x Hactive_x Hdfn_x) as
              [Hx_u | [a [Hsrc_a [Hedge_a
                [Hfa_a [Hfa_neq_a [Htree_ax Hreach_ax]]]]]]].
            -- left. exact Hx_u.
            -- right. exists a.
               split.
               { apply Hsrc_dst. exact Hsrc_a. }
               split; [exact Hedge_a |].
               split; [exact Hfa_a |].
               split; [exact Hfa_neq_a |].
               split; [exact Htree_ax | exact Hreach_ax].
          * intros block target w Hblock_target Hblock_valid Hreach Hnot_vis.
            specialize (Hblocks block target w Hblock_target) as Haccount.
            assert (Hblock_valid_src:
                      forall b,
                        block b ->
                        Edge u b /\ ~ src b /\ Active b s1 /\
                        dfn s1 u <= dfn s1 b).
            { intros b Hb.
              specialize (Hblock_valid b Hb) as
                [Hedge_b [Hnot_dst_b [Hactive_b Hdfn_b]]].
              split; [exact Hedge_b |].
              split.
              - apply Hnot_dst_src. exact Hnot_dst_b.
              - split; [exact Hactive_b | exact Hdfn_b]. }
            specialize (Haccount Hblock_valid_src Hreach Hnot_vis)
              as [Hpending | Hanchor].
            -- left.
               destruct Hpending as
                 [next [Htarget_u [Hedge_next [Hnot_src_block Hnext_w]]]].
               exists next.
               split; [exact Htarget_u |].
               split; [exact Hedge_next |].
               split.
               ++ intros Hdst_block.
                  apply Hnot_src_block.
                  sets_unfold in Hdst_block. sets_unfold.
                  destruct Hdst_block as [Hdst_next | Hblock_next].
                  ** left. apply Hdst_src. exact Hdst_next.
                  ** right. exact Hblock_next.
               ++ exact Hnext_w.
            -- right. exact Hanchor.
    }
    split; intro H.
    - apply (Htransport done1 done2); [apply Hdone | intros x; apply Hdone |].
      exact H.
    - apply (Htransport done2 done1); [intros x; apply Hdone | apply Hdone |].
      exact H.
  Qed.

  Lemma EdgeLoopDoneCandidate_from_process_edge_step_proof:
    EdgeLoopDoneCandidate_from_process_edge_step_statement.
  Proof.
    unfold EdgeLoopDoneCandidate_from_process_edge_step_statement.
    intro Hstep.
    apply EdgeLoopDone_from_process_edge_step_proof.
    - unfold LoopInvProper_statement, LowCandidateInterface.
      apply LoopInvPhase7Candidate_done_proper_proof.
    - exact Hstep.
  Qed.

  Lemma EdgeLoopPreservesFrameProgressCandidate_proof:
    forall W F child,
      RecursiveCallContractsCandidate W ->
      FrameProgressContractCandidate W ->
      Hoare
        (fun s =>
           LoopInvPhase7Candidate child ∅ s /\
           FrameProgressCandidate F child s)
        (edge_loop child W)
        (fun _ s =>
           LoopDonePhase7Candidate child s /\
           FrameProgressCandidate F child s).
  Proof.
    intros W F child Hcontracts Hprogress_contract.
    unfold edge_loop.
    eapply Hoare_conseq_post.
    2: {
      eapply Hoare_forset
        with
          (P := fun done s =>
             LoopInvPhase7Candidate child done s /\
             FrameProgressCandidate F child s).
      - unfold Proper, respectful.
        intros done1 done2 Hdone s1 s2 Hstate.
        subst s2.
        pose proof
          (LoopInvPhase7Candidate_done_proper_proof child)
          as Hproper_loop.
        unfold Proper, respectful in Hproper_loop.
        specialize (Hproper_loop done1 done2 Hdone s1 s1 eq_refl)
          as Hloop_iff.
        split.
        + intros [Hloop Hprogress].
          split.
          * apply Hloop_iff. exact Hloop.
          * exact Hprogress.
        + intros [Hloop Hprogress].
          split.
          * apply Hloop_iff. exact Hloop.
          * exact Hprogress.
      - intros done a _Hsubset Hedge Hnot_done.
        apply Hoare_conj
          with
            (Q1 := fun _ s =>
               LoopInvPhase7Candidate child (done_after done a) s)
            (Q2 := fun _ s => FrameProgressCandidate F child s).
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (ProcessEdgeStepCandidate_proof
                 W child a done Hcontracts Hedge Hnot_done).
          }
          intros s [Hloop _Hprogress]. exact Hloop.
        + eapply Hoare_conseq_pre.
          2: {
            apply
              (ProcessEdgePreservesFrameProgressCandidate_proof
                 W F child done a Hprogress_contract Hedge Hnot_done).
          }
          intros s [Hloop Hprogress].
          split; [exact Hprogress | exact Hloop].
    }
    intros _ s [Hloop Hprogress].
    split; [exact Hloop | exact Hprogress].
  Qed.

  Lemma BodyFrameEdgeLoopPreservesCandidate_from_process_edge_cut_proof:
    ProcessEdgePreservesFrameAndOlderCandidate_statement ->
    BodyFrameEdgeLoopPreservesCandidate_statement.
  Proof.
    unfold ProcessEdgePreservesFrameAndOlderCandidate_statement,
      BodyFrameEdgeLoopPreservesCandidate_statement,
      edge_loop.
    intros Hstep W F child Hcontracts.
    eapply Hoare_conseq_post.
    2: {
      eapply Hoare_conseq_pre.
      2: {
        eapply Hoare_forset
          with
            (P := fun done s =>
               FrameInvCandidate F s /\
               LoopInvPhase7Candidate child done s /\
               FrameProgressCandidate F child s).
        - unfold Proper, respectful.
          intros done1 done2 Hdone s1 s2 Hstate.
          subst s2.
          pose proof
            (LoopInvPhase7Candidate_done_proper_proof child)
            as Hproper_loop.
          unfold Proper, respectful in Hproper_loop.
          specialize (Hproper_loop done1 done2 Hdone s1 s1 eq_refl)
            as Hloop_iff.
          split.
          + intros [Hframe [Hloop Hprogress]].
            split; [exact Hframe |].
            split.
            * apply Hloop_iff. exact Hloop.
            * exact Hprogress.
          + intros [Hframe [Hloop Hprogress]].
            split; [exact Hframe |].
            split.
            * apply Hloop_iff. exact Hloop.
            * exact Hprogress.
        - intros done a _Hsubset Hedge Hnot_done.
          apply (Hstep W F child done a Hcontracts Hedge Hnot_done).
      }
      intros s [Hframe [Hloop Hprogress]].
      split; [exact Hframe |].
      split; [exact Hloop |].
      exact Hprogress.
    }
    intros _ s [Hframe [Hloop_done Hprogress]].
    destruct Hprogress as [_Hpending [Hparent_older Hdone_older]].
    split; [exact Hframe |].
    split; [exact Hloop_done |].
    split; [exact Hparent_older | exact Hdone_older].
  Qed.

  Lemma ProcessEdgeStepCandidate_interface_proof:
    ProcessEdgeStep_statement LowCandidateInterface.
  Proof.
    apply ProcessEdgeStepCandidate_to_interface_proof.
    apply ProcessEdgeStepCandidate_proof.
  Qed.

  Lemma EdgeLoopDoneCandidate_proof:
    EdgeLoopDone_statement LowCandidateInterface.
  Proof.
    apply EdgeLoopDoneCandidate_from_process_edge_step_proof.
    apply ProcessEdgeStepCandidate_interface_proof.
  Qed.

  Lemma EdgeLoopDoneCandidate_direct_proof:
    forall W u,
      RecursiveCallContractsCandidate W ->
      Hoare
        (LoopInvPhase7Candidate u ∅)
        (edge_loop u W)
        (fun _ s => LoopDonePhase7Candidate u s).
  Proof.
    intros W u [Hchild [Hlow Hframe]].
    pose proof EdgeLoopDoneCandidate_proof as Hedge_loop.
    unfold EdgeLoopDone_statement, LoopEntry, LoopDone,
      LowCandidateInterface in Hedge_loop.
    simpl in Hedge_loop.
    apply Hedge_loop.
    - apply ChildContractCandidate_to_interface_proof. exact Hchild.
    - apply LowContributionCandidate_to_interface_proof. exact Hlow.
    - apply FrameContractCandidate_to_interface_proof. exact Hframe.
  Qed.

  Lemma BodyChildProducesRootFinalCandidate_proof:
    forall W parent child done,
      RecursiveCallContractsCandidate W ->
      Edge parent child ->
      ~ done child ->
      Hoare
        (ChildEntryCandidate parent child done)
        (tarjan_scc_f g W child)
        (fun _ s => RootFinalCandidate child s).
  Proof.
    intros W parent child done Hcontracts _Hedge _Hnot_done.
    unfold tarjan_scc_f.
    eapply Hoare_bind.
    - apply PreloopFromChildEntryProducesLoopInvPhase7InitialCandidate_proof.
    - simpl. intros _.
      eapply Hoare_bind.
      + apply EdgeLoopDoneCandidate_direct_proof.
        exact Hcontracts.
      + simpl. intros _.
        eapply Hoare_conseq_pre.
        2: { apply MaybePopFinalCandidate_proof. }
        intros s Hloop_done.
        split; [exact Hloop_done |].
        pose proof RootBridgeCandidate_to_interface_proof as Hroot_bridge.
        unfold RootBridge_statement, LoopDone, LowCandidateInterface
          in Hroot_bridge.
        simpl in Hroot_bridge.
        apply Hroot_bridge.
        exact Hloop_done.
  Qed.

  Lemma RootFinalProvidesChildPostCoreCandidate_proof:
    forall child s,
      RootFinalCandidate child s ->
      Visited child s /\
      ChildRootCorrectForParentCandidate child s /\
      ChildClosednessContributionCandidate child s.
  Proof.
    unfold RootFinalCandidate,
      ChildRootCorrectForParentCandidate,
      ChildLowValidForParentCandidate,
      ChildIsLowForParentCandidate,
      RootFinalCorrectCandidate,
      RootFinalLowValidCandidate,
      RootFinalIsLowCandidate,
      ChildClosednessContributionCandidate,
      SettledClosedCandidate.
    intros child s [_Hshape [Hsettled [Hvis [[Hlow His_low] _Horder]]]].
    split; [exact Hvis |].
    split; [split; [exact Hlow | exact His_low] |].
    intros Hnot_active v Hreach.
    eapply Hsettled; eauto.
  Qed.

  Lemma BodyChildProducesPostCoreCandidate_proof:
    forall W parent child done,
      RecursiveCallContractsCandidate W ->
      Edge parent child ->
      ~ done child ->
      Hoare
        (ChildEntryCandidate parent child done)
        (tarjan_scc_f g W child)
        (fun _ s =>
           Visited child s /\
           ChildRootCorrectForParentCandidate child s /\
           ChildClosednessContributionCandidate child s).
  Proof.
    intros W parent child done Hcontracts Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply
        (BodyChildProducesRootFinalCandidate_proof
           W parent child done Hcontracts Hedge Hnot_done).
    }
    intros ret s Hfinal.
    apply RootFinalProvidesChildPostCoreCandidate_proof.
    exact Hfinal.
  Qed.

  Lemma BodyChildProducesInactiveSelfLowCandidate_proof:
    forall W parent child done,
      RecursiveCallContractsCandidate W ->
      Edge parent child ->
      ~ done child ->
      Hoare
        (ChildEntryCandidate parent child done)
        (tarjan_scc_f g W child)
        (fun _ s => ChildInactiveSelfLowForParentCandidate child s).
  Proof.
    intros W parent child done Hcontracts _Hedge _Hnot_done.
    unfold tarjan_scc_f.
    eapply Hoare_bind.
    - apply PreloopFromChildEntryProducesLoopInvPhase7InitialCandidate_proof.
    - simpl. intros _.
      eapply Hoare_bind.
      + apply EdgeLoopDoneCandidate_direct_proof.
        exact Hcontracts.
      + simpl. intros _.
        eapply Hoare_conseq_pre.
        2: { apply MaybePopProducesChildInactiveSelfLowCandidate_proof. }
        intros s Hloop_done.
        unfold LoopDonePhase7Candidate,
          LoopInvPhase7Candidate,
          LoopInvPhase6Candidate,
          LoopInvLowCandidate,
          LoopInvDoneCandidate,
          LocalActiveRootCandidate in Hloop_done.
        destruct Hloop_done as [Hphase6 _Hphase7_tail].
        destruct Hphase6 as [Hlow _Hphase6_tail].
        destruct Hlow as [Hdone_loop _Hpartial].
        destruct Hdone_loop as [Hlocal _Hdone_disc].
        destruct Hlocal as [_Hshape [_Hsettled [_Hvis [Hactive _Horder]]]].
        exact Hactive.
  Qed.

  Lemma BodyProducesChildLowDfnBoundCandidate_proof:
    BodyProducesChildLowDfnBoundCandidate_statement.
  Proof.
    unfold BodyProducesChildLowDfnBoundCandidate_statement.
    intros W parent child done Hcontracts Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      eapply Hoare_conseq_pre.
      2: {
        apply
          (BodyChildProducesRootFinalCandidate_proof
             W parent child done Hcontracts Hedge Hnot_done).
      }
      intros s [_Hframe [Hentry _Hpartial]].
      exact Hentry.
    }
    intros ret s Hfinal.
    unfold RootFinalCandidate,
      RootFinalCorrectCandidate,
      RootFinalLowValidCandidate in Hfinal.
    destruct Hfinal as
      [_Hshape [_Hsettled [_Hvis [[Hlow_valid _His_low] _Horder]]]].
    apply (scc_low_valid_v_bound_self g root s child).
    exact Hlow_valid.
  Qed.

  Lemma BodySatisfiesChildContractCandidate_from_tail_cut_proof:
    BodyChildPostTailCandidate_statement ->
    BodySatisfiesChildContractCandidate_statement.
  Proof.
    unfold BodyChildPostTailCandidate_statement,
      BodySatisfiesChildContractCandidate_statement,
      ChildContractCandidate,
      ChildPostCandidate.
    intros Htail W Hcontracts parent child done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s =>
             Visited child s /\
             ChildRootCorrectForParentCandidate child s /\
             ChildClosednessContributionCandidate child s)
          (Q2 := fun _ s =>
             ChildInactiveSelfLowForParentCandidate child s /\
             (Active child s -> ChildSegmentSummaryCandidate child s) /\
             ParentResumeShapeCandidate parent child done s /\
             ParentPendingChildEscapeAccountedCandidate
               parent done child s /\
             ActiveTargetBlocksEscapeAccountedCandidate
               parent (done_after done child) s).
      - apply
          (BodyChildProducesPostCoreCandidate_proof
             W parent child done Hcontracts Hedge Hnot_done).
      - apply Hoare_conj
          with
            (Q1 := fun _ s =>
               ChildInactiveSelfLowForParentCandidate child s)
            (Q2 := fun _ s =>
               (Active child s -> ChildSegmentSummaryCandidate child s) /\
               ParentResumeShapeCandidate parent child done s /\
               ParentPendingChildEscapeAccountedCandidate
                 parent done child s /\
               ActiveTargetBlocksEscapeAccountedCandidate
                 parent (done_after done child) s).
        + apply
            (BodyChildProducesInactiveSelfLowCandidate_proof
               W parent child done Hcontracts Hedge Hnot_done).
        + apply (Htail W parent child done Hcontracts Hedge Hnot_done).
    }
    intros _ s
      [[Hvis [Hroot Hclosed]]
       [Hinactive [Hsegment [Hresume [Hpending Hblocks]]]]].
    destruct Hroot as [Hlow_valid His_low].
    split; [exact Hvis |].
    split; [exact Hlow_valid |].
    split; [exact His_low |].
    split; [exact Hinactive |].
    split; [exact Hclosed |].
    split; [exact Hsegment |].
    split; [exact Hresume |].
    split; [exact Hpending | exact Hblocks].
  Qed.

  Lemma BodyProvidesLowContributionCandidate_from_field_cuts_proof:
    BodyPreservesPartialRootLowEquationCandidate_statement ->
    BodyPreservesChildParentPointerCandidate_statement ->
    BodyProducesChildLowDfnBoundCandidate_statement ->
    BodyProvidesLowContributionCandidate_statement.
  Proof.
    unfold BodyPreservesPartialRootLowEquationCandidate_statement,
      BodyPreservesChildParentPointerCandidate_statement,
      BodyProducesChildLowDfnBoundCandidate_statement,
      BodyProvidesLowContributionCandidate_statement,
      FramedChildProvidesLowContributionCandidate.
    intros Hpartial Hparent_pointer Hlow_bound
           W Hcontracts parent child done Hedge Hnot_done.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj
        with
          (Q1 := fun _ s =>
             PartialRootLowEquationCandidate parent done s)
          (Q2 := fun _ s =>
             (fa s child = parent /\ fa s child <> child) /\
             low s child <= dfn s child).
      - apply
          (Hpartial W parent child done Hcontracts Hedge Hnot_done).
      - apply Hoare_conj.
        + apply
            (Hparent_pointer W parent child done
               Hcontracts Hedge Hnot_done).
        + apply
            (Hlow_bound W parent child done Hcontracts Hedge Hnot_done).
    }
    intros _ s [Hpartial_post [[Hfa Hfa_neq] Hlow_bound_post]].
    split; [exact Hpartial_post |].
    split; [exact Hfa |].
    split; [exact Hfa_neq | exact Hlow_bound_post].
  Qed.

  Lemma BodyPreservesFrameContractCandidate_from_frame_cuts_proof:
    BodyFrameAfterPreloopCandidate_statement ->
    BodyFrameEdgeLoopPreservesCandidate_statement ->
    BodyPreservesFrameContractCandidate_statement.
  Proof.
    unfold BodyFrameAfterPreloopCandidate_statement,
      BodyFrameEdgeLoopPreservesCandidate_statement,
      BodyPreservesFrameContractCandidate_statement,
      FrameContractCandidate.
    intros Hpreloop Hedge_loop W Hcontracts F parent child done
           Hedge Hnot_done.
    unfold tarjan_scc_f.
    eapply Hoare_bind.
    - apply (Hpreloop F parent child done Hedge Hnot_done).
    - simpl. intros _.
      eapply Hoare_bind.
      + unfold edge_loop.
        eapply Hoare_conseq_pre.
        2: {
          apply (Hedge_loop W F child Hcontracts).
        }
        intros s
          [Hframe [Hloop [Hpending [Hparent_older Hdone_older]]]].
        split; [exact Hframe |].
        split; [exact Hloop |].
        split; [exact Hpending |].
        split; [exact Hparent_older |].
        intros v Hdone_v _Hactive_v.
        apply Hdone_older. exact Hdone_v.
      + simpl. intros _.
        eapply Hoare_conseq_pre.
        2: {
          apply
            (BodyMaybePopPreservesFrameInvFromLoopDoneOlderVerticesCandidate_proof
               F child).
        }
        intros s [Hframe [Hloop_done [Hparent_older Hdone_older]]].
        split; [exact Hframe |].
        split; [exact Hloop_done |].
        split; [exact Hparent_older | exact Hdone_older].
  Qed.

  Lemma BodySatisfiesChildContractCandidate_from_phase9_cuts_proof:
    BodyChildPostTailCandidate_statement ->
    BodySatisfiesChildContractCandidate_statement.
  Proof.
    apply BodySatisfiesChildContractCandidate_from_tail_cut_proof.
  Qed.

  Lemma BodyProvidesLowContributionCandidate_from_phase9_cuts_proof:
    BodyPreservesPartialRootLowEquationCandidate_statement ->
    BodyPreservesChildParentPointerCandidate_statement ->
    BodyProvidesLowContributionCandidate_statement.
  Proof.
    intros Hpartial Hparent_pointer.
    apply BodyProvidesLowContributionCandidate_from_field_cuts_proof.
    - exact Hpartial.
    - exact Hparent_pointer.
    - exact BodyProducesChildLowDfnBoundCandidate_proof.
  Qed.

  Lemma BodyPreservesFrameContractCandidate_from_phase9_cuts_proof:
    PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement ->
    ProcessEdgePreservesFrameAndOlderCandidate_statement ->
    BodyPreservesFrameContractCandidate_statement.
  Proof.
    intros Hpreloop_processed Hprocess_edge.
    apply BodyPreservesFrameContractCandidate_from_frame_cuts_proof.
    - apply BodyFrameAfterPreloopCandidate_from_processed_cut_proof.
      exact Hpreloop_processed.
    - apply BodyFrameEdgeLoopPreservesCandidate_from_process_edge_cut_proof.
      exact Hprocess_edge.
  Qed.

  Lemma BodyPreservesPartialRootLowEquationCandidate_from_frame_cuts_proof:
    PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement ->
    ProcessEdgePreservesFrameAndOlderCandidate_statement ->
    BodyPreservesPartialRootLowEquationCandidate_statement.
  Proof.
    unfold BodyPreservesPartialRootLowEquationCandidate_statement.
    intros Hpreloop_processed Hprocess_edge
           W parent child done Hcontracts Hedge Hnot_done.
    pose proof
      (BodyPreservesFrameContractCandidate_from_phase9_cuts_proof
         Hpreloop_processed Hprocess_edge)
      as Hbody_frame.
    unfold BodyPreservesFrameContractCandidate_statement,
      FrameContractCandidate in Hbody_frame.
    eapply Hoare_conseq_post.
    2: {
      eapply Hoare_conseq_pre.
      2: {
        apply
          (Hbody_frame W Hcontracts
             (FrameOfCallCandidate parent child done)
             parent child done Hedge Hnot_done).
      }
      intros s [Hframe [Hentry _Hpartial]].
      split; [exact Hframe |].
      split.
      - apply FrameCompatibleWithOwnCallCandidate_proof.
      - exact Hentry.
    }
    intros ret s Hframe_post.
    pose proof
      (FrameInvProvidesLoopInvLowCandidate_proof
         (FrameOfCallCandidate parent child done) s Hframe_post)
      as Hlow.
    simpl in Hlow.
    exact (proj2 Hlow).
  Qed.

  Lemma BodyPreservesChildParentPointerCandidate_from_frame_cuts_proof:
    PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement ->
    ProcessEdgePreservesFrameAndOlderCandidate_statement ->
    BodyPreservesChildParentPointerCandidate_statement.
  Proof.
    unfold BodyPreservesChildParentPointerCandidate_statement.
    intros Hpreloop_processed Hprocess_edge
           W parent child done Hcontracts Hedge Hnot_done.
    pose proof
      (BodyPreservesFrameContractCandidate_from_phase9_cuts_proof
         Hpreloop_processed Hprocess_edge)
      as Hbody_frame.
    unfold BodyPreservesFrameContractCandidate_statement,
      FrameContractCandidate in Hbody_frame.
    eapply Hoare_conseq_post.
    2: {
      eapply Hoare_conseq_pre.
      2: {
        apply
          (Hbody_frame W Hcontracts
             (FrameOfCallCandidate parent child done)
             parent child done Hedge Hnot_done).
      }
      intros s [Hframe [Hentry _Hpartial]].
      split; [exact Hframe |].
      split.
      - apply FrameCompatibleWithOwnCallCandidate_proof.
      - exact Hentry.
    }
    intros ret s Hframe_post.
    pose proof
      (FrameInvProvidesParentResumeShapeCandidate_proof
         (FrameOfCallCandidate parent child done) s Hframe_post)
      as Hresume.
    simpl in Hresume.
    unfold ParentResumeShapeCandidate in Hresume.
    destruct Hresume as [_Hedge [_Hnot_done [Hfa Hfa_neq]]].
    split; [exact Hfa | exact Hfa_neq].
  Qed.

  Lemma BodySatisfiesChildContractCandidate_to_interface_proof:
    BodySatisfiesChildContractCandidate_statement ->
    BodySatisfiesChildContract_statement LowCandidateInterface.
  Proof.
    unfold BodySatisfiesChildContractCandidate_statement,
      BodySatisfiesChildContract_statement,
      RecursiveCallContractsCandidate,
      ChildContractCandidate,
      FramedChildProvidesLowContributionCandidate,
      FrameContractCandidate,
      ChildContract,
      LowContributionContract,
      FrameContract,
      LowCandidateInterface.
    intros Hbody W Hchild Hlow Hframe.
    apply Hbody.
    split; [exact Hchild | split; [exact Hlow | exact Hframe]].
  Qed.

  Lemma BodyProvidesLowContributionCandidate_to_interface_proof:
    BodyProvidesLowContributionCandidate_statement ->
    BodyProvidesLowContributionContract_statement LowCandidateInterface.
  Proof.
    unfold BodyProvidesLowContributionCandidate_statement,
      BodyProvidesLowContributionContract_statement,
      RecursiveCallContractsCandidate,
      ChildContractCandidate,
      FramedChildProvidesLowContributionCandidate,
      FrameContractCandidate,
      ChildContract,
      LowContributionContract,
      FrameContract,
      LowCandidateInterface.
    intros Hbody W Hchild Hlow Hframe.
    apply Hbody.
    split; [exact Hchild | split; [exact Hlow | exact Hframe]].
  Qed.

  Lemma BodyPreservesFrameContractCandidate_to_interface_proof:
    BodyPreservesFrameContractCandidate_statement ->
    BodyPreservesFrameContract_statement LowCandidateInterface.
  Proof.
    unfold BodyPreservesFrameContractCandidate_statement,
      BodyPreservesFrameContract_statement,
      RecursiveCallContractsCandidate,
      ChildContractCandidate,
      FramedChildProvidesLowContributionCandidate,
      FrameContractCandidate,
      ChildContract,
      LowContributionContract,
      FrameContract,
      LowCandidateInterface.
    intros Hbody W Hchild Hlow Hframe.
    apply Hbody.
    split; [exact Hchild | split; [exact Hlow | exact Hframe]].
  Qed.

  Lemma LowCandidateObligations_from_body_contracts_proof:
    BodySatisfiesChildContractCandidate_statement ->
    BodyProvidesLowContributionCandidate_statement ->
    BodyPreservesFrameContractCandidate_statement ->
    LowProofObligations LowCandidateInterface.
  Proof.
    intros Hbody_child Hbody_low Hbody_frame.
    refine
      {| obligation_preloop_entry :=
           PreloopEntryCandidate_to_interface_proof;
         obligation_process_edge_step :=
           ProcessEdgeStepCandidate_interface_proof;
         obligation_edge_loop_done :=
           EdgeLoopDoneCandidate_proof;
         obligation_root_bridge :=
           RootBridgeCandidate_to_interface_proof;
         obligation_maybe_pop_final :=
           MaybePopFinalCandidate_to_interface_proof;
         obligation_body_satisfies_child_contract :=
           BodySatisfiesChildContractCandidate_to_interface_proof
             Hbody_child;
         obligation_body_provides_low_contribution_contract :=
           BodyProvidesLowContributionCandidate_to_interface_proof
             Hbody_low;
         obligation_body_preserves_frame_contract :=
           BodyPreservesFrameContractCandidate_to_interface_proof
             Hbody_frame |}.
  Qed.

  Lemma LowCandidateObligations_from_phase9_cuts_proof:
    BodyChildPostTailCandidate_statement ->
    PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement ->
    ProcessEdgePreservesFrameAndOlderCandidate_statement ->
    LowProofObligations LowCandidateInterface.
  Proof.
    intros Hchild_tail Hpreloop_processed Hprocess_edge.
    apply LowCandidateObligations_from_body_contracts_proof.
    - apply BodySatisfiesChildContractCandidate_from_phase9_cuts_proof.
      exact Hchild_tail.
    - apply BodyProvidesLowContributionCandidate_from_phase9_cuts_proof.
      + apply
          BodyPreservesPartialRootLowEquationCandidate_from_frame_cuts_proof;
          assumption.
      + apply
          BodyPreservesChildParentPointerCandidate_from_frame_cuts_proof;
          assumption.
    - apply BodyPreservesFrameContractCandidate_from_phase9_cuts_proof;
        assumption.
  Qed.

  Lemma FixIHProvidesChildContract_proof:
    FixIHProvidesChildContract_statement.
  Proof.
    unfold FixIHProvidesChildContract_statement,
      ChildContract.
    intros I W HIH parent child done Hedge Hnot_done.
    eapply Hoare_conseq with
      (P2 := FixPre I child (LowChildMode I parent done))
      (Q2 := FixPost I child (LowChildMode I parent done)).
    - intros s Hentry.
      unfold FixPre; simpl.
      repeat split; assumption.
    - intros r s Hpost.
      unfold FixPost in Hpost; simpl in Hpost.
      exact Hpost.
    - apply (HIH child (LowChildMode I parent done)).
  Qed.

  Lemma FixIHProvidesLowContributionContract_proof:
    FixIHProvidesLowContributionContract_statement.
  Proof.
    unfold FixIHProvidesLowContributionContract_statement,
      LowContributionContract.
    intros I W HIH parent child done Hedge Hnot_done.
    eapply Hoare_conseq with
      (P2 := FixPre I child (LowContributionMode I parent done))
      (Q2 := FixPost I child (LowContributionMode I parent done)).
    - intros s Hpre.
      unfold FixPre; simpl.
      repeat split; assumption.
    - intros r s Hpost.
      unfold FixPost in Hpost; simpl in Hpost.
      exact Hpost.
    - apply (HIH child (LowContributionMode I parent done)).
  Qed.

  Lemma FixIHProvidesFrameContract_proof:
    FixIHProvidesFrameContract_statement.
  Proof.
    unfold FixIHProvidesFrameContract_statement,
      FrameContract.
    intros I W HIH F direct_parent child direct_done Hedge Hnot_done.
    eapply Hoare_conseq with
      (P2 := FixPre I child
               (LowFrameMode I F direct_parent direct_done))
      (Q2 := FixPost I child
               (LowFrameMode I F direct_parent direct_done)).
    - intros s [Hframe [Hcompatible Hentry]].
      unfold FixPre; simpl.
      repeat split; assumption.
    - intros r s Hpost.
      unfold FixPost in Hpost; simpl in Hpost.
      exact Hpost.
    - apply (HIH child (LowFrameMode I F direct_parent direct_done)).
  Qed.

  Lemma FixpointModeStep_from_obligations_proof:
    forall I,
      FixpointModeStep_statement I.
  Proof.
    unfold FixpointModeStep_statement.
    intros I Hobs W HIH x mode.
    destruct mode as
      [| parent done | parent done | outer direct_parent direct_done];
      simpl.
    - destruct Hobs as
        [Hpreloop Hprocess Hedge_loop Hroot_bridge Hmaybe_pop
         Hbody_child Hbody_low Hbody_frame].
      unfold tarjan_scc_f.
      eapply Hoare_bind.
      { apply Hpreloop. }
      simpl. intros _.
      eapply Hoare_bind.
      { apply Hedge_loop.
        - apply FixIHProvidesChildContract_proof.
          exact HIH.
        - apply FixIHProvidesLowContributionContract_proof.
          exact HIH.
        - apply FixIHProvidesFrameContract_proof.
          exact HIH. }
      simpl. intros _.
      eapply Hoare_conseq_pre.
      2: { apply Hmaybe_pop. }
      intros s Hdone.
      unfold PrePopRootReady.
      split.
      + exact Hdone.
      + apply Hroot_bridge.
        exact Hdone.
    - destruct Hobs as
        [Hpreloop Hprocess Hedge_loop Hroot_bridge Hmaybe_pop
         Hbody_child Hbody_low Hbody_frame].
      unfold Hoare.
      intros s1 r s2 [Hentry [Hedge Hnot_done]] Hrun.
      pose proof
        (Hbody_child W
           (FixIHProvidesChildContract_proof I W HIH)
           (FixIHProvidesLowContributionContract_proof I W HIH)
           (FixIHProvidesFrameContract_proof I W HIH)
           parent x done Hedge Hnot_done) as Hchild_body.
      unfold Hoare in Hchild_body.
      eapply Hchild_body; [exact Hentry | exact Hrun].
    - destruct Hobs as
        [Hpreloop Hprocess Hedge_loop Hroot_bridge Hmaybe_pop
         Hbody_child Hbody_low Hbody_frame].
      unfold Hoare.
      intros s1 r s2 [Hpre [Hedge Hnot_done]] Hrun.
      pose proof
        (Hbody_low W
           (FixIHProvidesChildContract_proof I W HIH)
           (FixIHProvidesLowContributionContract_proof I W HIH)
           (FixIHProvidesFrameContract_proof I W HIH)
           parent x done Hedge Hnot_done) as Hlow_body.
      unfold Hoare in Hlow_body.
      eapply Hlow_body; [exact Hpre | exact Hrun].
    - destruct Hobs as
        [Hpreloop Hprocess Hedge_loop Hroot_bridge Hmaybe_pop
         Hbody_child Hbody_low Hbody_frame].
      unfold Hoare.
      intros s1 r s2
             [Hframe [Hcompatible [Hentry [Hedge Hnot_done]]]] Hrun.
      pose proof
        (Hbody_frame W
           (FixIHProvidesChildContract_proof I W HIH)
           (FixIHProvidesLowContributionContract_proof I W HIH)
           (FixIHProvidesFrameContract_proof I W HIH)
           outer direct_parent x direct_done Hedge Hnot_done) as Hframe_body.
      unfold Hoare in Hframe_body.
      assert (Hframe_pre:
                FrameInv I outer s1 /\
                FrameCompatible I outer direct_parent x s1 /\
                ChildEntry I direct_parent x direct_done s1).
      { split; [exact Hframe | split; [exact Hcompatible | exact Hentry]]. }
      eapply Hframe_body; [exact Hframe_pre | exact Hrun].
  Qed.

  Lemma LowLayerCorrect_from_obligations_proof:
    forall I,
      LowLayerCorrect_from_obligations_statement I.
  Proof.
    unfold LowLayerCorrect_from_obligations_statement,
      FixpointLowLayerCorrect_statement.
    intros I Hobs u.
    unfold tarjan_scc.
    apply
      (Hoare_fix_logicv
         (tarjan_scc_f g)
         (FixPre I)
         (FixPost I)
         u
         (LowRootMode I)).
    intros W HIH x mode.
    apply FixpointModeStep_from_obligations_proof.
    - exact Hobs.
    - exact HIH.
  Qed.

  Lemma LowCandidateLayerCorrect_from_phase9_cuts_proof:
    BodyChildPostTailCandidate_statement ->
    PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement ->
    ProcessEdgePreservesFrameAndOlderCandidate_statement ->
    FixpointLowLayerCorrect_statement LowCandidateInterface.
  Proof.
    intros Hchild_tail Hpreloop_processed Hprocess_edge.
    apply LowLayerCorrect_from_obligations_proof.
    apply LowCandidateObligations_from_phase9_cuts_proof; assumption.
  Qed.

End IS_LOW_SKELETON.
