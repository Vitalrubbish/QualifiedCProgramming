# Tarjan-Directed-Low-Workflow
**Author**: Codex
**Date**: 2026-06-30

## 1. Purpose

This document is the operating workflow for redesigning
`Tarjan_scc_is_low.v`.

It answers the recurring question:

```text
What is the next step, and when is it legitimate to move on?
```

The workflow is intentionally top-down and audit-driven.  Existing definitions
and lemmas are only candidate implementations until they pass the relevant
producer / consumer / lifetime / pop-stability audit.

## 2. Core Rule

Work in this order:

```text
Main theorem
  -> program cuts
  -> semantic interfaces
  -> candidate predicates
  -> producer audit
  -> consumer audit
  -> loop/frame invariant expansion
  -> fixed-point proof structure
  -> final theorem wrappers
```

Do not jump from a candidate predicate directly to proof search.  A candidate
must first pass the local audit that justifies its role in the proof plan.

## 3. Phase 0: Main Theorem And Cuts

Goal:

- Decide the low-layer theorem shape.
- Split the program by real Tarjan cuts.

Input:

- Tarjan body:

```coq
preloop u;;
forset (fun a => dg_step g u a) (process_edge u W);;
If (fun s => low s u = dfn s u) (pop_scc u)
```

Output:

- `LowProofInterface`.
- Cut statements:
  - `PreloopEntry_statement`
  - `ProcessEdgeStep_statement`
  - `EdgeLoopDone_statement`
  - `RootBridge_statement`
  - `MaybePopFinal_statement`
  - fixed-point body/frame statements.

Pass condition:

- Every theorem-level obligation is represented as a `Prop` statement.
- No concrete low-link predicate is assumed final.

Rollback trigger:

- A cut statement requires a predicate that is not consumed by any later cut.
- A cut statement hides a phase transition, especially around `pop_scc`.

Current status:

- Completed in the theorem skeleton.

## 4. Phase 1: Predicate Ledger

Goal:

- Design unknown predicates by meaning, producer, consumer, lifetime, and
  pop-stability.

Output:

- Ledger entries for:
  - `EntryPre`
  - `RootFinal`
  - `RootLowPrePop`
  - `LoopInv`
  - `ChildEntry`
  - `ChildPost`
  - `FrameInv`

Pass condition:

- Each predicate has at least one real producer and at least one real consumer,
  unless it is an entry or final predicate.
- Candidate mapping to existing definitions is marked as candidate, not trusted.

Rollback trigger:

- A predicate bundles fields with different lifetimes.
- A predicate includes facts that its producer cannot establish.
- A predicate includes stack-sensitive facts that are expected to survive pop
  without a bridge.

Current status:

- First ledger exists.
- `EntryPreCandidate`, `LoopEntryBaseCandidate`, and `ChildEntryCandidate`
  have been mapped to first candidates.

## 5. Phase 2: Producer Audit

Goal:

- Prove that candidate predicates can actually be produced by the program cut
  that claims to produce them.

This phase answers:

```text
Can the program produce this cut postcondition?
```

It does not answer:

```text
Is this postcondition sufficient for final low-link correctness?
```

### 5.1 Entry Producer

Audit target:

```coq
EntryPreCandidate u
  -- preloop u -->
LoopEntryBaseCandidate u
```

Field-level statements:

- `PreloopGlobalShapeCandidate_statement`
- `PreloopSettledClosedCandidate_statement`
- `PreloopOrderFactsCandidate_statement`
- `PreloopActiveSelfLowCandidate_statement`

Combined statement:

- `PreloopEntryBaseCandidate_statement`

Pass condition:

- All field-level statements are proved.
- The combined statement is proved from field-level statements.

Current status:

- Passed.
- Proved by `Preloop..._proof` lemmas and
  `PreloopEntryBaseCandidate_proof`.

### 5.2 Child-Entry Producer

Audit target:

```coq
ParentActiveBaseCandidate parent /\
Unvisited child /\
OrderFactsCandidate
  -- set_fa child parent -->
ChildEntryCandidate parent child done
```

with side conditions:

```coq
Edge parent child
~ done child
```

Field-level statements:

- `SetFaGlobalShapePreCandidate_statement`
- `SetFaSettledClosedCandidate_statement`
- `SetFaOrderFactsCandidate_statement`
- `SetFaParentPointerCandidate_statement`
- `SetFaKeepsChildUnvisitedCandidate_statement`
- `SetFaParentActiveCandidate_statement`

Combined statement:

- `SetFaCreatesPendingChildCandidate_statement`

Pass condition:

- All field-level statements are proved.
- The combined statement is proved.
- State facts are separated from branch side conditions.

Important result:

- `Edge parent child` and `~ done child` are not produced by `set_fa`; they are
  branch side conditions threaded through the Hoare proof.
- `GlobalShapePre child` is the correct child-entry shape after `set_fa`, not
  a loose `GlobalShape /\ Unvisited child` bundle.

Current status:

- Passed.
- Proved by `SetFa..._proof` lemmas and
  `SetFaCreatesPendingChildCandidate_proof`.

Rollback trigger:

- A producer proof needs a stronger precondition than the ledger assigned.
- A producer proof only works by smuggling future consumer facts into the
  predicate.

## 6. Phase 3: Consumer Audit For Loop Entry

Goal:

- Check whether `LoopEntryBaseCandidate` is enough to start the edge loop.

This is the next phase after producer audit.

Questions:

- Which facts from `LoopEntryBaseCandidate` are consumed by `process_edge`?
- Which facts are needed to initialize `done = empty`?
- Which facts are missing for the first real loop invariant?

Expected new candidates:

```coq
LocalActiveRootCandidate u s
DoneEmptyCandidate done
LoopInvBaseCandidate u done s
```

First statements to add:

```coq
Definition LoopEntryInitializesBaseCandidate_statement: Prop :=
  forall u,
    Hoare
      (LoopEntryBaseCandidate u)
      (return tt)
      (fun _ s => LoopInvBaseCandidate u empty s).
```

or, if no monadic step is needed:

```coq
Definition LoopEntryImpliesBaseCandidate_statement: Prop :=
  forall u s,
    LoopEntryBaseCandidate u s ->
    LoopInvBaseCandidate u empty s.
```

Pass condition:

- The base loop invariant can be initialized from `LoopEntryBaseCandidate`.
- The unvisited branch can consume the parent facts needed by `set_fa`.
- No low-equation or segment field is added before a consumer requires it.

Current status:

- Passed for the base invariant.
- Added and proved:
  - `LocalActiveRootCandidate`
  - `DoneEmptyCandidate`
  - `LoopInvBaseCandidate`
  - `LoopEntryImpliesBaseCandidate_proof`
  - `LoopInvBaseConsumesUnvisitedSetFaCandidate_proof`
- Low equation, segment accounting, and processed-child summaries remain
  intentionally excluded.

Rollback trigger:

- `LoopEntryBaseCandidate` lacks a fact needed by the first `process_edge`
  branch.
- A proposed `LoopInvBaseCandidate` includes facts not initialized at
  `done = empty`.

## 7. Phase 4: Done Discipline

Goal:

- Define the minimal facts explaining what `done` means.

Candidate fields:

```coq
DoneSubsetOfOutgoing u done
DoneVisited done s
DoneTreeClosed u done s
```

Questions:

- What is true when `done = empty`?
- What must be added when a target `a` is processed?
- Which branches need `done` to imply visitedness or closedness?

Pass condition:

- Empty-done initialization is proved.
- A single `process_edge` step has an explicit statement that extends `done`.

Current status:

- The pure first layer has passed.
- Added and proved:
  - `DoneSubsetOfOutgoingCandidate`
  - `DoneVisitedCandidate`
  - `DoneDisciplineCandidate`
  - `LoopInvDoneCandidate`
  - empty initialization proofs
  - pure `done_after` extension proofs
  - `LoopInvDoneConsumesUnvisitedSetFaCandidate_proof`
- Full `process_edge` integration is handled in Phase 4b, because it requires
  branch post facts such as `Visited a s` after the unvisited recursive call
  or the visited branch.

## 7.1. Phase 4b: Done Discipline Branch Integration

Goal:

- Connect the pure `done_after` extension lemma to the actual
  `process_edge u W a` program cut.

Required callback facts:

```coq
ChildReturnsVisitedCandidate W
ChildPreservesDoneVisitedCandidate W
```

Meaning:

- the recursive child call in the unvisited branch returns with the child
  target visited;
- the recursive child call preserves already processed `done` targets as
  visited facts.

Pass condition:

- `process_edge u W a` proves `Visited a` under the branch assumptions;
- `process_edge u W a` extends `DoneDisciplineCandidate u done` to
  `DoneDisciplineCandidate u (done_after done a)`.

Current status:

- Passed in `Tarjan_scc_is_low.v`.
- Added and proved:
  - `ChildReturnsVisitedCandidate`
  - `ChildPreservesDoneVisitedCandidate`
  - `ProcessEdgeProducesVisitedTargetCandidate_proof`
  - `ProcessEdgeExtendsDoneDisciplineCandidate_proof`
- This phase intentionally does not introduce `done_reachable_closed`,
  `done_tree_reachable_closed`, low equations, or segment accounting.

Rollback trigger:

- `done` facts depend on final low correctness too early.
- `done` facts are not stable through recursive child calls.

## 8. Phase 5: Partial Low Equation

Goal:

- Add only the low-value facts needed by `RootBridge` and by branch updates.

Candidate field:

```coq
PartialRootLowEquation u done s
```

Questions:

- Is an exact minimum equation needed, or are lower-bound/source witnesses
  enough?
- What does `preloop` initialize?
- How does each branch update or preserve the equation?

Pass condition:

- At `done = edge_set u`, the field can derive `RootLowEquation u s`.
- Each `process_edge` branch has a local update statement.

Current status:

- Phase 5 first ledger has passed in `Tarjan_scc_is_low.v`.
- Added the consumer-derived split:
  - `LowFrontierCandidate`
  - `LowSourceCandidate`
  - `PartialRootLowEquationCandidate`
  - `LoopInvLowCandidate`
- Proved the low-equation empty initialization from `low s u = dfn s u`.
- Proved pure `done_after` extension rules for:
  - preserving an old source;
  - adding a tree-child source;
  - adding an active-stack-edge source;
  - extending the frontier under explicit branch bounds.

Immediate next work item:

```text
Phase 5b: audit the actual process_edge branch producers that justify the
frontier bounds and select the right LowSource update case after update_low.
```

Phase 5b primitive-producer status:

- The `update_low u n` producer layer has passed in `Tarjan_scc_is_low.v`.
- Added and proved:
  - `UpdateLowBoundedByOldCandidate_proof`
  - `UpdateLowBoundedByIncomingCandidate_proof`
  - `UpdateLowSourceCandidate_proof`
  - `UpdateLowKeepsSnapshotFieldsCandidate_proof`
  - `UpdateLowPreservesFrontierWithIncomingBound_proof`
- This proves the primitive fact needed by later branches: after
  `update_low u n`, the new `low u` is bounded by both the old low and the
  incoming contribution, has source old-or-incoming, and preserves the fields
  needed to transport existing frontier obligations.

Next Phase 5b work item:

```text
Lift the update_low producer layer through the tree branch
get_low/update_low and the active-stack branch get_dfn/update_low.
```

Phase 5b composite-cut status:

- The composite cuts have passed in `Tarjan_scc_is_low.v`.
- Added and proved:
  - `UpdateLowPreservesFrontierCandidate_proof`
  - `UpdateLowSourceOrIncomingCandidate_proof`
  - `GetLowUpdateLowExtendsFrontierTreeCandidate_proof`
  - `GetDfnUpdateLowExtendsFrontierStackCandidate_proof`
  - `GetLowUpdateLowProducesTreeSourceCandidate_proof`
  - `GetDfnUpdateLowProducesStackSourceCandidate_proof`
- The low-equation producer audit is now factored into:
  - primitive `update_low` facts;
  - composite `get_low/update_low` and `get_dfn/update_low` facts.
- The tree-branch partial-low cut is now integrated through
  `ProcessEdgeTreeBranchExtendsPartialLowCandidate_proof` and the
  top-level `ProcessEdgeExtendsPartialLowCandidate_proof`.

Next Phase 5b work item:

```text
Begin Phase 6: audit the minimal child-post and segment facts required by the
root bridge and by suspended parent frames.
```

Rollback trigger:

- The equation refers to child facts that are not available after child pop.
- The field encodes an old proof artifact rather than a consumer need.

## 9. Phase 6: Child Post And Segment Summary

Current status:

- Phase 5b has completed in `Tarjan_scc_is_low.v`.
- Phase 6 consumer audit has completed in `Tarjan_scc_is_low.v`.
- The child-post interface is now split by its consumers:
  - `ChildLowValidForParentCandidate` for the root low-valid bridge;
  - `ChildIsLowForParentCandidate` for the root is-low bridge;
  - `ChildClosednessContributionCandidate` for done-closedness extension;
  - `ChildSegmentSummaryCandidate` for active-descendant segment reasoning;
  - `ParentResumeShapeCandidate` for the direct pending child facts.
- `LoopInvPhase6Candidate` extends the Phase 5 loop state with
  `DoneClosednessCandidate`, `ProcessedTreeChildrenCorrectCandidate`, and
  `ActiveProcessedChildSegmentSummaryCandidate`.

Goal:

- Define exactly what a recursive child returns to its parent.

Candidate fields:

```coq
ChildLowValidForParent child s
ChildIsLowForParent child s
ChildClosednessContribution child s
Active child s -> ChildSegmentSummary child s
ParentResumeShape parent child done s
```

Questions:

- What does the parent need immediately after `W child`?
- What remains meaningful if the child popped itself?
- What segment facts are only needed when the child remains active?

Pass condition:

- The unvisited-child branch can update parent `LoopInv`.
- The child post does not claim whole-subtree correctness unless a consumer
  actually needs it.
- Each child-post subinterface has a distinct consumer audit, so the final
  combined `ChildPost` shape is justified by proof dependency rather than by
  convenience.
- Empty and child-step consumer audit proofs are present for:
  - done closedness;
  - processed tree-child correctness;
  - active processed child segment summaries;
  - child-post extension of Phase 6 loop fields.

Immediate next work item:

```text
Begin Phase 7: define the root bridge target and audit which Phase 6 fields
are sufficient to derive root low-valid and root is-low at loop done.
```

Rollback trigger:

- Parent needs stack-sensitive child facts after child pop.
- `ChildPost` includes facts not preserved by `maybe_pop child`.

## 10. Phase 7: Root Bridge And Pop Bridge

Goal:

- Connect loop-done facts to root correctness, then transport final facts
  across optional pop.

Current status:

- Phase 7a/7b root-bridge interface and bridge adapters have been added to
  `Tarjan_scc_is_low.v`.
- The skeleton now defines:
  - `LoopDonePhase6Candidate`;
  - `RootBridgeInputCandidate`;
  - `RootBridgeLowValidInputCandidate`;
  - `RootBridgeIsLowInputCandidate`;
  - `RootLowValidPrePopCandidate`;
  - `RootIsLowPrePopCandidate`;
  - `RootLowPrePopCandidate`.
- `LoopDoneProvidesRootBridgeInputCandidate_proof` proves that
  `LoopInvPhase6Candidate u (edge_set u)` provides exactly the pre-pop
  material consumed by root bridge.
- `RootBridgeInputProvidesLowValidInputCandidate_proof` and
  `RootBridgeInputProvidesIsLowInputCandidate_proof` split the common bridge
  input into the two consumer-specific halves.
- `RootBridgeLowValidInputBuildsLowIterationDoneCandidate_proof` adapts the
  consumer-ledger input to the existing pure `low_iteration_done` interface.
- `RootBridgeLowValidCandidate_proof` derives `scc_low_valid_v` by reusing
  `low_frontier_and_src_imply_low_valid`.
- `RootBridgeIsLowCandidate_proof` derives `scc_is_low_v` by reusing
  `scc_is_low_induction_is_low`; this proof consumes
  `RootTreeChildrenIsLowReadyCandidate` and needs
  `ParentFrameResumeCandidate` because `tree_step_char` gives only
  parent-pointer facts, while the processed-child summary is indexed by
  original outgoing edges.
- `RootBridgePrePopCandidate_proof` combines separate low-valid and is-low
  bridge lemmas into the pre-pop root correctness bundle.
- The pre-pop mathematical bridge is complete in the skeleton.
- Phase 7c pop-bridge consumer interface has started.  The skeleton now
  defines:
  - `PoppedSegmentClosedCandidate`;
  - `SegmentClosedAtRootInputCandidate`;
  - `RootFinalLowValidCandidate`;
  - `RootFinalIsLowCandidate`;
  - `RootFinalCorrectCandidate`;
  - `RootFinalCandidate`;
  - `RootFinalFromPrePopCandidate`;
  - `RootPopLowValidStableFieldsCandidate_statement`;
  - `RootPopSettledClosedCandidate_statement`;
  - `RootPopIsLowCandidate_statement`;
  - `RootPopBridgeCandidate_statement`;
  - `PopBranchInputCandidate`;
  - `SkipBranchInputCandidate`.
- The no-pop branch is closed at the consumer-audit level:
  `SkipBranchProducesRootFinalCandidate_proof`.
- The pure projection from pre-pop root correctness to final root correctness
  without stack mutation is closed:
  `RootFinalFromPrePopCandidate_proof`.
- The pop branch remains deliberately stated, not assumed:
  `SegmentClosedAtRootCandidate_statement`,
  `RootPopSettledClosedCandidate_statement`, and
  `RootPopIsLowCandidate_statement`.
- `RootPopLowValidStableFieldsCandidate_proof` proves the low-valid and stable
  structural fields after `pop_scc u` by adapting the existing
  `pop_scc_preserves_low_valid_post_when_root` primitive.
- `RootPopIsLowCandidate_statement` has been narrowed through
  `RootPopIsLowInputCandidate`: it consumes only active root membership,
  pre-pop root is-low, and `low u = dfn u`.  Segment closure is reserved for
  `RootPopSettledClosedCandidate_statement`.
- `RootPopBridgeCandidate_from_parts_proof` assembles the full root-pop bridge
  from the low-valid/stable-fields, settled-closed, and root-is-low components.
- `PopBranchProducesRootFinalCandidate_from_root_pop_bridge_proof` proves the
  branch wrapper from the explicit root-pop bridge.
- `MaybePopFinalCandidate_statement` is now the control-flow composition
  target for the two branch obligations above.

Statements:

```coq
LoopDone u s -> RootLowPrePop u s

Hoare
  (fun s => LoopDone u s /\ RootLowPrePop u s)
  (maybe_pop u)
  (fun _ s => RootFinal u s)
```

Questions:

- Which root facts are pre-pop only?
- Which root facts are final and pop-stable?
- Which segment-closed fact is needed to update `SettledClosed` after pop?

Immediate next work item:

```text
Phase 7c: design the pop bridge.  Decide which segment-closure fact is needed
by the `low u = dfn u` branch and which root facts can be transported or must
be reconstructed after `pop_scc u`.
```

Current Phase 7c result:

- Final root correctness is separated from pre-pop root correctness.
- The maybe-pop layer consumes `LoopDonePhase7Candidate` and
  `RootLowPrePopCandidate`.  The skip branch then projects the Phase 6
  structural fields out of Phase 7.
- `LoopInvPhase7Candidate` extends Phase 6 with exactly the root-level
  `SegmentEscapeAccountingCandidate` field consumed by pop.
- `SegmentClosedAtRootCandidate_proof` proves that root escape accounting at
  `done = edge_set u` plus `root_pop_guard u` implies
  `PoppedSegmentClosedCandidate`.
- `SegmentCoverageByDoneCandidate` is not included in this pop extension,
  because the current `PoppedSegmentClosedCandidate` does not consume it.
- Final root correctness is split into `RootFinalLowValidCandidate` and
  `RootFinalIsLowCandidate`, because they have different pop producers.
- The low-valid/stable-fields part of the pop branch is proved.
- `RootPopSettledClosedCandidate_proof` proves settled-closed after pop by
  connecting `stack_split_at`'s removed prefix to the dfn segment consumed by
  `PoppedSegmentClosedCandidate`.
- `RootPopIsLowCandidate_proof` proves root is-low after pop by showing that
  the post-pop root low-tree is a subset of the pre-pop low-tree and then using
  `low u = dfn u` with `u` as the post-pop minimum witness.
- `RootPopBridgeCandidate_proof`, `PopBranchProducesRootFinalCandidate_proof`,
  and `MaybePopFinalCandidate_proof` close Phase 7c.

Producer-audit result so far:

- Empty initialization is not free for arbitrary states.  It requires:
  `LocalActiveRootCandidate u s` and `RootSegmentInitialCandidate u s`.
- `SegmentEscapeAccountingCandidate_empty_proof` is proved under exactly those
  entry-side assumptions.
- Child-step preservation is now factored through the consumer-minimal
  `ParentPendingChildEscapeAccountedCandidate u done child s`.
  This fact says that the old pending escape through the newly added child is
  still explained after `done_after done child`, either by a fresh pending
  root escape or by an old stack anchor.
- `ChildSegmentEscapeLiftsToParentCandidate_proof` and
  `SegmentEscapeAccountingCandidate_step_child_proof` are proved from that
  fact.
- Two branch producer facts are already proved:
  `ParentPendingChildEscapeAccountedCandidate_from_closed_proof` for a popped
  child whose reachable region is closed, and
  `ParentPendingChildEscapeAccountedCandidate_from_old_anchor_proof` for an
  active older stack anchor after the parent low update.
- The active-descendant audit has been reduced, not hidden:
  `ParentPendingChildEscapeAccountedCandidate_from_active_descendant_proof`
  proves the parent lift from parent segment accounting plus a new
  `ChildSelfPendingEscapeAccountedCandidate`.
- `ChildSelfPendingEscapeAccountedCandidate_from_child_summary_proof` proves
  that child segment accounting is enough once the old-anchor lift is
  supplied.  The apparent child-pending-root lift was audited and removed:
  at child loop-done, `edge_set child` is exactly `Edge child`, so the
  pending-root branch requiring both `Edge child a` and `~ edge_set child a`
  is impossible.
- `ChildOldAnchorLiftsToParentCandidate_from_all_older_proof` gives one
  proved sufficient producer for the old-anchor lift.

- The previous `ChildPendingRootEscapeLiftCaseCandidate` debt is closed by
  rejection, not by proof: the predicate had no real producer because its
  triggering branch is contradictory under the current child summary
  `SegmentEscapeAccountingCandidate child (edge_set child) s`.
- The pop branch now consumes `LoopDonePhase7Candidate`, not merely
  `LoopDonePhase6Candidate`, so `SegmentClosedAtRootCandidate_proof` is a real
  branch input.  The pop proof debts for settled-closed and root-is-low across
  `pop_scc u` are now proved.

Pass condition:

- Root correctness is root-only, not whole-subtree.
- Pop-sensitive facts are bridged, not assumed preserved.

Rollback trigger:

- `RootFinal` uses stack-sensitive definitions that fail after pop.
- `LoopDone` does not contain enough segment accounting to justify pop.

## 11. Phase 8: Frame Contract

Goal:

- Define what an inner recursive call must preserve for suspended outer loops.

Candidate:

```coq
FrameInv F s
```

Current Phase 8 status:

- `SuspendedFrameCandidate` now stores the suspended parent root, the pending
  child whose recursive call is in progress, and the parent's current `done`
  set.  The pending child is a consumer-driven field: without it the frame
  cannot state the `ParentResumeShapeCandidate` that the outer child-post
  proof must recover after deeper recursive calls.
- Phase 8b producer audit found that `FrameInvCandidate` must not contain the
  full `ParentFrameResumeCandidate parent done`: after `set_fa child parent`
  and before adding `child` to `done`, the old
  `fa_not_done_implies_eq_u parent done` field is intentionally false for that
  pending child.  The frame now carries
  `SuspendedParentFrameResumeCandidate parent child done`, which is the same
  parent `fa` discipline with the pending child as the only allowed exception.
- `FrameInvCandidate` is no longer just a bare Phase 7 loop snapshot.  It is
  `ParentResumeShapeCandidate` for the pending child plus the suspended loop
  material that must survive for the outer parent to resume: low loop fields,
  suspended parent frame-resume facts, done closedness, processed child
  correctness, active child segment summaries, and suspended segment escape
  accounting outside the pending child segment.
- `SuspendedLoopInvPhase7ProvidesFrameInvCandidate_proof` requires both
  `SuspendedLoopInvPhase7Candidate` and `ParentResumeShapeCandidate`; normal
  loop material alone is insufficient and, after `set_fa`, too strong.
- `FrameInvForgetsSuspendedLoopInvPhase6Candidate_proof` and the field
  projection proofs show the available consumers separately:
  `FrameInvProvidesParentResumeShapeCandidate_proof`,
  `FrameInvProvidesLoopInvLowCandidate_proof`,
  `FrameInvProvidesSuspendedParentFrameResumeCandidate_proof`,
  `FrameInvProvidesDoneClosednessCandidate_proof`,
  `FrameInvProvidesProcessedTreeChildrenCorrectCandidate_proof`,
  `FrameInvProvidesActiveProcessedChildSegmentSummaryCandidate_proof`, and
  `FrameInvProvidesSuspendedSegmentEscapeAccountingCandidate_proof`.
- `SuspendedParentFrameResumeClosesAfterChildCandidate_proof` proves that once
  the pending child is visited and added to `done_after`, the normal
  `ParentFrameResumeCandidate parent (done_after done child)` is recovered.
- `FrameContractCandidate_from_field_preservation_proof` closes the Phase 8b
  audit shape: the full frame contract follows mechanically from seven
  field-level preservation producers.  The field producers themselves remain
  the next proof obligations; they must be proved through `preloop`,
  `edge_loop`, and inner `maybe_pop` without widening the frame again.
- Phase 8c further narrows the contract to compatible recursive calls.  A
  frame must be preserved only when the call is its own pending child or when
  the direct parent is already inside the frame child's pending segment:
  `FrameCompatibleWithCallCandidate F parent child s`.
- `FrameFieldPreservationCandidate` now lets every field producer consume the
  full `FrameInvCandidate`, plus compatibility and the direct `ChildEntry`.
  The earlier field-only precondition was too strong: some field producers may
  legitimately need other frame fields.
- `FrameCompatibleWithOwnCallCandidate_proof` and
  `FrameCompatibleWithPendingParentCandidate_proof` record the two legal
  compatibility sources.  `FrameContractCandidate_to_field_preservation_bundle_proof`
  records the recursive-IH direction: an existing whole-frame contract can be
  projected into the seven field producers.
- Phase 8d has started the concrete field-producer audit with
  `ParentResumeShapeCandidate`.  `FrameParentResumeShapeAfterPreloopCandidate_proof`
  shows that the suspended frame's pending-child facts survive the inner
  `preloop child`, provided the frame is compatible with the call; compatibility
  is consumed exactly to recover `Visited (frame_child F)` after `preloop`.
- `FrameParentResumeShapePreservedByMaybePopCandidate_proof` shows that
  `maybe_pop u` preserves the same resume shape by using `pop_scc_keep_fa`.
  The proof deliberately keeps the field narrow: it preserves only the direct
  edge, `~ done child`, `fa child = parent`, and `fa child <> child`, not the
  whole suspended frame.
- The complete body-level producer for this single field should not be proved
  in isolation yet.  The inner `edge_loop` may call `W a`; applying the
  recursive frame contract to that call requires the whole `FrameInvCandidate`
  before each iteration, not merely `ParentResumeShapeCandidate`.  Therefore
  the next Phase 8 work is to audit the remaining frame fields at the cut
  level, then prove the `edge_loop` preservation at the bundle level.
- Phase 8e audits the remaining six fields at the cut level.  The
  `SuspendedParentFrameResumeCandidate` field passes the local audit:
  `FrameSuspendedParentFrameResumeAfterPreloopCandidate_proof` and
  `FrameSuspendedParentFrameResumePreservedByMaybePopCandidate_proof` show
  that it is stable through `preloop` and `maybe_pop`, because it only depends
  on `visited` and `fa`.
- The other five fields are not ready for body-level preservation.  The audit
  found that several current predicates are pop- or preloop-sensitive in ways
  not represented by the frame:
  `LoopInvLowCandidate` and `DoneClosednessCandidate` need a frame-pop
  separation fact before `maybe_pop`; `ProcessedTreeChildrenCorrectCandidate`
  needs dedicated low-valid/is-low preservation through DFS tree and stack
  changes; `ActiveProcessedChildSegmentSummaryCandidate` is too strong if the
  child segment is approximated only by a dfn interval; and the full
  `SegmentEscapeAccountingCandidate parent done` is too strong as a suspended
  frame field because `preloop` adds the pending child/descendants to the
  quantified active segment before they can be accounted by `done`.
- Rollback required before proving the frame bundle: refine the segment-summary
  and suspended-segment fields, then introduce the exact pop-separation
  producer consumed by `LoopInvLowCandidate` and `DoneClosednessCandidate`.
- Phase 8f performs the first rollback/refinement.  The full
  `SegmentEscapeAccountingCandidate parent done` field has been replaced by
  `SuspendedSegmentEscapeAccountingCandidate parent child done`, which excludes
  the current `PendingChildSegmentCandidate child s`.  This is produced from
  full segment accounting by `SegmentEscapeAccountingSuspendsCandidate_proof`
  when the frame is created.
- Because the frame now stores only suspended accounting,
  `FrameInvForgetsSuspendedLoopInvPhase7Candidate_proof` is no longer a valid
  projection.  It is replaced by
  `FrameInvForgetsSuspendedLoopInvPhase6Candidate_proof`; full Phase 7
  accounting must be reconstructed after child return by a dedicated close
  lemma.
- Phase 8g adds that close lemma interface.  The exact missing child-side
  input is named `PendingChildSegmentEscapeAccountedCandidate`; with it and
  `ParentPendingChildEscapeAccountedCandidate`,
  `SuspendedSegmentEscapeAccountingClosesAfterChildCandidate_proof` recovers
  full `SegmentEscapeAccountingCandidate parent (done_after done child)`.
  This keeps the proof consumer-driven: child summary is not assumed to be
  sufficient until its producer has been audited.
- Phase 8h audits that producer.  `ChildSegmentSummaryCandidate` produces
  `PendingChildSegmentEscapeAccountedCandidate` only when paired with two
  explicit facts: `PendingChildSegmentOrderCandidate` and
  `PendingChildSegmentOldAnchorLiftsToParentCandidate`.
  `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_proof`
  records exactly this composition and leaves those two facts as the next
  producer targets.
- The first target is now closed:
  `PendingChildSegmentOrderCandidate_from_global_shape_proof` derives it from
  `GlobalShapeCandidate` via DFS-tree reachability and `dfn_valid`.
- The second target was corrected to return the same
  pending-root/old-anchor disjunction consumed by parent accounting.  The
  all-older route is only a sufficient producer:
  `low parent <= low child` plus
  `PendingChildSegmentOldAnchorsBelowParentCandidate parent child s`.
  `GetLowUpdateLowProducesParentLowBelowChildCandidate_proof` produces the
  low inequality at the correct cut, after `update_low parent (low child)`.
  `PendingChildSegmentOldAnchorLiftsToParentCandidate_from_all_older_segment_proof`
  and
  `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_segment_producers_proof`
  record this sufficient producer path.
- The preferred path now splits the old-anchor witness by parent order.
  `PendingChildSegmentOldAnchorLiftsToParentCandidate_from_anchor_split_proof`
  uses the old-anchor branch when `dfn b < dfn parent`; otherwise it consumes
  `PendingChildSegmentNonOlderAnchorAccountedByParentCandidate`, which returns
  the same parent pending-root/old-anchor disjunction required by the
  consumer.
  `PendingChildSegmentNonOlderAnchorAccountedBySuspendedParent_proof` produces
  that fact from suspended parent accounting plus
  `ParentPendingChildEscapeAccountedCandidate`.
  `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_anchor_split_proof`
  records the preferred composition, and
  `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_suspended_parent_proof`
  closes the preferred producer path.
- The preferred producer path is now connected to the actual post-child
  `get low child ;; update_low parent` cut.
  `GetLowUpdateLowPreservesChildSegmentSummaryFromParentResumeCandidate_proof`
  preserves the child summary from the parent resume shape,
  `GetLowUpdateLowProducesNonOlderAnchorAccountedByParentFromParentResumeCandidate_proof`
  produces the non-older-anchor parent accounting from suspended parent
  accounting and parent-pending-child accounting, and
  `GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_proof`
  composes the exact post-cut facts consumed by the segment close lemma.
  The next Phase 8 audit is the frame-pop boundary predicate consumed by
  `LoopInvLowCandidate` and `DoneClosednessCandidate`.
- Phase 8i starts that frame-pop boundary audit.  The boundary is intentionally
  narrow: `FramePopBoundaryCandidate F u s` says the suspended frame parent
  and every active frame-`done` vertex survive the `stack_split_at (stack s) u`
  pop by lying in the returned `rest`.  The first producer,
  `MaybePopProducesFramePopBoundarySnapshotCandidate_proof`, turns that
  boundary into a snapshot fact after `maybe_pop u`: the frame parent remains
  active, active frame-`done` vertices remain active, and `visited`, `dfn`,
  `low`, and `fa` are unchanged.  The separate generic stack-subset producer
  needed by `LowFrontierCandidate` is now
  `MaybePopActivePostImpliesPreSnapshotCandidate_proof`, which proves
  `Active post -> Active pre` from the active pop root.  The remaining
  child pop-closedness input needed for `SettledClosedCandidate` is now
  `MaybePopPreservesSettledClosedWithSegmentClosedCandidate_proof`.  The next
  consumer facts are also audited:
  `FramePopBoundarySnapshotPreservesDoneClosednessCandidate_proof` preserves
  `DoneClosednessCandidate`, and
  `FramePopSnapshotsPreservePartialRootLowEquationCandidate_proof` preserves
  the low-equation half of `LoopInvLowCandidate`.
- Phase 8i now also closes the structural producers required by the full
  `LoopInvLowCandidate` preservation lemma:
  `PopSccKeepsDfnInjectiveCandidate_proof`,
  `MaybePopPreservesGlobalShapeCandidate_proof`, and
  `MaybePopPreservesOrderFactsCandidate_proof`.
  These, together with the settled-closed and snapshot producers, compose into
  `MaybePopPreservesLoopInvLowWithFramePopBoundaryCandidate_proof`.
  `MaybePopPreservesDoneClosednessWithFramePopBoundaryCandidate_proof` closes
  the analogous Hoare wrapper for `DoneClosednessCandidate`.
- The `ActiveProcessedChildSegmentSummaryCandidate` refinement is now closed at
  the cut level.  The frame stores only
  `ChildSelfSegmentEscapeSummaryCandidate`, which is stable through later
  sibling `preloop`; `MaybePopPreservesActiveProcessedChildSegmentSummaryCandidate_proof`
  preserves it through inner `maybe_pop` by requiring the real pop root
  `Active u` and using stack order to show that an old-anchor below an active
  surviving child also survives in `rest`.
- `ProcessedTreeChildrenCorrectCandidate` preservation is now closed at the
  frame-pop cut level.  The predicate was refined with
  `ChildInactiveSelfLowForParentCandidate`, so inactive processed children can
  transport root correctness from `low child = dfn child`, while active
  processed children use the lower-anchor preservation argument.  The closed
  cut-level producer is
  `MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryCandidate_proof`.
- Phase 8 is complete as a cut-level frame-contract audit.  It has not yet
  produced the body-level theorem
  `FramePreservesProcessedTreeChildrenCorrectCandidate (tarjan_scc_f g W)`;
  that assembly belongs to the Phase 9 fixed-point/body proof connection.

Rule:

- `FrameInv` is not the whole parent loop invariant.
- It contains only facts that are needed after the inner call returns and are
  stable through the inner body, including inner pop.

Pass condition:

- The seven field-level preservation producers in
  `FramePreservationBundleCandidate` can be proved for `tarjan_scc_f g W`
  under the compatible-call precondition.
- `FrameContractCandidate` is then obtained only through
  `FrameContractCandidate_from_field_preservation_proof`.
- Every field in `FrameInv` has a consumer after the inner call.

Rollback trigger:

- A frame field is not preserved by inner `preloop`, edge loop, or pop.
- A frame field is only needed before the inner call, not after it.

## 12. Phase 9: Fixed-Point Assembly

Goal:

- Use the audited root, child, and frame contracts to prove the recursive
  fixed-point statement.

Inputs:

- `BodySatisfiesChildContract_statement`
- `BodyProvidesLowContributionContract_statement`
- `BodyPreservesFrameContract_statement`
- cut transition statements

Current Phase 9a status:

- Fixed-point mode assembly is implemented in `Tarjan_scc_is_low.v`.
- `LowFixMode` now has four consumer-driven modes:
  `LowRootMode`, `LowChildMode`, `LowContributionMode`, and `LowFrameMode`.
- `LowContributionMode` was added because `process_edge`'s tree branch
  consumes `ChildProvidesLowContributionCandidate`; this contract depends on
  parent low-equation material and is not a plain child post.
- `FixIHProvidesChildContract_proof`,
  `FixIHProvidesLowContributionContract_proof`, and
  `FixIHProvidesFrameContract_proof` project the combined fixed-point IH into
  the three recursive contracts consumed by the body.
- `FixpointModeStep_from_obligations_proof` proves one recursive body step for
  all four modes from `LowProofObligations`.
- `LowLayerCorrect_from_obligations_proof` proves
  `LowLayerCorrect_from_obligations_statement`.
- This closes the abstract fixed-point assembly layer without changing any
  previously audited predicate meaning.
- The concrete `tarjan_scc_f g W` body contracts are not closed yet.  They
  remain the next Phase 9 work item, especially the frame-preservation bundle
  fields such as
  `FramePreservesProcessedTreeChildrenCorrectCandidate (tarjan_scc_f g W)`.

Current Phase 9b status:

- The concrete child-post bundle is closed at the child-owned field level.
- `ChildPostCandidate` now combines only the audited child-return fields:
  `Visited child`, child low-valid, child is-low, inactive-self-low,
  closedness contribution, and conditional child segment summary.
  Parent resume shape and parent accounting are not part of this naked child
  post; they belong to framed continuation paths.
- `ChildContractCandidate` packages this combined post as the concrete child
  contract for a recursive program `W`.
- `ChildContractCandidate_from_field_statements_proof` proves that the existing
  field-level child-post statement
  `ProcessEdgeUnvisitedChildPostCandidate_statement` implies the combined
  child contract.
- `ChildPostCandidate` now explicitly includes `Visited child s`, because the
  per-edge consumer must extend the done discipline after the child call.
  `ChildContractCandidate_provides_post_fields_proof` projects the individual
  child-post fields back out of the bundled contract.
- `LowCandidateInterface` now maps the low-contribution abstract contract to
  `ChildProvidesLowContributionCandidate`, and
  `LowContributionCandidate_to_interface_proof` connects the concrete contract
  to the abstract interface.
- `RootBridgeCandidate_to_interface_proof` and
  `MaybePopFinalCandidate_to_interface_proof` connect the completed Phase 7
  root/final cuts to the same interface.
- The body prefix entry is now explicit.  `ChildEntryProvidesEntryPreCandidate_proof`
  lets a recursive child-entry state reuse the ordinary `EntryPreCandidate`,
  and `PreloopProducesLoopInvPhase7InitialCandidate_proof` proves that
  `preloop u` establishes `LoopInvPhase7Candidate u ∅`.
- The edge-loop proof has been reduced to its real dependency:
  `EdgeLoopDone_from_process_edge_step_proof` derives `EdgeLoopDone_statement`
  from a per-edge `ProcessEdgeStep_statement` plus done-set extensionality of
  the loop invariant.  `LoopInvPhase7Candidate_done_proper_proof` and
  `EdgeLoopDoneCandidate_from_process_edge_step_proof` close that adapter for
  `LowCandidateInterface`.
- `ProcessEdgeStepCandidate_statement` is now the concrete candidate-level
  per-edge obligation.  `ProcessEdgeStepCandidate_to_interface_proof` lifts it
  to `ProcessEdgeStep_statement LowCandidateInterface`.
- `ProcessEdgeStepCandidate_proof` proves this concrete per-edge obligation.
  `ProcessEdgeStepCandidate_interface_proof` exposes it through the abstract
  interface, and `EdgeLoopDoneCandidate_proof` /
  `EdgeLoopDoneCandidate_direct_proof` close the concrete edge-loop adapter.
- The tree-branch frame-entry producer
  `SetFaCreatesSuspendedParentFrameCandidate_proof` is proved: after `set_fa`
  it provides the suspended parent frame shape and the direct
  `ParentResumeShapeCandidate` consumed by the recursive-call frame contract.
- The concrete child-body core is now available:
  `BodyChildProducesRootFinalCandidate_proof`,
  `RootFinalProvidesChildPostCoreCandidate_proof`,
  `BodyChildProducesPostCoreCandidate_proof`,
  `BodyChildProducesInactiveSelfLowCandidate_proof`, and
  `BodyChildProducesActiveSegmentSummaryCandidate_proof`.
- `BodySatisfiesChildContractCandidate_from_phase9_cuts_proof` is now proved
  directly from those concrete body producers.  It no longer depends on a
  parent-accounting tail cut.
- The major frame-pop cut is now closed without widening `FrameInvCandidate`.
  `MaybePopPreservesFrameSuspendedSegmentFieldsWithBoundaryCandidate_proof`
  transports the two suspended segment fields through inner `maybe_pop`;
  `MaybePopPreservesFrameNonSegmentFieldsWithBoundaryCandidate_proof` covers
  the other six fields; and
  `MaybePopPreservesFrameInvWithBoundaryCandidate_proof` assembles the full
  frame invariant.
- `MaybePopPreservesFrameInvFromLoopDoneOlderVerticesCandidate_proof` packages
  the consumer-facing body cut: from inner loop-done, older-frame-vertex facts,
  and popped-segment closedness, `maybe_pop child` preserves `FrameInv F`.
- `PreloopMakesFrameVerticesOlderThanChildCandidate_proof` records the first
  body-level producer for those older-frame-vertex facts: after
  `preloop child`, the suspended frame parent and every suspended frame-done
  vertex are older than the direct child.
- `PreloopProducesFrameBodyPrefixFactsCandidate_proof` packages the current
  `preloop child` body-prefix facts without claiming full frame preservation:
  outer parent resume shape, `Visited (frame_child F)`, suspended parent-frame
  resume, and the older-frame-vertex facts.  This is the safe input material
  for the next frame-body assembly step.
- The compatibility field has been strengthened to be parent-aware:
  `FrameCompatibleWithCallCandidate F parent child s`.  The deeper-call case
  now requires the direct parent to be in the suspended frame child's pending
  segment, not merely that `frame_child F` has been visited.
- `dfs_tree_step_transport_from_monotone_fields` and
  `dfs_tree_reachable_transport_from_monotone_fields` provide the one-way tree
  transport needed by `preloop`, whose visited set grows.  Using them,
  `PreloopProducesPendingChildSegmentFromFrameCompatibilityCandidate_proof`
  proves that after `preloop child`, the direct child lies in the suspended
  frame child's pending segment whenever the call is frame-compatible.
- `PreloopPreservesFrameSuspendedSegmentFieldsFromCompatibilityCandidate_proof`
  is now closed: the suspended escape-accounting and suspended tree-coverage
  fields survive `preloop child` by excluding the new direct child through the
  freshly produced pending segment and transporting old DFS-tree reachability
  with monotone visited/unchanged-`fa` fields.
- The non-segment preloop frame adapters now closed are
  `PreloopPreservesFrameLoopInvLowCandidate_proof`,
  `PreloopPreservesFrameDoneClosednessCandidate_proof`, and
  `PreloopPreservesFrameActiveProcessedChildSegmentSummaryCandidate_proof`.
  Their common pattern is consumer-driven: frame `done` vertices are old visited
  vertices, so they are not the new direct child; `preloop` only adds the direct
  child to `visited`/`stack` and preserves the old `fa` field.
- `PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_proof` closes
  the remaining preloop frame-field gap.  The body frame path is now assembled:
  `BodyPreservesFrameContractCandidate_from_phase9_cuts_proof` is
  premise-free.
- The auxiliary frame-progress mode is also closed by
  `BodyPreservesFrameProgressContractCandidate_proof`.
- The remaining concrete body dependency is the low-contribution accounting
  tail.  The current transitional surface is
  `BodyChildPostTailCandidate_statement`, but its naked
  `ChildEntryCandidate` precondition is too weak for parent accounting.
  The next proof should instead produce the accounting facts from the framed
  low-contribution precondition:
  `FrameInvCandidate (FrameOfCallCandidate parent child done)`,
  `ChildEntryCandidate parent child done`, and
  `PartialRootLowEquationCandidate parent done`.

Pass condition:

- `LowLayerCorrect_from_obligations_statement` is proved.
- No proof obligation requires changing previously frozen predicate meanings.

Rollback trigger:

- The fixpoint mode needs an extra postcondition not present in `RootFinal`,
  `ChildPost`, or `FrameInv`.
- A frame proof tries to modify the definition of an earlier predicate.

## 13. Phase 10: Public Wrapper

Goal:

- Derive the public theorem from the low-layer theorem.

Questions:

- Does public entry imply `EntryPre`?
- Does `RootFinal` imply the advertised public post?
- Is `settled_closed` available initially or from a driver invariant?

Pass condition:

- Public theorem is a wrapper, not a rewrite of the recursive low-layer proof.

Rollback trigger:

- The public theorem requires facts that the low-layer theorem deliberately
  excluded.

## 14. Status Summary

Current completed phases:

1. Main theorem skeleton and cut statements.
2. First predicate ledger.
3. Producer audit for `preloop`.
4. Producer audit for `set_fa child parent`.
5. Consumer audit for loop-entry base invariant.
6. Done discipline pure layer: subset-of-outgoing and visited targets.
7. Done discipline branch integration for `process_edge`.
8. Partial low-equation first ledger: frontier/source split and pure rules.
9. Partial low-equation branch producer audit through `process_edge`.
10. Child-post and segment-summary consumer audit.
11. Root bridge to pre-pop root correctness.
12. Phase 7c pop bridge and segment closure.
13. Phase 8 cut-level frame-contract audit: all frame fields have explicit
    pop/preloop-style preservation cuts, including
    `ProcessedTreeChildrenCorrectCandidate`.
14. Phase 9a fixed-point mode assembly:
    `LowLayerCorrect_from_obligations_proof` is proved from the abstract
    obligations.
15. Phase 9b contract alignment:
    `LowContributionContract` is an explicit recursive mode/contract and the
    concrete child/root/final/preloop/edge-loop adapters are in place.
16. Phase 9b concrete process-edge and child-body core:
    `ProcessEdgeStepCandidate_proof`,
    `ProcessEdgeStepCandidate_interface_proof`,
    `EdgeLoopDoneCandidate_proof`,
    `EdgeLoopDoneCandidate_direct_proof`, and the child-body core producers
    are proved.
17. Phase 9b frame-pop body cut:
    `MaybePopPreservesFrameInvWithBoundaryCandidate_proof` and
    `MaybePopPreservesFrameInvFromLoopDoneOlderVerticesCandidate_proof` are
    proved; the remaining frame work is preloop/edge-loop assembly.
18. Phase 9b preloop frame-field cuts:
    suspended segment fields, `LoopInvLowCandidate`, `DoneClosednessCandidate`,
    and `ActiveProcessedChildSegmentSummaryCandidate` now have compiled
    preloop frame adapters; `ProcessedTreeChildrenCorrectCandidate` is also
    closed by `PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_proof`.
19. Phase 9b body frame/progress assembly:
    `BodyPreservesFrameContractCandidate_from_phase9_cuts_proof` and
    `BodyPreservesFrameProgressContractCandidate_proof` are proved.
20. Phase 9b child-contract body assembly:
    `ChildPostCandidate` is child-only and
    `BodySatisfiesChildContractCandidate_from_phase9_cuts_proof` is proved
    without parent accounting.

Current next phase:

```text
Phase 9b: Concrete body contract assembly
```

Immediate next work item:

```text
Continue Phase 9b by replacing `BodyChildPostTailCandidate_statement` with a
framed low-contribution accounting producer.  The target facts are
`ParentPendingChildEscapeAccountedCandidate parent done child` and
`ActiveTargetBlocksEscapeAccountedCandidate parent (done_after done child)`,
produced under the full framed low-contribution precondition rather than under
bare `ChildEntryCandidate`.
```

## 15. General Stop Rules

Stop and revise the design when:

- A proof needs an unlisted producer.
- A consumer uses a fact not present in the ledger.
- A field has no consumer.
- A field has no producer.
- A fact crosses `pop_scc` without an explicit bridge.
- A candidate existing definition forces stronger facts than the interface
  actually needs.

These are design failures, not proof-search failures.
