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

Next Phase 5b work item:

```text
Integrate the composite cuts into process_edge branch statements for the tree,
active-stack, and non-stack branches.
```

Rollback trigger:

- The equation refers to child facts that are not available after child pop.
- The field encodes an old proof artifact rather than a consumer need.

## 9. Phase 6: Child Post And Segment Summary

Goal:

- Define exactly what a recursive child returns to its parent.

Candidate fields:

```coq
ChildRootCorrectForParent child s
ChildClosednessContribution parent child done s
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

Rollback trigger:

- Parent needs stack-sensitive child facts after child pop.
- `ChildPost` includes facts not preserved by `maybe_pop child`.

## 10. Phase 7: Root Bridge And Pop Bridge

Goal:

- Connect loop-done facts to root correctness, then transport final facts
  across optional pop.

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

Rule:

- `FrameInv` is not the whole parent loop invariant.
- It contains only facts that are needed after the inner call returns and are
  stable through the inner body, including inner pop.

Pass condition:

- `FrameContract` can be proved for `tarjan_scc_f g W`.
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
- `BodyPreservesFrameContract_statement`
- cut transition statements

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

Current next phase:

```text
Phase 5b: Partial Low Equation Branch Producer Audit
```

Immediate next work item:

```text
State and prove the process_edge-local producer cuts that update
LowFrontierCandidate and LowSourceCandidate in the tree, active-stack, and
non-stack branches.
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
