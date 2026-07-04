# Tarjan-Directed-Low-Phase9-Gaps
**Author**: Codex
**Date**: 2026-07-02
**Updated**: 2026-07-03

## 1. Scope

This note records the current Phase 9 status for
`SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`.

Phase 9a remains closed: `LowFixMode`,
`FixpointModeStep_from_obligations_proof`, and
`LowLayerCorrect_from_obligations_proof` assemble the abstract recursive
theorem from `LowProofObligations`.

Phase 9b is the concrete-body phase. The original goal is still to prove that
`tarjan_scc_f g W` satisfies the three candidate-level body contracts:

```coq
BodySatisfiesChildContractCandidate_statement
BodyProvidesLowContributionCandidate_statement
BodyPreservesFrameContractCandidate_statement
```

The current design also exposes an auxiliary consumer contract:

```coq
BodyPreservesFrameProgressContractCandidate_statement
```

This is intentional. The tree-branch consumer does not merely need
`FrameInvCandidate F`; it needs a progress fact saying that the suspended
frame is already older than the current direct parent and that its done
vertices remain older. This is represented by `FrameProgressCandidate` and
threaded through `RecursiveCallContractsCandidate`, `LowProofInterface`,
`LowProofObligations`, and fixed-point mode `LowFrameProgressMode`.

This follows the design principle: ask what the consumer needs, not what the
current local proof happens to provide.

## 2. Closed Since The Previous Ledger

The process-edge frame cut is now internal:

```coq
ProcessEdgePreservesFrameAndOlderCandidate_proof
```

It is assembled from the progress-aware process-edge lemmas and consumes the
new recursive progress contract. Downstream frame body assembly no longer
needs an external `ProcessEdgePreservesFrameAndOlderCandidate_statement`
argument.

The preloop processed-children cut is now proved:

```coq
PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_proof
```

The proof is deliberately consumer-shaped. It does not try to prove a global
state-unchanged transport for `preloop child`, because `preloop` legitimately
changes `visited`, `stack`, `dfn child`, and `low child`. Instead it proves
exactly what the frame and low-contribution consumers need: old processed
children of the suspended frame are distinct from the newly visited direct
child, their parent pointers and numeric facts are stable, and no new DFS-tree
path through the fresh child invalidates their low/is-low obligations.

The low-contribution body path is therefore reduced to internalizing this
proved preloop fact in the remaining assemblers:

```coq
BodyProvidesLowContributionCandidate_from_frame_phase9_cut_proof
```

The transitional preloop parameter has already been removed.  The current
low-contribution assembler still carries only the accounting-tail premise and
combines it with:

```coq
BodyPreservesPartialRootLowEquationCandidate_from_frame_cuts_proof
BodyPreservesChildParentPointerCandidate_from_frame_cuts_proof
BodyProducesChildLowDfnBoundCandidate_proof
```

The current high-level obligation assembler is:

```coq
LowCandidateObligations_from_phase9_cuts_proof
```

and the source now takes only:

```coq
BodyChildPostTailCandidate_statement
```

The previous transitional `PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement`
parameter has been internalized.  The frame and low-contribution assemblers now
call `PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_proof`
directly.

Additional closed items after the first 2026-07-03 cleanup:

- `BodyPreservesFrameContractCandidate_from_phase9_cuts_proof` is now
  premise-free.  It assembles the body frame path from
  `BodyFrameAfterPreloopCandidate_from_processed_cut_proof`,
  `BodyFrameEdgeLoopPreservesCandidate_from_process_edge_cut_proof`, and
  `MaybePopPreservesFrameInvFromLoopDoneOlderVerticesCandidate_proof`.
- `BodyPreservesFrameProgressContractCandidate_proof` is proved.  The progress
  mode is no longer an external Phase 9 cut.
- `ChildPostCandidate` has been narrowed to the child-only recursive post:
  `Visited child`, child low-valid, child is-low, inactive-self-low, child
  closedness contribution, and the conditional active child segment summary.
  It no longer exposes parent resume shape or parent accounting.
- `ChildContractCandidate_provides_post_fields_proof` now projects only those
  child-owned fields.  Parent resume is recovered from `FrameInvCandidate`
  where it is actually needed.
- `BodySatisfiesChildContractCandidate_from_phase9_cuts_proof` is proved
  directly from the concrete body producers:
  `BodyChildProducesPostCoreCandidate_proof`,
  `BodyChildProducesInactiveSelfLowCandidate_proof`, and
  `BodyChildProducesActiveSegmentSummaryCandidate_proof`.

This is the important design correction: the recursive child contract should
not smuggle parent continuation/accounting facts through a naked
`ChildEntryCandidate`.

## 3. Remaining Work

### 3.1 Low-Contribution Accounting Cut

The remaining Phase 9 gap is the low-contribution accounting tail currently
fed through:

```coq
BodyChildPostTailCandidate_statement
```

The statement is too strong as a standalone child-entry body cut:

```coq
Hoare
  (ChildEntryCandidate parent child done)
  (tarjan_scc_f g W child)
  ...
```

It tries to produce parent accounting from only the child call entry.  That is
not the right semantic boundary.  The consumer is the framed
low-contribution contract:

```coq
FramedChildProvidesLowContributionCandidate
```

whose precondition already contains the parent frame and parent partial-low
material:

```coq
FrameInvCandidate (FrameOfCallCandidate parent child done) s /\
ChildEntryCandidate parent child done s /\
PartialRootLowEquationCandidate parent done s
```

The first correction was to replace the naked child-entry cut with a framed
accounting producer, shaped around the two facts still consumed by
`LowContributionPost`:

```coq
ParentPendingChildEscapeAccountedCandidate parent done child s /\
ActiveTargetBlocksEscapeAccountedCandidate
  parent (done_after done child) s
```

A suitable proof-level target is:

```coq
Lemma BodyProducesLowContributionAccountingCandidate_proof:
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
         ParentPendingChildEscapeAccountedCandidate parent done child s /\
         ActiveTargetBlocksEscapeAccountedCandidate
           parent (done_after done child) s).
```

Expected accounting sources:

- child closedness and active segment summary from the already proved
  child-body producers;
- suspended segment escape accounting from
  `FrameInvCandidate (FrameOfCallCandidate parent child done)`;
- `ParentLowBelowChildCandidate` produced at the
  `get low child ;; update_low parent` cut;
- the existing segment/accounting producers around
  `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_suspended_parent_proof`
  and
  `GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_proof`.

Audit point: `FrameInvCandidate` currently stores suspended segment
accounting, not a raw
`ActiveTargetBlocksEscapeAccountedCandidate parent done` field.  If
`ActiveTargetBlocksEscapeAccountedCandidate parent (done_after done child)` is
not derivable from the existing frame and post-child accounting cuts, the
right fix is to refine the framed low-contribution path or frame invariant,
not to re-expand `ChildPostCandidate`.

2026-07-04 implementation check: the audit point is now active.  The framed
child-body post target above is still too early for the parent accounting
facts as currently defined.  In particular, existing producers for
`ParentLowBelowChildCandidate` and
`PendingChildSegmentEscapeAccountedCandidate` are intentionally placed after
the parent continuation step:

```coq
lv <- get' (fun s => low s child);; update_low parent lv
```

Trying to prove `ParentPendingChildEscapeAccountedCandidate parent done child`
and `ActiveTargetBlocksEscapeAccountedCandidate parent (done_after done child)`
immediately after the recursive child body therefore crosses the current
producer/consumer boundary.  The safe route is to stop treating those two
facts as direct `LowContributionPost` fields of the recursive child body.
Instead, keep the recursive low-contribution post child/local:

```coq
PartialRootLowEquationCandidate parent done s /\
fa s child = parent /\
fa s child <> child /\
low s child <= dfn s child
```

and move the parent-accounting production to the tree-branch continuation,
after the parent has read `low child` and updated `low parent`.  That
continuation already has the required frame fields, child post fields,
`ParentLowBelowChildCandidate`, and the existing
`GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_proof`
machinery.

The expected code change is therefore:

- narrow `FramedChildProvidesLowContributionCandidate` and
  `LowCandidateInterface.LowContributionPost` back to the four child/local
  fields;
- remove `BodyProducesLowContributionAccountingCandidate_statement` from the
  body low-contribution assembler;
- keep or add parent-accounting lemmas at the process-edge tree branch, where
  `ProcessEdgeTreeBranchExtendsPhase7SegmentFieldsCandidate_proof` already
  assembles segment accounting, coverage, and active-target blocks after the
  parent update;
- only add a new active-block closure lemma if the existing suspended
  active-block field cannot be closed at that post-update point.

### 3.2 Tail Statement Retirement

After the framed accounting producer is available, remove the
`BodyChildPostTailCandidate_statement` premise from:

```coq
BodyProvidesLowContributionCandidate_from_field_cuts_proof
BodyProvidesLowContributionCandidate_from_phase9_cuts_proof
BodyProvidesLowContributionCandidate_from_frame_phase9_cut_proof
LowCandidateObligations_from_phase9_cuts_proof
LowCandidateLayerCorrect_from_phase9_cuts_proof
```

At that point `BodyChildPostTailCandidate_statement` should either disappear
from the Phase 9 surface or remain only as an unused transitional statement.

### 3.3 Preloop Processed-Children Internalization

Completed:

```coq
PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_proof
```

The transitional external argument has been removed from the Phase 9 assemblers
that previously mentioned:

```coq
PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement
```

Updated consumers:

- `BodyFrameAfterPreloopCandidate_from_processed_cut_proof`
- `BodyPreservesFrameContractCandidate_from_phase9_cuts_proof`
- `BodyPreservesPartialRootLowEquationCandidate_from_frame_cuts_proof`
- `BodyPreservesChildParentPointerCandidate_from_frame_cuts_proof`
- `BodyProvidesLowContributionCandidate_from_frame_phase9_cut_proof`
- `LowCandidateObligations_from_phase9_cuts_proof`
- `LowCandidateLayerCorrect_from_phase9_cuts_proof`

After this edit, the high-level Phase 9 assembler no longer takes the preloop
processed-children parameter.  The only remaining external premise in the
current Phase 9 top-level path is the transitional low-contribution tail:

```coq
BodyChildPostTailCandidate_statement
```

### 3.4 Body Frame-Progress Cut

Completed:

```coq
BodyPreservesFrameProgressContractCandidate_proof
```

This is the auxiliary recursive contract required by the consumer-facing
process-edge frame proof. It preserves:

```coq
FrameProgressCandidate F progress_parent
```

through the full body `tarjan_scc_f g W child` by body-level assembly:

1. Transport `FrameProgressCandidate F progress_parent` through
   `preloop child`.
2. Use `EdgeLoopPreservesFrameProgressCandidate_proof` through the edge loop.
3. Transport the progress fact through `maybe_pop child`.

Important current design detail:

```coq
FrameProgressCandidate F progress_parent s
```

now includes `Visited (frame_parent F) s` in addition to the pending segment
and older-vertex facts. This was added because progress consumers need the
outer frame parent to be a stable old vertex, not merely a term appearing in
an inequality.

## 4. Current Assembly Surface

The current Phase 9 assembly surface is:

```coq
BodySatisfiesChildContractCandidate_from_phase9_cuts_proof
  : BodySatisfiesChildContractCandidate_statement

BodyProvidesLowContributionCandidate_from_frame_phase9_cut_proof
  : BodyChildPostTailCandidate_statement ->
    BodyProvidesLowContributionCandidate_statement

BodyPreservesFrameContractCandidate_from_phase9_cuts_proof
  : BodyPreservesFrameContractCandidate_statement

BodyPreservesFrameProgressContractCandidate_proof
  : BodyPreservesFrameProgressContractCandidate_statement
```

The final low-layer assembly still carries the same transitional premise:

```coq
LowCandidateObligations_from_phase9_cuts_proof
  : BodyChildPostTailCandidate_statement ->
    LowProofObligations LowCandidateInterface
```

Once the framed accounting producer replaces the tail premise, this surface
should become premise-free.

## 5. Verification Status

As of the 2026-07-03 update, the file compiles with:

```bash
eval $(opam env) && make -B -f _tarjan_is_low_only.mk \
  SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.vo
```

The current file has no new `Admitted`, `admit`, or `Axiom`.

Latest proof-level progress:

- `PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_statement` is
  closed by
  `PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_proof`.
- The preloop-related assembly cleanup is closed: high-level Phase 9 no longer
  takes the external preloop parameter and uses the proved lemma directly.
- The body frame contract and frame-progress contract are closed.
- The child recursive post has been narrowed and the concrete child contract is
  closed without parent accounting.
- The remaining true Phase 9 gap is no longer a child-body accounting
  producer.  The remaining work is to move parent accounting to the
  post-update tree-branch continuation and keep the recursive child
  low-contribution post at the four child/local fields.

## 6. Recommended Next Step

Narrow the recursive low-contribution post back to the four child/local
fields, remove the missing `BodyProducesLowContributionAccountingCandidate`
dependency, and finish the parent-accounting assembly in the tree branch after
`get low child ;; update_low parent`.

Do not prove `BodyChildPostTailCandidate_statement` as written unless its
precondition is refined.  Its current naked `ChildEntryCandidate` precondition
is weaker than the parent accounting facts it tries to produce.
