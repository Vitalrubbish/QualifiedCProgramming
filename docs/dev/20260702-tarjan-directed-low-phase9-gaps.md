# Tarjan-Directed-Low-Phase9-Gaps
**Author**: Codex
**Date**: 2026-07-02
**Updated**: 2026-07-05

## 1. Scope

This note records the current Phase 9 status for
`SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`.

2026-07-05 correction: this file is now scoped to proving that the Monad
program maintains low-link values.  SCC-output correctness and the full
Phase7 segment/accounting tail are postponed until after the low-link layer is
stable.  In code, the unresolved active-child accounting branch beginning at
`get_low_update_low_produces_phase7_accounting_after_child` is no longer part
of the compiled low-link path.

The compiled low-only closure currently keeps:

```coq
LoopDonePhase6Candidate
RootLowPrePopCandidate
RootLowOnlyFinalCandidate
LoopDonePhase6RootBridgeCandidate_proof
MaybePopLowOnlyFinalCandidate_proof
```

This is the correct boundary for the low-link file.  The postponed SCC-output
tail still needs a path-sensitive active-child producer, documented in
`20260705-tarjan-directed-low-phase9-path-sensitive-accounting.md`.

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

## 9. 2026-07-05 Combined Low/Closedness Rescope

The low-only core closure in Section 8 is now superseded as the final Phase 9
route.  The latest `chain.md` analysis makes the dependency explicit:
low-link correctness and closedness cannot be proved as two independent
layers.  They form a joint induction over the Monad `visit` body:

- Inside the edge loop, closedness justifies why an already visited
  non-active target contributes nothing to `low`.
- At the pop boundary, the computed low value justifies why the popped segment
  is closed: if an outgoing path reached an older stack vertex, the low value
  would have become strictly smaller than `dfn u`, contradicting the pop guard.

The first bullet is not just an informal skip argument.  In the
visited/non-active branch, the target has already been settled.  The proof
must use the current `DoneClosednessCandidate` to derive that no path starting
from that settled target can reach any current stack vertex.  Therefore the
set of stack `dfn` values reachable through that target is empty, so this edge
has no low-link contribution and the Monad branch may leave `low u`
unchanged.  This is the loop-side direction where low correctness consumes
closedness.

Therefore the final Phase 9 route should return to the already existing
combined invariant spine:

```coq
LoopInvPhase6Candidate
LoopInvPhase7Candidate
FrameInvCandidate
RootFinalCandidate
```

The low-only artifacts may remain as temporary projections, but they should no
longer drive fixed-point closure.  In particular, the final recursive surface
should not be:

```coq
LoopInvLowOnlyCoreCandidate
FrameLowOnlyCoreInvCandidate
LowOnlyCoreFixMode
```

as a standalone proof target.  That surface omits the fields needed to move
`low` across the visited-non-active branch and the pop boundary.

### 9.1 Target theorem shape

The main theorem should target the strong postcondition first:

```coq
Hoare
  (EntryPreCandidate u)
  (tarjan_scc g u)
  (fun _ s => RootFinalCandidate u s)
```

Then the low-only theorem should be recovered as a projection:

```coq
RootFinalCandidate u s -> RootLowOnlyFinalCandidate u s
```

This keeps the user-facing low-link theorem available for later SCC proofs,
but avoids trying to prove it through an invariant that is too weak to support
the program's actual skip/pop reasoning.

### 9.2 Reuse plan

The current source already contains most of the required combined machinery:

- `LoopInvPhase6Candidate` carries low, parent frame resume, done closedness,
  processed-child correctness, and active processed-child summaries.
- `LoopInvPhase7Candidate` extends Phase 6 with segment escape accounting,
  tree coverage, and active-target block accounting.
- `FrameInvCandidate` is the suspended-frame version of the same combined
  information.
- `RootFinalCandidate` already packages global shape, settled closedness,
  visited root, root low correctness, and order facts.
- `BodyPreservesFrameContractCandidate_from_phase9_cuts_proof`,
  `BodyPreservesFrameProgressContractCandidate_proof`, and the
  `LowCandidateInterface` assembly are the intended fixed-point route.

The proof work should therefore be reorganized as:

1. Stop extending the low-only core fixed-point path.
2. Restore the combined `RecursiveCallContractsCandidate` route as the main
   Phase 9 assembly.
3. Ensure the tree-edge branch uses the child recursive post only for
   child-owned facts, then performs the parent `update_low` step to extend
   the combined parent invariant.
4. Keep the visited-active branch as the direct `dfn` contribution to low.
5. Keep the visited-non-active branch as a closedness consumer: it must rely
   on `DoneClosednessCandidate`, not on a low-only skip argument.
6. At loop-done, use the root bridge and pop bridge to produce
   `RootFinalCandidate`.
7. Derive `RootLowOnlyFinalCandidate` as a final projection.

### 9.3 Potential blockers

1. The active-child Phase 7 accounting branch may still be incomplete.
   The combined route needs enough segment/closedness accounting to prove
   pop closedness.  If the current active-child producer remains blocked, the
   strong `RootFinalCandidate` theorem will also block there.

2. The old readiness route is still invalid unless proved through the full
   child body.  Do not revive a tail bridge from `ChildPostCandidate` to
   parent accounting; it loses the parent continuation information.

3. The current low-only core definitions can conflict with the main route by
   suggesting a weaker fixed-point obligation.  They should be treated as
   auxiliary/projection experiments, not as the final proof interface.

4. `RootFinalCandidate` includes `SettledClosedCandidate`.  That is stronger
   than a pure low theorem, but it is exactly the post-pop closedness needed by
   the joint induction.  The proof must distinguish this from full SCC-output
   correctness: settled closedness is required; component maximality/output
   correctness can still remain a later theorem.

5. Existing Section 6 and Section 7 notes still discuss a path-sensitive
   active-child accounting producer.  Under the combined route this producer
   is not optional if Phase 7 accounting is still required for pop closedness.
   The plan avoids low-only dead ends, but it does not magically remove that
   accounting obligation.

6. Some compiled low-only lemmas may become stale after the main theorem is
   retargeted.  Prefer leaving them unused until the combined theorem compiles;
   only delete or rewrite them after confirming they are not needed as
   low-only projections.
