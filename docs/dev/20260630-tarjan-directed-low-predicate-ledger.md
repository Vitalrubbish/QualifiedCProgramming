# Tarjan-Directed-Low-Predicate-Ledger
**Author**: Codex
**Date**: 2026-06-30

## 1. 目标

本文档继续 `Tarjan_scc_is_low.v` 中的 theorem skeleton，设计各个未知 predicate 的语义 ledger。

原则：

- 只把 Tarjan 程序结构和 `SCCSt` 字段视为已知；
- 不默认复用任何旧 low-link 中间定义；
- 每个 predicate 先给出 meaning / producer / consumer / lifetime；
- 之后再决定是否映射到现有定义。

Tarjan body：

```coq
preloop u;;
forset (fun a => dg_step g u a) (process_edge u W);;
If (fun s => low s u = dfn s u) (pop_scc u)
```

State fields：

```coq
visited : V -> Prop
timer   : nat
fa      : V -> V
dfn     : V -> nat
low     : V -> nat
stack   : list V
sccs    : list (V -> Prop)
```

## 2. Top-Level Interface Ledger

### 2.1 `EntryPre u s`

Meaning:

`tarjan_scc g u` 的 low-layer recursive entry。`u` 尚未访问，已有 DFS / stack / dfn / settled 区域满足可继续递归的全局条件。

Required semantic fields:

```coq
EntryPre u s :=
  GlobalShapePre u s /\
  SettledClosed s /\
  OrderFacts s.
```

Producer:

- root/public caller；
- parent `process_edge` 的 unvisited-child branch 在 `set_fa child parent` 后为 child 产生。

Consumer:

- `preloop u`。

Lifetime:

- entry only；`preloop` 后由 `LoopEntry` 替代。

Pop-stability:

- not applicable。

Candidate existing mapping:

- `GlobalShapePre u s` may map to `wf_scc_state_pre g root u s`;
- its stable component `GlobalShape s` may map to `wf_scc_state g root s`;
- `SettledClosed s` may map to `settled_closed g s`;
- `OrderFacts s` may map to `stack_dfn_order s /\ dfn_injective s`.

Audit questions:

- `GlobalShape` 是否应该包含 `settled_closed`？当前建议不包含，避免把 low-layer closedness 混入 DFS structural invariant。
- parent 在 `set_fa child parent` 后能产生的是 `GlobalShapePre child`，不是“裸”的 `Unvisited child` 旁边附加 `GlobalShape` 的无结构 bundle。
- `set_fa child parent` 保持 `GlobalShapePre child` 需要 `Visited parent s`；这是 `fa_visited` 字段的生产条件。

### 2.2 `RootFinal u s`

Meaning:

`tarjan_scc g u` final-state post。只描述 root `u` 的最终 low correctness，不要求整棵 DFS subtree 的 stack-sensitive correctness。

Required semantic fields:

```coq
RootFinal u s :=
  GlobalShape s /\
  SettledClosed s /\
  Visited u s /\
  RootLowCorrectFinal u s /\
  OrderFacts s.
```

Producer:

- `MaybePopFinal`。

Consumer:

- fixed-point `LowRootMode` post；
- public projection theorem。

Lifetime:

- final state；must be stable after optional `pop_scc u`。

Pop-stability:

- yes, by definition or by root-pop bridge。

Candidate existing mapping:

- `RootFinalLowValid u s` maps to `scc_low_valid_v g root s u`.
- `RootFinalIsLow u s` maps to `scc_is_low_v g root s u`.
- The two fields must remain separate in the producer ledger: low-valid has an
  existing `pop_scc` producer, while root is-low still needs its own pop-side
  reconstruction proof.

Audit questions:

- If `u` is popped, can existing `scc_low_valid_v u` still hold in final state?
- If not, should final correctness be weakened to `scc_is_low_v u`, or should `scc_is_low_v u` be redefined / proved root-pop-stable by the guard `low u = dfn u`?

Phase-7c candidate:

```coq
RootFinalLowValidCandidate u s :=
  scc_low_valid_v g root s u

RootFinalIsLowCandidate u s :=
  scc_is_low_v g root s u

RootFinalCorrectCandidate u s :=
  RootFinalLowValidCandidate u s /\
  RootFinalIsLowCandidate u s

RootFinalCandidate u s :=
  GlobalShapeCandidate s /\
  SettledClosedCandidate s /\
  Visited u s /\
  RootFinalCorrectCandidate u s /\
  OrderFactsCandidate s
```

Audit result:

- Keeping both final low-valid and final is-low is justified by consumers:
  parent continuation needs low-valid, while the public/root post needs is-low.
- They must not be hidden behind one monolithic producer.  Phase 7c now splits
  the pop bridge into low-valid/stable fields, settled-closed, and root-is-low
  components.
- The low-valid/stable-fields component is proved by
  `RootPopLowValidStableFieldsCandidate_proof`.
- The settled-closed component is proved by
  `RootPopSettledClosedCandidate_proof`, using the fact that vertices removed
  by `stack_split_at` are exactly the root popped segment covered by
  `PoppedSegmentClosedCandidate`.
- The root is-low component is proved by
  `RootPopIsLowCandidate_proof` from the narrowed input
  `RootPopIsLowInputCandidate`: `Active u`, pre-pop
  `RootIsLowPrePopCandidate u`, and `root_pop_guard u`.  It does not consume
  final low-valid, segment closure, or the full `LoopDonePhase7Candidate`.
  The proof shows that post-pop `scc_low_tree u` is a subset of the pre-pop
  low-tree, and the guard `low u = dfn u` lets `u` itself witness the post-pop
  minimum.

### 2.3 `RootLowPrePop u s`

Meaning:

Root correctness just after edge loop and before optional pop. This is the phase where stack-sensitive back-edge explanations are still valid.

Required semantic fields:

```coq
RootLowPrePop u s :=
  RootLowValidPrePop u s /\
  RootIsLowPrePop u s

RootBridgeInput u s :=
  LocalActiveRoot u s /\
  DoneClosedness u (edge_set u) s /\
  ParentFrameResume u (edge_set u) s /\
  RootLowEquationReady u s /\
  RootTreeChildrenLowValidReady u s /\
  RootTreeChildrenIsLowReady u s /\
  OrderFacts s
```

Producer:

- `RootBridge` from `LoopDone u s`。

Consumer:

- `MaybePopFinal`；
- root-pop bridge。

Lifetime:

- pre-pop only。

Pop-stability:

- not assumed。

Audit questions:

- Which part is needed to prove root low-valid?
- Which part is needed to prove root is-low?
- Does `RootLowPrePop` need both, or can one be derived from the other at this phase?

Phase-7a/7b result:

- The Coq skeleton separates root bridge input from root pre-pop correctness:
  `LoopDonePhase6Candidate` projects to `RootBridgeInputCandidate`.
- The common input is further split into consumer-facing halves:
  - `RootBridgeLowValidInputCandidate`, consumed by the low-valid bridge;
  - `RootBridgeIsLowInputCandidate`, consumed by the is-low bridge.
- The projection proofs are complete:
  `LoopDoneProvidesRootBridgeInputCandidate_proof`.
- The adapter proof
  `RootBridgeLowValidInputBuildsLowIterationDoneCandidate_proof` shows that
  the low-valid half is exactly enough to build the existing pure
  `low_iteration_done` interface.
- `RootBridgeLowValidCandidate_proof` reuses
  `low_frontier_and_src_imply_low_valid`.
- `RootBridgeIsLowCandidate_proof` reuses
  `scc_is_low_induction_is_low`.
- `ParentFrameResumeCandidate` is part of `RootBridgeInputCandidate` because
  the is-low bridge must turn a DFS-tree child from `tree_step_char` into an
  original outgoing edge before applying `RootTreeChildrenIsLowReadyCandidate`.
- `RootBridgePrePopCandidate_proof` now closes using the proved low-valid and
  is-low halves.

## 3. Loop Predicate Ledger

### 3.1 `LoopInv u done s`

Meaning:

State after `preloop u` and after processing exactly the outgoing edges in `done`.

Proposed semantic decomposition:

```coq
LoopInv u done s :=
  LocalActiveRoot u s /\
  DoneDiscipline u done s /\
  ParentTreeDiscipline u done s /\
  PartialRootLowEquation u done s /\
  ProcessedTreeChildrenCorrect u done s /\
  SegmentEscapeAccounting u done s /\
  SegmentCoverageByDone u done s /\
  ActiveProcessedChildSummary u done s /\
  OrderFacts s.
```

Producer:

- `preloop` initializes it at `done = empty`;
- `process_edge` extends it from `done` to `done ∪ [a]`。

Consumer:

- next `process_edge` step；
- `RootBridge` when `done = edge_set u`；
- `SegmentClosedAtRoot` when `done = edge_set u` and `low u = dfn u`；
- `FrameInv` for suspended outer parent。

Lifetime:

- from after `preloop` until before `maybe_pop`；
- parts may be transported through child recursive calls by frame contract；
- not a final post after pop。

Pop-stability:

- no; only selected consequences survive via `MaybePopFinal`。

Phase-3 base audit:

Before committing to the full decomposition above, the current Coq skeleton
uses a narrower base candidate:

```coq
LoopInvBaseCandidate u done s :=
  LocalActiveRootCandidate u s /\
  DoneEmptyCandidate done.
```

This candidate is intentionally weaker than final `LoopInv`.  Its only audited
consumers are:

- initialization from `LoopEntryBaseCandidate` at `done = empty`;
- providing the parent active facts needed by the unvisited branch before
  `set_fa child u`.

It deliberately does not include:

- partial low equation;
- processed child correctness;
- segment accounting or coverage;
- active child segment summaries.

These fields must be introduced only when their own consumers are audited.

### 3.2 `LocalActiveRoot u s`

Meaning:

The current root `u` has been initialized by `preloop` and remains active.

Fields:

```coq
Visited u s /\
Active u s /\
GlobalShape s /\
SettledClosed s /\
OrderFacts s
```

Where:

```coq
Active u s := In u (stack s).
```

Producer:

- `preloop` sets `dfn u`, `low u`, pushes `u`, visits `u`;
- recursive body / process_edge must preserve it until `maybe_pop u`。

Consumer:

- root low equation self case；
- branch classification for visited-stack edge；
- segment definition rooted at `u`；
- pop guard。

Lifetime:

- loop only；after pop, `u` may no longer be active。

Audit questions:

- Does `process_edge` ever pop `u` indirectly through recursive child? It should not; if child pop removes `u`, the invariant is invalid.
- Need an ancestor-stack-frame lemma ensuring recursive child calls preserve ancestors on stack.

Phase-3 audit result:

- `LocalActiveRootCandidate` has been proved as a consequence of
  `LoopEntryBaseCandidate`.
- It is sufficient to provide `ParentActiveBaseCandidate parent` for the
  unvisited branch's `set_fa child parent` producer audit.
- Low initialization `low u = dfn u` remains in `LoopEntryBaseCandidate`, but
  is not included in `LocalActiveRootCandidate` until the low-equation consumer
  is introduced.

### 3.3 `DoneDiscipline u done s`

Meaning:

`done` tracks the outgoing edge targets of `u` that have already been considered by `forset`.

Fields:

```coq
DoneSubsetOfOutgoing u done /\
DoneVisited done s
```

Producer:

- empty at `preloop`;
- each `process_edge` adds current target `a`。

Consumer:

- non-stack branch closedness；
- root bridge when `done = edge_set u`；
- segment escape accounting pending-edge exclusion。

Lifetime:

- loop only。

Audit questions:

- `forset` may represent `done` extension extensionally; all fields need proper lemmas under `done == done'`.
- `DoneVisited` for unvisited branch is only true after recursive call returns.

Phase-4 audit result:

- The current Coq skeleton introduces:

```coq
DoneSubsetOfOutgoingCandidate u done
DoneVisitedCandidate done s
DoneDisciplineCandidate u done s
LoopInvDoneCandidate u done s
```

- Empty initialization is proved by `DoneDisciplineCandidate_empty_proof`.
- Single-edge pure extension is proved by
  `DoneDisciplineCandidate_step_proof`, assuming `Edge u a` and
  `Visited a s`.
- `LoopInvDoneCandidate` still provides the unvisited branch's `set_fa`
  precondition, proved by `LoopInvDoneConsumesUnvisitedSetFaCandidate_proof`.
- Reachability closedness and tree-child closedness are not included yet; they
  require separate consumers from non-stack branch and child-post analysis.

Phase-4b branch-integration result:

- The actual `process_edge u W a` program cut extends done discipline under
  two callback assumptions:

```coq
ChildReturnsVisitedCandidate W
ChildPreservesDoneVisitedCandidate W
```

- `ChildReturnsVisitedCandidate W` is the unvisited-branch child contract:
  after `set_fa child parent`, the recursive call returns with `Visited child`.
- `ChildPreservesDoneVisitedCandidate W` is the frame contract fragment needed
  by the parent loop: already processed `done` targets remain visited through
  the recursive child call.
- The skeleton proves:

```coq
ProcessEdgeProducesVisitedTargetCandidate_proof
ProcessEdgeExtendsDoneDisciplineCandidate_proof
```

- This confirms that `DoneDisciplineCandidate` itself only needs outgoing-edge
  membership and visitedness.  Low equations, reachability closedness,
  tree-child closedness, and segment facts remain outside this predicate until
  their own consumers are audited.

### 3.4 `ParentTreeDiscipline u done s`

Meaning:

The DFS parent relation around `u` is consistent with processed/unprocessed edge state.

Required capabilities:

```coq
TreeChildOfU v s -> edge u v
UnprocessedFaChildImpossible:
  ~ done v -> fa s v = u -> v = u
TreeChildCharacterization:
  tree_edge u v in state_to_dfs_tree -> fa s v = u /\ fa s v <> v
```

Producer:

- global DFS shape plus `set_fa` in unvisited branch；
- process_edge done-extension preserves the discipline。

Consumer:

- root bridge: identify direct DFS-tree children of `u`;
- visited branch: prove newly added visited target is not a new tree child unless handled by recursive branch;
- child post: parent pending/resume facts。

Lifetime:

- loop only, plus frame preservation for outer parent。

Audit questions:

- `fa child = parent` is set before child `preloop`; does `state_to_dfs_tree` include only visited vertices? If yes, pending child is not yet a tree edge until visited.
- The discipline should not require dfn order for an unvisited pending child before `preloop child`。

### 3.5 `PartialRootLowEquation u done s`

Meaning:

`low u` is the minimum justified by:

- self `dfn u`;
- processed tree children through their `low child`;
- processed back/cross edges whose targets are active stack vertices;
- no unprocessed edge has yet been accounted for.

Interface:

```coq
PartialRootLowEquation u done s
```

must provide, when `done = edge_set u`:

```coq
RootLowEquation u s.
```

Phase-5 first candidate:

```coq
LowFrontierCandidate u done s :=
  low s u <= dfn s u /\
  forall a,
    done a ->
    Edge u a ->
    (fa s a = u -> low s u <= low s a) /\
    (Active a s -> low s u <= dfn s a)

LowSourceCandidate u done s :=
     low s u = dfn s u
  \/ exists a,
       done a /\ Edge u a /\
       fa s a = u /\ fa s a <> a /\
       low s u = low s a
  \/ exists a,
       done a /\ Edge u a /\
       Active a s /\ fa s a <> u /\
       low s u = dfn s a

PartialRootLowEquationCandidate u done s :=
  LowFrontierCandidate u done s /\
  LowSourceCandidate u done s
```

This split is consumer-derived:

- `LowFrontierCandidate` is the lower-bound side needed by the eventual
  root bridge.
- `LowSourceCandidate` records why the current low value is still anchored in
  a concrete processed contributor.
- Child correctness, reachability closedness, parent-tree discipline, and
  segment accounting are deliberately outside this predicate.

Producer:

- `preloop`: initialized by self case, `low u = dfn u`;
- unvisited child branch: after child returns, update `low u` with `low child`;
- visited active branch: update `low u` with `dfn a`;
- visited non-stack branch: no low contribution。

Consumer:

- root low-valid part of `RootBridge`;
- segment escape accounting may also use source/anchor information。

Lifetime:

- pre-pop root phase。

Audit questions:

- Should this be represented as an exact min equation, or as lower-bound plus source witness?
- Existing split into frontier/source is only a candidate; the required interface is the ability to derive `RootLowEquation` at loop done and to update branch-by-branch.

Phase-5 first audit result:

- The skeleton proves:

```coq
LowFrontierCandidate_empty_proof
LowSourceCandidate_empty_proof
PartialRootLowEquationCandidate_empty_proof
LoopEntryImpliesPartialLowCandidate_proof
LoopEntryImpliesLowCandidate_proof
LowFrontierCandidate_step_proof
LowSourceCandidate_step_keep_proof
LowSourceCandidate_step_tree_proof
LowSourceCandidate_step_stack_proof
PartialRootLowEquationCandidate_step_keep_proof
```

- These are pure ledger proofs.  They do not yet prove that
  `process_edge u W a` supplies the branch bounds or branch source equality
  after `update_low`.
- The next audit must decide, branch by branch, which source case survives:
  old source, new tree child source, or new active stack target source.

Phase-5b primitive-producer audit result:

- The skeleton now audits `update_low u n` as the only primitive that changes
  `low u`.
- It proves:

```coq
UpdateLowBoundedByOldCandidate_proof
UpdateLowBoundedByIncomingCandidate_proof
UpdateLowSourceCandidate_proof
UpdateLowKeepsSnapshotFieldsCandidate_proof
UpdateLowPreservesFrontierWithIncomingBound_proof
```

- The important design outcome is that branch proofs should not unfold the
  entire low predicate.  They only need to supply an incoming contribution
  bound `n` and then reuse the primitive audit to transport the frontier.
- Source selection remains branch-local:
  - tree branch: incoming source may become `low child`;
  - active-stack branch: incoming source may become `dfn a`;
  - non-stack branch: no `update_low`, so source is preserved.

Phase-5b composite-cut audit result:

- The skeleton lifts primitive `update_low` facts through the two concrete
  low-update command shapes:

```coq
lv <- get' (fun s => low s a);; update_low u lv
dv <- get' (fun s => dfn s a);; update_low u dv
```

- It proves:

```coq
UpdateLowPreservesFrontierCandidate_proof
UpdateLowSourceOrIncomingCandidate_proof
GetLowUpdateLowExtendsFrontierTreeCandidate_proof
GetDfnUpdateLowExtendsFrontierStackCandidate_proof
GetLowUpdateLowProducesTreeSourceCandidate_proof
GetDfnUpdateLowProducesStackSourceCandidate_proof
```

- The remaining work is not about `update_low`; it is the surrounding
  `process_edge` branch integration:
  - tree branch must provide `fa a = u`, `fa a <> a`, and the child-side
    low bound needed before the `get_low/update_low` composite cut;
  - active-stack branch must provide `Active a` and `fa a <> u`;
  - non-stack branch must preserve the old partial low equation unchanged
    while still extending `done`.

Phase-5b branch integration result:

- The tree branch now has a dedicated cut:

```coq
ProcessEdgeTreeBranchExtendsPartialLowCandidate_statement
ProcessEdgeTreeBranchExtendsPartialLowCandidate_proof
```

- The top-level `process_edge` partial-low cut is now proved by
  `ProcessEdgeExtendsPartialLowCandidate_proof`.
- `set_fa` is no longer treated as an implicit preservation step; the ledger
  records the explicit dependency `SetFaPreservesPartialLowCandidate_proof`
  because the child call needs the parent partial-low facts after parent-child
  linking.
- This confirms that the minimal Phase-5b consumer is the branch-local
  partial-low update, not a broader closedness or segment predicate.

### 3.6 `ProcessedTreeChildrenCorrect u done s`

Meaning:

Every processed direct DFS-tree child of `u` has enough root-level low correctness for `u`'s root bridge.

Interface:

```coq
ProcessedTreeChildrenCorrect u done s :=
  ProcessedTreeChildrenLowValid u done s /\
  ProcessedTreeChildrenIsLow u done s /\
  ProcessedTreeChildrenInactiveSelfLow u done s

ProcessedTreeChildrenLowValid u done s :=
  forall v,
    done v ->
    DirectTreeChild u v s ->
    ChildLowValidForParent v s

ProcessedTreeChildrenIsLow u done s :=
  forall v,
    done v ->
    DirectTreeChild u v s ->
    ChildIsLowForParent v s

ProcessedTreeChildrenInactiveSelfLow u done s :=
  forall v,
    done v ->
    DirectTreeChild u v s ->
    ChildInactiveSelfLowForParent v s

ChildInactiveSelfLowForParent v s :=
  ~ Active v s -> low s v = dfn s v
```

Producer:

- unvisited child recursive post；
- visited non-stack/active branch must prove the new target is not a new direct tree child, or already has the needed correctness。
- child post also produces the inactive-self-low component needed if the child
  is later popped by an inner `maybe_pop` before the parent root bridge.

Consumer:

- root low-valid bridge at `done = edge_set u` consumes the low-valid half;
- root is-low bridge at `done = edge_set u` consumes the is-low half;
- frame-pop transport consumes the inactive-self-low component for processed
  children that no longer remain active after the pop.  Active processed
  children instead use the lower-anchor preservation argument.

Lifetime:

- loop and frame；
- pre-pop parent resource, not final whole-subtree post。

Pop-stability:

- only required across inner child pop if `ChildRootCorrectForParent` is final-state root correctness for child。

Audit questions:

- Is child final root correctness sufficient for parent root bridge, or does parent need child pre-pop stack-sensitive `low` equation?
- Parent uses `low child` after child returns, so low value must remain meaningful even if child was popped.

### 3.7 `SegmentEscapeAccounting u done s`

Meaning:

Every possible escape from the current stack segment rooted at `u` to an unvisited vertex is explained either by an unprocessed outgoing edge of `u` or by an older active stack anchor.

Interface:

```coq
SegmentEscapeAccounting u done s
```

must support:

```coq
SegmentClosedAtRoot:
  LoopDone u s ->
  low s u = dfn s u ->
  PoppedSegmentClosed u s.
```

Producer:

- empty-done base case after `preloop`;
- non-stack branch removes pending escape through settled closedness;
- active ancestor branch creates old-stack anchor;
- active descendant branch uses child segment summary;
- unvisited child branch uses child closedness / segment summary。

Consumer:

- active descendant branch；
- `SegmentClosedAtRoot` before pop。

Lifetime:

- loop and frame, consumed by pop。

Phase-7 segment audit result:

- `LoopInvPhase7Candidate` currently adds only
  `SegmentEscapeAccountingCandidate u done s` to `LoopInvPhase6Candidate`.
- `SegmentClosedAtRootCandidate_proof` shows that at `done = edge_set u`,
  escape accounting plus `low s u = dfn s u` is enough to prove
  `PoppedSegmentClosedCandidate`.
- The proof uses the two alternatives in escape accounting:
  pending root escapes are impossible because every outgoing edge is done;
  old-stack anchors are impossible because `low u = dfn u` contradicts
  `dfn b < dfn u` and `low u <= dfn b`.
- `SegmentCoverageByDoneCandidate` is not included in this pop-specific loop
  extension.  It remains a candidate for the active-descendant branch, but it
  currently has no pop consumer.

Producer-audit refinement:

- The original empty producer `forall u s, SegmentEscapeAccounting u empty s`
  was too strong.
- The empty producer now requires:

```coq
LocalActiveRootCandidate u s
RootSegmentInitialCandidate u s
```

- `RootSegmentInitialCandidate` says every active vertex in the initial root
  dfn segment is the root itself.  This is an entry-only fact that should be
  produced by the preloop/loop-entry audit, not assumed for arbitrary states.
- `SegmentEscapeAccountingCandidate_empty_proof` is proved from these inputs.
- The child-step producer is factored through the consumer-minimal
  `ParentPendingChildEscapeAccountedCandidate u done child s`, not through a
  whole child summary.  The only stale case when moving from `done` to
  `done_after done child` is an old pending escape whose root edge is exactly
  `child`; the new fact explains that case under the extended `done`.
- `ChildSegmentEscapeLiftsToParentCandidate_proof` and
  `SegmentEscapeAccountingCandidate_step_child_proof` are proved from this
  parent-pending fact.
- `ParentPendingChildEscapeAccountedCandidate_from_closed_proof` proves the
  popped-child producer: if `ChildClosednessContribution child s` and
  `~ Active child s`, then the stale pending case is impossible because every
  vertex reachable from `child` is already visited.
- `ParentPendingChildEscapeAccountedCandidate_from_old_anchor_proof` proves
  the active older-anchor producer: if `child` is active, `dfn child < dfn u`,
  and the parent low value has been lowered to `low u <= dfn child`, then
  `child` itself is an old stack anchor for every escape through it.
- The active-descendant producer is now factored through
  `ChildSelfPendingEscapeAccountedCandidate`.  The proved lemma
  `ParentPendingChildEscapeAccountedCandidate_from_active_descendant_proof`
  lifts child-root accounting to any parent segment vertex `x` satisfying the
  actual step-consumer assumptions (`Active x` and `dfn u <= dfn x`).
- Remaining proof debt is therefore narrower: produce
  `ChildSelfPendingEscapeAccountedCandidate` from child segment
  coverage/summary for the self-cycle case `child ->* u -> child ->* w`.

Audit questions:

- Does accounting need to mention all segment vertices, or only vertices reachable from `u` within processed children?
- Existing `segment_escape_accounted` is a candidate; verify it exactly supports the pop proof and descendant branch.

### 3.7.1 `ParentPendingChildEscapeAccounted u done child s`

Meaning:

When extending `done` with `child`, any old pending escape whose first root
edge is exactly `child` is still explainable under `done_after done child`.

Interface:

```coq
forall x w,
  Active x s ->
  dfn u <= dfn x ->
  reachable x u ->
  reachable child w ->
  ~ Visited w s ->
  PendingRootEscape u (done_after done child) s x w \/
  OldStackEscapeAnchor u s x w
```

Producer:

- popped child: `ChildClosednessContribution child s` plus `~ Active child s`;
- active older stack edge: parent low update gives `low u <= dfn child` with
  `dfn child < dfn u`;
- active descendant: parent lift is proved from parent accounting plus
  `ChildSelfPendingEscapeAccountedCandidate`.

Consumer:

- `SegmentEscapeAccountingCandidate_step_child_proof`.

### 3.7.2 `ChildSelfPendingEscapeAccounted u done child s`

Meaning:

The remaining active-descendant corner case: from the child segment, an escape
first reaches back to parent root `u`, then goes again through the child root
edge.  Once `child` is added to `done`, that direct pending edge is stale and
must be re-explained.

Interface:

```coq
forall w,
  reachable child u ->
  reachable child w ->
  ~ Visited w s ->
  PendingRootEscape u (done_after done child) s child w \/
  OldStackEscapeAnchor u s child w
```

Producer:

- `ChildSelfPendingEscapeAccountedCandidate_from_child_summary_proof` is
  proved from:
  - `ChildSegmentSummaryCandidate child s`;
  - `ChildOldAnchorLiftsToParentCandidate u done child s`.
- The child-local pending-root branch is impossible at child loop-done:
  `ChildSegmentSummaryCandidate` uses
  `SegmentEscapeAccountingCandidate child (edge_set child) s`, and
  `edge_set child` is definitionally the same outgoing-edge predicate as
  `Edge child`.
- This confirms that the remaining non-vacuous vocabulary conversion is the
  child old-anchor lift.

Consumer:

- `ParentPendingChildEscapeAccountedCandidate_from_active_descendant_proof`.

### 3.7.3 Rejected: `ChildPendingRootEscapeLiftsToParent u done child s`

Meaning:

This predicate was introduced to explain a pending escape in the child's root
vocabulary using a parent root edge `u -> ?` under `done_after done child`, or
by a parent old-stack anchor.

The audit rejected it as a real dependency.  The only consumer used it after
`ChildSegmentSummaryCandidate child s`, whose segment accounting is already at
`done = edge_set child`.  Therefore the pending-root branch would require both
`Edge child a` and `~ edge_set child a`, which is contradictory because
`edge_set child a` is `dg_step g child a`, the same predicate wrapped by
`Edge child a`.

Interface:

```coq
forall a w,
  reachable child u ->
  Edge child a ->
  ~ edge_set child a ->
  reachable a w ->
  ~ Visited w s ->
  PendingRootEscape u (done_after done child) s child w \/
  OldStackEscapeAnchor u s child w
```

Producer:

- none needed; the predicate was removed from
  `ChildSelfPendingEscapeAccountedCandidate_from_child_summary_statement`.
- The former `ChildPendingRootEscapeLiftCaseCandidate` debt was not a missing
  theorem. It was an artifact of an impossible branch.

Consumer:

- none. If a future design uses a child summary at a strict partial `done`
  rather than `edge_set child`, this predicate must be redesigned from that
  consumer and re-audited.

### 3.7.4 `ChildOldAnchorLiftsToParent u done child s`

Meaning:

A child-local old anchor `b` must become either a parent pending escape or a
valid parent old-stack anchor.

Producer:

- `ChildOldAnchorLiftsToParentCandidate_from_all_older_proof` is proved as a
  sufficient condition:
  `low u <= low child`, and every child old anchor candidate is older than
  `u`.
- This sufficient condition may later be produced by the concrete
  active-descendant branch after `update_low u (dfn/low child)`, or refined if
  it is still too strong.

Consumer:

- `ChildSelfPendingEscapeAccountedCandidate_from_child_summary_proof`.

### 3.8 `SegmentCoverageByDone u done s`

Meaning:

Every active vertex in the stack segment rooted at `u` is reachable from `u` through already processed child subsegments, or is `u` itself.

Interface:

```coq
SegmentCoverageByDone u done s
```

Producer:

- empty base after `preloop`: only `u` is in the segment or no processed descendants;
- unvisited active child branch adds child segment coverage;
- other branches preserve / monotonically extend。

Consumer:

- active descendant branch: locate which processed child segment contains the target;
- segment closure at pop。

Lifetime:

- loop and frame。

Audit questions:

- Is this independent from escape accounting, or should a combined segment summary replace both?
- Does stack order make the segment boundary `dfn u <= dfn x` stable under child pop?

### 3.9 `ActiveProcessedChildSummary u done s`

Meaning:

For every processed direct tree child of `u` that is still active, parent has a summary sufficient to reason about that child's stack segment.

Interface:

```coq
ActiveProcessedChildSummary u done s :=
  forall child,
    done child ->
    DirectTreeChild u child s ->
    Active child s ->
    ChildSegmentSummary child s.
```

Producer:

- child recursive post, conditional on `child` remaining active after its own `maybe_pop`。

Consumer:

- active descendant branch；
- segment coverage / escape accounting lifting。

Lifetime:

- only while child remains in stack。

Pop-stability:

- no; guard with `Active child s`。

Audit questions:

- Should `ChildSegmentSummary child s` be full `LoopDone child s`, or only segment accounting + coverage + root active facts?
- Prefer a weaker summary if full child loop invariant contains facts not needed by parent.

### 3.10 `OrderFacts s`

Meaning:

Stable dfn/stack side conditions needed for branch classification and min/root proofs.

Fields:

```coq
StackDfnOrder s /\
DfnInjective s /\
DfnBounds s
```

Producer:

- entry caller；
- preloop/process_edge/pop preserve。

Consumer:

- classify visited stack target as ancestor/descendant；
- root bridge tree-child dfn ordering；
- stack segment boundary lemmas；
- final post side conditions。

Lifetime:

- whole call。

Audit questions:

- Existing `stack_dfn_order` and `dfn_injective` may be enough; if root bridge needs timer bounds, include them explicitly or derive from `GlobalShape`。

## 4. Child Predicate Ledger

### 4.1 `ChildEntry parent child done s`

Meaning:

State immediately after `set_fa child parent` in the unvisited branch, before recursive call `W child`.

Required fields:

```coq
ChildEntry parent child done s :=
  ParentLoopSuspended parent child done s /\
  ChildReadyToPreloop parent child s.
```

`ChildReadyToPreloop`:

```coq
GlobalShapePre child s /\
SettledClosed s /\
Visited parent s /\
edge parent child /\
fa s child = parent /\
OrderFacts s.
```

Producer:

- `process_edge` unvisited branch after `set_fa child parent`。

Consumer:

- recursive `ChildContract W`；
- recursive body `preloop child`。

Lifetime:

- child entry only。

Audit questions:

- `set_fa child parent` 的字段级 producer 必须先证明：
  - `GlobalShape + Visited parent + Unvisited child` produces `GlobalShapePre child + Visited parent`;
  - `SettledClosed` is preserved;
  - `OrderFacts` is preserved;
  - parent active/context facts needed by the suspended loop are preserved.
- If `fa child = parent` while child unvisited, `GlobalShapePre child` is the correct entry shape. It should map to `wf_scc_state_pre child`, because existing `fa_visited` requires the parent pointer target to be visited even before `child` itself is visited.

Audit result:

- These producer obligations are proved in `Tarjan_scc_is_low.v` by the
  `Preloop..._proof` and `SetFa..._proof` lemmas.
- `~ done child` and `edge parent child` are not state facts produced by
  `set_fa`; they are branch side conditions threaded through the Hoare proof.

### 4.2 `ChildPost parent child done s`

Meaning:

What parent needs after recursive child call returns.

Required fields:

```coq
ChildPost parent child done s :=
  ParentResumeShape parent child done s /\
  ChildLowValidForParent child s /\
  ChildIsLowForParent child s /\
  ChildClosednessContribution child s /\
  (Active child s -> ChildSegmentSummary child s).
```

Producer:

- fixed-point child mode;
- recursive body theorem。

Consumer:

- unvisited branch extension of parent `LoopInv`。

Lifetime:

- parent loop after child return。

Audit questions:

- `ChildRootCorrectForParent` must be final-state child correctness if child may have popped.
- `ChildSegmentSummary` is only available when child remains active.
- `ParentResumeShape` should include only facts actually needed to resume parent loop; avoid bundling whole parent loop invariant if too strong.

Phase-6 refinement:

- Treat the following as separate consumer-led subinterfaces before accepting
  the combined `ChildPost` bundle:

```coq
ChildLowValidForParentCandidate child s
ChildIsLowForParentCandidate child s
ChildClosednessContributionCandidate child s
ChildSegmentSummaryCandidate child s
ParentResumeShapeCandidate parent child done s
```

- The combined `ChildPost` bundle is only justified if all subinterfaces
  are individually consumer-necessary.
- If one of them has no distinct consumer, it should be dropped rather than
  kept for symmetry.
- The skeleton proves the consumer-side empty and step lemmas that show these
  child-post fields extend the Phase 6 loop fields.

### 4.3 `ChildLowValidForParent child s` and `ChildIsLowForParent child s`

Meaning:

The child has enough root-level low correctness to be used as a processed tree
child in the parent's root bridge.

Minimum capabilities:

```coq
ChildLowValidForParent child s
ChildIsLowForParent child s
```

Producer:

- child's `RootFinal`。

Consumer:

- parent `PartialRootLowEquation` extension via `low child` consumes the
  low-valid side only where the root bridge needs it;
- parent `ProcessedTreeChildrenCorrect` stores the low-valid and is-low halves
  separately。

Pop-stability:

- yes for child root, by child final theorem。

Audit questions:

- Does parent need existing `scc_low_valid_v`, existing `scc_is_low_v`, or a
  custom root summary?
- If child was popped, existing stack-sensitive low-valid may not hold; use a pop-stable child root summary instead.
- Current recommendation: do not bake `scc_low_valid_v` into the child root
  summary unless a later consumer explicitly needs the full stack-sensitive
  relation.

### 4.4 `ChildClosednessContribution child s`

Meaning:

Child-local fact needed to extend parent done-closedness after processing child.

Required capability:

```coq
~ Active child s -> forall v, reachable child v -> Visited v s
```

This is deliberately child-local.  Parent-specific extension to
`done ∪ [child]` is a separate consumer audit:

```coq
DoneClosedness parent done s ->
ParentResumeShape parent child done s ->
ChildClosednessContribution child s ->
DoneClosedness parent (done ∪ [child]) s
```

Producer:

- child final post and `SettledClosed`;
- child pop segment closure if child popped;
- if child remains active, contribution may be deferred to active segment summary.

Consumer:

- parent non-stack/closedness reasoning；
- parent `LoopInv` done extension。

Audit questions:

- Need to distinguish active child vs popped child.
- A single unconditional closedness statement may be too strong if child remains active.
- If the parent only needs closedness after the child has popped, split this
  from any active-child segment summary and keep the pop-sensitive part here.

## 5. Frame Predicate Ledger

### 5.1 `FrameInv F s`

Meaning:

Facts about an outer parent loop that must survive while an inner recursive call runs.

Suggested shape:

```coq
Record SuspendedFrameCandidate := {
  frame_parent : V;
  frame_child  : V;
  frame_done   : V -> Prop
}.

FrameInv F s :=
  ParentResumeShape
    (frame_parent F) (frame_child F) (frame_done F) s /\
  LoopInvLow
    (frame_parent F) (frame_done F) s /\
  SuspendedParentFrameResume
    (frame_parent F) (frame_child F) (frame_done F) s /\
  DoneClosedness
    (frame_parent F) (frame_done F) s /\
  ProcessedTreeChildrenCorrect
    (frame_parent F) (frame_done F) s /\
  ActiveProcessedChildSegmentSummary
    (frame_parent F) (frame_done F) s /\
  SuspendedSegmentEscapeAccounting
    (frame_parent F) (frame_child F) (frame_done F) s.
```

Producer:

- before invoking inner recursive call, extracted from the post-`set_fa`
  suspended loop state plus `ParentResumeShape` for the pending child.  The
  normal `LoopInvPhase7` is too strong after `set_fa child parent`, because
  `fa_not_done_implies_eq_u parent done` must exclude the pending child until
  it is added to `done_after`.

Consumer:

- after inner call returns, recover the pending child resume facts and rebuild
  the outer `LoopInvPhase7` fields.

Lifetime:

- during nested recursive call。

Pop-stability:

- each field must survive arbitrary inner `maybe_pop` operations。

Audit questions:

- If a field mentions stack membership of vertices below the inner child, inner pop may break it. Such fields must either be guarded by activity or replaced by a weaker summary.
- The frame should not require the exact outer `LoopInv` if only some fields are needed after return.
- If a field is not projected by a named `FrameInvProvides...` theorem, it has
  no recorded consumer and should not be kept in `FrameInv`.

Phase-8a implementation result:

- `FrameInvCandidate` now records `ParentResumeShapeCandidate` explicitly.
- `FrameOfCallCandidate parent child done` replaces the older child-free frame
  shape.
- `SuspendedLoopInvPhase7ProvidesFrameInvCandidate_proof` is intentionally not
  a projection from normal loop material alone; it consumes suspended outer
  loop payload plus the pending child resume shape.
- The first consumer audit is closed by projection proofs for each current
  frame field.  The next Phase 8 task is the producer audit for preserving
  these fields through `preloop`, `edge_loop`, and inner `maybe_pop`.

Phase-8b producer-audit result:

- Full `ParentFrameResumeCandidate parent done` was rejected as a frame field.
  It contradicts the suspended call state where `~ done child` and
  `fa child = parent`.
- `SuspendedParentFrameResumeCandidate parent child done` replaces it.  It
  keeps `done_visited done` and `fa_child_of_u parent`, but weakens
  `fa_not_done_implies_eq_u` with `v <> child`.
- `SuspendedParentFrameResumeClosesAfterChildCandidate_proof` recovers the
  normal `ParentFrameResumeCandidate parent (done_after done child)` once the
  child has returned visited.
- `FramePreservationBundleCandidate` names the seven field-level producer
  obligations.  `FrameContractCandidate_from_field_preservation_proof` proves
  that the full frame contract follows from that bundle, so later proof work
  must target the field producers rather than widening `FrameInvCandidate`.

Phase-8c producer-audit result:

- The frame contract is not for arbitrary unrelated frames.  It is restricted
  by `FrameCompatibleWithCallCandidate F parent child s`, meaning either the
  call is the frame's own pending child or the direct parent is already inside
  the frame child's pending segment.
- This compatibility is required by the `ParentResumeShape` producer: without
  it, a deeper call could discover the frame child as an unvisited vertex and
  rewrite its `fa`.
- `FrameFieldPreservationCandidate` now consumes the full `FrameInvCandidate`,
  not just the individual field.  This is the correct consumer shape because
  the final goal is whole-frame preservation, and field producers may rely on
  other frame fields.
- `FrameContractCandidate_to_field_preservation_bundle_proof` gives the
  recursive-IH direction: an existing whole-frame contract supplies all seven
  field producers for recursive calls.

Phase-8d producer-audit result:

- The first concrete field producer targets only `ParentResumeShapeCandidate`.
  This is consumer-driven: the parent post-child step needs the pending edge,
  `~ done child`, `fa child = parent`, and the non-root-child inequality.
- `FrameParentResumeShapeAfterPreloopCandidate_proof` consumes the full
  `FrameInvCandidate`, compatibility, and direct `ChildEntryCandidate`.
  Compatibility is not ornamental: after `preloop child`, the proof of
  `Visited (frame_child F)` comes either from the pending-parent segment case
  or from the own-pending-child equality.
- `FrameParentResumeShapePreservedByMaybePopCandidate_proof` audits the pop
  edge of the same field.  It uses only `pop_scc_keep_fa`; the inequality is
  re-derived in the post-state from the preserved `fa` value instead of
  reusing a pre-state fact directly.
- No wider parent loop or full frame fact is produced by these lemmas.  The
  remaining Phase 8 work must continue field by field for the other six
  members of `FramePreservationBundleCandidate`.
- The full body producer for this field is not an independent next theorem.
  The inner `edge_loop` needs the whole `FrameInvCandidate` before recursive
  calls to `W a`, so the body-level proof must be assembled after all fields
  have cut-level preservation producers.

Phase-8e remaining-field cut-level audit:

| Frame field | Cut-level producer audit |
|---|---|
| `LoopInvLowCandidate` | `preloop` preservation is plausible but not field-local; `maybe_pop` needs a frame-pop separation fact so active low-source witnesses and `Active parent` are not removed by an inner pop. |
| `SuspendedParentFrameResumeCandidate` | Passed. It depends only on `done_visited`, `fa_child_of_u`, and the suspended `fa_not_done` discipline. `FrameSuspendedParentFrameResumeAfterPreloopCandidate_proof` and `FrameSuspendedParentFrameResumePreservedByMaybePopCandidate_proof` are proved. |
| `DoneClosednessCandidate` | `preloop` is monotone for visited/stack, but `maybe_pop` can turn an active `done` vertex into a non-active vertex. Preservation needs a producer saying frame-`done` vertices are below the inner pop boundary, or a closedness contribution for any popped frame-`done` vertex. |
| `ProcessedTreeChildrenCorrectCandidate` | Cut-level preservation is closed after refining the field with `ProcessedTreeChildrenInactiveSelfLowCandidate`. It is still not a primitive frame-stable fact: active processed children are transported by lower-anchor preservation, while inactive processed children use `ChildInactiveSelfLowForParentCandidate`. The closed cut-level producers include `ChildRootCorrectTransportFromStackShrinkCandidate_proof`, `ChildRootCorrectTransportFromInactiveSelfLowCandidate_proof`, `MaybePopProducesChildLowerStackAnchorsPreservedCandidate_proof`, and `MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryCandidate_proof`. Later Phase 9 assembly closes the body-level producer through `PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_proof` and `BodyPreservesFrameContractCandidate_from_phase9_cuts_proof`; this field is no longer the active Phase 9 gap. |
| `ActiveProcessedChildSegmentSummaryCandidate` | Refined. The frame stores only the child-root self escape summary, not full child segment coverage. The refined field is stable through later sibling `preloop` and through inner `maybe_pop`; the latter consumes the actual pop root `Active u`, because stack-split reasoning cannot use the suspended parent active fact as a substitute. |
| `SegmentEscapeAccountingCandidate` | Full accounting over all active vertices is too strong as suspended frame state. `preloop` for the pending child introduces the child/descendants into the active segment before they are part of `done`; the frame should store a suspended accounting that excludes the pending child segment and closes it with the returned child summary. |

Immediate design consequence at the end of Phase 8e:

- Do not prove `FramePreservationBundleCandidate` against the then-current
  seven fields.  First refine the segment-related frame fields and add the
  explicit pop-boundary/separation predicate consumed by `LoopInvLowCandidate`
  and `DoneClosednessCandidate`.

Phase-8f predicate-refinement result:

- `PendingChildSegmentCandidate child s x` names the part of the current
  DFS-tree state owned by the pending recursive child:

```coq
Visited child s /\
dg_reachable (state_to_dfs_tree g s root) child x
```

- `SuspendedSegmentEscapeAccountingCandidate u child done s` is the narrowed
  frame field.  It is the old parent `SegmentEscapeAccountingCandidate u done`
  only for active vertices outside `PendingChildSegmentCandidate child s`.
  Before `preloop child`, `child` is not visited, so the suspended field is
  produced from the full parent segment accounting by weakening.  After
  `preloop child`, the child and its DFS descendants are excluded from the
  parent frame and must be closed later using the returned child summary.
- `FrameInvCandidate` now stores
  `SuspendedSegmentEscapeAccountingCandidate frame_parent frame_child frame_done`,
  not full `SegmentEscapeAccountingCandidate frame_parent frame_done`.
- `FrameInvForgetsSuspendedLoopInvPhase7Candidate_proof` was intentionally
  replaced by `FrameInvForgetsSuspendedLoopInvPhase6Candidate_proof`.
  A suspended frame no longer claims full Phase 7 accounting; full
  `LoopInvPhase7Candidate parent (done_after done child)` must be rebuilt
  after the child returns.
- `SegmentEscapeAccountingSuspendsCandidate_proof` records the weakening from
  full accounting to suspended accounting, and
  `SuspendedLoopInvPhase7ProvidesFrameInvCandidate_proof` uses that weakening
  when creating a frame.

Phase-8g close-lemma result:

- `PendingChildSegmentEscapeAccountedCandidate u done child s` names the exact
  remaining consumer-side obligation for active vertices inside
  `PendingChildSegmentCandidate child s`.  It says escapes from that segment
  have already been lifted into the parent pending/old-anchor form for
  `done_after done child`.
- `SuspendedSegmentEscapeAccountingClosesAfterChildCandidate_proof` is proved.
  It recovers full parent
  `SegmentEscapeAccountingCandidate parent (done_after done child)`.
  The proof splits on whether the queried active vertex is inside the pending
  child segment:
  outside uses suspended parent accounting; inside uses
  `PendingChildSegmentEscapeAccountedCandidate`.  If the outside case still
  points to the pending child edge, it is discharged by
  `ParentPendingChildEscapeAccountedCandidate`.

Remaining segment work:

- Phase 8h audits production of `PendingChildSegmentEscapeAccountedCandidate`
  from `ChildSegmentSummaryCandidate`.  The audit found that child summary is
  sufficient only with two explicit producers:
  `PendingChildSegmentOrderCandidate child s`, which supplies
  `dfn child <= dfn x` for active vertices in the pending child segment, and
  `PendingChildSegmentOldAnchorLiftsToParentCandidate parent done child s`,
  which accounts the child's old-anchor witnesses in the parent's
  pending-root/old-anchor disjunction.
- `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_proof` is
  proved from exactly those inputs.  The proof also records that the child
  summary's pending-root case is impossible when the child's `done` set is
  `edge_set child`.
- `PendingChildSegmentOrderCandidate_from_global_shape_proof` closes the first
  producer from `GlobalShapeCandidate`: DFS-tree reachability plus
  `dfn_valid` gives the required `dfn child <= dfn x`.
- The second producer was corrected during audit: its conclusion must be the
  same disjunction consumed by parent accounting, not only the parent
  old-anchor branch.  This matters for cases such as an anchor at `parent`,
  which should be handled by parent pending-root escape rather than by forcing
  `dfn parent < dfn parent`.
- `PendingChildSegmentOldAnchorsBelowParentCandidate parent child s` is now a
  sufficient old-anchor-only producer: every old-anchor witness reachable from
  any active vertex in the pending child segment is older than `parent`.
  `PendingChildSegmentOldAnchorLiftsToParentCandidate_from_all_older_segment_proof`
  proves that this fact, together with `low parent <= low child`, produces
  `PendingChildSegmentOldAnchorLiftsToParentCandidate`.
- The consumer-driven replacement is the anchor split:
  `PendingChildSegmentNonOlderAnchorAccountedByParentCandidate parent done child s`
  says that a child old-anchor witness that is not older than `parent` must
  already be accounted in the parent's pending-root/old-anchor disjunction
  under `done_after done child`.
  `PendingChildSegmentOldAnchorLiftsToParentCandidate_from_anchor_split_proof`
  proves the exact split:
  if `dfn b < dfn parent`, use the parent old-anchor branch; otherwise consume
  that parent-accounted disjunction.
- `PendingChildSegmentNonOlderAnchorAccountedBySuspendedParent_proof` proves
  this non-older-anchor accounting from suspended parent segment accounting,
  `ParentPendingChildEscapeAccountedCandidate`, and pending-child segment
  order.  The proof queries suspended parent accounting at the anchor `b`.
  If the suspended pending-root branch points to the pending child edge, it
  delegates to `ParentPendingChildEscapeAccountedCandidate`; otherwise it
  prefixes the pending-root/old-anchor witness with `x ->* b`.
- `GetLowUpdateLowProducesParentLowBelowChildCandidate_proof` closes the
  `low parent <= low child` producer at the correct program cut:
  `get low child ;; update_low parent`.  It is not a child-post fact.
- `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_segment_producers_proof`
  is the all-older sufficient composition from global shape, child summary,
  `low parent <= low child`, and the segment-below-parent fact to
  `PendingChildSegmentEscapeAccountedCandidate`.
- `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_anchor_split_proof`
  is now the preferred audited composition.  It consumes global shape, child
  summary, `ParentLowBelowChildCandidate`, and the non-older-anchor accounted
  predicate.
- `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_suspended_parent_proof`
  is the closed preferred conditional producer path for child-segment
  accounting: global shape, child summary, `ParentLowBelowChildCandidate`,
  suspended parent segment accounting, and parent-pending-child accounting
  imply `PendingChildSegmentEscapeAccountedCandidate`.  It does not produce
  parent-pending-child accounting by itself.
- The segment lane is conditionally connected to the actual post-child cut:
  `GetLowUpdateLowPreservesChildSegmentSummaryFromParentResumeCandidate_proof`,
  `GetLowUpdateLowProducesNonOlderAnchorAccountedByParentFromParentResumeCandidate_proof`,
  and
  `GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_proof`
  show that after `get low child ;; update_low parent`, the exact facts
  consumed by the preferred segment-close producer are available together only
  after `ParentPendingChildEscapeAccountedCandidate parent done child` has
  been supplied.  Producing that parent-pending fact belongs to the Phase 9
  tree-branch post-update accounting producer, not to the recursive child post.
- Active-target block closure needs one additional refinement beyond ordinary
  parent pending.  `ParentPendingChildEscapeAccountedCandidate parent done
  child` excludes pending-root witnesses in `done_after done child`, while
  `ActiveTargetBlockEscapeAccountedCandidate parent (done_after done child)
  block` must exclude witnesses in `(done_after done child) ∪ block`.  The
  route-2 implementation therefore needs a block-aware parent-pending subgoal
  for sources in the current mixed block; the ordinary parent-pending
  predicate remains the right segment-close input but is not by itself a
  block-close input.

Frame-pop boundary audit:

- `FramePopBoundaryCandidate F u s` is the frame-specific pop-separation
  predicate.  It says the suspended frame parent and every active
  frame-`done` vertex are in the `rest` component of
  `stack_split_at (stack s) u`; therefore an inner pop at `u` cannot remove
  them.
- `FramePopBoundarySnapshotCandidate F snap s` is the first consumer-facing
  snapshot produced after `maybe_pop u`: the frame parent remains active,
  every frame-`done` vertex active in `snap` remains active in the post-state,
  and `visited`, `dfn`, `low`, and `fa` are unchanged.
- `MaybePopProducesFramePopBoundarySnapshotCandidate_proof` proves this
  producer.  This is deliberately not a full preservation theorem for
  `LoopInvLowCandidate` or `DoneClosednessCandidate`; it only provides the
  frame-specific active-survival facts those consumers need.
- `MaybePopActivePostImpliesPreSnapshotCandidate_proof` proves the separate
  generic pop fact that `maybe_pop` does not add stack vertices
  (`Active post -> Active pre`) when the pop root is active in the snapshot.
  This fact is consumed by `LowFrontierCandidate`; it is intentionally not
  folded into the frame-specific boundary.
- `MaybePopPreservesSettledClosedWithSegmentClosedCandidate_proof` proves the
  separate settled-closed producer: if the pop root is active, stack order is
  available, and `PoppedSegmentClosedCandidate u s` holds, then `maybe_pop u`
  preserves `SettledClosedCandidate`.
- `FramePopBoundarySnapshotPreservesDoneClosednessCandidate_proof` proves the
  `DoneClosednessCandidate` consumer over the frame snapshot.  If a frame
  `done` vertex is non-active after pop, then it was already non-active in
  the snapshot; otherwise frame active-survival gives a contradiction.
- `FramePopSnapshotsPreservePartialRootLowEquationCandidate_proof` proves the
  low-equation consumer over the frame snapshot plus the generic stack-subset
  fact.  `LowFrontierCandidate` consumes `Active post -> Active pre`, while
  `LowSourceCandidate` consumes frame-`done` active-survival for its active
  source witness.
- The remaining structural producers are also proved:
  `PopSccKeepsDfnInjectiveCandidate_proof`,
  `MaybePopPreservesGlobalShapeCandidate_proof`, and
  `MaybePopPreservesOrderFactsCandidate_proof`.
- `MaybePopPreservesLoopInvLowWithFramePopBoundaryCandidate_proof` is the
  closed Hoare wrapper for the full `LoopInvLowCandidate` field at this cut.
  It composes the frame boundary snapshot, generic stack-subset, global shape,
  settled-closed, order, and low-equation consumers without widening
  `FramePopBoundaryCandidate`.
- `MaybePopPreservesDoneClosednessWithFramePopBoundaryCandidate_proof` closes
  the analogous Hoare wrapper for `DoneClosednessCandidate` at the same cut.
- The `ActiveProcessedChildSegmentSummaryCandidate` refinement is closed at the
  cut level:
  `PreloopPreservesActiveProcessedChildSegmentSummaryCandidate_proof` handles
  later sibling `preloop`, and
  `MaybePopPreservesActiveProcessedChildSegmentSummaryCandidate_proof` handles
  inner `maybe_pop`.  The stack lemma
  `old_anchor_in_rest_when_child_in_rest` is the critical old-anchor
  preservation argument: if a processed child remains in the post-pop `rest`,
  then any older anchor with smaller `dfn` must also be in `rest`.
- `ProcessedTreeChildrenCorrectCandidate` preservation is now closed at the
  frame-pop cut level.  The final refinement adds
  `ChildInactiveSelfLowForParentCandidate` to the processed-child record:
  inactive processed children transport correctness from
  `low child = dfn child`, while active processed children use
  `old_anchor_in_rest_when_child_in_rest` through the lower-anchor preservation
  producer.
- The closed cut-level producer is
  `MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryCandidate_proof`.
  The later Phase 9 body assembly closes the full frame-field path with
  `PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_proof` and the
  premise-free
  `BodyPreservesFrameContractCandidate_from_phase9_cuts_proof`.  The remaining
  active Phase 9 gap is not a frame-field transport issue; it is the framed
  low-contribution accounting producer currently hidden behind
  `BodyChildPostTailCandidate_statement`.

## 6. Root-Pop Predicate Ledger

### 6.1 `PoppedSegmentClosed u s`

Meaning:

Before pop, every vertex in the stack segment that will be popped with root `u` has no path to an unvisited vertex.

Phase-7c current candidate:

```coq
PoppedSegmentClosedCandidate u s :=
  forall x w,
    Visited x s ->
    Active x s ->
    dfn s u <= dfn s x ->
    dg_reachable g x w ->
    Visited w s
```

This is deliberately marked as candidate: it uses the dfn interval as the
pre-pop segment approximation.  The next audit must check that this matches
the actual `stack_split_at (stack s) u` popped segment using stack order.

Producer:

- `SegmentClosedAtRoot` from `LoopDone u s` and `low s u = dfn s u`。

Consumer:

- `SettledClosedAfterPop`。

Lifetime:

- pop branch only。

Audit questions:

- Must match the actual `stack_split_at` popped segment, not merely all vertices with `dfn u <= dfn x` unless stack order proves equivalence.

### 6.2 `RootPopBridge`

Meaning:

Transport or reconstruct root final low correctness across `pop_scc u`.

Required theorem:

```coq
RootPopBridge:
  LoopDone u s ->
  root_pop_guard u s ->
  RootLowPrePop u s ->
  pop_effect u s s' ->
  RootLowCorrectFinal u s'.
```

Audit questions:

- If final correctness is existing `scc_is_low_v`, prove it after pop from self case and `low u = dfn u`.
- Do not attempt to preserve child/subtree low correctness across pop.

Phase-7c skeleton result:

- `RootFinalFromPrePopCandidate_proof` closes the unchanged-state projection.
- `LoopDonePhase6ProvidesFinalFromPrePopCandidate_proof` extracts final
  structural fields from the Phase 6 component of `LoopDonePhase7Candidate`.
- `SkipBranchProducesRootFinalCandidate_proof` closes the no-pop branch from
  `LoopDonePhase7Candidate`.
- The pop branch is represented by:

```coq
SegmentClosedAtRootCandidate_statement
RootPopLowValidStableFieldsCandidate_statement
RootPopSettledClosedCandidate_statement
RootPopIsLowInputCandidate
RootPopIsLowCandidate_statement
RootPopBridgeCandidate_statement
PopBranchProducesRootFinalCandidate_statement
MaybePopFinalCandidate_statement
```

`SegmentClosedAtRootCandidate_statement` is proved and is now consumed by
the pop bridge.  `RootPopLowValidStableFieldsCandidate_proof` proves the
low-valid/stable-fields part using the existing `pop_scc` low-valid primitive.
`RootPopSettledClosedCandidate_proof` closes the settled-closed component from
`PoppedSegmentClosedCandidate`.  `RootPopIsLowCandidate_proof` is intentionally
narrower: it consumes only `RootPopIsLowInputCandidate`, while
`RootPopBridgeCandidate_from_parts_proof` projects that input out of the full
pop-branch precondition.  `RootPopBridgeCandidate_proof`,
`PopBranchProducesRootFinalCandidate_proof`, and `MaybePopFinalCandidate_proof`
close the Phase 7c pop bridge.

## 7. Branch Producer/Consumer Table

| Branch | Produces | Consumes | Critical audit |
|---|---|---|---|
| `preloop u` | `LocalActiveRoot`, empty `DoneDiscipline`, self `PartialRootLowEquation`, empty child/segment summaries | `EntryPre` | Can every field be initialized from empty done? |
| unvisited child | child correctness, child closedness, optional active segment summary, parent low update | `ChildContract`, `FrameContract`, parent loop facts | Child final correctness must be usable even if child popped |
| visited non-stack | done closedness extension, no low update | `SettledClosed`, tree-child exclusion | New `done` target must not require child correctness |
| visited active ancestor | low update with `dfn a`, old-stack anchor | stack order, dfn facts | Prove target is ancestor and not direct unprocessed child |
| visited active descendant | parent segment lifting, low update | active child segment summary, coverage | Summary must be strong enough but not whole-subtree final post |
| root pop | final settled closed, root final correctness | segment closedness, root-pop bridge | Stack-sensitive facts need reconstruction |

## 8. Mapping Order to Coq Definitions

Do not expand everything at once. Recommended order:

1. Define only small semantic aliases that are clearly program-field facts:
   - `Visited`, `Unvisited`, `Active`, `GlobalShape`, `GlobalShapePre`, `OrderFacts`。
2. Audit the entry producer before full `LoopInv`:
   - `preloop u` must produce the base loop-entry facts from `EntryPre u`;
   - in Coq, this first appears as `PreloopGlobalShapeCandidate_statement`,
     `PreloopSettledClosedCandidate_statement`,
     `PreloopOrderFactsCandidate_statement`, and
     `PreloopActiveSelfLowCandidate_statement`;
   - status: proved by corresponding `Preloop..._proof` lemmas.
3. Audit the unvisited-child producer before full `LoopInv`:
   - `set_fa child parent` must produce `ChildEntry parent child done`;
   - in Coq, this first appears as `SetFaGlobalShapePreCandidate_statement`,
     `SetFaSettledClosedCandidate_statement`,
     `SetFaOrderFactsCandidate_statement`, and
     `SetFaParentPointerCandidate_statement`,
     `SetFaKeepsChildUnvisitedCandidate_statement`, plus
     `SetFaParentActiveCandidate_statement`;
   - status: proved by corresponding `SetFa..._proof` lemmas and combined by
     `SetFaCreatesPendingChildCandidate_proof`.
4. Define root phase predicates:
   - `RootLowPrePop`, `RootLowCorrectFinal`, `RootPopBridge` target。
5. Define `LoopInv` subfields one by one:
   - start with `LocalActiveRoot` and `DoneDiscipline`;
   - then `PartialRootLowEquation`;
   - then child correctness;
   - then segment accounting/coverage;
   - finally active child summary。
6. Define `ChildPost` only after unvisited branch consumers are explicit。
7. Define `FrameInv` last, as the subset of parent loop facts that nested calls must preserve。

## 9. Stop Conditions

Revise the ledger if:

1. `ChildEntry` cannot be produced after `set_fa child parent` from `GlobalShape + Visited parent + Unvisited child`.
2. `ChildRootCorrectForParent` relies on stack-sensitive child facts after child pop.
3. `ProcessedTreeChildrenCorrect` cannot be extended in visited non-stack / active branches.
4. `SegmentEscapeAccounting` cannot derive `PoppedSegmentClosed`.
5. `FrameInv` includes a fact not preserved by inner `maybe_pop`.
6. Existing candidate definitions force stronger facts than their consumers need.

These are predicate-design failures, not proof-search failures.
