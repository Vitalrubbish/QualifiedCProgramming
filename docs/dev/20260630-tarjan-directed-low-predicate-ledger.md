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

- `RootLowCorrectFinal u s` may map to `scc_low_valid_v g root s u /\ scc_is_low_v g root s u`, but this is not automatic because both may inspect current `stack` through back-edge semantics.

Audit questions:

- If `u` is popped, can existing `scc_low_valid_v u` still hold in final state?
- If not, should final correctness be weakened to `scc_is_low_v u`, or should `scc_is_low_v u` be redefined / proved root-pop-stable by the guard `low u = dfn u`?

### 2.3 `RootLowPrePop u s`

Meaning:

Root correctness just after edge loop and before optional pop. This is the phase where stack-sensitive back-edge explanations are still valid.

Required semantic fields:

```coq
RootLowPrePop u s :=
  RootLowEquation u s /\
  RootTreeChildrenCorrect u s.
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

### 3.6 `ProcessedTreeChildrenCorrect u done s`

Meaning:

Every processed direct DFS-tree child of `u` has enough root-level low correctness for `u`'s root bridge.

Interface:

```coq
ProcessedTreeChildrenCorrect u done s :=
  forall v,
    done v ->
    DirectTreeChild u v s ->
    ChildRootCorrectForParent v s.
```

Producer:

- unvisited child recursive post；
- visited non-stack/active branch must prove the new target is not a new direct tree child, or already has the needed correctness。

Consumer:

- root is-low bridge at `done = edge_set u`。

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

Audit questions:

- Does accounting need to mention all segment vertices, or only vertices reachable from `u` within processed children?
- Existing `segment_escape_accounted` is a candidate; verify it exactly supports the pop proof and descendant branch.

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
  ChildRootCorrectForParent child s /\
  ChildClosednessContribution parent child done s /\
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

### 4.3 `ChildRootCorrectForParent child s`

Meaning:

The child has enough low correctness to be used as a processed tree child in parent's root bridge and low equation.

Minimum capabilities:

```coq
low child is final after child call /\
root low correctness for child
```

Producer:

- child's `RootFinal`。

Consumer:

- parent `PartialRootLowEquation` extension via `low child`;
- parent `ProcessedTreeChildrenCorrect`。

Pop-stability:

- yes for child root, by child final theorem。

Audit questions:

- Does parent need child `scc_low_valid_v`, child `scc_is_low_v`, or a custom root summary?
- If child was popped, existing stack-sensitive low-valid may not hold; use a pop-stable child root summary instead.

### 4.4 `ChildClosednessContribution parent child done s`

Meaning:

Facts needed to extend parent done-closedness after processing child.

Required capability:

```coq
done_tree_closed parent (done ∪ [child]) s
```

or an equivalent semantic relation:

```coq
if child is no longer active, all vertices reachable from child are visited.
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

## 5. Frame Predicate Ledger

### 5.1 `FrameInv F s`

Meaning:

Facts about an outer parent loop that must survive while an inner recursive call runs.

Suggested shape:

```coq
FrameInv F s :=
  OuterParentResumeShape F s /\
  OuterPartialRootLowEquation F s /\
  OuterProcessedTreeChildrenCorrect F s /\
  OuterSegmentEscapeAccounting F s /\
  OuterSegmentCoverageByDone F s /\
  OuterActiveProcessedChildSummary F s /\
  OuterOrderFacts F s.
```

Producer:

- before invoking inner recursive call, extracted from outer `LoopInv` and child entry context。

Consumer:

- after inner call returns, rebuild outer `LoopInv`。

Lifetime:

- during nested recursive call。

Pop-stability:

- each field must survive arbitrary inner `maybe_pop` operations。

Audit questions:

- If a field mentions stack membership of vertices below the inner child, inner pop may break it. Such fields must either be guarded by activity or replaced by a weaker summary.
- The frame should not require the exact outer `LoopInv` if only some fields are needed after return.

## 6. Root-Pop Predicate Ledger

### 6.1 `PoppedSegmentClosed u s`

Meaning:

Before pop, every vertex in the stack segment that will be popped with root `u` has no path to an unvisited vertex.

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
