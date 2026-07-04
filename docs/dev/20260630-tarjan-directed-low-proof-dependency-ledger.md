# Tarjan-Directed-Low-Proof-Dependency-Ledger
**Author**: Codex
**Date**: 2026-06-30

## 1. Kosaraju 可借鉴的证明范式

Kosaraju 的成功结构不是先设计一个全能不变量，而是：

1. 固定最终 theorem 的 consumer；
2. 按程序 phase 拆出 proof cut；
3. 为每个 cut 设计刚好够用的 `Q` / loop invariant / outer invariant；
4. 用 dependency ledger 追踪每个事实的 producer、consumer 和生命周期。

对应到 `SeparationLogic/algorithms/Kosaraju/Kosaraju.v`：

- `kosaraju_correct` 只消费两个最终事实：
  - `forall v, visited2 s' v`;
  - `scc_id s' u = scc_id s' v <-> mutually_reachable u v`.
- Phase 1 不直接证明最终 SCC correctness，而是产出 Phase 2 需要的 `R`：
  - `Phase1_Order`;
  - `visited1` all;
  - `ForwardReachClosed` 的启动条件；
  - 不变字段保持。
- Phase 1 内部 DFS 使用专门的 `Q_finish_after` / `Q_phase1`，只为外层 `kosaraju_finish_phase1_order` 服务。
- Phase 2 外层使用 `R`，每轮 `DFS_scc_R` 只证明“本轮 SCC 标号后 `R` 继续成立”。
- C refinement 中的 `dfs_finish_from` / `dfs_finish_after`、`dfs_scc_from` / `dfs_scc_after` 把“递归返回后继续父循环”显式化；Tarjan low 的 `low_frame_contract` 应承担类似职责。

Tarjan low 的 ledger 应遵循同一原则：先写出 final consumer，再反推每个 cut 需要什么事实。

## 2. Final Target 与 API 决策

### 2.1 Low-layer theorem

递归 low 层建议先证明 stronger-but-root-level theorem：

```coq
Theorem tarjan_scc_keep_low_full (u: V):
  Hoare
    (fun s =>
       low_pre_full u s /\
       stack_dfn_order s /\
       dfn_injective s)
    (tarjan_scc g u)
    (fun _ s =>
       low_full_post u s /\
       stack_dfn_order s /\
       dfn_injective s).
```

其中 final post 只包含 root-level correctness：

```coq
Definition low_full_post (u: V) (s: @SCCSt V): Prop :=
  wf_scc_state g root s /\
  settled_closed g s /\
  u ∈ visited s /\
  RootFinalLowValid u s /\
  RootFinalIsLow u s.
```

不把 whole-subtree low-valid / is-low 放进 final post。

Entry side should use the preloop-ready shape:

```coq
Definition low_pre_full (u: V) (s: @SCCSt V): Prop :=
  wf_scc_state_pre g root u s /\
  settled_closed g s.
```

This matters for the unvisited-child branch: after `set_fa child parent`,
the child has a parent pointer but has not yet been visited.  The producer is
therefore `wf_scc_state + parent visited + child unvisited -> wf_scc_state_pre child`,
not a loose `wf_scc_state /\ child unvisited` bundle.

### 2.2 Public wrapper

如果最终 public theorem 必须保持旧 pre：

```coq
low_pre g root u s
```

则必须单独设计 wrapper，而不是把 `settled_closed` 隐含在 low-layer theorem 中。

```coq
Theorem tarjan_scc_keep_is_low_public (u: V):
  Hoare
    (fun s =>
       low_pre g root u s /\
       public_context_implies_settled_closed g root u s /\
       stack_dfn_order s /\
       dfn_injective s)
    (tarjan_scc g u)
    (fun _ s =>
       low_post g root u s /\
       u ∈ visited s /\
       stack_dfn_order s /\
       dfn_injective s).
```

`public_context_implies_settled_closed` 需要在调用场景中实例化，例如 `initSt` 或全局 Tarjan driver invariant。

## 3. Program Cuts

Tarjan body 的证明必须围绕以下 cut 展开：

```coq
tarjan_scc_f g W u =
  preloop u;;
  forset (fun v => dg_step g u v) (process_edge u W);;
  If (fun s => low s u = dfn s u) (pop_scc u)
```

| Cut | 位置 | 目标事实 |
|---|---|---|
| `C0` | before `preloop u` | `low_pre_full u`, `stack_dfn_order`, `dfn_injective` |
| `C1` | after `preloop u` | `low_segment_loop_entry u` |
| `Cedge(done)` | after processing `done` outgoing vertices | `low_segment_loop_inv u done` |
| `Cdone` | after `forset` | `low_segment_loop_done u` |
| `Croot` | before `if_pop` | root `scc_low_valid_v u` and `scc_is_low_v u` |
| `Cfinal` | after `if_pop` | `low_full_post u`, order/injectivity side conditions |

The core invariant is derived from `Cedge(done)`, not designed upfront.

## 4. Backward Obligations

### 4.1 Final post obligation

To prove `Cfinal`, `if_pop` needs:

```coq
low_segment_loop_done u s /\
RootFinalLowValid u s /\
RootFinalIsLow u s.
```

Skip branch:

- state unchanged;
- root correctness and side conditions are preserved.

Pop branch:

- `low s u = dfn s u`;
- segment closure must be derived from `low_segment_loop_done`;
- `settled_closed` must be extended using segment closure;
- root low-valid / is-low after pop must be reconstructed or transported by a dedicated root-pop lemma.

Do not use whole-subtree low-valid after pop.

### 4.2 Root bridge obligation

To obtain `Croot` from `Cdone`, prove:

```coq
low_segment_loop_done u s ->
scc_low_valid_v g root s u.
```

and:

```coq
low_segment_loop_done u s ->
scc_is_low_v g root s u.
```

The second lemma consumes:

```coq
children_is_low u (dg_step g u) s.
```

This is the reason `children_is_low` must be part of the loop invariant.

### 4.3 Forset obligation

`forset` only needs the standard done-extension theorem:

```coq
low_segment_loop_inv u done s
process_edge u W a
--------------------------------
low_segment_loop_inv u (done ∪ [a]) s'
```

The loop invariant must contain exactly the facts consumed by `process_edge` and `Croot`.

### 4.4 Recursive child obligation

When `process_edge` discovers an unvisited child `a`, the recursive call must return enough to extend the parent loop:

```coq
low_child_post u a done s'
```

It must include:

- parent pending facts after the recursive return;
- done-tree closedness for `done ∪ [a]`;
- child root low-valid, tracked separately from is-low;
- child root is-low, tracked separately from low-valid;
- conditional child segment summary if `a` remains active.

### 4.5 Frame obligation

While proving a nested child, the recursive call must preserve the outer parent frame.

This is analogous to Kosaraju's continuation wrappers: after an inner DFS returns, the outer loop resumes with its facts intact.

For Tarjan low, the frame must preserve:

- outer parent pending;
- outer segment accounting;
- outer stack segment coverage;
- outer active child summaries;
- outer processed child is-low summaries.

## 5. Fact Lifecycle Ledger

| Fact ID | Fact | Producer | Consumer | Lifetime | Pop-stable | Invariant field |
|---|---|---|---|---|---|---|
| `F-pre` | `low_pre_full u`, including `wf_scc_state_pre u` | caller / wrapper; unvisited branch after `set_fa` | `preloop` | entry only | N/A | no |
| `F-wf` | `wf_scc_state g root s` | preloop, primitives, recursive post | almost all obligations | whole call | yes, with pop lemma | `low_iteration_inv'` / post |
| `F-wf-pre-child` | `wf_scc_state_pre g root child s` | `set_fa child parent` with `parent ∈ visited` and `child` unvisited | child recursive call | child entry only | N/A | `ChildEntry` |
| `F-settled` | `settled_closed g s` | caller; pop extends it | non-stack branch, final post | whole call | yes, must be proved | `low_iteration_inv'` / post |
| `F-order` | `stack_dfn_order s` | caller; primitives preserve | branch classification, bridges, final | whole call | should be yes | loop side condition |
| `F-inj` | `dfn_injective s` | caller; primitives preserve | branch classification, bridges, final | whole call | should be yes | loop side condition |
| `F-done-vis` | `done_visited done s` | preloop vacuous; edge extension | visited/done reasoning | loop only | pre-pop | `dfs_local_inv` |
| `F-done-closed` | `done_reachable_closed done s` | non-stack/tree child extension | settled/non-stack reasoning | loop only | pre-pop | `closedness_inv` |
| `F-done-tree-closed` | `done_tree_reachable_closed u done s` | child post / edge extension | parent pending and closedness | loop only | pre-pop | `closedness_inv` |
| `F-fa-child` | `fa_child_of_u u s` | preloop / wf facts | tree child characterization | loop only | pre-pop | `dfs_local_inv` |
| `F-fa-not-done` | `fa_not_done_implies_eq_u u done s` | preloop / edge extension | excludes stale tree children | loop only | pre-pop | `dfs_local_inv` |
| `F-low-frontier` | `low_frontier u done s` | preloop; update_low branches | root low-valid bridge | loop only | pre-pop | `low_equation_inv` |
| `F-low-src` | `low_src u done s` | preloop; update_low branches | root low-valid bridge | loop only | pre-pop | `low_equation_inv` |
| `F-children-low-valid` | `children_low_valid u done s` | child post low-valid | root low-valid bridge | loop only | pre-pop | `low_equation_inv` |
| `F-children-is-low` | `children_is_low u done s` | child post is-low | root is-low bridge | loop and frame | pre-pop | `low_segment_loop_inv` |
| `F-seg-account` | `segment_escape_accounted u done s` | preloop; edge branch extension | active descendant branch, pop segment closure | loop and frame | consumed by pop | `low_segment_loop_inv` |
| `F-seg-covered` | `stack_segment_covered_by_done u done s` | preloop; edge branch extension | active descendant lifting, segment closure | loop and frame | consumed by pop | `low_segment_loop_inv` |
| `F-active-summary` | `active_done_child_segment_summaries u done s` | child post if child remains in stack | active descendant branch | while child active | no | `low_segment_loop_inv` |
| `F-parent-pending` | `low_tree_child_parent_pending parent child done s` | set_fa + recursive body | child post, frame preservation | child/frame | pre-pop | `low_child_post` / `low_frame_inv` |
| `F-root-valid` | `scc_low_valid_v u` | root bridge | `if_pop`, final post | pre-pop to final via pop lemma | root only | derived |
| `F-root-is-low` | `scc_is_low_v u` | root bridge | `if_pop`, final post | pre-pop to final via pop lemma | root only | derived |
| `F-seg-closed` | `stack_segment_reachable_closed u` | `F-seg-account` + `F-seg-covered` + guard | pop extends `settled_closed` | pop branch only | N/A | derived |

Every invariant field must appear in this table. If a candidate field has no consumer, remove it. If it has no producer, weaken the cut or add the missing child/frame contract.

## 6. Loop Invariant Derived From the Ledger

The parent edge loop should carry:

```coq
Definition low_segment_loop_inv (u: V) (done: V -> Prop)
                                (s: @SCCSt V): Prop :=
  low_iteration_inv' u done s /\
  segment_escape_accounted g u done s /\
  stack_segment_covered_by_done g u done s /\
  active_done_child_segment_summaries g root u done s /\
  children_is_low u done s /\
  stack_dfn_order s /\
  dfn_injective s.
```

Field consumers:

| Field | Main consumer |
|---|---|
| `low_iteration_inv'` | ordinary low equation, visited/done/fa facts |
| `segment_escape_accounted` | active descendant branch; pop segment closure |
| `stack_segment_covered_by_done` | descendant lifting; pop segment closure |
| `active_done_child_segment_summaries` | visited-stack active descendant branch |
| `children_is_low` | root is-low bridge at loop done |
| `stack_dfn_order`, `dfn_injective` | branch classification, dfn comparisons, final side conditions |

## 7. Branch Obligation Ledger for `process_edge`

### Branch A: `a` unvisited

Action:

```coq
set_fa a u;;
W a;;
update_low u (low a)
```

Producer before the recursive call:

```coq
wf_scc_state g root s /\
u ∈ visited s /\
~ a ∈ visited s
  -- set_fa a u -->
wf_scc_state_pre g root a s' /\
u ∈ visited s'
```

Together with `settled_closed`, `OrderFacts`, `edge u a`, and the suspended
parent loop context, this is the candidate `ChildEntry u a done`.

Needed from recursive child post:

```coq
ParentResumeShape u a done s'
ChildClosednessContribution a s'
ChildLowValidForParent a s'
ChildIsLowForParent a s'
(In a (stack s') -> ChildSegmentSummary a s')
```

Consumes:

- fixed-point IH in `LowChildMode`;
- fixed-point IH in `LowFrameMode` to preserve outer frames.

Produces/extensions:

- `children_low_valid u (done ∪ [a])`;
- `children_is_low u (done ∪ [a])`;
- `active_done_child_segment_summaries u (done ∪ [a])` if `a` remains active;
- segment accounting and coverage for parent;
- ordinary `low_iteration_inv'`.

Phase-6 skeleton status:

- The child post is split into consumer-specific interfaces:
  `ChildLowValidForParentCandidate`,
  `ChildIsLowForParentCandidate`,
  `ChildClosednessContributionCandidate`,
  `ChildSegmentSummaryCandidate`, and
  `ParentResumeShapeCandidate`.
- The pure consumer audit is proved for empty fields and child-step field
  extension:
  `DoneClosednessCandidate_step_child_proof`,
  `ProcessedTreeChildrenCorrectCandidate_step_child_proof`,
  `ActiveProcessedChildSegmentSummaryCandidate_step_child_proof`, and
  `Phase6ChildPostExtendsLoopFieldsCandidate_proof`.
- The actual root bridge consuming the low-valid / is-low halves remains Phase 7.

### Branch B: `a` visited and not in stack

Action:

```coq
skip
```

or no low update, depending on the program branch.

Consumes:

- `settled_closed g s`;
- `done_reachable_closed`;
- `fa_not_done_implies_eq_u` / tree-child exclusion facts.

Produces/extensions:

- `done ∪ [a]` closedness;
- segment accounting remains valid because any pending escape through `a` is closed by settledness;
- `children_is_low` extension is vacuous unless `a` is a tree child; tree-child case must be excluded.

Required local lemma:

```coq
visited_nonstack_new_done_not_tree_child_or_already_solved
```

The exact name is flexible, but the proof obligation must state how the new
`children_is_low` case for `a` is discharged.

### Branch C: `a` visited, in stack, active ancestor

Action:

```coq
update_low u (dfn a)
```

Consumes:

- `dfn a < dfn u`;
- `stack_dfn_order`;
- `low_frontier` / `low_src`.

Produces/extensions:

- old-stack escape anchor for segment accounting;
- updated `low_frontier`;
- updated `low_src`;
- `children_is_low` extension is vacuous unless `a` is a tree child, which must be excluded.

### Branch D: `a` visited, in stack, active descendant

Action:

```coq
update_low u (dfn a)
```

or equivalent visited-stack update.

Consumes:

- `active_done_child_segment_summaries u done s`;
- coverage showing the descendant lies inside a processed child segment;
- child segment done summary to lift escape accounting back to parent.

Produces/extensions:

- parent `segment_escape_accounted u (done ∪ [a])`;
- parent `stack_segment_covered_by_done u (done ∪ [a])`;
- ordinary low equation update.

This is the directed-graph-specific branch that justifies keeping active summaries in the main loop invariant.

## 8. Frame Ledger

The unified frame records the facts an inner recursive call must preserve for an outer parent.

```coq
Record low_frame: Type := {
  frame_parent : V;
  frame_child  : V;
  frame_done   : V -> Prop
}.

Definition low_frame_inv (F: low_frame) (s: @SCCSt V): Prop :=
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

Frame field ledger:

| Frame field | Why it must be preserved |
|---|---|
| `ParentResumeShape` | parent must resume after the pending child with `fa child = parent`, `child` not done, and the direct edge fact intact |
| `LoopInvLow` | parent still needs done discipline and the partial low equation to perform the post-child low update |
| `SuspendedParentFrameResume` | the suspended call must preserve parent `fa` discipline while allowing the current pending child as the only `~done` exception |
| `DoneClosedness` | parent done extension and root bridge consume closedness |
| `ProcessedTreeChildrenCorrect` | root low-valid and root is-low bridges consume processed child correctness |
| `ActiveProcessedChildSegmentSummary` | active-descendant branch consumes summaries of already processed active children |
| `SuspendedSegmentEscapeAccounting` | parent resume needs the old segment escape accounting outside the pending child segment; child segment accounting is closed after return |

Phase-8a status:

- The frame is now produced from `SuspendedLoopInvPhase7Candidate` plus
  `ParentResumeShapeCandidate`; a normal loop invariant alone is not a
  suspended call frame because it does not identify the pending child, and
  after `set_fa child parent` it is too strong.
- `FrameInvProvides...` projection proofs record the current consumer set.
  Producer audit for preservation through the inner body must now be performed
  field by field.  If a preservation proof only works for a weaker field, the
  corresponding frame field should be narrowed rather than forcing the current
  statement.

Phase-8b status:

- Full `ParentFrameResumeCandidate parent done` was rejected as a frame field:
  `ParentResumeShapeCandidate parent child done` contains `~ done child` and
  `fa child = parent`, exactly the exception that violates
  `fa_not_done_implies_eq_u parent done`.
- `SuspendedParentFrameResumeCandidate parent child done` is the narrowed
  field.  `SuspendedParentFrameResumeClosesAfterChildCandidate_proof` restores
  the normal `ParentFrameResumeCandidate parent (done_after done child)` once
  the child is known visited.
- `SuspendedLoopInvPhase7ClosesAfterChildCandidate_proof` records the
  re-entry shape for the parent loop after the child has been added to `done`.
- `FramePreservationBundleCandidate` is the producer ledger for the seven
  frame fields.  `FrameContractCandidate_from_field_preservation_proof`
  assembles those field producers into `FrameContractCandidate`; it does not
  prove any field preservation by itself.

Phase-8c status:

- `FrameContractCandidate` and `FrameFieldPreservationCandidate` now require
  `FrameCompatibleWithCallCandidate F parent child s`.  This removes the
  over-strong obligation to preserve arbitrary unrelated frames and records the
  direct parent needed by pending-segment transport.
- Compatibility has exactly two producers:
  `FrameCompatibleWithOwnCallCandidate_proof` for the frame's own pending
  child, and `FrameCompatibleWithPendingParentCandidate_proof` for deeper calls
  whose direct parent is already in the frame child's pending segment.
- Field producers now consume the whole `FrameInvCandidate`, not just their
  individual field.  This avoids artificial proof obligations where a field
  would need facts intentionally stored in another frame field.
- The ledger has both assembly directions:
  `FrameContractCandidate_from_field_preservation_proof` bundles field
  producers into the whole contract, while
  `FrameContractCandidate_to_field_preservation_bundle_proof` projects a
  whole-frame recursive IH back into field producers.

Phase-8d status:

- `FrameParentResumeShapeAfterPreloopCandidate_proof` is the first concrete
  frame-field producer.  Dependency shape:

```text
FrameInv F s
FrameCompatibleWithCall F child s
ChildEntry parent child done s
preloop child
  -> ParentResumeShape (frame_parent F) (frame_child F) (frame_done F) s'
  -> Visited (frame_child F) s'
```

- The only non-frame dependency in this producer is the operational effect of
  `preloop`: the called child becomes visited.  Compatibility supplies the
  bridge from the direct call child to the frame child when the frame is the
  own pending call, and otherwise the frame child was already visited.
- `FrameParentResumeShapePreservedByMaybePopCandidate_proof` audits the pop
  side:

```text
ParentResumeShape (frame_parent F) (frame_child F) (frame_done F) s
maybe_pop u
  -> ParentResumeShape (frame_parent F) (frame_child F) (frame_done F) s'
```

- Its primitive dependency is `pop_scc_keep_fa`; edge and `done` facts are pure
  frame parameters.  The post-state inequality
  `fa s' (frame_child F) <> frame_child F` is derived from the preserved
  `fa = frame_parent F` relation, not assumed as state-invariant syntax.
- The full `FramePreservesParentResumeShapeCandidate (tarjan_scc_f g W)`
  theorem is intentionally deferred.  During the inner `edge_loop`, an
  unvisited edge calls `W a`; the recursive frame contract for that call
  requires the whole `FrameInvCandidate F` before the call.  A proof that
  tracks only `ParentResumeShapeCandidate` would lose the precondition needed
  for the next recursive call.  The correct dependency order is:

```text
audit all seven frame fields through preloop / process_edge / maybe_pop
  -> prove edge_loop preserves the whole frame bundle
  -> project FramePreservesParentResumeShapeCandidate from the bundle
```

Phase-8e status:

- `SuspendedParentFrameResumeCandidate` is the second field with concrete
  cut-level producers:

```text
FrameInv F s
FrameCompatibleWithCall F child s
ChildEntry parent child done s
preloop child
  -> SuspendedParentFrameResume (frame_parent F) (frame_child F) (frame_done F) s'

SuspendedParentFrameResume (frame_parent F) (frame_child F) (frame_done F) s
maybe_pop u
  -> SuspendedParentFrameResume (frame_parent F) (frame_child F) (frame_done F) s'
```

- The primitive reason is simple: `preloop` only grows `visited` and does not
  change `fa`; `pop_scc` changes stack/sccs but not `visited` or `fa`.
- The remaining five fields expose missing dependencies:

| Field | Missing producer before bundle proof |
|---|---|
| `LoopInvLowCandidate` | frame-pop separation preserving the parent and any active low-source witness below the pending child boundary |
| `DoneClosednessCandidate` | proof that inner pop does not newly expose a frame-`done` vertex as non-active, unless that vertex's reachable region is already closed |
| `ProcessedTreeChildrenCorrectCandidate` | cut-level pop preservation is now closed after adding the inactive-self-low child field; active processed children use lower-anchor preservation, while inactive processed children use `ChildInactiveSelfLowForParentCandidate` |
| `ActiveProcessedChildSegmentSummaryCandidate` | replacement of the dfn-only child-segment approximation with a segment predicate stable under later sibling `preloop` |
| `SegmentEscapeAccountingCandidate` | resolved for the frame field by replacing it with `SuspendedSegmentEscapeAccountingCandidate`; still needs a post-child close lemma |

- Therefore the next proof dependency is not another field proof.  It is a
  predicate refinement step: define the suspended segment/frame-pop boundary
  facts that these consumers actually need, then restart the remaining field
  producer audit against those narrowed fields.

Phase-8f status:

- The suspended segment refinement is now explicit in the skeleton:

```text
PendingChildSegment child s x :=
  Visited child s /\
  dg_reachable (state_to_dfs_tree g s root) child x

SuspendedSegmentEscapeAccounting u child done s :=
  SegmentEscapeAccounting u done s restricted to active x outside
  PendingChildSegment child s
```

- `SegmentEscapeAccountingSuspendsCandidate_proof` is the producer from full
  parent accounting to the suspended frame field.
- `SuspendedLoopInvPhase7ProvidesFrameInvCandidate_proof` now consumes full
  pre-call Phase 7 accounting and stores only the suspended accounting in
  `FrameInvCandidate`.
- `FrameInvForgetsSuspendedLoopInvPhase7Candidate_proof` was removed as an
  invalid projection.  The valid projection is
  `FrameInvForgetsSuspendedLoopInvPhase6Candidate_proof`.
- New dependency created by this refinement:

```text
SuspendedSegmentEscapeAccounting parent child done s
ParentPendingChildEscapeAccounted parent done child s
PendingChildSegmentEscapeAccounted parent done child s
  -> SegmentEscapeAccounting parent (done_after done child) s
```

- `SuspendedSegmentEscapeAccountingClosesAfterChildCandidate_proof` closes this
  dependency.  It deliberately does not assume that `ChildSegmentSummary` alone
  is enough; instead it exposes the exact remaining producer obligation as
  `PendingChildSegmentEscapeAccountedCandidate`.
- The next producer dependency is:

```text
ChildSegmentSummary child s
PendingChildSegmentOrder child s
PendingChildSegmentOldAnchorLiftsToParent parent done child s
  -> PendingChildSegmentEscapeAccounted parent done child s
```

- `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_proof`
  closes this composition.  It leaves two explicit producers:

```text
PendingChildSegmentOrder child s
PendingChildSegmentOldAnchorLiftsToParent parent done child s
```

- `PendingChildSegmentOrderCandidate_from_global_shape_proof` closes the first
  producer from `GlobalShapeCandidate`, using DFS-tree reachability and
  `dfn_valid`.
- The second producer was corrected to return the parent accounting
  disjunction:

```text
old anchor from child segment
  -> PendingRootEscape parent (done_after done child)
     or OldStackEscapeAnchor parent
```

- The all-older branch is a sufficient producer for the old-anchor side:

```text
low parent <= low child
PendingChildSegmentOldAnchorsBelowParent parent child s
  -> PendingChildSegmentOldAnchorLiftsToParent parent done child s
```

- `PendingChildSegmentOldAnchorLiftsToParentCandidate_from_all_older_segment_proof`
  closes that decomposition, and
  `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_segment_producers_proof`
  composes that sufficient producer path.
- `GetLowUpdateLowProducesParentLowBelowChildCandidate_proof` closes
  `low parent <= low child` at the `get low child ;; update_low parent` cut.
- The preferred consumer-driven split is now explicit:

```text
ParentLowBelowChild parent child s
PendingChildSegmentNonOlderAnchorAccountedByParent parent done child s
  -> PendingChildSegmentOldAnchorLiftsToParent parent done child s
```

- `PendingChildSegmentOldAnchorLiftsToParentCandidate_from_anchor_split_proof`
  closes this split.  The proof sends `dfn b < dfn parent` to the old-anchor
  branch and sends `dfn parent <= dfn b` to the parent-accounted disjunction.
- `PendingChildSegmentNonOlderAnchorAccountedBySuspendedParent_proof` proves
  that disjunction from:

```text
PendingChildSegmentOrder child s
SuspendedSegmentEscapeAccounting parent child done s
ParentPendingChildEscapeAccounted parent done child s
```

  It queries suspended parent accounting at the non-older anchor `b`.  A
  pending-root witness through the pending child edge is repaired by
  `ParentPendingChildEscapeAccounted`; all other pending-root and old-anchor
  witnesses are prefixed by `x ->* b`.
- `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_anchor_split_proof`
  composes the preferred path from global shape, child summary,
  `ParentLowBelowChildCandidate`, and the non-older-anchor accounted predicate.
- `PendingChildSegmentEscapeAccountedCandidate_from_child_summary_and_suspended_parent_proof`
  composes the closed preferred path from global shape, child summary,
  `ParentLowBelowChildCandidate`, suspended parent accounting, and
  parent-pending-child accounting.
- The closed preferred path is now connected to the actual post-child cut by
  `GetLowUpdateLowPreservesChildSegmentSummaryFromParentResumeCandidate_proof`,
  `GetLowUpdateLowProducesNonOlderAnchorAccountedByParentFromParentResumeCandidate_proof`,
  and
  `GetLowUpdateLowProducesPendingChildSegmentEscapeAccountedCandidate_proof`.
- The frame-pop boundary predicate has been introduced as
  `FramePopBoundaryCandidate F u s`: the frame parent and active frame-`done`
  vertices must lie in the `rest` side of `stack_split_at (stack s) u`.
  `MaybePopProducesFramePopBoundarySnapshotCandidate_proof` produces the
  first post-`maybe_pop` snapshot: frame-protected active vertices survive and
  `visited`/`dfn`/`low`/`fa` are unchanged.
- The generic stack-subset producer for `maybe_pop` is now proved as
  `MaybePopActivePostImpliesPreSnapshotCandidate_proof`
  (`Active post -> Active pre`, assuming the pop root is active in the
  snapshot).  It is separate from the frame-specific boundary and is consumed
  by `LowFrontierCandidate`.
- The child pop-closedness producer for `SettledClosedCandidate` is now proved
  as `MaybePopPreservesSettledClosedWithSegmentClosedCandidate_proof`: active
  pop root, stack order, and `PoppedSegmentClosedCandidate` are enough to
  preserve settled closedness through `maybe_pop`.
- `FramePopBoundarySnapshotPreservesDoneClosednessCandidate_proof` closes the
  `DoneClosednessCandidate` consumer over the frame snapshot.
- `FramePopSnapshotsPreservePartialRootLowEquationCandidate_proof` closes the
  low-equation consumer over the frame snapshot plus the generic stack-subset
  fact.
- The remaining structural producers are now proved:
  `PopSccKeepsDfnInjectiveCandidate_proof`,
  `MaybePopPreservesGlobalShapeCandidate_proof`, and
  `MaybePopPreservesOrderFactsCandidate_proof`.
- `MaybePopPreservesLoopInvLowWithFramePopBoundaryCandidate_proof` closes the
  concrete `LoopInvLowCandidate` Hoare preservation lemma at the frame-pop
  cut, without widening the frame-specific boundary.
- `MaybePopPreservesDoneClosednessWithFramePopBoundaryCandidate_proof` closes
  the analogous Hoare wrapper for `DoneClosednessCandidate`.
- The `ActiveProcessedChildSegmentSummaryCandidate` refinement is now closed at
  the cut level.  `PreloopPreservesActiveProcessedChildSegmentSummaryCandidate_proof`
  preserves the child-root self summary through later sibling `preloop`.
  `MaybePopPreservesActiveProcessedChildSegmentSummaryCandidate_proof` preserves
  it through inner `maybe_pop`; this proof deliberately requires the actual
  pop root `Active u`, and uses `old_anchor_in_rest_when_child_in_rest` to keep
  old-anchor witnesses below any surviving active processed child.
- `ProcessedTreeChildrenCorrectCandidate` preservation is now closed at the
  frame-pop cut level.  The decisive split is:
  active processed children consume lower-anchor preservation through
  `old_anchor_in_rest_when_child_in_rest`, while inactive processed children
  consume `ChildInactiveSelfLowForParentCandidate`.
- The closed producer chain includes
  `ChildRootCorrectTransportFromStackShrinkCandidate_proof`,
  `ChildRootCorrectTransportFromInactiveSelfLowCandidate_proof`,
  `MaybePopProducesChildLowerStackAnchorsPreservedCandidate_proof`, and
  `MaybePopPreservesProcessedTreeChildrenCorrectWithFramePopBoundaryCandidate_proof`.
- The two suspended segment fields are now also preserved through inner
  `maybe_pop` by
  `MaybePopPreservesFrameSuspendedSegmentFieldsWithBoundaryCandidate_proof`.
  The key consumer-side bridge is not a new frame field: if a post-pop active
  vertex would be in the suspended child segment in the snapshot, then the
  suspended child itself remains in the post-pop rest side.  This is supplied
  by `stack_split_tree_ancestor_of_rest_active_in_rest`.
- `MaybePopPreservesFrameNonSegmentFieldsWithBoundaryCandidate_proof` covers
  the non-segment frame fields, and
  `MaybePopPreservesFrameInvWithBoundaryCandidate_proof` assembles the full
  frame invariant from the non-segment and suspended-segment cuts.
- The body-facing wrapper is
  `MaybePopPreservesFrameInvFromLoopDoneOlderVerticesCandidate_proof`: it
  produces `FramePopBoundaryCandidate` from inner loop-done plus older-frame
  facts, then consumes `MaybePopPreservesFrameInvWithBoundaryCandidate_proof`.
- Phase 8 is therefore complete as a cut-level frame-contract audit, and the
  first Phase 9 body-level frame-pop cut is also closed.  The remaining frame
  dependency is to produce and carry the older-frame facts through the body
  prefix and edge loop.

This mirrors Kosaraju's continuation idea: `dfs_finish_after` / `dfs_scc_after`
resume an outer traversal after an inner DFS. Tarjan's frame mode is the Hoare
logic version of that continuation state.

## 9. Theorem Dependency Graph

The proof should be implemented in this order.

### Layer 0: pure/projection lemmas

```coq
low_iteration_inv_equiv_new
low_segment_loop_inv projections
tree_child_characterization
children_is_low proper/monotone lemmas
```

### Layer 1: primitive preservation

```coq
preloop_establishes_low_segment_loop_entry
update_low preserves/updates low_frontier
update_low preserves segment accounting as needed
pop_scc preserves dfn/low/fa fields needed by root-pop lemmas
```

### Layer 2: root bridge before pop

```coq
LoopDoneProvidesRootBridgeInputCandidate
low_segment_loop_done_implies_low_valid_root
low_segment_loop_done_implies_is_low_root
```

Phase-7a/7b status:

- `LoopDoneProvidesRootBridgeInputCandidate_proof` is proved in the skeleton.
- It projects `LoopInvPhase6Candidate u (edge_set u)` into the exact root
  bridge input fields.
- `RootBridgeLowValidInputBuildsLowIterationDoneCandidate_proof` adapts the
  consumer-ledger fields to the existing pure `low_iteration_done` record.
- `RootBridgeLowValidCandidate_proof` proves the low-valid half by reusing
  `low_frontier_and_src_imply_low_valid`.
- `RootBridgeIsLowCandidate_proof` proves the is-low half by reusing
  `scc_is_low_induction_is_low`.
- `RootBridgePrePopCandidate_proof` combines the two halves into
  `RootLowPrePopCandidate`.

The second lemma depends on:

```coq
scc_is_low_induction_is_low
children_is_low u (dg_step g u) s
tree_child_characterization
fa_child_of_u u s
```

The `fa_child_of_u` dependency is not optional: `tree_step_char` turns a
DFS-tree edge into `fa s child = u /\ fa s child <> child`, but
`ProcessedTreeChildrenIsLowCandidate` is indexed by original outgoing edges.
The bridge therefore consumes `ParentFrameResumeCandidate` to recover
`dg_step g u child`.

### Layer 3: segment closure and root pop

```coq
low_segment_loop_done_root_implies_segment_closed
pop_scc_preserves_or_reconstructs_root_low_valid
pop_scc_preserves_or_reconstructs_root_is_low
if_pop_preserves_low_full_post
```

Important: root correctness after pop should be a dedicated lemma. It should not
be treated as automatic preservation of stack-sensitive low-valid facts.

Phase-7c status:

- The skeleton now defines the pop-bridge consumer interfaces:
  `PoppedSegmentClosedCandidate`,
  `SegmentClosedAtRootInputCandidate`,
  `RootFinalLowValidCandidate`,
  `RootFinalIsLowCandidate`,
  `RootFinalCandidate`,
  `RootPopLowValidStableFieldsCandidate_statement`,
  `RootPopSettledClosedCandidate_statement`,
  `RootPopIsLowCandidate_statement`,
  `RootPopBridgeCandidate_statement`,
  `PopBranchInputCandidate`, and
  `SkipBranchInputCandidate`.
- The unchanged-state path is proved:
  `RootFinalFromPrePopCandidate_proof`.
- Loop-done structural fields are projected into the final pre-pop bundle by
  `LoopDonePhase6ProvidesFinalFromPrePopCandidate_proof`.
- The no-pop branch is closed by
  `SkipBranchProducesRootFinalCandidate_proof`.
- `LoopInvPhase7Candidate` adds the root-level
  `SegmentEscapeAccountingCandidate` field needed by pop.
- `SegmentClosedAtRootCandidate_proof` proves the segment-closed consequence
  from `LoopDonePhase7Candidate` and `root_pop_guard`.
- `PopBranchInputCandidate` now uses `LoopDonePhase7Candidate`, so the segment
  field has a real pop consumer.  `PopBranchProvidesSegmentClosedAtRootCandidate_proof`
  performs this projection.
- The low-valid/stable-fields part of the pop bridge is already proved:
  `RootPopLowValidStableFieldsCandidate_proof` adapts
  `pop_scc_preserves_low_valid_post_when_root`.
- The final predicate is split into final low-valid and final is-low fields;
  this avoids hiding the fact that their pop producers are different.
- The pop branch is factored through the explicit root-pop bridge:
  `RootPopBridgeCandidate_from_parts_proof` assembles the bridge from
  low-valid/stable fields, settled-closed, and root-is-low components.
  `PopBranchProducesRootFinalCandidate_from_root_pop_bridge_proof` proves
  `PopBranchProducesRootFinalCandidate_statement` from
  `RootPopBridgeCandidate_statement`.
- The remaining pop producers are now proved:
  `RootPopSettledClosedCandidate_proof` and
  `RootPopIsLowCandidate_proof`.
- `RootPopBridgeCandidate_proof`,
  `PopBranchProducesRootFinalCandidate_proof`, and
  `MaybePopFinalCandidate_proof` close the Phase 7c pop bridge.

Segment-producer status:

- The empty producer is proved as
  `SegmentEscapeAccountingCandidate_empty_proof`.
- The child-step producer is proved as
  `SegmentEscapeAccountingCandidate_step_child_proof`, factored through
  `ChildSegmentEscapeLiftsToParentCandidate_proof`.
- The fact consumed by that step is now explicit:
  `ParentPendingChildEscapeAccountedCandidate u done child s`.
  It is the minimal repair for the only stale pending escape introduced by
  adding `child` to `done`.
- Two producers for that fact are proved:
  `ParentPendingChildEscapeAccountedCandidate_from_closed_proof` and
  `ParentPendingChildEscapeAccountedCandidate_from_old_anchor_proof`.
- The active-descendant parent lift is also proved:
  `ParentPendingChildEscapeAccountedCandidate_from_active_descendant_proof`.
  It consumes parent segment accounting and the exact step-side assumptions on
  the source vertex `x`.
- The self-cycle case is further factored:
  `ChildSelfPendingEscapeAccountedCandidate_from_child_summary_proof` derives
  `ChildSelfPendingEscapeAccountedCandidate` from child segment accounting plus
  the non-vacuous old-anchor vocabulary-lift fact.
- `ChildOldAnchorLiftsToParentCandidate_from_all_older_proof` proves one
  sufficient old-anchor lift condition.
- The former child-pending-root lift was rejected during producer audit.  Under
  the actual consumer, child segment accounting is at `done = edge_set child`;
  therefore a pending child root edge would require both `Edge child a` and
  `~ edge_set child a`, which is contradictory by definition.
- The pop branch now consumes `LoopDonePhase7Candidate`, so
  `SegmentClosedAtRootCandidate_proof` is connected to the real branch input.
  `RootPopSettledClosedCandidate_proof` uses the stack split helper
  `stack_split_removed_vertex_dfn_ge_root` to connect the actual popped list
  to the dfn-defined segment.  `RootPopIsLowCandidate_proof` is deliberately
  narrowed to `RootPopIsLowInputCandidate`: active root membership, pre-pop
  `RootIsLowPrePopCandidate`, and the root guard.  It is independent of
  `PoppedSegmentClosedCandidate`; the bridge lemma projects this smaller input
  out of the full pop-branch precondition before composing the three pop
  producers.

### Layer 4: process-edge branch theorem

```coq
process_edge_preserves_low_segment_loop
```

This theorem consumes:

```coq
low_child_contract W
low_frame_contract W
```

and discharges the four branch ledgers in Section 7.

### Layer 5: forset

```coq
forset_preserves_low_segment_loop
```

This is the standard `Hoare_forset` closure over `process_edge`.

### Layer 6: recursive body contracts

```coq
tarjan_scc_f_satisfies_child_contract
tarjan_scc_f_preserves_low_frame
```

These are the analogues of Kosaraju's per-round preservation lemmas such as
`DFS_scc_R` and `round_preserves_R`.

### Layer 7: fixed-point theorem

```coq
tarjan_scc_keep_low_full
tarjan_scc_keep_low_valid_projection
tarjan_scc_keep_is_low_projection
public wrapper, if required
```

## 10. Fixed-Point Modes

The mode design follows directly from the ledger:

```coq
Inductive low_fix_mode: Type :=
| LowRootMode
| LowChildMode (parent: V) (done: V -> Prop)
| LowContributionMode (parent: V) (done: V -> Prop)
| LowFrameMode (outer: low_frame)
               (direct_parent: V)
               (direct_done: V -> Prop).
```

`LowRootMode` consumes the final proof path:

```text
C0 -> C1 -> Cdone -> Croot -> Cfinal
```

`LowChildMode` exists because parent `process_edge` needs a child post.

`LowContributionMode` exists because the tree branch low update consumes a
recursive Hoare contract whose precondition includes parent
`PartialRootLowEquation`; this is not derivable from a state-only child post.

`LowFrameMode` exists because an inner recursive call must preserve the outer continuation state.

Do not add a new mode unless a ledger consumer cannot be served by these four.

Phase-9a status:

- The fixed-point mode assembly is now proved in `Tarjan_scc_is_low.v`.
- `FixIHProvidesChildContract_proof` projects the combined mode IH to
  `ChildContract I W`.
- `FixIHProvidesLowContributionContract_proof` projects the combined mode IH
  to `LowContributionContract I W`.
- `FixIHProvidesFrameContract_proof` projects the same IH to
  `FrameContract I W`.
- `FixpointModeStep_from_obligations_proof` proves the one-step recursive
  body obligation for `LowRootMode`, `LowChildMode`, `LowContributionMode`,
  and `LowFrameMode` from `LowProofObligations I`.
- `LowLayerCorrect_from_obligations_proof` applies `Hoare_fix_logicv` with
  `LowFixMode` as the logic variable and closes
  `LowLayerCorrect_from_obligations_statement`.
- The remaining Phase 9 dependency is not another fixpoint mode.  It is the
  concrete body-contract assembly for `tarjan_scc_f g W`.
- Phase 9b has started on the concrete child-contract side:
  `ChildPostCandidate` bundles the audited child-return fields, and
  `ChildContractCandidate_from_field_statements_proof` shows that
  `ProcessEdgeUnvisitedChildPostCandidate_statement` implies this combined
  child contract.
- The bundled child post now includes `Visited child s`.  This is not a
  generic preservation claim: it is consumed specifically by per-edge
  done-extension after the child returns.  The bundled contract is projected by
  `ChildContractCandidate_provides_post_fields_proof`.
- Current Phase 9 cleanup narrows this bundled post to child-owned facts only:
  `Visited child`, child low-valid, child is-low, inactive-self-low,
  closedness contribution, and the conditional active child segment summary.
  Parent resume shape and parent accounting are no longer fields of
  `ChildPostCandidate`.
- Phase 9b also aligned the abstract interface with the concrete
  low-contribution consumer: `LowContributionContract` is now an explicit
  recursive contract, `LowCandidateInterface` maps it to
  `ChildProvidesLowContributionCandidate`, and
  `LowContributionCandidate_to_interface_proof` provides the adapter.  The
  body-prefix entry side is also connected:
  `PreloopProducesLoopInvPhase7InitialCandidate_proof` proves that `preloop`
  establishes the concrete Phase 7 loop invariant with empty done, and
  `PreloopEntryCandidate_to_interface_proof` exposes it through
  `LowCandidateInterface`.
- The edge-loop dependency is now factored instead of duplicated:
  `EdgeLoopDone_from_process_edge_step_proof` derives `EdgeLoopDone_statement`
  from `ProcessEdgeStep_statement` using `Hoare_forset`; the only extra
  requirement is done-set extensionality of `LoopInv`.
  `LoopInvPhase7Candidate_done_proper_proof` closes that requirement for the
  concrete invariant, and
  `EdgeLoopDoneCandidate_from_process_edge_step_proof` gives the concrete
  adapter.
- The candidate-level per-edge obligation is now named explicitly as
  `ProcessEdgeStepCandidate_statement`, and
  `ProcessEdgeStepCandidate_to_interface_proof` adapts it to the abstract
  interface.
- `ProcessEdgeStepCandidate_proof` now proves the concrete per-edge
  obligation.  `ProcessEdgeStepCandidate_interface_proof` exposes it through
  `LowCandidateInterface`, while `EdgeLoopDoneCandidate_proof` and
  `EdgeLoopDoneCandidate_direct_proof` close the concrete edge-loop adapter.
- The tree-branch entry into the recursive child call has one more audited
  producer: `SetFaCreatesSuspendedParentFrameCandidate_proof` proves that
  `set_fa child parent` creates the suspended parent-frame field and
  `ParentResumeShapeCandidate` needed by the frame contract.
- The concrete child-body core is now proved by
  `BodyChildProducesRootFinalCandidate_proof`,
  `RootFinalProvidesChildPostCoreCandidate_proof`,
  `BodyChildProducesPostCoreCandidate_proof`,
  `BodyChildProducesInactiveSelfLowCandidate_proof`, and
  `BodyChildProducesActiveSegmentSummaryCandidate_proof`.
- `BodySatisfiesChildContractCandidate_from_phase9_cuts_proof` is now closed
  directly from these child-body producers.
- The frame-pop side of body preservation is now packaged by
  `MaybePopPreservesFrameInvFromLoopDoneOlderVerticesCandidate_proof`.
  `PreloopMakesFrameVerticesOlderThanChildCandidate_proof` is the first
  producer for its older-frame-vertex premises after the direct child's
  `preloop`.
- `PreloopProducesFrameBodyPrefixFactsCandidate_proof` packages the currently
  proved preloop prefix for the frame body path: parent resume shape,
  `Visited (frame_child F)`, suspended parent-frame resume, and the
  older-frame-vertex facts.  It intentionally does not claim full
  `FrameInvCandidate` preservation through `preloop`.
- The compatibility field is now parent-aware:
  `FrameCompatibleWithCallCandidate F parent child s`.  This is a
  consumer-driven strengthening: the later suspended segment proofs need to
  know that a deeper call's direct parent is already in the frame child's
  pending segment.
- `dfs_tree_step_transport_from_monotone_fields` and
  `dfs_tree_reachable_transport_from_monotone_fields` are the one-way tree
  transport lemmas for phases like `preloop`, where visited grows rather than
  staying equivalent.
- `PreloopProducesPendingChildSegmentFromFrameCompatibilityCandidate_proof`
  consumes the parent-aware compatibility and direct `ChildEntryCandidate` to
  prove that the direct child is in the suspended frame child's pending segment
  after `preloop child`.
- `PreloopPreservesFrameSuspendedSegmentFieldsFromCompatibilityCandidate_proof`
  closes the two suspended segment fields through `preloop child`.
- The compiled preloop adapters now also include
  `PreloopPreservesFrameLoopInvLowCandidate_proof`,
  `PreloopPreservesFrameDoneClosednessCandidate_proof`, and
  `PreloopPreservesFrameActiveProcessedChildSegmentSummaryCandidate_proof`.
  These do not widen `FrameInvCandidate`; they transport only the old
  frame-`done` and frame-parent facts that their consumers require.
- `PreloopPreservesFrameProcessedTreeChildrenCorrectCandidate_proof` closes
  the remaining preloop frame-field transport.  The body frame contract is now
  premise-free via
  `BodyPreservesFrameContractCandidate_from_phase9_cuts_proof`.
- `BodyPreservesFrameProgressContractCandidate_proof` closes the auxiliary
  frame-progress recursive contract.
- The remaining concrete dependency is not a recursive child-body accounting
  producer.  The attempted framed producer is still too early for the current
  predicate boundaries because `ParentLowBelowChildCandidate` and
  `PendingChildSegmentEscapeAccountedCandidate` are produced after
  `get low child ;; update_low parent`.  The next target is to narrow the
  recursive low-contribution post to the four child/local fields and assemble
  `ParentPendingChildEscapeAccountedCandidate parent done child` plus
  `ActiveTargetBlocksEscapeAccountedCandidate parent (done_after done child)`
  in the tree-branch continuation after the parent update.

## 11. Open Checks Before Implementation

Before starting the Rocq proof, each of these should be made explicit:

1. Exact public API: `low_pre_full` theorem only, or old `low_pre` wrapper.
2. Exact `tree_child_characterization` lemma used by the root bridge.
3. Exact root-pop lemmas for stack-sensitive `scc_low_valid_v` and `scc_is_low_v`.
4. Exact contradiction lemma for visited-but-new direct tree child cases in `process_edge`.
5. Proper/monotone lemmas for `children_is_low` under `done == done'`.

These checks are the Tarjan analogue of Kosaraju's `Q_phase1` and `R` design:
the proof should only promote a fact into an invariant after its producer,
consumer, and lifetime are known.
