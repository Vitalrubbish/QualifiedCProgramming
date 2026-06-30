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
  scc_low_valid_v g root s u /\
  scc_is_low_v g root s u.
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
scc_low_valid_v g root s u /\
scc_is_low_v g root s u.
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
- child root low-valid;
- child root is-low;
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
low_tree_child_parent_pending u a done s'
done_tree_reachable_closed g u (done ∪ [a]) s'
low_full_valid_post a s'
scc_is_low_v g root s' a
(In a (stack s') -> low_segment_loop_done a s')
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
  low_tree_child_parent_pending
    (frame_parent F) (frame_child F) (frame_done F) s /\
  segment_escape_accounted
    (frame_parent F) (frame_done F) s /\
  stack_segment_covered_by_done
    (frame_parent F) (frame_done F) s /\
  active_done_child_segment_summaries
    (frame_parent F) (frame_done F) s /\
  children_is_low
    (frame_parent F) (frame_done F) s.
```

Frame field ledger:

| Frame field | Why it must be preserved |
|---|---|
| `low_tree_child_parent_pending` | parent must resume after child with pending facts intact |
| `segment_escape_accounted` | parent pop and active-descendant branches depend on it |
| `stack_segment_covered_by_done` | parent segment lifting depends on it |
| `active_done_child_segment_summaries` | already processed active child summaries must not disappear |
| `children_is_low` | parent root bridge consumes it after parent loop finishes |

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
low_segment_loop_done_implies_low_valid_root
low_segment_loop_done_implies_is_low_root
```

The second lemma depends on:

```coq
scc_is_low_induction_is_low
children_is_low u (dg_step g u) s
tree_child_characterization
```

### Layer 3: segment closure and root pop

```coq
low_segment_loop_done_root_implies_segment_closed
pop_scc_preserves_or_reconstructs_root_low_valid
pop_scc_preserves_or_reconstructs_root_is_low
if_pop_preserves_low_full_post
```

Important: root correctness after pop should be a dedicated lemma. It should not
be treated as automatic preservation of stack-sensitive low-valid facts.

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
| LowFrameMode (outer: low_frame)
               (direct_parent: V)
               (direct_done: V -> Prop).
```

`LowRootMode` consumes the final proof path:

```text
C0 -> C1 -> Cdone -> Croot -> Cfinal
```

`LowChildMode` exists because parent `process_edge` needs a child post.

`LowFrameMode` exists because an inner recursive call must preserve the outer continuation state.

Do not add a new mode unless a ledger consumer cannot be served by these three.

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
