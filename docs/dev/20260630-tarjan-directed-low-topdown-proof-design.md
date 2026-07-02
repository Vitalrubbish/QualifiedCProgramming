# Tarjan-Directed-Low-Topdown-Proof-Design
**Author**: Codex
**Date**: 2026-06-30

## 1. 方法原则

本文档从主定理出发，自顶向下分解证明需求。除程序结构本身外，不预设任何现有 low-link 定义或已证明定理是合理接口。

已有名字只能作为候选实现：

```text
Need -> Semantic interface -> Candidate definition/lemma -> Audit -> Use or replace
```

设计时必须先回答：

- final theorem 真正需要什么语义事实；
- 每个程序 cut 消费什么事实；
- 每个事实由哪个前序 cut 产生；
- 事实是否跨 `pop_scc` 稳定；
- 事实是否需要被 recursive frame 保持。

不能因为某个定义已经存在或某个定理已经可证明，就把它作为证明主线的一部分。

## 2. 主定理

目标分两层。

### 2.1 Low-layer theorem

递归 low 层 theorem 显式要求调用环境已经满足 settled 区域闭合：

```coq
Theorem tarjan_scc_low_layer_correct (u: V):
  Hoare
    (fun s =>
       EntryPre u s)
    (tarjan_scc g u)
    (fun _ s =>
       RootFinal u s).
```

其中先不绑定到已有定义：

```coq
EntryPre u s :=
  state_well_formed_for_low_entry u s /\
  settled_region_closed s /\
  order_side_conditions s.

RootFinal u s :=
  state_well_formed_for_low s /\
  settled_region_closed s /\
  u_visited u s /\
  root_low_correct_final u s /\
  order_side_conditions s.
```

### 2.2 Public theorem

如果最终 public theorem 不能要求 `settled_region_closed`，则必须另有 wrapper：

```coq
Theorem tarjan_scc_public_correct (u: V):
  Hoare
    (fun s =>
       PublicEntryPre u s /\
       PublicEntryPre_implies_EntryPre u s)
    (tarjan_scc g u)
    (fun _ s =>
       PublicRootFinal u s).
```

这个 wrapper 是 API 设计问题，不应混入递归 low-layer 证明。

## 3. 程序 Cut

只根据程序结构设 cut：

```coq
tarjan_scc_f g W u =
  preloop u;;
  edge_loop u W;;
  maybe_pop u
```

其中：

```coq
edge_loop u W :=
  forset (fun a => edge u a) (process_edge u W)

maybe_pop u :=
  If (fun s => root_condition u s) (pop_scc u)
```

Cut 列表：

| Cut | 位置 | 后续 consumer |
|---|---|---|
| `C0` | call entry | `preloop` |
| `C1` | after `preloop` | edge loop |
| `Cedge(done)` | after processed outgoing set `done` | next edge / loop done |
| `Cdone` | after all outgoing edges | root bridge |
| `Croot` | before pop | maybe-pop |
| `Cfinal` | after maybe-pop | theorem post |

## 4. 从 Final Post 反推

### 4.1 `maybe_pop` 必须证明什么

最终只要求 root-level correctness，不要求 whole-subtree correctness：

```coq
RootFinal u s_final
```

因此 `maybe_pop` 的 pre-pop cut 应提供：

```coq
PrePopRootReady u s :=
  LoopDone u s /\
  root_low_correct_prepop u s.
```

`maybe_pop` obligation：

```coq
Hoare
  (PrePopRootReady u)
  (maybe_pop u)
  (fun _ s => RootFinal u s).
```

这里必须分清两个语义：

```coq
root_low_correct_prepop u s
root_low_correct_final u s
```

它们可以相同，也可以不同。若 low correctness 引用了当前 stack，则必须证明 root 在 pop 后仍正确，或者把 final correctness 定义成 pop-stable 的形式。

### 4.2 Root-pop lemma 的需求

Pop branch 需要一个专门接口：

```coq
RootPopBridge:
  LoopDone u s ->
  root_condition u s ->
  root_low_correct_prepop u s ->
  pop_effect u s s' ->
  root_low_correct_final u s'.
```

这个 lemma 不能假设所有 descendant 的 low correctness 在 pop 后仍成立。

### 4.3 Settled-region update 的需求

Pop branch 还需要：

```coq
SegmentClosedAtRoot:
  LoopDone u s ->
  root_condition u s ->
  popped_segment_closed u s.

SettledClosedAfterPop:
  settled_region_closed s ->
  popped_segment_closed u s ->
  pop_effect u s s' ->
  settled_region_closed s'.
```

这两个需求决定 edge loop 是否必须维护 segment accounting 类事实。

## 5. 从 Root Bridge 反推

`Cdone -> Croot` 的目标是：

```coq
LoopDone u s ->
root_low_correct_prepop u s.
```

不要先假设已有 `low_valid` 或 `is_low` 定义。先抽象 root correctness 所需的最小输入：

```coq
RootEquationReady u s :=
  root_low_equation u s /\
  direct_tree_children_low_correct u s.
```

Root bridge：

```coq
RootBridge:
  LoopDone u s ->
  RootEquationReady u s ->
  root_low_correct_prepop u s.
```

因此 `LoopDone` 必须至少能导出：

```coq
root_low_equation u s
direct_tree_children_low_correct u s
```

这两个事实分别来自不同 producer：

- `root_low_equation` 来自所有 outgoing edge 处理完后的 low-value equation；
- `direct_tree_children_low_correct` 来自每个 recursive child 的 post。

## 6. Edge Loop 需要维护什么

对 `done` 的 loop cut：

```coq
LoopInv u done s
```

只根据 consumer 推导字段。

### 6.1 为 RootBridge 服务的字段

当 `done = edge u` 时必须得到：

```coq
root_low_equation u s
direct_tree_children_low_correct u s
```

所以 loop invariant 需要：

```coq
partial_root_low_equation u done s
processed_tree_children_low_correct u done s
```

### 6.2 为 SegmentClosedAtRoot 服务的字段

当 `done = edge u` 且 `root_condition u s` 时必须得到：

```coq
popped_segment_closed u s
```

所以 loop invariant 需要能说明：

```coq
segment_escape_accounting u done s
segment_coverage_by_processed_edges u done s
```

这些名字只是语义接口，不等同于任何已有定义。

### 6.3 为 directed active-descendant branch 服务的字段

处理 visited-stack edge 时，若 target 是 active descendant，parent 需要 child segment 的已完成 summary。

所以 loop invariant 需要：

```coq
active_processed_child_segment_summary u done s
```

但该 summary 的内容应由 branch consumer 决定，不应默认等于完整 child `LoopDone`。

### 6.4 为普通 DFS 结构服务的字段

edge loop 还需要基础 DFS bookkeeping：

```coq
local_dfs_shape u done s
done_vertices_visited u done s
done_closed_when_settled u done s
tree_parent_consistency u done s
order_side_conditions s
```

这些字段只应包含 branch proof 必须消费的内容。

## 7. Derived Loop Interface

自顶向下得到的 loop interface 是：

```coq
LoopInv u done s :=
  local_dfs_shape u done s /\
  partial_root_low_equation u done s /\
  processed_tree_children_low_correct u done s /\
  segment_escape_accounting u done s /\
  segment_coverage_by_processed_edges u done s /\
  active_processed_child_segment_summary u done s /\
  order_side_conditions s.

LoopEntry u s := LoopInv u empty s.
LoopDone u s := LoopInv u (edge u) s.
```

Audit rule:

- If a field is not consumed by RootBridge, SegmentClosedAtRoot, process-edge branches, or final side conditions, remove it.
- If a field cannot be produced by preloop, process-edge, or child post, weaken or replace it.

## 8. `preloop` Obligation

`preloop` must establish:

```coq
Hoare
  (EntryPre u)
  (preloop u)
  (fun _ s => LoopEntry u s).
```

This determines what `LoopEntry` may contain:

- `u` is visited and active;
- low/dfn initialized for `u`;
- no outgoing edge has been processed;
- partial root equation is initialized to the self case;
- processed-child correctness is vacuous;
- active child summaries are vacuous;
- segment accounting/coverage must have an empty-done base case.

If any proposed field cannot be initialized here, it is not a valid loop invariant field.

## 9. `process_edge` Branch Decomposition

The main loop step:

```coq
ProcessEdgeStep:
  ChildContract W ->
  FrameContract W ->
  edge u a ->
  ~ done a ->
  Hoare
    (fun s => LoopInv u done s)
    (process_edge u W a)
    (fun _ s => LoopInv u (done ∪ singleton a) s).
```

### 9.1 Unvisited child branch

Consumer need:

```coq
ChildPost u a done s'
```

to extend:

```coq
processed_tree_children_low_correct u (done ∪ [a]) s'
partial_root_low_equation u (done ∪ [a]) s'
active_processed_child_segment_summary u (done ∪ [a]) s'
segment_escape_accounting u (done ∪ [a]) s'
segment_coverage_by_processed_edges u (done ∪ [a]) s'
```

Therefore `ChildPost` should contain exactly:

```coq
parent_resume_shape u a done s' /\
child_root_low_correct_final_or_prepop a s' /\
child_segment_summary_if_active a s' /\
child_closedness_contribution u a done s'.
```

Important audit point: if child was popped, parent should not rely on child subtree stack-sensitive correctness. It may rely only on child root final correctness and closedness contribution.

### 9.2 Visited non-stack branch

Needed theorem:

```coq
VisitedNonStackStep:
  LoopInv u done s ->
  edge u a ->
  visited a s ->
  not_active a s ->
  LoopInv u (done ∪ [a]) s.
```

This branch must discharge any new processed-child obligation. Therefore one of the following must be true:

- `a` cannot be a new direct tree child of `u`; or
- the needed child correctness follows from settled-region closedness/finalized correctness.

This is an explicit design choice, not something to hide in an old lemma.

### 9.3 Visited active ancestor branch

Needed theorem:

```coq
VisitedAncestorStep:
  LoopInv u done s ->
  edge u a ->
  active a s ->
  ancestor_of a u s ->
  update_low_effect u (dfn a) s s' ->
  LoopInv u (done ∪ [a]) s'.
```

This branch produces an old-stack escape explanation and updates the partial root low equation.

### 9.4 Visited active descendant branch

Needed theorem:

```coq
VisitedDescendantStep:
  LoopInv u done s ->
  edge u a ->
  active a s ->
  descendant_of u a s ->
  active_processed_child_segment_summary u done s ->
  update_low_effect u (dfn a) s s' ->
  LoopInv u (done ∪ [a]) s'.
```

This branch decides the exact strength of `active_processed_child_segment_summary`.
The summary should be no stronger than needed to lift descendant escape accounting and segment coverage to parent.

## 10. Child Contract

`ChildContract` is not copied from existing definitions. It is derived from unvisited-child branch consumers:

```coq
ChildContract W :=
  forall parent child done,
    edge parent child ->
    ~ done child ->
    Hoare
      (ChildEntry parent child done)
      (W child)
      (fun _ s => ChildPost parent child done s).
```

`ChildEntry` is whatever `set_fa child parent` establishes before the recursive call:

```coq
ChildEntry parent child done s :=
  parent_loop_context_before_child parent child done s /\
  state_well_formed_for_low_entry child s /\
  parent_is_visited_and_active parent s /\
  parent_child_edge parent child.
```

`ChildPost` must serve exactly these consumers:

| Consumer | Needed from child |
|---|---|
| parent low equation | child root low value is meaningful |
| parent root bridge | child root low correctness |
| parent active-descendant branch | child segment summary if child remains active |
| parent closedness | child contributes done-tree closedness |
| parent resume | parent pending/frame facts still hold |

Therefore:

```coq
ChildPost parent child done s :=
  parent_resume_shape parent child done s /\
  child_root_low_correct_for_parent child s /\
  child_closedness_contribution parent child done s /\
  (active child s -> child_segment_summary child s).
```

## 11. Frame Contract

Frame facts are also derived from consumers, not old modes.

An outer frame is needed when a recursive call occurs while another parent loop is suspended.

```coq
Frame F := {
  frame_parent : V;
  frame_child  : V;
  frame_done   : V -> Prop
}

FrameInv F s :=
  parent_resume_shape
    (frame_parent F) (frame_child F) (frame_done F) s /\
  outer_loop_low_fields (frame_parent F) (frame_done F) s /\
  suspended_parent_frame_resume
    (frame_parent F) (frame_child F) (frame_done F) s /\
  outer_done_closedness (frame_parent F) (frame_done F) s /\
  outer_processed_tree_children_correct
    (frame_parent F) (frame_done F) s /\
  outer_active_child_segment_summaries
    (frame_parent F) (frame_done F) s /\
  outer_segment_escape_accounting (frame_parent F) (frame_done F) s.
```

`FrameContract`:

```coq
FrameContract W :=
  forall F direct_parent child direct_done,
    Hoare
      (fun s =>
         FrameInv F s /\
         frame_compatible_with_call F child s /\
         ChildEntry direct_parent child direct_done s)
      (W child)
      (fun _ s => FrameInv F s).
```

Audit rule:

- If a frame field is not needed after the inner call returns, remove it.
- If a frame field is not preserved by `preloop`, edge loop, or pop of the inner call, it must not be in `FrameInv`; replace it by a weaker pop-stable summary.
- A frame is produced from an outer loop invariant plus the pending child's
  resume shape, not from the loop invariant alone.  The pending child is part
  of the continuation state because later child-post reconstruction consumes
  exactly that resume shape.
- During the suspended call, normal `parent_frame_resume parent done` is too
  strong: the current pending child is deliberately `~ done` and has
  `fa child = parent`.  Use a suspended variant that allows this one exception,
  and prove a closure lemma that restores the normal parent-frame field after
  adding the child to `done_after`.
- The frame contract should only cover compatible calls: either the recursive
  call is the frame's own pending child, or the frame child has already been
  visited before a deeper call.  Do not require preservation for arbitrary
  unrelated frames.
- Field-level producers may consume the whole frame invariant.  The design
  should decompose the postcondition by consumer fields, not artificially
  restrict each proof to a single-field precondition.

## 12. Candidate Mapping to Existing Names

Only after the semantic interfaces above are fixed should existing definitions be considered.

| Semantic need | Candidate existing name | Audit question |
|---|---|---|
| `state_well_formed_for_low_entry u` | `wf_scc_state_pre u` | Is this exactly the `preloop u` entry shape, including `u` unvisited? |
| `state_well_formed_for_low` | `wf_scc_state` | Does it contain exactly the stable structural facts needed after `preloop`? |
| `settled_region_closed` | `settled_closed` | Is it preserved/extended by pop as needed? |
| `root_low_correct_prepop` | `scc_low_valid_v` + `scc_is_low_v` | Are these stack-sensitive; can root be transported over pop? |
| `partial_root_low_equation` | `low_frontier` + `low_src` + child low summaries | Is this minimal, or overfitted to old proof? |
| `processed_tree_children_low_correct` | `children_low_valid`, `children_is_low` | Is root child correctness enough, or is subtree correctness needed pre-pop? |
| `segment_escape_accounting` | `segment_escape_accounted` | Does it exactly support descendant branch and root segment closure? |
| `segment_coverage_by_processed_edges` | `stack_segment_covered_by_done` | Is it independent, or can it be merged with accounting? |
| `active_processed_child_segment_summary` | `active_done_child_segment_summaries` | Is full child loop done too strong? |
| `parent_resume_shape` | `low_tree_child_parent_pending` | Does it mix unrelated fields? |
| `RootBridge` | `low_frontier_and_src_imply_low_valid`, `scc_is_low_induction_is_low` | Are assumptions phase-correct and root-only? |

If any candidate fails its audit, replace the definition or theorem interface before proof work starts.

## 13. Theorem Plan Generated by the Top-Down Design

### Layer A: semantic interface definitions

Define the abstract predicates or choose audited existing definitions for:

```coq
EntryPre
RootFinal
LoopInv
LoopEntry
LoopDone
ChildEntry
ChildPost
FrameInv
```

### Layer A0: producer audits for candidate mappings

Before committing the semantic interface to existing definitions, audit the
two earliest producers:

```coq
PreloopGlobalShape:
  Hoare (GlobalShapePre u) (preloop u) (fun _ s => GlobalShape s).

PreloopBaseFacts:
  Hoare (EntryPre u) (preloop u) (fun _ s => LoopEntryBase u s).

SetFaGlobalShapePre:
  Hoare
    (fun s => GlobalShape s /\ Visited parent s /\ Unvisited child s)
    (set_fa child parent)
    (fun _ s => GlobalShapePre child s /\ Visited parent s).

SetFaChildEntry:
  Hoare
    (fun s => ParentLoopSuspended parent child done s /\ Unvisited child s)
    (set_fa child parent)
    (fun _ s => ChildEntry parent child done s).
```

These audits are intentionally before the full `LoopInv`: if either producer
cannot establish its advertised target, the predicate ledger is wrong and must
be revised before proof search.

### Layer B: cut transition theorems

```coq
PreloopEntry:
  Hoare EntryPre preloop LoopEntry.

ProcessEdgeStep:
  ChildContract W ->
  FrameContract W ->
  edge u a ->
  ~ done a ->
  Hoare (LoopInv u done) (process_edge u W a)
        (fun _ s => LoopInv u (done ∪ [a]) s).

EdgeLoopDone:
  ChildContract W ->
  FrameContract W ->
  Hoare (LoopEntry u) (edge_loop u W)
        (fun _ s => LoopDone u s).

RootBridge:
  LoopDone u s ->
  root_low_correct_prepop u s.

MaybePopFinal:
  Hoare (fun s => LoopDone u s /\ root_low_correct_prepop u s)
        (maybe_pop u)
        (fun _ s => RootFinal u s).
```

### Layer C: recursive body contracts

```coq
BodySatisfiesChildContract:
  ChildContract W ->
  LowContributionContract W ->
  FrameContract W ->
  ChildContract (tarjan_scc_f g W).

BodyProvidesLowContributionContract:
  ChildContract W ->
  LowContributionContract W ->
  FrameContract W ->
  LowContributionContract (tarjan_scc_f g W).

BodyPreservesFrameContract:
  ChildContract W ->
  LowContributionContract W ->
  FrameContract W ->
  FrameContract (tarjan_scc_f g W).
```

Status:

- The concrete child-contract bundle has started with
  `ChildPostCandidate` and `ChildContractCandidate`.
- `ChildContractCandidate_from_field_statements_proof` composes the previously
  audited child-post field statements into the combined child contract.
- `LowContributionContract` is now explicit in the abstract interface because
  `process_edge`'s tree branch consumes parent low-equation preservation
  across the recursive call.
- The body-level producers for the child, low-contribution, and
  frame-preservation contracts remain to be assembled for `tarjan_scc_f g W`.

### Layer D: fixpoint theorem

```coq
FixpointLowLayerCorrect:
  Hoare EntryPre (tarjan_scc g u) RootFinal.
```

Status:

- The abstract fixed-point assembly is now proved by
  `LowLayerCorrect_from_obligations_proof`.
- The proof uses `LowFixMode` as the `Hoare_fix_logicv` logic variable and
  projects the combined IH into `ChildContract`, `LowContributionContract`,
  and `FrameContract` before each body step.
- The remaining work is below this layer: prove the concrete
  body obligations for `tarjan_scc_f g W`.

Then derive public projections/wrappers only after the low-layer theorem is stable.

## 14. Stop Conditions

During implementation, stop and revise the design if any of the following occurs:

1. A proposed invariant field has no direct consumer in Sections 4 or 9.
2. A field is consumed but has no producer in `preloop`, `process_edge`, or `ChildPost`.
3. A stack-sensitive fact is used after `pop_scc` without a dedicated pop bridge.
4. A frame field cannot be preserved by the entire inner recursive body.
5. A candidate existing lemma requires assumptions that are not available at its cut.

These are design failures, not proof-search failures.
