# Tarjan-Directed-Recursive-Phase-Proof-Plan
**Author**: Codex
**Date**: 2026-07-07

## 1. 目标

本文档基于 `20260707-tarjan-directed-recursive-contract-design.md`，给出递归层每个阶段的证明计划。

最终目标是：

```coq
tarjan_scc_f_preserves_visit_contract:
  VisitContract W ->
  VisitContract (tarjan_scc_f W).
```

其中：

```coq
VisitContract W :=
  VisitMainContract W /\
  VisitChildContract W /\
  VisitFrameContract W.
```

当前阶段不要直接冲最终 theorem；应先完成相邻阶段 bridge theorem。

## 2. 阶段 0：`set_fa` 建立递归入口

已有：

```coq
set_fa_pending_prepares_child_entry:
  Hoare
    (fun s =>
       LoopInv parent done s /\
       Edge parent child /\
       ~ Visited child s)
    (set_fa child parent)
    (fun _ s =>
       LoopInv parent done s /\
       EntryPre child s /\
       fa s child = parent /\
       fa s child <> child).
```

建议补包装 theorem：

```coq
set_fa_pending_prepares_parent_recursive_pre:
  Hoare
    (fun s =>
       LoopInv parent done s /\
       Edge parent child /\
       ~ Visited child s)
    (set_fa child parent)
    (fun _ s =>
       ParentRecursivePre parent child done s).
```

证明方式只是重排字段。`Edge parent child` 应来自 precondition，不要从 `EntryPre child` 中反推出，避免让证明依赖不必要的 `fa` 细节。

## 3. 阶段 1：`preloop` 建立当前调用 `LoopInv`

已有：

```coq
preloop_initializes_loop_inv:
  Hoare
    (EntryPre u)
    (preloop u)
    (fun _ s => LoopInv u ∅ s).
```

它服务于三条 pipeline：

```text
main line:              EntryPre u -> LoopInv u ∅
child-return line:      EntryPre child -> LoopInv child ∅
frame-preservation line: EntryPre next -> LoopInv next ∅
```

这一 theorem 已完成，不需要改变 statement。

## 4. 阶段 1b：`preloop child` 建立 immediate parent frame

目标：

```coq
preloop_establishes_parent_frame_for_child:
  Hoare
    (ParentRecursivePre parent child done)
    (preloop child)
    (fun _ s =>
       exists s_before,
         LoopInv child ∅ s /\
         LoopInv parent done s_before /\
         ParentFrameForChild parent child done s_before s).
```

证明计划：

1. 取 `s_before` 为 `preloop child` 前状态。
2. `LoopInv child ∅ s` 由 `preloop_initializes_loop_inv`。
3. `LoopInv parent done s_before` 直接来自 `ParentRecursivePre`。
4. `ParentLowFrame parent done s_before s` 需要证明 `preloop child` 不改变 parent low，也不改变 parent 旧 `done` candidate 集。
5. `LoopCoreShape parent (done_after done child) s`：旧 done 字段来自 `LoopInv parent done s_before`，新 child 字段来自 `Edge parent child`、`Visited child s`、`fa s child = parent`。
6. `LoopAuxFacts parent s`：parent 仍 active，`OrderFacts` 由 preloop 保持，`NoUnvisitedReach` 由 `preloop_keep_settled_closed`。
7. `dfn parent < dfn child` 由 `preloop_after_visited_dfn_lt`，前提来自 parent 的 `LoopCoreShape` 和 child 的 `EntryPre`。

建议先拆：

```coq
preloop_preserves_parent_low_frame:
  Hoare
    (ParentRecursivePre parent child done)
    (preloop child)
    (fun _ s =>
       exists s_before,
         ParentLowFrame parent done s_before s).
```

若 candidate 集等价难证，再拆成：

```coq
preloop_preserves_parent_old_candidates_forward
preloop_preserves_parent_old_candidates_backward
```

这一步的关键风险是 child 新入栈后成为 active vertex。必须证明 parent 旧 `done` 的 partial tree 不会新增到 child 的 active target；不能把这个风险塞进 `LoopInv`。

## 5. 阶段 1c：`preloop next` 保持 outer frame

目标：

```coq
preloop_preserves_nested_parent_frame:
  Hoare
    (NestedFramePre ancestor current loop_root next
       ancestor_done loop_done s_before)
    (preloop next)
    (fun _ s =>
       LoopInv next ∅ s /\
       ParentFrameForChild ancestor current ancestor_done s_before s).
```

证明计划：

1. `LoopInv next ∅` 由 `preloop_initializes_loop_inv`。
2. `ParentFrameForChild ancestor current ...` 的字段保持类似阶段 4，但这里 `current` 是被保护 frame 中的 child，`loop_root` 是实际调用 `next` 的当前 edge-loop root。
3. `ParentLowFrame ancestor ancestor_done s_before` 的 candidate 集不应因 `next` 新入栈而变化。
4. `LoopAuxFacts ancestor`、`Closed`、`TreeEdgesAreGraphEdges` 用 preloop 保持 lemma。
5. `dfn ancestor < dfn current` 不变；不需要证明 `dfn current < dfn next`，除非后续 frame predicate 显式需要。

这个 theorem 是 `VisitFrameContract (tarjan_scc_f W)` 的 preloop 部分。

## 6. 阶段 2：edge loop 保持当前调用 `LoopInv`

已有核心 theorem：

```coq
edge_loop_preserves_loop_inv:
  (forall done v, ... ChildContributionContract u v done ...) ->
  Hoare
    (fun s => LoopInv u ∅ s)
    (forset (edge_set u) (process_edge u W))
    (fun _ s => LoopInv u (edge_set u) s).
```

建议补包装：

```coq
edge_loop_preserves_loop_inv_from_visit_contract:
  VisitChildContract W ->
  Hoare
    (fun s => LoopInv u ∅ s)
    (forset (edge_set u) (process_edge u W))
    (fun _ s => LoopInv u (edge_set u) s).
```

证明只需展开 `VisitChildContract W`，把它适配到 `edge_loop_preserves_loop_inv` 的递归调用参数。

## 7. 阶段 2b：edge loop 保持 immediate parent frame

目标：

```coq
edge_loop_preserves_parent_frame_for_child:
  VisitChildContract W ->
  VisitFrameContract W ->
  Hoare
    (fun s =>
       LoopInv child ∅ s /\
       ParentFrameForChild parent child done s_before s)
    (forset (edge_set child) (process_edge child W))
    (fun _ s =>
       LoopInv child (edge_set child) s /\
       ParentFrameForChild parent child done s_before s).
```

证明计划：

1. `LoopInv child ...` 由阶段 6 的 current-line theorem 维护。
2. `ParentFrameForChild parent child ...` 需要对 `process_edge child W a` 做逐边保持。
3. visited-active 分支只执行 `update_low child dfn[a]`，不改 parent low、parent old candidate、fa、visited、stack。
4. visited-inactive 分支是 skip，frame 直接保持。
5. unvisited tree-child 分支中：
   - `set_fa a child` 不应破坏外层 parent frame，因为 `a` 未 visited。
   - `W a` 保持外层 frame，使用 `VisitFrameContract W` 与 `NestedFramePre parent child child a ...`。
   - `update_low child low[a]` 不改 parent frame。
6. 用 `Hoare_forset` 或现有 forset induction 把 process-edge frame theorem 提升到整个 edge loop。

建议拆：

```coq
process_edge_preserves_parent_frame_for_child:
  VisitChildContract W ->
  VisitFrameContract W ->
  Hoare
    (fun s =>
       LoopInv child current_done s /\
       ParentFrameForChild parent child done s_before s /\
       Edge child a /\
       ~ current_done a)
    (process_edge child W a)
    (fun _ s =>
       ParentFrameForChild parent child done s_before s).
```

然后再证明：

```coq
forset_process_edge_preserves_parent_frame_for_child
```

如果这一阶段没有 `VisitFrameContract W`，unvisited grandchild 分支会缺少递归调用保持外层 frame 的 IH，这是上一版大证明容易失控的位置。

## 8. 阶段 2c：edge loop 保持 outer frame

目标：

```coq
edge_loop_preserves_nested_parent_frame:
  VisitChildContract W ->
  VisitFrameContract W ->
  Hoare
    (fun s =>
       LoopInv next ∅ s /\
       ParentFrameForChild ancestor current ancestor_done s_before s)
    (forset (edge_set next) (process_edge next W))
    (fun _ s =>
       LoopInv next (edge_set next) s /\
       ParentFrameForChild ancestor current ancestor_done s_before s).
```

证明结构与阶段 7 相同，只是 `current` 不是当前 edge loop root，而是更外层需要保护的 ancestor frame 的 child。建议复用更一般的 theorem：

```coq
edge_loop_preserves_external_parent_frame:
  VisitChildContract W ->
  VisitFrameContract W ->
  Hoare
    (fun s =>
       LoopInv loop_root ∅ s /\
       ParentFrameForChild ancestor current ancestor_done s_before s)
    (forset (edge_set loop_root) (process_edge loop_root W))
    (fun _ s =>
       LoopInv loop_root (edge_set loop_root) s /\
       ParentFrameForChild ancestor current ancestor_done s_before s).
```

然后阶段 7 取 `loop_root = child` 且 `current = child`，阶段 8 取 `loop_root = next`。

## 9. 阶段 3：edge loop 后桥接到 `RootPrePop`

定义展开 theorem：

```coq
edge_loop_post_to_root_pre_pop:
  LoopInv u (edge_set u) s ->
  StackRestOlderThanRoot u s ->
  RootPrePop u s.
```

真正需要证明：

```coq
loop_inv_derives_stack_rest_older_than_root:
  LoopInv u (edge_set u) s ->
  StackRestOlderThanRoot u s.
```

证明计划：

1. `LoopAuxFacts u s` 给出 `Active u s` 和 `OrderFacts s`。
2. 对任意 `b` 满足 `RestStack u s b`，先用列表结构 lemma 得到 `b` 在 stack 中位于 `u` 下方。
3. 由 `stack_dfn_order_strict`、`StackNoDup`、`dfn_injective` 推出 `dfn s b < dfn s u`。

建议列表 lemma：

```coq
rest_stack_below_root:
  Active u s ->
  RestStack u s b ->
  exists l1 l2,
    stack s = l1 ++ u :: l2 /\ In b l2.
```

## 10. 阶段 3b：构造 `ChildReturnPreMaybePop`

目标：

```coq
edge_loop_post_to_child_return_pre_maybe_pop:
  LoopInv child (edge_set child) s ->
  ParentFrameForChild parent child done s_before s ->
  ChildReturnPreMaybePop parent child done s_before s.
```

证明：

1. 用阶段 9 得到 `RootPrePop child s`。
2. 合并 `ParentFrameForChild parent child done s_before s`。

这个 theorem 应该只是组合，不应引入新的数学事实。

## 11. 阶段 4：maybe_pop 产生当前调用 `RootFinal`

目标：

```coq
maybe_pop_produces_root_final:
  Hoare
    (RootPrePop u)
    (If (fun s => low s u = dfn s u) (pop_scc u))
    (fun _ s => RootFinal u s).
```

证明计划：

1. skip-pop 分支状态不变，用 `RootLowCorrect u` 推出 `scc_is_low_v s u`。
2. pop 分支先由 `RootLowCorrect u` 和 `low[u] = dfn[u]` 产生 pop-local cuts。
3. 用 `PoppedSegmentClosed` 恢复 `NoUnvisitedReach`。
4. 用 `PoppedSegmentNoActiveReach` 恢复 `Closed`。

这里不应依赖任何 parent frame。

## 12. 阶段 4b：maybe_pop 产生 child contribution

目标：

```coq
maybe_pop_produces_child_contribution:
  Hoare
    (ChildReturnPreMaybePop parent child done s_before)
    (If (fun s => low s child = dfn s child) (pop_scc child))
    (fun _ s =>
       ChildContributionContract parent child done s_before s).
```

证明计划：

1. skip-pop 分支选择 `ChildLowContribution` 的 active 分支：

```coq
Active child s /\
LoopCoreShape child (edge_set child) s /\
RootLowCorrect child s.
```

2. pop 分支选择 inactive 分支：

```coq
~ Active child s_after /\
low s_after child = dfn s_after child /\
dfn s_after parent < dfn s_after child /\
ChildNoActiveTarget child s_after.
```

3. `ParentLowFrame`、`LoopCoreShape parent (done_after done child)`、`LoopAuxFacts parent`、`Closed`、`TreeEdgesAreGraphEdges` 由 `ChildReturnPreMaybePop` 和 pop frame lemmas 保持。
4. `ChildNoActiveTarget` 由 `PoppedSegmentNoActiveReach` 和 pop 后 active stack 等于 pre-pop rest stack 推出。

## 13. 阶段 4c：maybe_pop 保持 outer frame

目标：

```coq
maybe_pop_preserves_nested_parent_frame:
  Hoare
    (fun s =>
       RootPrePop next s /\
       ParentFrameForChild ancestor current ancestor_done s_before s)
    (If (fun s => low s next = dfn s next) (pop_scc next))
    (fun _ s =>
       ParentFrameForChild ancestor current ancestor_done s_before s).
```

证明计划：

1. skip-pop 分支状态不变，直接保持 frame。
2. pop 分支需要证明 `pop_scc next` 不弹出 `current` 或 `ancestor`，因为它们在 stack 中比 `next` 更老。
3. `ParentLowFrame ancestor ancestor_done` 只谈 ancestor 旧 `done` candidates；需要证明 pop 掉 `next` segment 不会删除这些 candidates。
4. `LoopAuxFacts ancestor` 中 `Active ancestor` 由 stack-below preservation 保持。
5. `Closed` 与 `NoUnvisitedReach` 由 maybe_pop 的 pop-local cuts 恢复。

这条 theorem 是 `VisitFrameContract (tarjan_scc_f W)` 的 maybe_pop 部分。

## 14. 阶段 5：组合当前调用主线

目标：

```coq
tarjan_scc_f_produces_root_final:
  VisitContract W ->
  Hoare
    (EntryPre u)
    (tarjan_scc_f W u)
    (fun _ s => RootFinal u s).
```

组合顺序：

1. `preloop_initializes_loop_inv`
2. `edge_loop_preserves_loop_inv_from_visit_contract`
3. `loop_inv_derives_stack_rest_older_than_root`
4. `maybe_pop_produces_root_final`

只使用 `VisitChildContract W`，不需要 parent frame。

## 15. 阶段 5b：组合 immediate-child 返回线

目标：

```coq
tarjan_scc_f_produces_child_contribution:
  VisitContract W ->
  Hoare
    (ParentRecursivePre parent child done)
    (tarjan_scc_f W child)
    (fun _ s =>
       exists s_before,
         LoopInv parent done s_before /\
         Edge parent child /\
         ChildContributionContract parent child done s_before s).
```

组合顺序：

1. `preloop_establishes_parent_frame_for_child`
2. `edge_loop_preserves_parent_frame_for_child`
3. `edge_loop_post_to_child_return_pre_maybe_pop`
4. `maybe_pop_produces_child_contribution`
5. 包装 existential postcondition。

这里同时使用 `VisitChildContract W` 和 `VisitFrameContract W`。

## 16. 阶段 5c：组合 outer frame preservation 线

目标：

```coq
tarjan_scc_f_preserves_nested_parent_frame:
  VisitContract W ->
  Hoare
    (NestedFramePre ancestor current loop_root next
       ancestor_done loop_done s_before)
    (tarjan_scc_f W next)
    (fun _ s =>
       ParentFrameForChild ancestor current ancestor_done s_before s).
```

组合顺序：

1. `preloop_preserves_nested_parent_frame`
2. `edge_loop_preserves_nested_parent_frame`
3. `loop_inv_derives_stack_rest_older_than_root`
4. `maybe_pop_preserves_nested_parent_frame`

这条线是为了在阶段 7 的 unvisited grandchild 分支中提供递归 IH。

## 17. 阶段 6：最终递归 contract

目标：

```coq
tarjan_scc_f_preserves_visit_contract:
  VisitContract W ->
  VisitContract (tarjan_scc_f W).
```

证明：

1. 展开 `VisitContract`。
2. `VisitMainContract` 用阶段 14。
3. `VisitChildContract` 用阶段 15。
4. `VisitFrameContract` 用阶段 16。

随后使用 fixpoint induction 得到：

```coq
tarjan_scc_satisfies_visit_contract:
  VisitContract tarjan_scc.
```

## 18. 推荐实现顺序

1. 在证明文件中加入 `ParentRecursivePre`、`ParentFrameForChild`、`ChildReturnPreMaybePop`、`NestedFramePre`、`VisitContract` 相关定义。
2. 证明 `set_fa_pending_prepares_parent_recursive_pre`。
3. 证明 `preloop_establishes_parent_frame_for_child`。
4. 证明 `preloop_preserves_nested_parent_frame`。
5. 证明 `edge_loop_preserves_loop_inv_from_visit_contract`。
6. 证明 `process_edge_preserves_parent_frame_for_child`。
7. 证明 `edge_loop_preserves_parent_frame_for_child`。
8. 泛化并证明 `edge_loop_preserves_nested_parent_frame`。
9. 证明 `loop_inv_derives_stack_rest_older_than_root`。
10. 证明 `edge_loop_post_to_child_return_pre_maybe_pop`。
11. 回到 maybe_pop 计划，证明 `maybe_pop_produces_root_final`。
12. 证明 `maybe_pop_produces_child_contribution`。
13. 证明 `maybe_pop_preserves_nested_parent_frame`。
14. 组合三条 `tarjan_scc_f_*` pipeline。
15. 组合 `tarjan_scc_f_preserves_visit_contract`。
16. 最后关闭 `tarjan_scc_satisfies_visit_contract`。

## 19. 阻塞条件

1. 如果 `ParentLowFrame` 在 preloop 中不可证，先拆 old-candidate frame lemma，不要扩大 `LoopInv`。
2. 如果 edge loop 中 unvisited grandchild 分支缺 IH，使用 `VisitFrameContract`，不要把 outer frame 混入 child 的 `LoopInv`。
3. 如果 maybe_pop 保持 outer frame 失败，需要补 stack segment preservation lemma，不能弱化 `ChildContributionContract`。
4. 如果 `RootLowCorrect -> scc_is_low_v` 需要额外结构事实，应从 `LoopCoreShape u (edge_set u)` 推出，不要把字段加入 `LowCorrect`。
5. 如果 pop-local facts 被迫加入 `LoopInv`，说明阶段边界错误，应回到 maybe_pop cut 设计。
