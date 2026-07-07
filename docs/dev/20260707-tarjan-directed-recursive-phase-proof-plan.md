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
4. `ParentLowFrame parent done s_before s` 需要证明 `preloop child` 不改变 parent low；pre-state 中已有的 parent 旧 `done` candidate 在 post-state 中保留；post-state 中任何 parent 旧 `done` candidate 的 `dfn` 不小于旧 `low[parent]`。
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

建议拆成：

```coq
preloop_preserves_parent_old_candidates_forward
preloop_parent_old_candidates_backward_or_low_bound
```

这一步的关键风险是 child 新入栈后成为 active vertex。不能要求 parent 旧 `done` 的 partial tree 完全没有新增 active target；正确证明目标是：新增 target 不会比旧 `low[parent]` 更小，因此不会破坏 parent old part 的 low completeness。

### 4.1 第3步的细化设计

第3步不要直接展开证明 `preloop_establishes_parent_frame_for_child`。应先把它拆成四组 cut lemma：

```text
A. preloop 的状态增量刻画
B. ParentLowFrame 的三个字段
C. ParentFrameForChild 中除 low frame 外的字段
D. 最终 Hoare 组合
```

其中 A 和 B 是关键；C 基本是已有 preloop preservation lemma 的组合。

#### A. preloop 状态增量刻画

需要先补几个“小而通用”的状态事实。下面涉及“`preloop child` 从 `s_before` 执行到 `s_after`”的条目是关系式伪签名；实现时可以展开 `Hoare` 后直接使用执行关系，也可以先包装成正式 relation lemma。

```coq
preloop_preserves_any_fa:
  Hoare
    (fun s => fa s x = p)
    (preloop child)
    (fun _ s => fa s x = p).
```

现有 `preloop_keep_fa` 要求 `x` 已 visited，不能用于 `fa child = parent`，因为 child 在 `preloop child` 前未访问。这个 lemma 只表达 `preloop` 不修改 `fa`。

```text
preloop_tree_edge_post_cases:
  ParentRecursivePre parent child done s_before ->
  preloop child 从 s_before 执行到 s_after ->
  tree_edge s_after x y ->
  tree_edge s_before x y \/ (x = parent /\ y = child).
```

这说明 `preloop child` 只可能新增一条 DFS tree edge：`parent -> child`。它用于证明旧 non-tree target 不会被错误变成 tree edge。

```coq
tree_reachable_dfn_monotone:
  wf_scc_state g root s ->
  dg_reachable (state_to_dfs_tree g s root) x y ->
  dfn s x <= dfn s y.
```

该 lemma 由 `dfn_valid` 对每条 tree edge 的严格递增推出。它用于排除旧 processed child 子树在 post-tree 中“绕回 parent 再进入新 child”的情况。

```text
preloop_old_processed_child_reach_backward:
  ParentRecursivePre parent child done s_before ->
  preloop child 从 s_before 执行到 s_after ->
  done old_child ->
  fa s_after old_child = parent ->
  fa s_after old_child <> old_child ->
  dg_reachable (state_to_dfs_tree g s_after root) old_child x ->
  dg_reachable (state_to_dfs_tree g s_before root) old_child x.
```

证明思路：

1. `done old_child` 给出 `Visited old_child s_before`，所以 `old_child <> child`。
2. `fa old_child = parent` 和 `Edge parent old_child` 给出 `dfn parent < dfn old_child`。
3. 若 post reachability 使用新增边 `parent -> child`，则必须先从 `old_child` reach 到 `parent`。
4. 由 `tree_reachable_dfn_monotone` 得到 `dfn old_child <= dfn parent`，与第 2 步矛盾。
5. 因此这条 reachability 完全由旧 tree edge 构成，可回收到 pre-state。

这个 lemma 是第3步最容易卡住的地方；它不应加入任何 invariant。

#### B. ParentLowFrame 的字段

`ParentLowFrame parent done s_before s_after` 的三个字段分别证明：

```coq
preloop_preserves_parent_low_value:
  Hoare
    (ParentRecursivePre parent child done)
    (preloop child)
    (fun _ s =>
       exists s_before,
         low s parent = low s_before parent).
```

证明只需 `preloop_keep_low`，前提 `parent <> child` 由 `fa child = parent` 和 `fa child <> child` 得到，`Visited parent` 来自 parent 的 `LoopCoreShape`。

```text
preloop_parent_old_candidate_forward:
  ParentRecursivePre parent child done s_before ->
  preloop child 从 s_before 执行到 s_after ->
  PartialLowCandidate parent done s_before b ->
  PartialLowCandidate parent done s_after b /\
  dfn s_after b = dfn s_before b.
```

证明按 `PartialLowCandidate` 拆：

1. `b = parent`：parent 不是 child，`dfn parent` 由 `preloop_keep_dfn` 保持。
2. direct target：`done a` 推出 `Visited a s_before`，从 child 未访问得 `a <> child`；active 和 dfn 保持；`preloop_tree_edge_post_cases` 排除旧 non-tree edge 变成新 tree edge。
3. subtree target：`done old_child` 推出 `old_child <> child`；fa 保持；旧 reachability lift 到 post；target active/dfn 保持；non-tree 同样用 `preloop_tree_edge_post_cases`。

```text
preloop_parent_post_candidate_cases:
  ParentRecursivePre parent child done s_before ->
  preloop child 从 s_before 执行到 s_after ->
  PartialLowCandidate parent done s_after b ->
  PartialLowCandidate parent done s_before b \/ b = child.
```

证明按 post candidate 拆：

1. root candidate 给出 old candidate。
2. direct target 中若 target 是新 active vertex，只能是 `child`；否则 active 来自旧 stack，可回收到 old candidate。
3. subtree target 中先用 `preloop_old_processed_child_reach_backward` 把 post reachability 回收到 pre-state；若 active target 是新入栈点，则 `b = child`，否则回收到 old candidate。

```text
preloop_parent_old_candidates_low_bound:
  ParentRecursivePre parent child done s_before ->
  preloop child 从 s_before 执行到 s_after ->
  PartialLowCandidate parent done s_after b ->
  low s_before parent <= dfn s_after b.
```

证明由 `preloop_parent_post_candidate_cases` 分支：

1. old candidate：用 pre-state 的 `LowComplete parent done s_before`，再用 old candidate 的 `dfn` 保持。
2. `b = child`：用 root candidate 得到 `low s_before parent <= dfn s_before parent`；再用 `preloop_after_visited_dfn_lt parent child` 得到 `dfn s_after parent < dfn s_after child`；parent 的 `dfn` 保持后由 `lia` 结束。

最后组合：

```coq
preloop_preserves_parent_low_frame:
  Hoare
    (ParentRecursivePre parent child done)
    (preloop child)
    (fun _ s =>
       exists s_before,
         ParentLowFrame parent done s_before s).
```

这里 `s_before` 就是 Hoare 展开后的 pre-state。不要把 `s_before` 设计成 invariant 字段；它是递归层 bridge 的 ghost witness。

#### C. ParentFrameForChild 的非 low 字段

```coq
preloop_establishes_parent_shape_done_after:
  Hoare
    (ParentRecursivePre parent child done)
    (preloop child)
    (fun _ s =>
       exists s_before,
         LoopCoreShape parent (done_after done child) s).
```

注意不能复用 `loop_core_shape_done_after_active`。`preloop child` 后 `LoopCoreShape parent done s` 已不成立，因为 child 已 visited 且 `fa child = parent`，但还不属于旧 `done`。因此必须直接证明 `done_after` 版本：

1. `wf_scc_state`、`TreeEdgesAreGraphEdges` 用 preloop preservation。
2. `Visited parent` 用 visited preservation。
3. `done_after` 的 old 部分来自旧 shape，新元素 child 来自 `Edge parent child` 和 `preloop_self_visited child`。
4. `ProcessedTreeChild parent (done_after done child)` 对 post-state 的 tree child 分两类：若是 child，用 `done_after` 新元素；否则它 pre-state 已 visited 且 fa 不变，用旧 `ProcessedTreeChild parent done`。

其余 frame 字段：

```text
LoopAuxFacts parent s      : preloop_keep_settled_closed, preloop_keep_in_stack,
                             preloop_preserves_stack_dfn_order,
                             preloop_preserves_dfn_injective,
                             preloop_preserves_stack_nodup
Closed s                  : preloop_preserves_closed
TreeEdgesAreGraphEdges s  : preloop_preserves_tree_edges_are_graph_edges
Edge parent child         : 来自 ParentRecursivePre
Visited child s           : preloop_self_visited
fa child = parent         : preloop_preserves_any_fa
fa child <> child         : preloop_preserves_any_fa
dfn parent < dfn child    : preloop_after_visited_dfn_lt
```

#### D. 最终 Hoare 组合

最终 theorem：

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

组合顺序建议：

1. 先在 Hoare 证明中展开一次 `preloop`，固定 `s_before` 和 `s_after`，避免多个 Hoare lemma 各自产生不同的 existential。
2. 用 `preloop_initializes_loop_inv child` 得到 `LoopInv child ∅ s_after`。
3. 从 precondition 保留 `LoopInv parent done s_before`。
4. 用 B 组得到 `ParentLowFrame parent done s_before s_after`。
5. 用 C 组补齐 `ParentFrameForChild` 剩余字段。

如果实现时 B 组太重，可以先完成 C 组和最终 theorem 的骨架，把唯一缺口集中到：

```coq
preloop_preserves_parent_low_frame
```

但不要 `Admitted` 后继续推进主线；该 lemma 是递归调用返回后 `low[parent] := min(low[parent], low[child])` 可证性的基础。

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
3. `ParentLowFrame ancestor ancestor_done s_before` 的 forward 部分应保持；同时需要证明 post-state 中任何 ancestor old candidate 的 `dfn` 不小于旧 `low[ancestor]`。
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
3. visited-active 分支只执行 `update_low child dfn[a]`，不改 parent low、fa、visited、stack；`ParentLowFrame` 的 forward / low-bound 字段直接保持。
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
3. `ParentLowFrame ancestor ancestor_done` 只谈 ancestor 旧 `done` candidates 的 forward 保留与新增低界；需要证明 pop 掉 `next` segment 不会删除 forward witness，且不会引入更低的新 candidate。
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

1. `[done]` 在证明文件中加入 `ParentRecursivePre`、`ParentFrameForChild`、`ChildReturnPreMaybePop`、`NestedFramePre`、`VisitContract` 相关定义。
2. `[done]` 证明 `set_fa_pending_prepares_parent_recursive_pre`。
3. `[done]` 证明 `preloop_establishes_parent_frame_for_child`。
4. 证明 `preloop_preserves_nested_parent_frame`。
5. `[done]` 证明 `edge_loop_preserves_loop_inv_from_visit_contract`。
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

1. 如果 `ParentLowFrame` 在 preloop 中不可证，先拆 forward-preservation 和 backward-or-low-bound lemma，不要扩大 `LoopInv`。
2. 如果 edge loop 中 unvisited grandchild 分支缺 IH，使用 `VisitFrameContract`，不要把 outer frame 混入 child 的 `LoopInv`。
3. 如果 maybe_pop 保持 outer frame 失败，需要补 stack segment preservation lemma，不能弱化 `ChildContributionContract`。
4. 如果 `RootLowCorrect -> scc_is_low_v` 需要额外结构事实，应从 `LoopCoreShape u (edge_set u)` 推出，不要把字段加入 `LowCorrect`。
5. 如果 pop-local facts 被迫加入 `LoopInv`，说明阶段边界错误，应回到 maybe_pop cut 设计。
