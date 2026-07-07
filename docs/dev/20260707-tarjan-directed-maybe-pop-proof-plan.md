# Tarjan-Directed-Maybe-Pop-Proof-Plan
**Author**: Codex
**Date**: 2026-07-07

## 1. 目标范围

本计划覆盖 `tarjan_scc_f` 中 edge loop 结束后的最后一步：

```coq
If (fun s => low s u = dfn s u) (pop_scc u)
```

当前已经有：

```coq
edge_loop_preserves_loop_inv:
  Hoare
    (fun s => LoopInv u ∅ s)
    (forset (edge_set u) (process_edge u W))
    (fun _ s => LoopInv u (edge_set u) s).
```

`maybe_pop` 阶段的输入应先桥接为：

```coq
RootPrePop u s :=
  LoopInv u (edge_set u) s /\
  StackRestOlderThanRoot u s.
```

本阶段需要证明两类输出：

```coq
RootFinal u s
```

以及父调用递归 contract 需要的：

```coq
ChildContributionContract parent u done s_before s_after.
```

这两类输出应分开证明，再在 `VisitContract W -> VisitContract (tarjan_scc_f W)` 中组合。不要把父调用 frame 混入 `RootFinal`。

## 2. 与 `chain.md` 的对应关系

`chain.md` 中 pop 阶段是 “Closedness 依赖 Low” 的时刻：

1. edge loop 已经给出完整 `RootLowCorrect u`。
2. 若 `low[u] = dfn[u]`，说明 `u` 的完整 DFS 子树没有指向更老 active stack 顶点的有效 low target。
3. 因而从将被弹出的 segment 出发，不可能到达剩余栈。
4. 同时，由 `NoUnvisitedReach` 和 edge loop 已处理完所有出边，pop segment 不会逃到 unvisited 区域。
5. 所以 pop 后 `Closed` 和 `NoUnvisitedReach` 可以恢复。

这对应当前文件中的 pop-local predicates：

```coq
PoppedSegmentClosed u s
PoppedSegmentNoActiveReach u s
StackRestOlderThanRoot u s
```

这些事实只在 `maybe_pop` 分支中临时产生和消费，不应加入 `LoopInv`。

## 3. 当前谓词职责

### 3.1 当前调用主线

`RootFinal u s` 当前定义为：

```coq
RootAfterMaybePop u s :=
  wf_scc_state g root s /\
  NoUnvisitedReach s /\
  Closed s /\
  scc_is_low_v s u.
```

它是 `tarjan_scc u` 自己的公开后置条件，不携带 `RootLowCorrect u`，因为 pop 可能改变 `stack`，从而改变 active-target 语义。

### 3.2 父调用递归返回接口

父调用需要：

```coq
ChildContributionContract parent u done s_before s_after.
```

其中关键字段是：

```coq
ChildLowContribution parent u s_after :=
  (Active u s_after /\
   LoopCoreShape u (edge_set u) s_after /\
   RootLowCorrect u s_after)
  \/
  (~ Active u s_after /\
   low s_after u = dfn s_after u /\
   dfn s_after parent < dfn s_after u /\
   ChildNoActiveTarget u s_after).
```

注意 active 分支必须在 skip-pop 情况使用；pop 分支不能保留 `RootLowCorrect u` 作为父调用接口，因为 pop 后 active target 语义已经变了。

## 4. 前置桥接：edge loop 到 `RootPrePop`

edge loop 后已经有：

```coq
LoopInv u (edge_set u) s.
```

还需要补：

```coq
edge_loop_post_to_root_pre_pop:
  LoopInv u (edge_set u) s ->
  StackRestOlderThanRoot u s ->
  RootPrePop u s.
```

真正困难的是：

```coq
derive_stack_rest_older_than_root:
  LoopInv u (edge_set u) s ->
  (* parent/frame facts, if needed *) ->
  StackRestOlderThanRoot u s.
```

证明思路：

1. `LoopAuxFacts u s` 给出 `Active u s` 和 `OrderFacts s`。
2. `OrderFacts` 中的 `stack_dfn_order`、`dfn_injective`、`StackNoDup` 给出栈上严格顺序。
3. 对任意 `b ∈ RestStack u s`，由 `stack_split_at` 结构得到 `u` 在 `b` 上方。
4. 用 `stack_dfn_order_strict` 推出：

```coq
dfn s b < dfn s u.
```

这里可能需要先补 `stack_split_at` 的列表结构 lemma：

```coq
rest_stack_below_root:
  Active u s ->
  RestStack u s b ->
  exists l1 l2, stack s = l1 ++ u :: l2 /\ In b l2.
```

## 5. skip-pop 分支

程序分支：

```coq
low s u <> dfn s u
```

状态不变，所以当前调用主线应直接得到：

```coq
maybe_pop_skip_produces_root_final:
  RootSkipBranchPre u s ->
  RootFinal u s.
```

证明内容：

1. `wf_scc_state` 来自 `LoopCoreShape`。
2. `NoUnvisitedReach` 来自 `LoopAuxFacts`.
3. `Closed` 来自 `LoopCoreInv`.
4. `scc_is_low_v s u` 需要从 `RootLowCorrect u s` 转换为 public `scc_is_low_v s u`。

第 4 点需要一个 full-tree bridge：

```coq
root_low_correct_to_scc_is_low_v:
  LoopCoreShape u (edge_set u) s ->
  RootLowCorrect u s ->
  scc_is_low_v s u.
```

其语义是：当 `done = edge_set u` 时，`PartialTree(u, done)` 覆盖完整 DFS subtree，`PartialActiveTarget` 覆盖 `scc_low_tree` 中所有 active back-edge target。

父调用递归接口在 skip-pop 分支应给出 active child contribution：

```coq
maybe_pop_skip_produces_child_contribution:
  ParentLowFrame parent done s_before s ->
  LoopAuxFacts parent s ->
  Closed s ->
  TreeEdgesAreGraphEdges s ->
  Visited u s ->
  fa s u = parent ->
  fa s u <> u ->
  RootSkipBranchPre u s ->
  ChildContributionContract parent u done s_before s.
```

其中 `ChildLowContribution` 选择 active 分支：

```coq
Active u s /\
LoopCoreShape u (edge_set u) s /\
RootLowCorrect u s.
```

`Active u s` 来自 `RootPrePop u s` 中的 `StackRestOlderThanRoot u s`。

## 6. pop 分支

程序分支：

```coq
low s u = dfn s u
pop_scc u
```

需要先在 pre-pop 状态建立 pop-local cuts：

```coq
root_low_eq_dfn_implies_popped_segment_closed:
  RootPopBranchPre u s ->
  PoppedSegmentClosed u s.

root_low_eq_dfn_implies_no_active_reach:
  RootPopBranchPre u s ->
  PoppedSegmentNoActiveReach u s.
```

核心证明逻辑对应 `chain.md`：

1. 若 popped segment 中某点 `x` 能到达 rest stack 中的 `b`。
2. 由 `StackRestOlderThanRoot` 得到 `dfn b < dfn u`。
3. 由完整 `RootLowCorrect u`，这条逃逸路径会产生一个 active target，使 `low[u] <= dfn[b]`。
4. 与 `low[u] = dfn[u]` 矛盾。

还需要处理到 unvisited 区域：

```coq
root_low_eq_dfn_implies_popped_segment_closed:
  PoppedSegment u s x ->
  dg_reachable g x y ->
  Visited y s.
```

证明来源：

1. 对 popped segment 中 `x`，它在 `u` 的 DFS subtree 内。
2. `u` 的 edge loop 已处理完所有 outgoing edges。
3. 若能到 unvisited，则与 `NoUnvisitedReach` / DFS traversal completion 事实矛盾。

这一部分可能需要补一个 subtree membership lemma：

```coq
popped_segment_in_root_subtree:
  RootPrePop u s ->
  PoppedSegment u s x ->
  dg_reachable (state_to_dfs_tree g s root) u x.
```

## 7. pop 后恢复 `NoUnvisitedReach` 和 `Closed`

`pop_scc u` 只修改 `stack` 和 `sccs`。因此基础保持可以拆成：

```coq
pop_scc_preserves_wf_scc_state:
  Hoare (wf_scc_state g root) (pop_scc u) (fun _ s => wf_scc_state g root s).

pop_scc_preserves_scc_is_low_v:
  Hoare (scc_is_low_v u) (pop_scc u) (fun _ s => scc_is_low_v s u).
```

`NoUnvisitedReach` 恢复：

```coq
pop_scc_restores_no_unvisited_reach:
  Hoare
    (fun s => NoUnvisitedReach s /\ PoppedSegmentClosed u s)
    (pop_scc u)
    (fun _ s => NoUnvisitedReach s).
```

`Closed` 恢复：

```coq
pop_scc_restores_closed:
  Hoare
    (fun s =>
       Closed s /\
       PoppedSegmentClosed u s /\
       PoppedSegmentNoActiveReach u s /\
       StackRestOlderThanRoot u s)
    (pop_scc u)
    (fun _ s => Closed s).
```

证明分 case：

1. 原本 inactive 的点：用旧 `Closed`。
2. 新弹出的点：用 `PoppedSegmentNoActiveReach` 排除到 rest stack 的可达。
3. 目标 active 点只能在 rest stack 中，因为 popped segment 已经被移出 stack。

## 8. pop 分支输出

当前调用主线：

```coq
maybe_pop_pop_produces_root_final:
  Hoare
    (RootPopBranchPre u)
    (pop_scc u)
    (fun _ s => RootFinal u s).
```

父调用递归接口：

```coq
maybe_pop_pop_produces_child_contribution:
  Hoare
    (fun s =>
       RootPopBranchPre u s /\
       ParentLowFrame parent done s_before s /\
       LoopCoreShape parent (done_after done u) s /\
       LoopAuxFacts parent s /\
       fa s u = parent /\
       fa s u <> u /\
       dfn s parent < dfn s u)
    (pop_scc u)
    (fun _ s =>
       ChildContributionContract parent u done s_before s).
```

`ChildLowContribution` 选择 inactive 分支：

```coq
~ Active u s_after /\
low s_after u = dfn s_after u /\
dfn s_after parent < dfn s_after u /\
ChildNoActiveTarget u s_after.
```

字段来源：

1. `~ Active u s_after`：`pop_scc u` 把包含 `u` 的 popped segment 从 stack 移除。
2. `low[u] = dfn[u]`：`pop_scc` 不改 `low/dfn`。
3. `dfn parent < dfn u`：由 tree parent relation 和 `dfn_valid`，或由进入 child 的 `set_fa` 后 preloop/DFS order 保持。
4. `ChildNoActiveTarget u s_after`：由 `PoppedSegmentNoActiveReach` 和 `pop_scc` 后 active stack = pre-pop rest stack。

## 9. 组合 theorem

建议最终提供两个独立 theorem。

当前调用主线：

```coq
maybe_pop_produces_root_final:
  Hoare
    (RootPrePop u)
    (If (fun s => low s u = dfn s u) (pop_scc u))
    (fun _ s => RootFinal u s).
```

父调用递归返回接口：

```coq
maybe_pop_produces_child_contribution:
  Hoare
    (fun s =>
       RootPrePop u s /\
       ParentLowFrame parent done s_before s /\
       LoopCoreShape parent (done_after done u) s /\
       LoopAuxFacts parent s /\
       Closed s /\
       TreeEdgesAreGraphEdges s /\
       Visited u s /\
       fa s u = parent /\
       fa s u <> u /\
       dfn s parent < dfn s u)
    (If (fun s => low s u = dfn s u) (pop_scc u))
    (fun _ s =>
       ChildContributionContract parent u done s_before s).
```

这两个 theorem 在 `VisitContract W -> VisitContract (tarjan_scc_f W)` 中共同使用。

## 10. 推荐实现顺序

1. 证明 `stack_split_at` / `RestStack` 的列表结构 lemma。
2. 证明 `derive_stack_rest_older_than_root`，把 edge loop 结果桥接为 `RootPrePop`。
3. 证明 `RootLowCorrect -> scc_is_low_v` 的 full-tree bridge。
4. 证明 skip-pop 分支的 `RootFinal` 和 active `ChildContributionContract`。
5. 证明 `PoppedSegmentClosed` 与 `PoppedSegmentNoActiveReach` 两个 pop-local cuts。
6. 证明 `pop_scc` 对 `wf_scc_state`、`scc_is_low_v`、`ParentLowFrame`、`LoopCoreShape parent ...`、`LoopAuxFacts parent` 的 frame 保持。
7. 证明 `pop_scc_restores_no_unvisited_reach` 和 `pop_scc_restores_closed`。
8. 证明 pop 分支的 `RootFinal` 和 inactive `ChildContributionContract`。
9. 组合 `maybe_pop_produces_root_final`。
10. 组合 `maybe_pop_produces_child_contribution`。

## 11. 风险点

1. `RootLowCorrect -> scc_is_low_v` 可能是最大数学 bridge，因为需要把 `PartialActiveTarget u (edge_set u)` 与 `scc_low_tree s u` 对齐。
2. `PoppedSegmentClosed` 不能只靠 `Closed`，因为 popped segment 在 pre-pop 状态仍 active；必须使用 edge-loop 完成性和 low 正确性。
3. `ChildNoActiveTarget` 应在 pop 后证明，不要把它加入 `RootFinal`。
4. 父调用的 `ParentLowFrame` 在 pop 后仍需保持；`pop_scc` 改 stack，可能影响 `PartialActiveTarget`，所以只能对父旧 `done` candidates 证明 frame，不能泛化到所有新 active targets。
5. 如果证明中需要把 pop-local facts 加入 `LoopInv`，说明职责边界出错，应回到本计划拆分 cut，而不是扩张 invariant。

## 12. 完成标准

本阶段完成时至少应有：

```coq
edge_loop_post_to_root_pre_pop
maybe_pop_produces_root_final
maybe_pop_produces_child_contribution
```

并满足：

1. `LoopInv` 不新增 pop-local 字段。
2. `RootFinal` 不携带父调用 frame。
3. `ChildContributionContract` 只作为递归调用返回接口使用。
4. pop 分支中的 `Closed` 恢复明确依赖 `LowCorrect` 和 `low[u] = dfn[u]`。
5. 不新增 `Admitted` 或 `Axiom`。
