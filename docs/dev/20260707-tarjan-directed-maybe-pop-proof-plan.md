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

RootPreMaybePop u s :=
  RootPrePop u s /\
  RootTraversalComplete u s.
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
RootPopCuts u s
StackRestOlderThanRoot u s
```

这些事实只在 `maybe_pop` 分支中临时产生和消费，不应加入 `LoopInv`。
edge-loop completion 不应无条件给出 `PoppedSegmentClosed`；在
skip-pop 情况下，当前 segment 可能通过更老 stack frame 到达未访问点。
因此当前 cut 拆为：

```coq
PoppedSegmentNoUnvisitedStep u s
PoppedSegmentRestTargetCut u s

RootTraversalComplete u s :=
  PoppedSegmentNoUnvisitedStep u s /\
  PoppedSegmentRestTargetCut u s.
```

其中完整 `PoppedSegmentClosed` 只在 pop 分支由
`RootTraversalComplete + RootPrePop + low[u] = dfn[u]` 推出。

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

## 4. 前置桥接：edge loop 到 `RootPreMaybePop`

edge loop 后已经有：

```coq
LoopInv u (edge_set u) s /\
RootTraversalComplete u s.
```

还需要补：

```coq
edge_loop_post_to_root_pre_maybe_pop:
  LoopInv u (edge_set u) s ->
  RootTraversalComplete u s ->
  RootPreMaybePop u s.
```

其中 `RootPrePop` 的栈顺序部分来自：

```coq
derive_stack_rest_older_than_root:
  LoopInv u (edge_set u) s ->
  (* parent/frame facts, if needed *) ->
  StackRestOlderThanRoot u s.
```

`RootTraversalComplete u s` 不能从 `RootPrePop` 反推，必须作为
edge loop completion 的并列后置事实产出。

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

状态：`[partial done]`，当前调用主线已完成：
`root_low_correct_to_scc_is_low_v` 和
`maybe_pop_skip_produces_root_final` 已在证明文件中实现并通过编译。
父调用递归接口的 skip 分支属于后续
`maybe_pop_produces_child_contribution`，尚未处理。

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

需要先在 pre-pop 状态建立 strengthened edge-loop completion cut。
注意这个 cut 不能直接包含 `PoppedSegmentClosed`，否则 skip-pop
状态下不成立。

```coq
RootTraversalComplete u s :=
  PoppedSegmentNoUnvisitedStep u s /\
  PoppedSegmentRestTargetCut u s.

root_pre_pop_low_eq_derives_pop_cuts_with_traversal:
  RootPrePop u s ->
  RootTraversalComplete u s ->
  low s u = dfn s u ->
  RootPopCuts u s.
```

核心证明逻辑对应 `chain.md`：

1. 若 popped segment 中某点 `x` 能到达 rest stack 中的 `b`。
2. 由 `StackRestOlderThanRoot` 得到 `dfn b < dfn u`。
3. 由 `PoppedSegmentRestTargetCut`，这条逃逸路径会产生一个 full-loop low candidate `target`，且 `dfn target <= dfn b`。
4. 由完整 `RootLowCorrect u` 得到 `low[u] <= dfn[target]`。
5. 与 `low[u] = dfn[u]` 矛盾。

还需要处理到 unvisited 区域：

```coq
root_pre_pop_low_eq_derives_popped_segment_closed_with_traversal:
  RootPrePop u s ->
  RootTraversalComplete u s ->
  low s u = dfn s u ->
  PoppedSegment u s x ->
  dg_reachable g x y ->
  Visited y s.
```

证明来源：

1. 先由上一个 no-active-reach 结论排除 popped segment 到 rest stack。
2. 若存在从 popped segment 到 unvisited 的路径，取路径上最后一个
   visited 到 unvisited 的出边 `a -> b`。
3. 若 `a` 已不在栈中，由 `NoUnvisitedReach` 矛盾。
4. 若 `a` 在 rest stack 中，由 no-active-reach 矛盾。
5. 若 `a` 仍在 popped segment 中，由 `PoppedSegmentNoUnvisitedStep` 矛盾。

因此 edge-loop completion 侧真正需要证明的是两个弱字段：

```coq
PoppedSegmentNoUnvisitedStep u s
PoppedSegmentRestTargetCut u s
```

它们比直接证明 `PoppedSegmentClosed` 更贴合 `chain.md`：closedness
只在 `low[u] = dfn[u]` 的 pop 分支由 low 反推。

## 7. pop 后恢复 `NoUnvisitedReach` 和 `Closed`

状态：`[done under cuts]`，已实现并编译通过：
`pop_scc_restores_no_unvisited_reach` 和
`pop_scc_restores_closed`。这两条 lemma 明确以
`PoppedSegmentClosed` / `PoppedSegmentNoActiveReach` 为前提，
没有把 pop-local facts 加入 `LoopInv`。

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
       PoppedSegmentNoActiveReach u s)
    (pop_scc u)
    (fun _ s => Closed s).
```

证明分 case：

1. 原本 inactive 的点：用旧 `Closed`。
2. 新弹出的点：用 `PoppedSegmentNoActiveReach` 排除到 rest stack 的可达。
3. 目标 active 点只能在 rest stack 中，因为 popped segment 已经被移出 stack。

## 8. pop 分支输出

状态：`[done under cuts]`，已实现
`root_pop_branch_pre_scc_is_low_after_pop_state`、
`pop_scc_root_pop_branch_preserves_scc_is_low_v` 和
`maybe_pop_pop_produces_root_final_from_pop_cuts`。当前调用主线的
pop 分支在给定两个 pop-local cuts 后已经完成。

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

状态：`[done]`，已实现以 edge-loop 后置 `RootPreMaybePop` 为入口的组合 theorem：

```coq
maybe_pop_produces_root_final:
  Hoare
    (RootPreMaybePop u)
    (If (fun s => low s u = dfn s u) (pop_scc u))
    (fun _ s => RootFinal u s).
```

edge-loop 侧已经补上 completion 子证明，并通过 traversal 专用接口接入：

```coq
LoopTraversalComplete u done s :=
  LoopNoUnvisitedStep u done s /\
  LoopRestTargetCut u done s.

edge_loop_preserves_root_pre_maybe_pop_from_traversal_contract:
  VisitChildContract W ->
  VisitChildTraversalContract W ->
  Hoare
    (fun s => LoopInv u ∅ s /\ LoopTraversalComplete u ∅ s)
    (forset (edge_set u) (process_edge u W))
    (fun _ s => RootPreMaybePop u s).
```

这里 `LoopTraversalComplete` 是 proof-only 辅助 invariant，不进入
`LoopInv`。它允许尚未处理的 root outgoing edge 作为 pending case；
`done = edge_set u` 时 pending case 被消去，产出
`PoppedSegmentNoUnvisitedStep` 与 `PoppedSegmentRestTargetCut` 两个弱字段。

当前已经完成 `RootTraversalComplete + RootPrePop + low[u]=dfn[u]`
到 `RootPopCuts` 的桥接：

```coq
root_pre_pop_low_eq_derives_pop_cuts_with_traversal:
  RootPrePop u s ->
  RootTraversalComplete u s ->
  low s u = dfn s u ->
  RootPopCuts u s.
```

当前调用主线：

```coq
maybe_pop_produces_root_final:
  Hoare
    (RootPreMaybePop u)
    (If (fun s => low s u = dfn s u) (pop_scc u))
    (fun _ s => RootFinal u s).
```

父调用递归返回接口：

```coq
maybe_pop_produces_child_contribution:
  Hoare
    (fun s =>
       RootPreMaybePop u s /\
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
3. `[done]` 证明 `RootLowCorrect -> scc_is_low_v` 的 full-tree bridge。
4. `[partial done]` 证明 skip-pop 分支的 `RootFinal`；active `ChildContributionContract` 属于后续递归返回接口证明。
5. `[done]` 证明 strengthened cut 到 pop-local cuts 的桥接；edge-loop completion 已产出新的 `RootTraversalComplete` 两个字段。
6. `[partial done]` 证明 `pop_scc` 对当前调用主线所需的 `wf_scc_state`、`scc_is_low_v` 保持 / 重建；parent frame 保持属于后续 child contribution / outer frame 阶段。
7. `[done under cuts]` 证明 `pop_scc_restores_no_unvisited_reach` 和 `pop_scc_restores_closed`。
8. `[partial done]` 证明 pop 分支的 `RootFinal` under cuts；inactive `ChildContributionContract` 属于后续递归返回接口证明。
9. `[done]` 组合 `maybe_pop_produces_root_final`，入口为 `RootPreMaybePop`。
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
