# Tarjan-Directed-Preloop-Init-Proof-Plan
**Author**: Codex
**Date**: 2026-07-07

## 1. 目标

本计划只覆盖初始化压栈阶段：

```coq
preloop u
```

目标是从入口前提建立邻居循环的初始不变量：

```coq
preloop_initializes_loop_inv:
  Hoare (EntryPre u)
        (preloop u)
        (fun _ s => LoopInv u ∅ s).
```

按当前设计：

```coq
LoopInv u done s :=
  LoopAuxFacts u s /\
  LoopCoreInv u done s.
```

其中核心联合不变量为：

```coq
LoopCoreInv u done s :=
  LoopCoreShape u done s /\
  Closed s /\
  LowCorrect u done s.
```

初始化证明必须分别建立：

```coq
LoopAuxFacts u s'
LoopCoreShape u ∅ s'
Closed s'
LowCorrect u ∅ s'
```

其中 `s'` 是 `preloop u` 后的状态。

## 2. 入口前提拆解

当前入口前提：

```coq
EntryPre u s :=
  wf_scc_state_pre g root u s /\
  NoUnvisitedReach s /\
  Closed s /\
  TreeEdgesAreGraphEdges s /\
  OrderFacts s /\
  (fa s u <> u -> Edge (fa s u) u).
```

需要从中使用：

```coq
wf_scc_state_pre g root u s
```

提供：

```coq
wf_scc_state g root s
~ Visited u s
stack_in_visited s
dfn_inv s
dfn_valid s root
fa_visited s
```

`OrderFacts s` 提供：

```coq
stack_dfn_order s
dfn_injective s
StackNoDup s
```

`fa s u <> u -> Edge (fa s u) u` 只服务于 `TreeEdgesAreGraphEdges` 在 `preloop` 后新增可能 tree edge 的证明。

## 3. 证明分解

建议按以下 lemma 顺序实现。

### 3.1 `preloop` 建立 `LoopCoreShape u ∅`

目标形状：

```coq
preloop_produces_loop_core_shape:
  Hoare (EntryPre u)
        (preloop u)
        (fun _ s => LoopCoreShape u ∅ s).
```

字段证明：

```coq
wf_scc_state g root s
```

直接使用已有：

```coq
preloop_preserves_wf_scc_state
```

```coq
TreeEdgesAreGraphEdges s
```

需要新增一个专门 lemma：

```coq
preloop_preserves_tree_edges_are_graph_edges:
  Hoare
    (fun s =>
       wf_scc_state_pre g root u s /\
       TreeEdgesAreGraphEdges s /\
       (fa s u <> u -> Edge (fa s u) u))
    (preloop u)
    (fun _ s => TreeEdgesAreGraphEdges s).
```

证明思路：

1. 展开 `preloop` 后，`visited` 变为旧 `visited ∪ [u]`，`fa` 不变。
2. 对 post-state tree edge `x -> y` 用 `state_to_dfs_tree` 定义拆出 witness `y`。
3. 若 `y` 是旧 visited 点，则该 tree edge 已经存在于旧 DFS tree，用旧 `TreeEdgesAreGraphEdges` 得到 `Edge x y`。
4. 若 `y = u`，则 `x = fa old u`，由 tree edge 的 `fa old u <> u` 和入口前提得到 `Edge (fa old u) u`。

```coq
Visited u s
```

直接使用已有：

```coq
preloop_self_visited
```

```coq
forall a, ∅ a -> Edge u a
forall a, ∅ a -> Visited a s
```

集合为空，`sets_unfold` 后矛盾即可。

### 3.2 `preloop` 建立 `Closed`

目标：

```coq
preloop_preserves_closed:
  Hoare
    (fun s =>
       wf_scc_state_pre g root u s /\
       NoUnvisitedReach s /\
       Closed s)
    (preloop u)
    (fun _ s => Closed s).
```

证明思路：

1. 展开 `preloop`，post stack 为 `u :: stack old`，post visited 为 `visited old ∪ [u]`。
2. 要证明：

```coq
Visited v post ->
~ Active v post ->
dg_reachable g v b ->
Active b post ->
False
```

3. `v = u` 不可能，因为 `u` 在 post stack 顶部，和 `~ Active v post` 矛盾。
4. 所以 `v` 是旧 visited 且旧 inactive。
5. 若 `b` 是旧 stack 中的 active 点，则用旧 `Closed`。
6. 若 `b = u`，由于入口有 `~ Visited u old`，旧 `NoUnvisitedReach` 会推出 `Visited u old`，矛盾。

注意：这里正是 `NoUnvisitedReach` 在初始化阶段的作用。它不是主 closedness，但用于排除“旧 settled 点 reach 新入栈点 u”。

### 3.3 `preloop` 建立 `LowCorrect u ∅`

目标：

```coq
preloop_produces_low_correct_empty:
  Hoare (fun s => True)
        (preloop u)
        (fun _ s => LowCorrect u ∅ s).
```

可先证明中间等式：

```coq
preloop_low_eq_dfn:
  Hoare (fun s => True)
        (preloop u)
        (fun _ s => low s u = dfn s u).
```

证明方式二选一：

1. 直接展开 `preloop`，计算 `set_dfn u t` 与 `set_low u t`。
2. 或用已有 `preloop_dfn_set` / `preloop_low_set`，用同一个 timer snapshot 连接。

然后复用当前已存在的纯 lemma：

```coq
low_correct_empty:
  low s u = dfn s u ->
  LowCorrect u ∅ s.
```

关键语义：

```coq
PartialActiveTarget u ∅ s b
```

为空，因此：

```coq
PartialLowCandidate u ∅ s b
```

只剩 `b = u`。

### 3.4 `preloop` 建立 `LoopAuxFacts`

目标：

```coq
preloop_produces_loop_aux_facts:
  Hoare (EntryPre u)
        (preloop u)
        (fun _ s => LoopAuxFacts u s).
```

字段证明：

```coq
NoUnvisitedReach s
```

`NoUnvisitedReach` 当前是 `settled_closed g s` 的别名，直接复用：

```coq
preloop_keep_settled_closed
```

```coq
Active u s
```

直接使用：

```coq
preloop_in_stack
```

```coq
OrderFacts s
```

拆为三项。

已有：

```coq
preloop_preserves_stack_dfn_order
preloop_preserves_dfn_injective
```

需要新增：

```coq
preloop_preserves_stack_nodup:
  Hoare
    (fun s =>
       StackNoDup s /\
       stack_in_visited s /\
       ~ Visited u s)
    (preloop u)
    (fun _ s => StackNoDup s).
```

证明思路：

1. `preloop` 后 stack 为 `u :: stack old`。
2. 旧 stack `NoDup` 来自 `StackNoDup old`。
3. 由 `stack_in_visited old` 和 `~ Visited u old` 推出 `~ In u (stack old)`。
4. 用 `NoDup_cons` 完成。

## 4. 组合定理

最终组合：

```coq
preloop_initializes_loop_inv:
  Hoare (EntryPre u)
        (preloop u)
        (fun _ s => LoopInv u ∅ s).
```

证明结构：

```coq
unfold LoopInv.
apply Hoare_conj.
- apply preloop_produces_loop_aux_facts.
- unfold LoopCoreInv.
  apply Hoare_conj.
  + apply preloop_produces_loop_core_shape.
  + apply Hoare_conj.
    * apply preloop_preserves_closed.
    * apply preloop_produces_low_correct_empty.
```

实际 Coq 中可能需要使用 `Hoare_conseq_pre` 从 `EntryPre` 投影各子 lemma 的前提。

## 5. 建议实现顺序

1. 证明 `preloop_low_eq_dfn`。
2. 证明 `preloop_preserves_stack_nodup`。
3. 证明 `preloop_preserves_tree_edges_are_graph_edges`。
4. 证明 `preloop_preserves_closed`。
5. 组合 `preloop_produces_loop_core_shape`。
6. 组合 `preloop_produces_loop_aux_facts`。
7. 最后证明 `preloop_initializes_loop_inv`。

这个顺序能先解决纯状态计算和 frame facts，再进入 `Closed` 这种路径性质。

## 6. 风险点

1. `TreeEdgesAreGraphEdges` 的证明必须认真区分旧 visited 点和新点 `u`。不要试图从 `wf_scc_state` 推出 tree edge 是原图边；`wf_scc_state` 没有这个信息。
2. `Closed` 的初始化保持不能只用旧 `Closed`。当 active target 是新压栈的 `u` 时，必须用 `NoUnvisitedReach` 和 `~ Visited u old` 反驳。
3. `StackNoDup` 是新加入 `OrderFacts` 的字段，现有库可能没有对应保持 lemma，需要先补。
4. `LowCorrect u ∅` 不应展开成复杂 target 证明；应先证明 `low[u] = dfn[u]`，再调用 `low_correct_empty`。
5. 初始化阶段不应引入任何 child / suspended frame predicate；`set_fa` 问题属于 tree-child 分支，不能污染 preloop 证明。

## 7. 完成标准

初始化阶段完成时应满足：

```coq
preloop_initializes_loop_inv:
  Hoare (EntryPre u)
        (preloop u)
        (fun _ s => LoopInv u ∅ s).
```

并且：

1. 不新增 `Admitted` 或 `Axiom`。
2. 不修改生成文件。
3. `make -B -f _tarjan_is_low_only.mk SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.vo` 通过。
4. 所有新增 lemma 的职责只服务初始化阶段，不提前引入 tree-child 分支的 suspended/frame 设计。
