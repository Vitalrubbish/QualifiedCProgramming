# Tarjan SCC Low Correctness — 证明中的前置条件缺口

**Author**: Vitalrubbish / Claude
**Date**: 2026-06-23

## 概述

在证明 `Tarjan_scc_is_low.v` 中剩余 Admitted 引理时，发现两个引理的前置条件不足以支撑其结论。本文档形式化描述这两个缺口，并给出修正建议。

---

## 问题一：`pop_scc_preserves_ancestor_inv` 前置条件不足

### 涉及引理

**文件**: `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`
**引理**: `pop_scc_preserves_ancestor_inv`（泛化版，`(ancestor parent cur: V)`）

### 当前声明

```coq
Lemma pop_scc_preserves_ancestor_inv (ancestor parent cur: V) (done: V -> Prop):
    ancestor <> cur -> parent <> cur -> dg_step g parent cur ->
    (ancestor = parent \/ dg_step g ancestor parent) ->
    Hoare (fun s => ... /\ In ancestor (stack s) /\ ... )
          (pop_scc cur)
          (fun _ s => ... /\ In ancestor (stack s) /\ ... ).
```

### 无法证明的后置条件

`In ancestor (stack s)` — `pop_scc cur` 执行后，`ancestor` 必须仍在栈上。

### 证明路径与断裂点

1. `pop_scc cur` 用 `stack_split_at (stack s) cur = (popped, rest)` 分割栈。
2. 由 `stack_split_at_partition`，`ancestor` 要么在 `popped` 中，要么在 `rest` 中。
3. 若 `ancestor ∈ rest`，目标得证。
4. 若 `ancestor ∈ popped`，需导出矛盾。由 `stack_split_at_in_popped_before_a` 得：`stack = l1 ++ ancestor :: l2` 且 `In cur l2`。由 `stack_dfn_order` 得：

   ```
   dfn s cur ≤ dfn s ancestor    (1)
   ```

   要导出矛盾，需要：

   ```
   dfn s ancestor < dfn s cur    (2)
   ```

5. 从前提出发推导 (2)：
   - 前提 `dg_step g parent cur` + 前置中 `fa s cur = parent` + `In cur (stack s)` → `cur ∈ visited s`（由 `stack_in_visited`）+ `fa s cur ≠ cur`（因 `parent ≠ cur`）→ 应用 `state_to_dfs_tree_step_char_backward` 得 DFS 树边 `parent → cur` → 应用 `dfn_valid` 得 `dfn s parent < dfn s cur`。
   - 现在需要 `dfn s ancestor ≤ dfn s parent`（结合上一步即得 (2)）。从前提 4 的两个分支看：

     | 分支 | 能推出 `dfn s ancestor ≤ dfn s parent` 吗？ | 原因 |
     |------|--------------------------------------------|------|
     | `ancestor = parent` | ✅ | 直接代入 |
     | `dg_step g ancestor parent` | ❌ | 需将原始图边转为 DFS 树边才能用 `dfn_valid`，但缺少 `fa s parent = ancestor` 和 `parent ∈ visited s` |
   - 在更深层递归中（`ancestor` 与 `parent` 之间隔了多层），`dg_step g ancestor parent` 甚至不一定成立——原始图 `g` 中可能没有从 `ancestor` 到 `parent` 的直接边。

### 根因

前提 4 的第二分支 `dg_step g ancestor parent` 太弱——它只说了原始图中有边，但不保证在 DFS 树中这是父子关系（缺少 `fa s parent = ancestor`），更无法处理 ancestor 与 parent 隔了多层的情况。

### 建议修正

**方案 A**（最简）：将前提 4 替换为直接的 dfn 排序条件：

```coq
dfn s ancestor < dfn s cur
```

此条件在调用方 `W_preserves_ancestor_inv` 的不动点归纳中是可得的（归纳不变量维护了祖先链上的 dfn 严格递减序）。

**方案 B**（保留结构但补全条件）：

```coq
(ancestor = parent) \/
(dg_step g ancestor parent /\ fa s parent = ancestor /\ parent ∈ visited s)
```

但此方案仍无法处理 ancestor 与 parent 相隔多层的情况。

---

## 问题二：`tree_edge_preserves_low_forset_inv_lowlink` 缺少 frame 条件

### 涉及引理

**文件**: `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`
**引理**: `tree_edge_preserves_low_forset_inv_lowlink`

### 当前声明

```coq
Lemma tree_edge_preserves_low_forset_inv_lowlink (u a0: V) (done: V -> Prop) (W: ...):
    u <> a0 -> dg_step g u a0 -> ~ done a0 ->
    (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s /\ In u (stack s) /\
                            stack_dfn_order s /\ dfn_injective s)
                     (W x)
                     (fun _ s => low_post x s /\ u ∈ visited s /\ In u (stack s) /\
                                 stack_dfn_order s /\ dfn_injective s)) ->
    Hoare (fun s => low_forset_inv u done s /\ ... )
          (set_fa a0 u;; W a0)
          (fun _ s => low_forset_inv u done s /\ ... ).
```

参数含义：
- `u`：当前顶点（DFS 树中的父亲）
- `a0`：`u` 的一个未访问邻居（树边目标，将成为 `u` 的 DFS 孩子）
- `done`：`u` 的已处理孩子集合（`done ⊆ dg_step g u`）
- `W`：递归处理器（满足 `low_pre x → low_post x` 规范）

### 无法证明的后置条件

`low_forset_inv u done s` 在 `W a0` 执行后的保持性。

### 被破坏的可能性

展开 `low_forset_inv_core u done`：

```coq
min_value_of_subset Nat.le
  (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
   min_value_of_subset Nat.le
     (fun w => back_edges_done s u done w \/ w = u) (dfn s))
  (fun x => x) (low s u)
```

其中 `back_edges_done s u done w` 定义为：

```coq
w ∈ done /\ In w (stack s) /\ fa s w <> u
```

关键依赖项：`In w (stack s)`。若 `W a0` 内部执行的 `pop_scc` 弹出了某个 `w ∈ done`，则 `w` 不再在栈上，`back_edges_done` 集合收缩，`low_forset_inv` 的最小值条件可能不再成立。

### 直觉上为何不会发生

DFS 的不变量保证：
- `done` 中的顶点是 `u` 的已处理孩子
- 它们被发现的 dfn 均小于 `a0`（因为 `a0` 是 `u` 的孩子，`u` 的所有先前孩子在 DFS 序中更早被访问）
- 它们在栈上位于 `a0` 下方（更靠近栈底）
- `pop_scc a0` 只弹出 `a0` 及以上（栈顶方向）的顶点
- 因此 `done` 中仍在栈上的顶点不会被弹出

### 形式化此论证需要的前提

库中已有引理 `done_not_popped_by_subtree_pop_scc`：

```coq
Lemma done_not_popped_by_subtree_pop_scc (u a: V) (done: V -> Prop) (s: SCCSt):
    low_forset_inv u done s -> done_visited done s -> ~ done a ->
    In a (stack s) -> stack_dfn_order s ->
    (forall w, done w -> In w (stack s) -> dfn s w < dfn s a) ->
    forall w, done w -> forall popped' rest',
      stack_split_at (stack s) a = (popped', rest') -> ~ In w popped'.
```

该引理的关键前提是：

```coq
(forall w, done w -> In w (stack s) -> dfn s w < dfn s a)
```

即：对所有 `w ∈ done` 仍在栈上的，`dfn s w < dfn s a`。

**此条件不在 `tree_edge_preserves_low_forset_inv_lowlink` 的当前前置条件中**，也不在 `W` 的 `low_pre → low_post` 规范中。`W` 的规范只保证被处理顶点自身的 low-link 正确性和几个栈属性的保持性，对 `done` 集合中顶点的状态没有任何承诺。

### 能从现有前提推出吗？

不能。`W` 的 `low_post` 规范是：

```coq
low_post x s = wf_scc_state s /\ scc_low_valid_v s x
```

其中 `wf_scc_state` 包含 `stack_in_visited`、`dfn_inv`、`dfn_valid`、`fa_visited`，但**不含** `done` 集合中顶点的 dfn 排序信息。`W a0` 作为一个满足该规范的黑盒程序，可以在其执行过程中任意修改栈（只要最终满足 `wf_scc_state` 和 `scc_low_valid_v s a0`），包括弹出 `done` 中的顶点。

实际上 `W` 是 `tarjan_scc g`，其行为遵守 DFS 的不变量，不会弹出 `done`。但这属于 `W` 的**元性质**（meta-property），未在其 Hoare 规范中编码。

### 根因

`W` 的 `low_pre → low_post` 规范不足以表达 frame 条件——它不承诺"不修改与当前顶点无关的祖先状态"。`low_forset_inv u done` 的保持性是一个跨层（cross-layer）的 frame 性质，需要通过显式的 dfn 排序前提（或增强的 `W` 规范）来保证。

### 建议修正

向 `tree_edge_preserves_low_forset_inv_lowlink` 添加显式的 dfn 排序前提：

```coq
(forall w, done w -> In w (stack s) -> dfn s w < dfn s a0)
```

**此条件在调用方可得**：`forset_keep_low_forset_inv` 使用的 forset 不变量 `P(done)` 包含 `(forall w, done w -> In w (stack s) -> dfn s w < dfn s u)`，结合 `dg_step g u a0`（前置中已有）和 `fa s a0 = u`（由 `set_fa` 建立）可传递到 `a0`：

```
dfn s w < dfn s u < dfn s a0   ⇒   dfn s w < dfn s a0
```

---

## 总结

| | 问题一 | 问题二 |
|---|---|---|
| **涉及引理** | `pop_scc_preserves_ancestor_inv` | `tree_edge_preserves_low_forset_inv_lowlink` |
| **缺失前提** | `dfn s ancestor < dfn s cur` | `forall w ∈ done ∩ stack, dfn s w < dfn s a0` |
| **无法证明的后置** | `In ancestor (stack s)` | `low_forset_inv u done s` |
| **本质** | 祖先链 dfn 传递的前提链不完整 | `W` 的 Hoare 规范缺少 done 集合的 frame 条件 |
| **修复难度** | 低：加一个前提即可 | 低：加一个前提即可（调用方可得） |
| **调用方可得性** | ✅ 不动点归纳维护了 dfn 序 | ✅ forset 不变量 P(done) 中已有，传递可得 |
