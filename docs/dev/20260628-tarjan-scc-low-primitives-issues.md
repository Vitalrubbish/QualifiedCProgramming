# Tarjan SCC Low Primitives — 已知问题与证明状态

**Author**: Vitalrubbish (via Claude)
**Date**: 2026-06-28

---

## 概述

`Tarjan_scc_low_primitives.v` 包含 10 个引理，为 Tarjan SCC 算法的 low-link 相关操作（`preloop`、`update_low`、`set_fa`、`pop_scc`）提供 Hoare 逻辑合约。当前 6 个引理已完全证明（Qed），4 个引理待完成（Admitted）。

---

## 当前证明状态

### 已完全证明 (Qed) — 6 个

| 引理 | 说明 |
|------|------|
| `preloop_low_eq_dfn` | `preloop u` 后 `low s u = dfn s u` |
| `preloop_establishes_low_iteration_entry` | `preloop u` 建立 `low_iteration_entry g root u`（11 组件全证明） |
| `update_low_preserves_done_visited` | `update_low u n` 保持 `done_visited done` |
| `update_low_other_preserves_low_iteration_frame` | `update_low a n` (a ≠ u, ~done a) 保持 8/9 组件（不含 children_low_valid） |
| `pop_scc_preserves_low_valid_post_when_root` | `pop_scc u`（low = dfn 时）保持 full postcondition |
| `if_pop_preserves_low_valid_post` | `If (low = dfn) (pop_scc u)` 版本 |

### 部分证明 (Admitted，有一个内部 admit) — 1 个

| 引理 | 说明 |
|------|------|
| `set_fa_establishes_low_iteration_before_new_child` | `set_fa a u` 建立 9 组件后条件。8/9 组件已验证通过，仅 `children_low_valid` 有一个 `admit` |

### 完全 Admitted — 3 个

| 引理 | 阻塞原因 |
|------|----------|
| `set_low_preserves_scc_low_valid_v_when_not_child` | 需要在 `min_value_of_subset` 层面证明 `set_low` 不影响 `scc_low_valid_v` |
| `update_low_preserves_children_low_valid_when_not_tree_child` | 依赖上一个辅助引理 |
| `update_low_other_preserves_low_iteration_inv_when_not_child` | 依赖前两个（框架部分已完成，children_low_valid 部分未完成） |

### 疑似有语义问题的引理 — 1 个

| 引理 | 问题 |
|------|------|
| `set_fa_establishes_new_child_tree_edge` | 后条件中 `dg_step (state_to_dfs_tree ...) u a` 在 `~a ∈ visited` 前提下不可满足 |

---

## 详细问题分析

### 问题 1：`set_fa_establishes_new_child_tree_edge` 的后条件语义矛盾

**引理声明**（当前版本）：

```coq
Lemma set_fa_establishes_new_child_tree_edge (u a: V):
    Hoare (fun s: @SCCSt V =>
             dg_step g u a /\
             u ∈ visited s /\
             ~ a ∈ visited s)
          (set_fa a u)
          (fun _ s =>
             fa s a = u /\
             fa s a <> a /\
             dg_step (state_to_dfs_tree g s root) u a).
```

**问题分析**：

后条件要求 `dg_step (state_to_dfs_tree g s root) u a`，即在 DFS tree 中存在一条从 `u` 到 `a` 的边。

`state_to_dfs_tree` 的定义（来自 `Tarjan_scc.v`）：

```coq
Definition state_to_dfs_tree (s: SCCSt) (root: V): OriginalGraphType V E :=
  {| original_vvalid := fun v => v ∈ visited s;
     original_step := fun e =>
       exists v, v ∈ visited s /\ fa s v <> v /\
                 original_step_fst g e = fa s v /\
                 original_step_snd g e = v;
     (* ... *)
  |}.
```

`dg_step G x y` 的定义要求存在一条边 `e` 满足 `original_step G e` 且 `original_step_fst G e = x`、`original_step_snd G e = y`。

对 `state_to_dfs_tree` 而言，`dg_step (tree) u a` 要求：
1. 存在边 `e` 和顶点 `v`
2. `v ∈ visited s`
3. `fa s v ≠ v`
4. `original_step_fst g e = fa s v` 且 `original_step_snd g e = v`
5. `original_step_fst g e = u` 且 `original_step_snd g e = a`

由 (4) 和 (5) 得 `fa s v = u` 且 `v = a`。因此需要 `a ∈ visited s` 且 `fa s a ≠ a`。

然而前提条件明确包含 `~ a ∈ visited s`，且 `set_fa a u` 只修改 `fa` 字段，不修改 `visited`。因此在 `set_fa` 之后 `a` 仍然不在 visited 中，无法满足 `dg_step (tree) u a`。

**对比一致实现**：同类引理 `set_fa_adds_tree_edge`（在 `Tarjan_scc_basics.v` 中）要求 `v ∈ visited s` 作为前提条件：

```coq
Lemma set_fa_adds_tree_edge (s: SCCSt) (root v p: V):
  v ∈ visited s -> p ∈ visited s -> p <> v ->
  dg_step (state_to_dfs_tree (set_fa_state s v p) root) p v.
```

这证实了 tree edge 的存在性需要目标顶点已 visited。

**算法层面的解释**：`set_fa a u` 在 `process_edge` 的 tree-edge 分支中调用，此时 `a` 尚未被访问。紧接着会执行 `W a = tarjan_scc a`，其中 `preloop a` 会调用 `visit a` 将 `a` 加入 visited。因此 tree edge `u → a` 在 `visit a` 之后才真正形成。`set_fa a u` 只是设置了 parent 指针，不足以建立完整的 tree edge。

**建议修复方案**：
- **方案 A**：从后条件中删除 `dg_step (state_to_dfs_tree g s root) u a`，保留 `fa s a = u` 和 `fa s a <> a`
- **方案 B**：增加一个中间引理，说明在 `visit a` 之后 tree edge 成立（组合 `set_fa_adds_tree_edge` 与 `visit` 的效果）

### 问题 2：`children_low_valid` 在状态更新下的保持性

**影响范围**：
- `set_low_preserves_scc_low_valid_v_when_not_child`（未完成）
- `set_fa_establishes_low_iteration_before_new_child` 的 `children_low_valid` 组件（admit）

**问题描述**：

`children_low_valid g root u done s` 定义为：

```coq
forall v, done v -> dg_step g u v -> fa s v = u -> fa s v <> v ->
  scc_low_valid_v g root s v
```

其中 `scc_low_valid_v` 通过 `min_value_of_subset` 定义，依赖于 `low s` 在 tree children of `v` 上的值以及 `dfn s` 在 back edges from `v` 上的值。

当 `set_low a n` 或 `set_fa a u` 改变状态时，需要证明 `scc_low_valid_v s v` 在以下额外条件下保持不变：
- `a` 不是 `v` 的 tree child（即 `~ dg_step (state_to_dfs_tree ...) v a`）
- `v ≠ a`（由 `done v` 和 `~ done a` 保证）

**为什么这个条件充分**：

`set_low a n` 只改变 `low s a`，而 `low s a` 出现在 `scc_low_valid_v s v` 中的唯一途径是 `a` 属于 `dg_step (tree) v`（即 `a` 是 `v` 的 tree child）。如果 `a` 不是 tree child of `v`，则 `scc_low_valid_v` 不变。

`set_fa a u` 只改变 `fa s a`，但 `scc_low_valid_v` 不直接依赖 `fa`——它通过 `state_to_dfs_tree` 间接依赖。`state_to_dfs_tree` 只对 visited 顶点使用 `fa` 信息。如果 `~ a ∈ visited s`（如 `set_fa_establishes_low_iteration_before_new_child` 的前提条件），则 tree 结构不变。

**证明困难**：

在 Rocq 中形式化这个论证需要展开 `min_value_of_subset` 和 `min_object_of_subset` 的定义，产生大量关于集合中值相等的义务。最内层的证明涉及记录访问的简化（`low (set_low a n s) x = low s x` 当 `x ≠ a`），以及与 `state_to_dfs_tree` 等复合定义的交互。

**建议**：
- 在 MaxMinLib 层面增加 `Proper` 实例：如果两个状态在 `dg_step (tree) v` 的顶点上的 `low` 值一致，则 `scc_low_valid_v` 一致
- 或者提供更细粒度的引理来分解 `min_value_of_subset` 在函数子集上的保持性

---

## 已完成证明的技术要点

### `preloop_establishes_low_iteration_entry`（11 组件）

策略：`Hoare_conj` 拆分为 `low_iteration_inv`（9 组件）+ `stack_dfn_order` + `dfn_injective`。前 3 个组件（`wf_scc_state`、`u ∈ visited`、`In u`）使用现有引理。剩余 6 个组件（涉及 `∅`）通过 `intro_state` + `hoare_auto_s` 直接证明，其中 `fa_child_of_u` 和 `fa_not_done_implies_eq_u` 利用 `fa_visited` + `~u ∈ visited` 导出矛盾（空前提）。

### `update_low_other_preserves_low_iteration_frame`（8 组件）

策略：`intro_state` + `hoare_auto_s` 分两支：`set_low a n` 执行或跳过。跳过分支持平。执行分支对每个组件做 `simpl` + `unfold RecordSet.set` + `simpl` 后，用 `equiv_decb` case analysis 处理 `low` 记录访问（区分 `x = a` 和 `x ≠ a`）。`low_frontier` 和 `low_src` 的 forall 分支利用 `~ done a` 排除 `a`。

### `pop_scc_preserves_low_valid_post_when_root`

策略：直接 `intro_state` + `hoare_auto_s`，用 `stack_split_at_decomp` 分解 stack 结构。
- `stack_in_visited`：利用 `stack_split_at_decomp` 将 `rest` 表达为 `stack s0` 的后缀
- `dfn_valid`：展开 `state_to_dfs_tree` 和 `dg_step`，对 `original_step` 做 case analysis
- `stack_dfn_order`：复制 `pop_scc_preserves_stack_dfn_order` 的证明结构
- `scc_low_valid_v`：展开 `min_value_of_subset`，通过 `low s u = dfn s u` 和 `low_frontier` 建立最小值论证

---

## 相关文件

- `Tarjan_scc_low_primitives.v`：本文档分析的目标文件
- `Tarjan_scc_low_defs.v`：所有 low-link 相关不变式的定义
- `Tarjan_scc_low_pure.v`：纯数学性质（`scc_low_tree_decompose`、`scc_low_valid_implies_is_low`）
- `Tarjan_scc_basics.v`：基本操作的 Hoare 引理（`set_low_new_low`、`set_fa_new_fa` 等）
- `Tarjan_scc_is_dfn.v`：`wf_scc_state`、`stack_dfn_order`、`dfn_injective` 及其保持性引理
- `Tarjan_scc.v`：算法主程序及 `state_to_dfs_tree` 定义
- `MaxMinLib/MaxMin/Interface.v`：`min_value_of_subset` 和 `min_object_of_subset` 的定义
