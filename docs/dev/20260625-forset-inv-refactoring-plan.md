# Forset-Inv 重构计划

**Author**: Vitalrubbish
**Date**: 2026-06-25

## 背景

当前 `Tarjan_scc_is_low.v` 使用 `low_forset_inv`（基于 `min_value_of_subset` 的精确等式）作为 forset 迭代不变式。这个设计有三个问题：

1. **不单调**：递归调用 `W v` 可能弹出栈中顶点，改变 `back_edges_done` 集合，破坏精确 min 等式
2. **需要 frame condition**：为保持 `low_forset_inv u done` 在 `W v` 期间不被破坏，需要 `W_preserves_ancestor_inv`（当前最大 Admitted，含 12 前提的复杂 strengthen）
3. **证明复杂**：`min_value_of_subset` 需要同时维护下界和上界，导致大量辅助引理

## 方案

用 `forset_inv`（不等式版本，来自设计文档 Section 8.3）完全替代 `low_forset_inv`：

```coq
Definition forset_inv (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
  wf_scc_state s /\
  u ∈ visited s /\
  In u (stack s) /\
  low s u <= dfn s u /\
  (forall v, done v -> dg_step g u v ->
    (fa s v = u -> low s u <= low s v) /\
    (In v (stack s) -> low s u <= dfn s v)).
```

### 核心优势

| | `low_forset_inv` (旧) | `forset_inv` (新) |
|---|---|---|
| **单调性** | 否（弹出顶点改变集合） | 是（`low[u]`只降，弹出使不等式 vacuously true） |
| **需要 frame condition** | 是（`W_preserves_ancestor_inv`） | **否**（递归调用自动保持） |
| **迭代证明** | 复杂（精确 min 追踪） | 简单（不等式保持） |
| **桥接到正确性** | 直接（`low_forset_inv` → `scc_low_valid_v`） | 需一次性桥接引理（done = dg_step g u 时） |

### 桥接引理

Forset 循环结束后，`done = dg_step g u`（所有邻居已处理）。此时从不等式 `forset_inv` 推出 `scc_low_valid_v s u`：

```
forset_inv u (dg_step g u) s
  → [Step A: 下界] forall w ∈ scc_low_tree u, low[u] <= dfn[w]
  → [Step B: 上界] exists w ∈ scc_low_tree u, low[u] = dfn[w]
  → scc_low_valid_v s u
  → low_post u s
```

## 修改计划

### Phase 1: 定义层（4个删除，1个保留）

**删除**：
- `children_done`
- `back_edges_done`
- `low_forset_inv_core`
- `low_forset_inv`

**保留**（已添加）：
- `forset_inv`（line 530）✓
- `low_post` = `wf_scc_state /\ scc_low_valid_v s u` ✓

### Phase 2: 删除 min_value 辅助引理（11个）

这些引理仅服务于 `low_forset_inv_core` 的 `min_value_of_subset` 推理：

- `children_done_empty`
- `back_edges_done_empty_char`
- `low_eq_dfn_to_min_empty`
- `children_done_add`
- `children_done_no_add`
- `back_edges_done_add`
- `back_edges_done_no_add`
- `set_fa_preserves_min`
- `children_done_full_eq`
- `back_edges_done_full_eq`
- `back_edges_done_union_beta`

### Phase 3: 替换核心保持引理（6个重写）

| 旧引理 | 新引理 | 简化原因 |
|--------|--------|----------|
| `set_low_preserves_low_forset_inv` | `set_low_preserves_forset_inv` | set_low 只改 low field |
| `update_low_tree_edge` | `update_low_tree_preserves_forset_inv` | 只降 low[u]，旧不等式保持 |
| `update_low_back_edge` | `update_low_back_preserves_forset_inv` | 同上，新增 low[u] ≤ dfn[v] |
| `cross_edge_preserves_low_forset_inv` | `cross_edge_preserves_forset_inv` | skip 不改状态 |
| `low_forset_inv_expand_child_done` | ——合并到 tree edge 引理—— | done 扩张只是 forall 加一项 |
| `set_fa_preserves_low_forset_inv_for_new_child` | `set_fa_preserves_forset_inv` ✓ 已有 | fa 不改 low/dfn/stack/visited |

### Phase 4: 替换"其他顶点"保持引理（4个重写）

`preloop a` / `pop_scc a` / `update_low a` 对 u 的 `forset_inv` 保持（`u ≠ a`）：

| 旧引理 | 新引理 |
|--------|--------|
| `preloop_keeps_low_forset_inv_other` | `preloop_keeps_forset_inv_other` |
| `pop_scc_keeps_low_forset_inv_other` | `pop_scc_keeps_forset_inv_other` |
| `update_low_preserves_low_forset_inv_for_other` | `update_low_preserves_forset_inv_for_other` |
| `low_forset_inv_children_done_low_le` | ——删除（不等式直接给出）—— |

### Phase 5: 重写 preloop 建立引理（1个）

`preloop_establishes_low_forset_inv` → `preloop_establishes_forset_inv`：

preloop u 后：`low[u] = dfn[u]`，`done = ∅` 时 forall vacuously true。

### Phase 6: 重写桥接引理（2个）

- `low_forset_inv_to_scc_low_valid` → 重写为从 `forset_inv u (dg_step g u) s` 出发
- `forset_end_implies_scc_low_valid_v` → 同上

需要一次性证明下界（Step A）+ 上界（Step B），组合得到 `scc_low_valid_v`。

### Phase 7: 重写 forset 组装引理（3个）

| 旧引理 | 操作 |
|--------|------|
| `set_fa_W_preserves_low_forset_inv` | 重写为 `set_fa_W` + `forset_inv` 版本，不再需要 frame condition |
| `tree_edge_preserves_low_forset_inv_lowlink` | 重写，移除 `Hframe` 假设；`W a` 自动保持 `forset_inv u done` |
| `low_forset_inv_proper` | 重写为 `forset_inv_proper`（更简单：done 只在 forall 中出现） |

### Phase 8: 删除祖先前保持引理（6个删除）

**`forset_inv` 的不等式在递归调用中自动保持，不再需要 ancestor frame**：

- `done_not_popped_by_subtree_pop_scc`
- `pop_scc_preserves_ancestor_inv`
- `preloop_preserves_ancestor_inv`
- `preloop_establishes_ancestor_inv`
- `preloop_establishes_ancestor_inv_hoare`
- **`W_preserves_ancestor_inv`**（最大 Admitted，~500 行复杂 strengthen 证明）

相关但保留（不依赖 `low_forset_inv`）：
- `stack_split_at_in_popped_before_a` ✓
- `pop_scc_preserves_done_visited` ✓
- `pop_scc_preserves_dfn_injective` ✓
- `preloop_keeps_fa` ✓

### Phase 9: 证明主定理（5个 Admitted → 0）

| 定理 | 操作 |
|------|------|
| `forset_keep_low_forset_inv` | 用 `Hoare_forset` + `forset_inv` 版辅助引理重写 |
| `tarjan_scc_keep_low_valid` | 用 `Hoare_fix_logicv`（P=`low_pre`, Q=`low_post`），组装 preloop/forset/pop_scc |
| `tarjan_scc_preserves_stack_element` | 用类似 fixpoint 模式重写，或不依赖 `low_forset_inv` 保留 |
| `tarjan_scc_establishes_and_preserves_scc_low_valid` | 依赖上述引理，用 Hoare_forset 组装 |
| `tarjan_scc_all_scc_low_valid` | 依赖上述 |
| `tarjan_scc_all_scc_is_low` | 最终定理 |

## 修改量统计

| 操作 | 数量 |
|------|------|
| 新增定义 | 0 (已有 `forset_inv`) |
| 删除定义 | 4 |
| 新增引理 | ~8 (`forset_inv` 版本保持引理) |
| 删除引理 | ~20 (min_value 辅助 + ancestor frame) |
| 重写引理 | ~10 |
| 最终目标 | **0 Admitted** |

## 风险与回退

- `tarjan_scc_preserves_stack_element`：尚未分析是否依赖 `low_forset_inv`。可能可以保留或独立重写。
- 桥接引理（Phase 6）是最具挑战性的新证明，需要验证 Step A+B 在当前 MaxMinLib 下可证明。
- 撤回方案：回退到 git commit `2108974`（refactoring 前状态），仅保留已证明的 Layer 2 改动。
