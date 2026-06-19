# Tarjan_scc_is_low — 开发设计与可行性分析

**Author**: Vitalrubbish
**Date**: 2026-06-17

## 概述

本文档分析 `Tarjan_scc_is_low.v` 的开发可行性与详细设计。
该文件是 Tarjan SCC 有向图验证体系（Layer 2→1）的第四个证明文件，
位于 `Tarjan_scc_is_dfn.v`（dfn 语义层）之上，
负责证明 low 值的正确性——`low s u` 等于从 `u` 出发经树边和至多一条回边可达的最小 dfn 值。

**关键设计决策**: GraphLib 的 `low_valid` / `is_low` 定义是为无向图桥判定设计的，
依赖 `no_cross_edge`（"任意非树边两端点在 DFS 树中必有祖先—后代关系"），
该性质对有向 SCC 图不成立（交叉边存在且被算法显式跳过）。因此本文件**定义 SCC 专用的
low 正确性谓词**，使用栈成员资格（`In v (stack s)`）精确刻画回边，
排除交叉边对 low 值的干扰。

---

## 1. 当前状态

### 1.1 已完成的前置文件

| 文件 | 状态 | 与本文件的关系 |
|------|------|---------------|
| `Tarjan_scc.v` | ✅ | `process_edge`（树边/回边/交叉边分支）、`state_to_dfs_tree` 结构引理 |
| `SCC_basic.v` | ✅ | 有向图基础定义 |
| `Tarjan_scc_basics.v` | ✅ | 72 个 Hoare 引理：`update_low_nonincreasing`、`preloop_low_set`、`process_edge_keep_low`、`tarjan_scc_keep_low` 等原语/复合操作保持性 |
| `Tarjan_scc_is_dfn.v` | ✅ | `dfn_inv`、`dfn_valid`、`fa_visited`、`dfn_unique` 全套 Hoare 定理 |

### 1.2 后续依赖本文件的模块

```
Tarjan_scc_is_dfn.v
    ↓
Tarjan_scc_is_low.v  ← 本文件
    ↓
Tarjan_scc_stack.v   （栈不变量 + SCC 弹出定理，需要 low 正确性判断 dfn=low 触发弹出）
    ↓
SCC_correctness.v    （最终功能正确性）
```

### 1.3 已在本文件中使用的 GraphLib 定义

`low_valid` 和 `is_low` 在 `GraphLib/examples/tarjan.v` 中已定义，但它们是**为无向图桥判定设计的**（依赖 `no_cross_edge` 和 `reachable_visited` 假设，参见该文件第 366–373 行）。对于 SCC 有向图，交叉边存在且被算法显式跳过，因此本文件**不直接复用**这两个谓词，而是定义 SCC 专用的对应版本（见 Section 3）。

本文件复用的 GraphLib 基础设施：
- `rooted_tree_induction_bottom_up`（`GraphLib/directed/rootedtree.v`）— 树上的自底向上归纳原理
- `min_value_of_subset`、`NatLe_TotalOrder`（`MaxMinLib`）— 最小值算子
- `son`、`subtree`、`dg_reachable`（`GraphLib`）— 树结构关系

---

## 2. 参考文件分析

### 2.1 桥判定版本 `Tarjan_is_low.v`

**路径**: `SeparationLogic/algorithms/Tarjan/Tarjan_is_low.v`
**规模**: 2812 行
**核心成果**: 证明 `tarjan g root` 执行后 `is_low g (state_to_rootedtree g root s) s.(dfn) s.(low)` 和 `low_valid g (state_to_rootedtree g root s) s.(dfn) s.(low)`

**关键不变量**:
1. `low_valid_v_inv_with_eset u done s` — u 在状态 s 下相对于已处理边集 done 的 low 正确性
2. `low_valid_loop_inv u done s` — forset 循环不变量：`low_valid_v_inv_with_eset u done s ∧ tree_sub_conj_P root g u s ∧ eset_in_visited g u done s ∧ tree_edge_in_eset u done s`
3. `closed_low_valid v s` — 子树 v 已封闭（所有出边已处理）时的 low 正确性
4. `processed_low_valid u s` — u 的所有后代（除自身外）满足 `closed_low_valid`

**证明策略**:
1. `Tarjan_low_valid_single_inv u` — 核心 Hoare 三元组：对 `tarjan u`，从前置 `tree_sub_conj_P ∧ isleaf u` 到后置 `low_valid_v_inv_with_eset u (full_eset u)`
2. 使用 `hoare_fix_nolv_fs_auto` + 6 个辅助不变量做不动点归纳
3. `Tarjan_low_valid` — 最终定理：组合根节点的 single_inv 与后代节点的 processed_low_valid，通过 `closed_low_valid_to_final` 转为 `low_valid`

### 2.2 桥判定版本的复杂性来源

桥判定版本 2812 行的复杂性主要来自：
1. **eset 管理**：显式追踪哪些边已被处理（`full_eset`、`done` 集），需要大量集合等价引理
2. **tree_edge 结构**：`state_to_rootedtree` 的 `tedge` 字段需要额外的不变量（`tree_edge_in_eset`）
3. **多不变量并发归纳**：6 个辅助不变量通过 `hoare_fix_nolv_fs_auto` 同时做不动点归纳

**SCC 版本有望大幅简化**：SCC 的 `forset (dg_step g u w)` 天然按邻居迭代，不需要 eset 追踪；`state_to_dfs_tree` 从 `fa`/`visited` 隐式推导，不需要 tree_edge 不变量。

### 2.3 桥判定与 SCC 版本的关键差异

| 维度 | 桥判定 | SCC |
|------|--------|-----|
| 图类型 | 无向图 | **有向图** |
| 树结构 | `state_to_rootedtree`（含 `tedge`）| `state_to_dfs_tree`（从 `fa`/`visited` 推导）|
| 非树边种类 | 仅回边（无向 DFS 无交叉边）| 回边 + **交叉边** |
| 边迭代 | `forset` over eset + tree_edge 不变量 | `forset` over `dg_step g u w` |
| eset 管理 | 需要显式 `done`/`full_eset` 推理 | 不需要，forset 的 done 隐式追踪 |
| 叶节点检测 | `isleaf` 谓词 | 隐式：`fa v = v` 时无子节点 |
| low 定义 | `low_valid`（含所有非树边）| **SCC 专用定义**（仅含回边，排除交叉边）|
| GraphLib 复用 | 直接复用 `low_valid`/`is_low` | 仅复用 `min_value_of_subset` 和树归纳原理 |
| 递归假设 | 6 个辅助不变量并发 | 预期 2–3 个不变量 |
| 栈检测 | `in_stack` 等价 | `In v (stack s)` 直接判断 |
| low 更新 | 树边：`update_low u (low v)`；回边：类似 | 完全相同 |

---

## 3. SCC 语境下 low 正确性的数学定义

### 3.1 为什么不能直接复用 GraphLib 的 `low_valid` / `is_low`

GraphLib 的 `low_valid` / `is_low` 定义在 `GraphLib/examples/tarjan.v` 的 `Section LOW` 中，
该 section 的 context 包含：

```coq
Context {nocross: no_cross_edge}
        {reacheable_is_visited: reachable_visited}.
```

其中 `no_cross_edge` 定义为：

```coq
Definition no_cross_edge :=
  forall x y, reachable g theroot x -> reachable g theroot y ->
  step g x y -> reachable dfstree x y \/ reachable dfstree y x.
```

该性质对**有向图 DFS 树不成立**：在有向 SCC 算法中，DFS 可能产生交叉边——
连接 DFS 树中不相关分支的边，既非祖先—后代关系，也非后代—祖先关系。

SCC 算法对交叉边的处理是**显式跳过**（`Tarjan_scc.v:124`，`v ∈ visited ∧ v ∉ stack` 分支为空）：
```
树边    (~v ∈ visited)          → set_fa v u ;; tarjan_scc v ;; update_low u (low v)
回边    (v ∈ visited ∧ v ∈ stack) → update_low u (dfn v)
交叉边  (v ∈ visited ∧ v ∉ stack) → skip
```

因此算法计算的 `low u` = min(dfn u, min{low v | v 是树子节点}, min{dfn w | w 是回边目标})。
GraphLib 的 `low_valid_v` 要求 `low u` 也考虑 `step_without_tree` 中的所有非树边（包括交叉边），
但交叉边可能指向 dfn 非常小的节点，使得算法实际值不等于 `low_valid_v` 的数学期望。

**结论**: 必须为 SCC 定义专用的 low 正确性谓词。

### 3.2 SCC 专用定义：`scc_low_valid`（构造式）

```coq
(* 回边: 原图中从 x 到 y 的边，y 仍在栈中，且该边不是 DFS 树边 *)
Definition scc_back_edge (s: SCCSt) (x y: V): Prop :=
  dg_step g x y /\
  In y (stack s) /\
  ~ dg_step (state_to_dfs_tree s root) x y.

(* 单点 low 正确性（构造式）:
   low s u = min( min{low s v | son u v},
                  min{dfn s w | scc_back_edge s u w} ∪ {dfn s u} ) *)
Definition scc_low_valid_v (s: SCCSt) (u: V): Prop :=
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le (son (state_to_dfs_tree s root) u) (low s) ∪
     min_value_of_subset Nat.le (scc_back_edge s u ∪ [u]) (dfn s))
    (fun x => x) (low s u).

(* 全局 low 正确性 *)
Definition scc_low_valid (s: SCCSt): Prop :=
  forall v, v ∈ visited s -> scc_low_valid_v s v.
```

**语义**: `scc_low_valid_v s u` 精确刻画了算法对 u 的 low 值的更新行为——
`low u` 只受树子节点的 low 和回边目标的 dfn 影响，**不受交叉边影响**。

> **重要说明（low 值的历史快照性质）**: `scc_low_valid_v s u` 中的 `scc_back_edge s u w`
> 是对**计算 `low u` 时**回边目标集合的描述。`low u` 一旦被写入就是一个普通的自然数，
> 不随后续 `stack s` 的变化而变化。因此，即使某个节点 w 后来因 `pop_scc` 被弹出栈，
> 只要它在计算 `low u` 时满足 `scc_back_edge`，其对 `low u` 的贡献仍然有效。
> 这一性质对 `pop_scc_keep_scc_low_valid_v` 的证明至关重要。

### 3.3 SCC 专用定义：`scc_is_low`（声明式）

```coq
(* 从 x 出发，经树边和至多一条回边可达 y *)
Definition scc_low_reachable (s: SCCSt) (x y: V): Prop :=
  exists z,
    dg_reachable (state_to_dfs_tree s root) x z /\
    (z = y \/ scc_back_edge s z y).

(* x 的 low-子树: 从 x 经树边+至多一条回边可达的所有节点 *)
Definition scc_low_tree (s: SCCSt) (x: V): V -> Prop :=
  fun y => scc_low_reachable s x y.

(* 声明式 low 正确性: low s u 是 scc_low_tree s u 中所有节点的 dfn 的最小值 *)
Definition scc_is_low_v (s: SCCSt) (u: V): Prop :=
  min_value_of_subset Nat.le (scc_low_tree s u) (dfn s) (low s u).

(* 全局声明式 low 正确性 *)
Definition scc_is_low (s: SCCSt): Prop :=
  forall v, v ∈ visited s -> scc_is_low_v s v.
```

### 3.4 关键引理（需在本文件中证明）

| 引理 | 含义 |
|------|------|
| `scc_low_valid_induction` | 子节点 `scc_is_low_v` 成立 ⇒ `min_value_of_subset (son u) low == min_value_of_subset (∪_{z∈son u} scc_low_tree z) dfn` |
| `scc_low_valid_induction_is_low` | `scc_low_valid_v u` + 子节点 `scc_is_low_v` ⇒ `scc_is_low_v u` |
| `scc_low_valid_implies_is_low` | 全局 `scc_low_valid` ⇒ 全局 `scc_is_low`（通过 `rooted_tree_induction_bottom_up`）|

这三个引理的结构**完全仿照** GraphLib 的 `low_valid_induction`（第 523 行）、
`low_valid_induction_is_low`（第 557 行）、`low_valid_implies_is_low`（第 576 行），
但使用 `scc_back_edge` 替代 `step_without_tree`，从而**不需要 `no_cross_edge` 假设**。

证明 `scc_low_valid_implies_is_low` 时，关键步骤是 `scc_low_tree` 的分解：

```
scc_low_tree u == [u] ∪ scc_back_edge s u ∪ (fun w => exists v, son u v /\ scc_low_tree s v w)
```

这与 GraphLib 的 `low_tree_decompose`（第 500 行）结构相同，但右侧第二项用 `scc_back_edge s u`
替换了 `step_without_tree u`。证明通过展开 `scc_low_reachable` 定义并对树路径做 case analysis 完成，
**不依赖 `no_cross_edge`**。

### 3.5 `scc_back_edge` 与 `step_without_tree` 的关系

对于 SCC 算法执行完毕后的状态 s：

- `scc_back_edge s u w` ⊆ `step_without_tree (state_to_dfs_tree s root) u w`
  （回边是非树边的子集）
- 两者**不相等**：`step_without_tree` 还包含交叉边（`v ∈ visited ∧ v ∉ stack`）
- 算法对交叉边执行 skip，故交叉边的 dfn **不应影响** `low u`
- `scc_low_valid` 正确地排除了交叉边，而 GraphLib 的 `low_valid` 错误地包含了它们

---

## 4. SCC 版本的证明策略

### 4.1 核心思路

SCC 版本的关键简化：**不需要 eset 追踪**。`process_edge` 通过 `forset` 按邻居迭代，
每个邻居处理后的效果直接反映在 `low u` 的更新中。

对于 `tarjan_scc u`：
1. `preloop u` 后：`low u = dfn u`（仅自身），此时 `scc_low_valid_v s u` 平凡成立
2. `forset` 迭代每个邻居 v：
   - **树边**（`~v ∈ visited`）：`set_fa v u ;; tarjan_scc v ;; update_low u (low v)`
     - 递归后 `low v` 对其子树正确
     - `set_fa v u` 将 v 加入 `son u`，递归将 v 的子树加入 `subtree u`
     - `update_low u (low v)` 将 `son u` 的 low 贡献纳入 `low u`
   - **回边**（`v ∈ visited ∧ v ∈ stack`）：`update_low u (dfn v)`
     - v 仍在栈中 ⇒ v 是 u 的祖先 ⇒ 边 u→v 是回边
     - `update_low u (dfn v)` 将回边贡献纳入 `low u`
   - **交叉边**（`v ∈ visited ∧ v ∉ stack`）：skip
     - v 已出栈 ⇒ v 在不同的 SCC 中 ⇒ **不应影响** `low u`
     - 在 `scc_back_edge` 中已被 `In y (stack s)` 条件排除
3. 所有邻居处理完毕后：`low u` 正确反映了 `scc_low_valid_v s u`
4. 若 `low u = dfn u`，则 `pop_scc u`（栈不变式的范畴，本文件可能不需要证明弹出正确性，只需保持 low 不变）

### 4.2 不变量设计

#### 顶层：`tarjan_scc` 的前后条件

```coq
Definition low_pre (u: V) (s: SCCSt) (root: V): Prop :=
  ~ u ∈ visited s /\
  dfn_valid s root /\
  dfn_inv s /\
  fa_visited s.

Definition low_post (u: V) (s: SCCSt) (root: V): Prop :=
  scc_low_valid_v s u /\
  dfn_valid s root /\
  dfn_inv s /\
  fa_visited s.
```

#### forset 循环不变量

需要追踪：在 forset 中，哪些邻居已经被处理。使用 forset 自带的 `done` 谓词。

```coq
(* 已处理的邻居中，哪些成为了树子节点（fa 被设置） *)
Definition children_done (s: SCCSt) (u: V) (done: V -> Prop) (v: V): Prop :=
  v ∈ done /\ fa s v = u /\ fa s v <> v.

(* 已处理的邻居中，哪些是回边目标（仍在栈中，且不是 u 的树子节点） *)
Definition back_edges_done (s: SCCSt) (u: V) (done: V -> Prop) (v: V): Prop :=
  v ∈ done /\ In v (stack s) /\
  fa s v <> u.

(* forset 不变量：low u 正确反映了 done 中已处理邻居的贡献 *)
Definition low_forset_inv (u: V) (done: V -> Prop) (s: SCCSt) (root: V): Prop :=
  dfn_inv s /\
  dfn_valid s root /\
  fa_visited s /\
  u ∈ visited s /\
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
     min_value_of_subset Nat.le
       (fun w => back_edges_done s u done w \/ w = u) (dfn s))
    (fun x => x) (low s u).
```

**注**: 这个不变量设计的核心思想是——`low u` 始终等于"已处理部分"的最小值。
当 `done` 从空集增长到全部邻居时，`low u` 从 `dfn u` 逐步更新到最终的 `scc_low_valid_v`。

**与 GraphLib 版本的关键区别**:
- `back_edges_done` 使用 `In v (stack s)` 而非 `step_without_tree`
- 交叉边（visited ∧ not in stack）被加入 done，但既不满足 `children_done`（fa 未被设置）也不满足 `back_edges_done`（不在栈中），因此**对 low 值无贡献**——与算法行为一致
- 当 done = all_neighbors 时，`children_done` ↔ `son (state_to_dfs_tree s root) u`，`back_edges_done` ↔ `scc_back_edge s u`，两者精确对应

**为什么这个对应关系成立**:

1. **树子节点方向**: forset 遍历 `dg_step g u w`。对于 `~w ∈ visited`，执行 `set_fa w u` 后 `fa s w = u ≠ w`；对于已访问的 w，不执行 `set_fa`，`fa s w` 保持不变（由 `set_fa` 的语义，已被访问的节点的父节点已在之前设定）。因此 `children_done` 精确等于 `{w | dg_step g u w ∧ fa s w = u ∧ fa s w ≠ w}` = `son (state_to_dfs_tree s root) u`（由 `state_to_dfs_tree_step_char` / `state_to_dfs_tree_step_char_backward` 保证）。

2. **回边方向**: 对于 `w ∈ visited ∧ In w (stack s)`，执行 `update_low u (dfn w)`。此时 `fa s w ≠ u`：若 `fa s w = u`，则 w 应以 u 为父节点，但 w 已被访问而 u 当前才进入访问流程，这与 DFS 父节点先于子节点被访问的时序矛盾。因此 `back_edges_done` 精确等于 `{w | dg_step g u w ∧ In w (stack s) ∧ fa s w ≠ u}`。在 `state_to_dfs_tree` 的边由 `fa` 决定的前提下，这又等价于 `{w | dg_step g u w ∧ In w (stack s) ∧ ~ dg_step (state_to_dfs_tree s root) u w}` = `scc_back_edge s u`。

3. **交叉边方向**: 对于 `w ∈ visited ∧ w ∉ stack`，算法 skip。此时 w 在 done 中，但既不满足 `children_done` 也不满足 `back_edges_done`，对 low 无贡献——正确。

### 4.3 证明步骤分解

#### 步骤 1: preloop 建立初始 low (~40–60 行)

```coq
Lemma preloop_establishes_low_forset_inv (u: V):
  Hoare (fun s => low_pre u s root)
        (preloop u)
        (fun _ s => low_forset_inv u ∅ s root).
```

preloop 后：
- `low u = dfn u = timer s`（`preloop_low_set`）
- `children_done s u ∅ = ∅`、`back_edges_done s u ∅ = ∅`
- 故 `low_forset_inv u ∅` = `dfn_inv ∧ dfn_valid ∧ fa_visited ∧ u∈visited ∧ min(∅ ∪ min(∅ ∪ [u]) dfn) id (low u)` = `dfn u = low u`

#### 步骤 2: process_edge 保持 low_forset_inv (~200–350 行)

这是最大的子任务。需要对三个分支分别证明：

**2a. 树边分支** (`~v ∈ visited`):
```
set_fa v u ;; tarjan_scc v ;; get' low v ;; update_low u lv
```

前提: `low_forset_inv u done s`、`~v ∈ visited s`
目标: `low_forset_inv u (done ∪ [v]) s'`

关键推理:
1. `set_fa v u` 后 `fa v = u ≠ v`，故 v ∈ `children_done s' u (done ∪ [v])`
2. 递归调用 `tarjan_scc v` 的前提: `low_pre v` — 由 `set_fa` 后的状态满足
   （`~v∈visited` 保持，dfn_inv/dfn_valid/fa_visited 由已有引理保持）
3. 递归返回后: `scc_low_valid_v s' v` — 由归纳假设
4. `update_low u (low s' v)` 更新 `low u = min(old_low_u, low s' v)`
5. 更新后的 `low u` 将新子节点 v 的贡献纳入，保持 `low_forset_inv u (done ∪ [v])`
6. 注意：v ∈ `children_done` 意味着其 low 值通过 `min_value_of_subset (children_done) (low s)` 参与计算，
   而归纳假设 `scc_low_valid_v s' v` 保证了 `low s' v` 的正确性

**2b. 回边分支** (`v ∈ visited ∧ v ∈ stack`):
```
get' dfn v ;; update_low u dv
```

前提: `low_forset_inv u done s`、`v ∈ visited s`、`v ∈ stack s`
目标: `low_forset_inv u (done ∪ [v]) s'`

关键推理:
1. `v ∈ visited` ⇒ `dfn v < timer`（由 `dfn_inv`）
2. `update_low u (dfn v)` 更新 `low u = min(old_low_u, dfn v)`
3. 新 `back_edges_done` 包含 v（v ∈ done ∪ [v] ∧ In v stack ∧ ~(fa v = u ∧ fa v ≠ v)），故 `low_forset_inv` 保持
4. 注意：v 已被 visited，`fa s v ≠ u` 成立（否则 v 不会在 visited 中而 u 还未被 visited——由 DFS 性质，
   每个节点只有一个父节点，且 u 的递归在 v 之前开始，如果 `fa s v = u` 则矛盾）

**2c. 交叉边分支** (`v ∈ visited ∧ v ∉ stack`):
```
skip
```

前提: `low_forset_inv u done s`、`v ∈ visited s`、`v ∉ stack s`
目标: `low_forset_inv u (done ∪ [v]) s`

关键推理:
1. 不执行任何更新，`low u` 不变
2. v 加入 done 但不满足 `children_done`（v 已访问，不设 fa）也不满足 `back_edges_done`（v 不在栈中）
3. 因此 `low_forset_inv` 平凡保持——这正是 SCC 算法排除交叉边的机制

**2d. Hoare 层面**：需要类似 `process_edge_keep_dfn_valid` 的通用 Hoare 引理：
```coq
Lemma process_edge_keep_low_forset_inv (u v: V) (W: V -> program SCCSt unit):
  (forall x, Hoare (fun s => low_pre x s root /\ ...) (W x)
                   (fun _ s => low_post x s root)) ->
  Hoare (fun s => low_forset_inv u done s)
        (process_edge u W v)
        (fun _ s => low_forset_inv u (done ∪ [v]) s).
```

#### 步骤 3: forset 归纳 (~60–100 行)

```coq
Lemma forset_process_edge_keep_low_forset_inv (u: V) (W: ...):
  Hoare (fun s => low_forset_inv u ∅ s)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => scc_low_valid_v s u /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s).
```

`hoare_fix_nolv_auto` 归纳，done 从 ∅ 增长到全体邻居。当 done 覆盖所有邻居时：
- `children_done s u (all_neighbors)` = `son (state_to_dfs_tree s root) u`
- `back_edges_done s u (all_neighbors) ∪ [u]` = `scc_back_edge s u ∪ [u]`
- 故 `low_forset_inv` 的后件等价于 `scc_low_valid_v s u` ∧ ...

#### 步骤 4: tarjan_scc 归纳 (~100–150 行)

```coq
Theorem tarjan_scc_keep_low_valid (u: V):
  Hoare (fun s => low_pre u s root)
        (tarjan_scc g u)
        (fun _ s => low_post u s root).
```

使用 `Hoare_fix_logicv_conj`，与 `tarjan_scc_keep_dfn_valid` 相同的结构：
- 主性质: `low_pre x → low_post x`
- 辅助性质: `tarjan_scc_keep_visited`（visited 保持性）
- `tarjan_scc_f` 展开: preloop → forset → If-then-pop_scc
- `pop_scc` 分支: 需要 `pop_scc_keep_scc_low_valid_v`（类似 `pop_scc_keep_dfn_valid`）

#### 步骤 5: 全局 scc_low_valid (~50–80 行)

```coq
Theorem tarjan_scc_all_scc_low_valid:
  Hoare (fun s => dfn_inv s /\ fa_visited s /\ dfn_valid s root)
        (tarjan_scc_all g)
        (fun _ s => scc_low_valid s).
```

策略:
1. 对每个顶点 a，`tarjan_scc a` 建立 `scc_low_valid_v s a`
2. 使用 `tarjan_scc_all` 的 forset 结构将单点性质提升为全局 `scc_low_valid s`

#### 步骤 6: scc_is_low (~80–120 行)

```coq
Theorem tarjan_scc_all_scc_is_low:
  Hoare (fun s => dfn_inv s /\ fa_visited s /\ dfn_valid s root)
        (tarjan_scc_all g)
        (fun _ s => scc_is_low s).
```

通过两步证明：
1. 证明 `scc_low_valid_implies_is_low`（本文件内部，使用 `rooted_tree_induction_bottom_up`）
2. 组合 `tarjan_scc_all_scc_low_valid` + 步骤 1 得到最终结论

`tarjan_scc_all_scc_is_low` 是本文件的**最终交付定理**——它精确刻画了 SCC 算法中 low 值的数学含义：
`low s u` 等于从 u 经树边和至多一条回边可达的最小 dfn 值。

---

## 5. 可行性分析

### 5.1 逐项评估

| 子目标 | 复杂度 | 可行性 | 关键前提 |
|--------|--------|--------|----------|
| SCC low 定义及基础引理 | 中 | ✅ | `scc_back_edge` 精确定义回边，`scc_low_valid_implies_is_low` 使用 `rooted_tree_induction_bottom_up` 不依赖 `no_cross_edge` |
| preloop 建立 low_forset_inv | 低 | ✅ | `preloop_low_set`（已有）、`dfn_inv` 保持性（已有）|
| 树边分支 process_edge 保持 | **高** | ⚠️ | `tarjan_scc` 的归纳假设需要返回 `scc_low_valid_v`；需 `set_fa` + 递归 + `update_low` 组合推理 |
| 回边分支 process_edge 保持 | 中 | ✅ | `update_low_nonincreasing`（已有）、`dfn_inv` 保持性（已有）|
| 交叉边分支 | 低 | ✅ | 平凡跳过，不变量不变——`back_edges_done` 用 `In v (stack s)` 排除交叉边 |
| forset 不动点归纳 | 中 | ✅ | `hoare_fix_nolv_auto` + done 增长推理 |
| tarjan_scc Hoare_fix 归纳 | **高** | ⚠️ | 参照 `tarjan_scc_keep_dfn_valid` 的模式，已在 is_dfn 中验证可行 |
| pop_scc 保持 low_valid | 低 | ✅ | `pop_scc` 不修改 dfn/low/fa/visited |
| 全局 scc_low_valid 提升 | 中 | ✅ | `tarjan_scc_all` 的 forset 结构 |
| scc_is_low（声明式）| 中 | ✅ | 自证明 SCC 版 `low_valid_implies_is_low`，使用 `rooted_tree_induction_bottom_up` |

### 5.2 主要风险点

#### 风险 1: `scc_low_valid_implies_is_low` 的证明需要正确的集合分解引理

**问题**: 证明 `scc_low_tree` 的分解（类似 GraphLib 的 `low_tree_decompose`）需要处理
`scc_back_edge`（而非 `step_without_tree`）的 case analysis。

**分析**: 分解引理 `scc_low_tree_decompose` 的结构与 GraphLib 的 `low_tree_decompose` 平行，
但用 `scc_back_edge s u` 替代 `step_without_tree u`。证明通过展开 `scc_low_reachable` 并对
树路径做 case analysis。关键差异在于 `scc_back_edge` 的定义中包含 `In y (stack s)`
（而非 `~ evalid dfstree e`），在集合推理中更易处理。

此外，`scc_low_valid_induction` 的证明可以**完全仿照** GraphLib 的 `low_valid_induction`（第 523–555 行）：
- 用 `scc_back_edge s u` 替换 `step_without_tree u`
- 用 `scc_low_tree s u` 替换 `low_tree u`
- 用 `scc_is_low_v s u` 替换 `is_low_v u (fun_low u)`
- 证明结构不变，因为 `min_eq_forward` 只依赖 `NatLe_TotalOrder` 和 `min_value_of_subset` 的抽象性质，
  不依赖 `no_cross_edge`

**缓解策略**: 从 GraphLib 的 `low_tree_decompose` 和 `low_valid_induction` 证明中提取框架，
替换集合定义为 SCC 版本。预计需要约 80–120 行。

#### 风险 2: `tarjan_scc` 的归纳假设需要返回 `scc_low_valid_v`，而不仅仅是 low 值保持

**问题**: `Hoare_fix_logicv_conj` 的归纳假设形状需要匹配。`scc_low_valid_v` 涉及
`min_value_of_subset` 的复杂命题。

**分析**: `tarjan_scc_keep_dfn_valid` 的模式已经验证 `Hoare_fix_logicv_conj` 可以处理
包含复合不变量的归纳。`scc_low_valid_v` 虽然内部结构更复杂，但作为 Hoare 后件使用时
与其他不变量无异——它只是需要被保持和传递。

**缓解策略**: 参照 `tarjan_scc_keep_dfn_valid` 的结构，逐步组装归纳假设。

#### 风险 3: `pop_scc` 对 `scc_low_valid_v` 的影响

**问题**: `pop_scc u` 修改栈和 sccs 字段，但不修改 dfn/low/fa/visited。
因此 `state_to_dfs_tree` 不变（仅依赖 visited/fa），但 `scc_back_edge s x y` 可能因 `stack s` 变化而变化。

但注意：`scc_low_valid_v s w` 中使用的 `scc_back_edge` 只描述“计算 `low w` 的那一刻”哪些节点在栈中。
`low w` 一旦写入就不再改变，因此后续 `pop_scc` 弹出某些节点不会影响已经成立的 `scc_low_valid_v s w`。
形式化地说，设 `s_pre` 是计算 `low w` 时的状态，`s_post` 是 `pop_scc` 后的状态，则：

- `dfn s_pre = dfn s_post`，`low s_pre = low s_post`，`fa s_pre = fa s_post`，`visited s_pre = visited s_post`；
- `scc_low_valid_v s_pre w` 仅由上述字段和 `stack s_pre` 决定；
- 对 w 而言，`scc_low_valid_v s_post w` 仍然成立，因为 `low w` 没有变，且它等于 `scc_back_edge s_pre` 中 dfn 的最小值，而 `scc_back_edge s_pre` 是历史事实。

**缓解策略**: 证明 `state_to_dfs_tree`、`dfn`、`low`、`fa` 在 `pop_scc` 下不变；然后直接利用 `scc_low_valid_v` 的历史快照性质得到保持性，无需重新计算 `scc_back_edge s_post`。

#### 风险 4: `back_edges_done` 中 `fa s v ≠ u` 条件在回边分支中需要证明

**问题**: 在 process_edge 的回边分支（`v ∈ visited ∧ v ∈ stack`）中，需要证明 `fa s v ≠ u`。
如果 `fa s v = u`，则 v 是 u 的子节点——但 v 已被 visited，这意味着 v 在 u 之前被访问，
且 fa 已设置为 u。这在 DFS 中不可能，因为 u 当前正在被处理（u 刚进入 visited），
而 u 的邻居 v 如果已 visited 且有 `fa s v = u`，则意味着 u→v 是树边（而不是回边）。

**分析**: 由 DFS 的不变量：对于任意一对节点 x, y，如果 `fa s y = x`，则 x 在 y 之前被访问，
且 `tarjan_scc x` 的调用在 `tarjan_scc y` 之前。当 `process_edge u v` 在 forset 中处理时，
u 正在被访问中，如果 v 已被 visited 且 `fa s v = u`，则意味着 u 在 v 之前被访问——
但 v 已被 visited，矛盾（v 不可能在 u 之前被访问却以 u 为父节点，因为 u 的递归调用
在设置子节点 fa 之前必须先被访问）。由于 `fa s v = v` 只在 v 为根时成立，而 u 当前访问的邻居 v 不可能是以 u 为父节点的根，故 `fa s v ≠ u` 与 `~(fa s v = u ∧ fa s v ≠ v)` 等价；使用更简洁的 `fa s v ≠ u` 即可。

**缓解策略**: 使用 `dfn_inv` + `fa_visited` 建立时序推理引理，或从 `Tarjan_scc_basics.v` 的
`set_fa_keep_not_visited` 等引理推导。这是一个中等难度但可解决的问题。

---

## 6. 详细实现计划

### 6.0 实现前的检查清单

在按 6.1 节的代码骨架开始证明之前，建议先完成以下确认，避免中期返工：

1. **Import 模式对齐**：6.1 节的 `Require Import` / `From ... Require Import` / `Import` / `Open Scope`
   需与 `Tarjan_scc_is_dfn.v` 的实际开头保持一致；若该项目使用 `_CoqProject`/`_RocqProject`
   管理命名空间，应避免重复导入或作用域冲突。
2. **`state_to_dfs_tree` 的边语义**：确认 `dg_step (state_to_dfs_tree s root) x y` 与
   `fa s y = x ∧ y ≠ x ∧ y ∈ visited s`（或项目实际采用的等价形式）之间的双向等价引理已可用。
   这是 `children_done ↔ son` 和 `back_edges_done ↔ scc_back_edge` 对应关系的基础。
3. **`min_value_of_subset` 接口确认**：确认 `MaxMinLib` 中该谓词的参数顺序和空集行为
   （特别是空集时是否返回某个默认值或不可证），以保证 `scc_low_valid_v` 在叶节点情形（无子节点、无回边）下能推出 `low u = dfn u`。
4. **先证 `scc_low_valid_implies_is_low`**：在进入复杂的 Hoare 证明之前，先完成
   `scc_low_tree_decompose` 和 `scc_low_valid_implies_is_low` 的证明。这是整个定义体系的
   “冒烟测试”：如果这两个引理无法走通，说明 `scc_back_edge` / `scc_low_valid_v` / `scc_is_low_v`
   的定义需要调整。

### 6.1 文件结构

```coq
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.EquivDec.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib Require Import directed.rootedtree.      (* rooted_tree_induction_bottom_up *)
From MaxMinLib Require Import MaxMin Interface.
From Algorithms.Tarjan_directed Require Import SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section IS_LOW.
  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  (* ================================================================ *)
  (* 1. SCC Low Correctness Definitions                               *)
  (* ================================================================ *)
  Definition scc_back_edge (s: SCCSt) (x y: V): Prop :=
    dg_step g x y /\
    In y (stack s) /\
    ~ dg_step (state_to_dfs_tree s root) x y.

  Definition scc_low_valid_v (s: SCCSt) (u: V): Prop :=
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (son (state_to_dfs_tree s root) u) (low s) ∪
       min_value_of_subset Nat.le (scc_back_edge s u ∪ [u]) (dfn s))
      (fun x => x) (low s u).

  Definition scc_low_valid (s: SCCSt): Prop :=
    forall v, v ∈ visited s -> scc_low_valid_v s v.

  Definition scc_low_reachable (s: SCCSt) (x y: V): Prop :=
    exists z,
      dg_reachable (state_to_dfs_tree s root) x z /\
      (z = y \/ scc_back_edge s z y).

  Definition scc_low_tree (s: SCCSt) (x: V): V -> Prop :=
    fun y => scc_low_reachable s x y.

  Definition scc_is_low_v (s: SCCSt) (u: V): Prop :=
    min_value_of_subset Nat.le (scc_low_tree s u) (dfn s) (low s u).

  Definition scc_is_low (s: SCCSt): Prop :=
    forall v, v ∈ visited s -> scc_is_low_v s v.

  (* ================================================================ *)
  (* 2. Invariant Definitions                                         *)
  (* ================================================================ *)
  Definition children_done (s: SCCSt) (u: V) (done: V -> Prop) (v: V): Prop :=
    v ∈ done /\ fa s v = u /\ fa s v <> v.

  Definition back_edges_done (s: SCCSt) (u: V) (done: V -> Prop) (v: V): Prop :=
    v ∈ done /\ In v (stack s) /\
    fa s v <> u.

  Definition low_forset_inv (u: V) (done: V -> Prop) (s: SCCSt): Prop :=
    dfn_inv s /\
    dfn_valid s root /\
    fa_visited s /\
    u ∈ visited s /\
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
       min_value_of_subset Nat.le
         (fun w => back_edges_done s u done w \/ w = u) (dfn s))
      (fun x => x) (low s u).

  Definition low_pre (u: V) (s: SCCSt): Prop :=
    ~ u ∈ visited s /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s.

  Definition low_post (u: V) (s: SCCSt): Prop :=
    scc_low_valid_v s u /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s.

  (* ================================================================ *)
  (* 3. SCC Low Induction Lemmas (SCC-specific versions of GraphLib)  *)
  (* ================================================================ *)
  Lemma scc_low_tree_decompose (s: SCCSt) (u: V):
    u ∈ visited s ->
    scc_low_tree s u ==
    [u] ∪ scc_back_edge s u ∪
    (fun w => exists v, son (state_to_dfs_tree s root) u v /\ scc_low_tree s v w).

  Lemma scc_low_valid_induction (s: SCCSt) (u: V)
    (IHu: forall v, son (state_to_dfs_tree s root) u v -> scc_is_low_v s v):
    min_value_of_subset Nat.le (son (state_to_dfs_tree s root) u) (low s) ==
    min_value_of_subset Nat.le
      ((fun w => exists v, son (state_to_dfs_tree s root) u v /\ scc_low_tree s v w))
      (dfn s).

  Lemma scc_low_valid_induction_is_low (s: SCCSt) (u: V)
    (Hu: u ∈ visited s)
    (IHu: forall v, son (state_to_dfs_tree s root) u v -> scc_is_low_v s v):
    scc_low_valid_v s u -> scc_is_low_v s u.

  Lemma scc_low_valid_implies_is_low (s: SCCSt):
    scc_low_valid s -> scc_is_low s.

  (* ================================================================ *)
  (* 4. preloop establishes initial low                               *)
  (* ================================================================ *)
  Lemma preloop_establishes_low_forset_inv (u: V):
    Hoare (fun s => low_pre u s) (preloop u) (fun _ s => low_forset_inv u ∅ s).

  (* ================================================================ *)
  (* 5. process_edge preserves low_forset_inv                         *)
  (* ================================================================ *)
  Lemma process_edge_keep_low_forset_inv (u v: V) (W: V -> program SCCSt unit):
    (forall x, Hoare (fun s => low_pre x s) (W x) (fun _ s => low_post x s)) ->
    Hoare (fun s => low_forset_inv u done s)
          (process_edge u W v)
          (fun _ s => low_forset_inv u (done ∪ [v]) s).

  Lemma forset_keep_low_forset_inv (u: V) (W: V -> program SCCSt unit):
    (forall x, Hoare (fun s => low_pre x s) (W x) (fun _ s => low_post x s)) ->
    Hoare (fun s => low_forset_inv u ∅ s)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => scc_low_valid_v s u /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s).

  (* ================================================================ *)
  (* 6. pop_scc preserves low_valid                                   *)
  (* ================================================================ *)
  Lemma pop_scc_keep_scc_low_valid_v (u: V):
    Hoare (fun s => scc_low_valid_v s u /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s)
          (pop_scc u)
          (fun _ s => scc_low_valid_v s u /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s).

  (* ================================================================ *)
  (* 7. tarjan_scc core theorem                                       *)
  (* ================================================================ *)
  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s => low_pre u s) (tarjan_scc g u) (fun _ s => low_post u s).

  (* ================================================================ *)
  (* 8. Global scc_low_valid / scc_is_low                             *)
  (* ================================================================ *)
  Theorem tarjan_scc_all_scc_low_valid:
    Hoare (fun s => dfn_inv s /\ fa_visited s /\ dfn_valid s root)
          (tarjan_scc_all g)
          (fun _ s => scc_low_valid s).

  Theorem tarjan_scc_all_scc_is_low:
    Hoare (fun s => dfn_inv s /\ fa_visited s /\ dfn_valid s root)
          (tarjan_scc_all g)
          (fun _ s => scc_is_low s).

End IS_LOW.
```

### 6.2 与已有基础设施的衔接

| 需要的引理 | 来源 | 状态 |
|-----------|------|------|
| `preloop_low_set` | `Tarjan_scc_basics.v` | ✅ |
| `update_low_nonincreasing` | `Tarjan_scc_basics.v` | ✅ |
| `update_low_keep_dfn` | `Tarjan_scc_basics.v` | ✅ |
| `process_edge_keep_low` | `Tarjan_scc_basics.v` | ✅ |
| `tarjan_scc_keep_low` | `Tarjan_scc_basics.v` | ✅ |
| `tarjan_scc_keep_dfn_low_order` | `Tarjan_scc_basics.v` | ✅ |
| `dfn_inv` 全套 | `Tarjan_scc_is_dfn.v` | ✅ |
| `dfn_valid` 全套 | `Tarjan_scc_is_dfn.v` | ✅ |
| `fa_visited` 全套 | `Tarjan_scc_is_dfn.v` | ✅ |
| `tarjan_scc_keep_visited` | `Tarjan_scc_basics.v` | ✅ |
| `state_to_dfs_tree_step_char` | `Tarjan_scc.v` | ✅ |
| `state_to_dfs_tree_step_char_backward` | `Tarjan_scc.v` | ✅ |
| `state_to_dfs_tree_step_fa` | `Tarjan_scc.v` | ✅ |
| `set_fa_adds_tree_edge` | `Tarjan_scc.v` | ✅ |
| `set_fa_preserves_tree_edges` | `Tarjan_scc.v` | ✅ |
| `set_fa_preserves_tree_vvalid` | `Tarjan_scc.v` | ✅ |
| `rooted_tree_induction_bottom_up` | `GraphLib/directed/rootedtree.v` | ✅ |
| `min_value_of_subset` / `NatLe_TotalOrder` | `MaxMinLib` | ✅ |
| `min_union_iff` | `MaxMinLib.Interface` | ✅ |
| `min_eq_forward` | `MaxMinLib.MaxMin` | ✅ |

**不再需要**（与初版设计相比）:
| ~~`low_valid_induction`~~ | ~~`GraphLib/examples/tarjan.v`~~ | ❌ 自行证明 SCC 版本 |
| ~~`low_valid_implies_is_low`~~ | ~~`GraphLib/examples/tarjan.v`~~ | ❌ 自行证明 SCC 版本 |

---

## 7. 工作量估算

### 7.1 修订后的估算

| 步骤 | 内容 | 预估行数 | 预估时间 | 风险 |
|------|------|---------|---------|------|
| 1 | SCC low 定义 + 分解引理 (`scc_low_tree_decompose`) | 80–120 | 3–5 小时 | 中 |
| 2 | SCC 归纳引理 (`scc_low_valid_induction` 等 3 个) | 60–100 | 2–4 小时 | 中 |
| 3 | 不变量定义 (`children_done`, `back_edges_done`, `low_forset_inv`, `low_pre`/`low_post`) | 40–60 | 1–2 小时 | 低 |
| 4 | preloop 建立不变量 | 40–60 | 1–2 小时 | 低 |
| 5 | process_edge 保持不变量（树边）| 150–250 | 4–8 小时 | 高 |
| 6 | process_edge 保持不变量（回边/交叉边）| 80–120 | 2–4 小时 | 中 |
| 7 | forset 归纳 | 60–100 | 2–4 小时 | 中 |
| 8 | tarjan_scc Hoare_fix 归纳 | 100–150 | 3–6 小时 | 高 |
| 9 | pop_scc 保持 + 全局提升 | 60–100 | 2–4 小时 | 低 |
| 10 | 整体编译验证 + 调试 | — | 2–4 小时 | 中 |
| **合计** | | **670–1060** | **22–43 小时** | |

### 7.2 与桥判定版本的工作量对比

| | 桥判定 | SCC（修订后预估）|
|------|--------|-------------------|
| 行数 | 2812 | 670–1060 |
| eset 管理 | ~800 行 | 0 行（不需要）|
| 多不变量并发归纳 | 6 个辅助不变量 | 1–2 个不变量 |
| tree_edge 不变量 | ~300 行 | 0 行（不需要）|
| 核心 low 正确性（含 SCC 专用定义）| ~600 行 | ~350–550 行 |
| low 归纳引理（含 SCC 专用版本）| 复用 GraphLib（0 行）| ~140–220 行（新增）|
| 全局提升 + 最终定理 | ~300 行 | ~120–200 行 |

SCC 版本预期比桥判定版本简化 **3–4 倍**，主要因为不需要 eset 追踪和 tree_edge 不变量。
新增的 SCC 专用定义和归纳引理（约 140–220 行）是可控的代价，换来对交叉边的正确处理。

### 7.3 与初版设计的差异

| 项目 | 初版预估 | 修订后预估 | 变化原因 |
|------|---------|-----------|---------|
| 行数 | 480–770 | 670–1060 | 新增 SCC 专用定义 + 归纳引理 |
| 时间 | 14–29 h | 22–43 h | 上述新增内容 + 交叉边推理 |
| SCC 专用定义 | 0 行（复用 GraphLib）| 140–220 行 | 修正 GraphLib 不兼容问题 |
| GraphLib 依赖 | `low_valid`/`is_low` 直接复用 | 仅复用 `min_value_of_subset` + 树归纳 | 避免 `no_cross_edge` 陷阱 |

---

## 8. 依赖关系图

```
Tarjan_scc.v (程序定义 + state_to_dfs_tree 结构引理)
    ↓
Tarjan_scc_basics.v (原语 low 保持性：preloop_low_set, update_low_nonincreasing,
                     process_edge_keep_low, tarjan_scc_keep_low)
    ↓
Tarjan_scc_is_dfn.v (dfn_inv, dfn_valid, fa_visited, dfn_unique)
    ↓
Tarjan_scc_is_low.v  ← 本文件
    ├── scc_back_edge, scc_low_valid_v, scc_low_valid (构造式)
    ├── scc_low_reachable, scc_low_tree, scc_is_low_v, scc_is_low (声明式)
    ├── scc_low_tree_decompose (SCC 版 low_tree_decompose)
    ├── scc_low_valid_induction (SCC 版 low_valid_induction)
    ├── scc_low_valid_implies_is_low (SCC 版，不依赖 no_cross_edge)
    ├── low_forset_inv (forset 循环不变量，用 scc_back_edge 排除交叉边)
    ├── low_pre / low_post (tarjan_scc 前后条件，基于 scc_low_valid_v)
    ├── tarjan_scc_keep_low_valid (核心 Hoare 定理)
    ├── tarjan_scc_all_scc_low_valid (全局构造式 low 正确性)
    └── tarjan_scc_all_scc_is_low (全局声明式 low 正确性，最终交付定理)
    ↓
Tarjan_scc_stack.v (栈不变量 + SCC 弹出，需要 scc_is_low 判断 dfn=low 触发弹出)
    ↓
SCC_correctness.v (最终功能正确性)
```

**依赖的 GraphLib 模块**:
```
GraphLib/graph_basic.v         → dg_step, dg_reachable, Graph typeclass
GraphLib/directed/rootedtree.v → rooted_tree_induction_bottom_up, son, subtree
MaxMinLib/MaxMin.v             → min_value_of_subset, min_eq_forward
MaxMinLib/Interface.v          → NatLe_TotalOrder, min_union_iff
```

**不再依赖**:
```
GraphLib/examples/tarjan.v     → 仅参考其证明框架，不复用 low_valid/is_low 定义
```

---

## 9. 结论

**Tarjan_scc_is_low.v 的开发是可行的**，预计 670–1060 行，22–43 小时工作量。

**关键优势**（相比桥判定版本）:
1. **不需要 eset 追踪** — SCC 的 `forset (dg_step g u w)` 天然按邻居迭代
2. **不需要 tree_edge 不变量** — `state_to_dfs_tree` 从 `fa`/`visited` 隐式推导
3. **只需 1–2 个不变量** — vs 桥判定的 6 个并发不变量
4. **dfn 基础设施已完备** — `dfn_inv`、`dfn_valid`、`fa_visited` 全套可用
5. **已有 low 原语保持性** — `Tarjan_scc_basics.v` 提供了 `update_low`、`process_edge_keep_low` 等基础引理

**关键修正**（相比初版设计）:
1. **定义 SCC 专用的 low 正确性谓词** — `scc_low_valid_v` / `scc_low_valid` / `scc_is_low_v` / `scc_is_low`
2. **使用 `scc_back_edge`（`In y (stack s)`）而非 `step_without_tree`** — 精确排除交叉边
3. **自行证明 SCC 版归纳引理** — 仿照 GraphLib 框架但不依赖 `no_cross_edge`
4. **`back_edges_done` 精确定义** — 排除了交叉边，与 `scc_back_edge` 一致

**主要挑战**:
1. `scc_low_tree_decompose` 和 `scc_low_valid_induction` 需要仔细处理 `scc_back_edge`
   的集合分解——但证明框架可从 GraphLib 的 `low_tree_decompose` / `low_valid_induction` 移植
2. `tarjan_scc` 的 Hoare_fix 归纳假设需要返回 `scc_low_valid_v`——虽然结构上参照
   `tarjan_scc_keep_dfn_valid` 可行，但 `min_value_of_subset` 的推理较 `dfn_valid` 更复杂
3. `back_edges_done` 中 `fa s v ≠ u` 条件在回边分支中需要 DFS 时序推理支持

**建议**: 先完成 SCC 专用定义和归纳引理（步骤 1–2），验证 `scc_low_valid_implies_is_low`
可通过 `rooted_tree_induction_bottom_up` 证明（这确认了定义的正确性），再进入 Hoare 证明。
对于栈相关的推理（如 `v ∈ stack` 时 `fa s v ≠ u`），可先作为辅助引理在 `Tarjan_scc_basics.v`
级别证明，或在本文件中基于 `dfn_inv` + `fa_visited` + `set_fa_keep_not_visited` 推导。

---

## 10. 待确认假设与早期验证

在投入完整实现前，下列假设需要在编码初期得到确认；任何一条不成立都可能导致本设计返工：

| 编号 | 假设内容 | 验证方式 | 若不成立的影响 |
|------|---------|---------|--------------|
| A1 | `state_to_dfs_tree` 的边恰好由 `fa` 字段导出：即 `dg_step (state_to_dfs_tree s root) x y` 当且仅当 `fa s y = x ∧ y ≠ x ∧ y ∈ visited s`（或项目实际采用的等价形式） | 查阅 `Tarjan_scc.v` 中 `state_to_dfs_tree_step_char` 系列引理 | `children_done ↔ son`、`back_edges_done ↔ scc_back_edge` 的对应关系失效 |
| A2 | `min_value_of_subset Nat.le S f m` 在 `S = ∅` 时的行为允许推出 `m = f u` 当集合为 `{u}` 时 | 做一个小型 Rocq 查询或查看 `MaxMinLib.Interface` | `preloop_establishes_low_forset_inv` 无法 trivially 完成 |
| A3 | `rooted_tree_induction_bottom_up` 对 `state_to_dfs_tree s root` 适用，且其 `son` 与本文件使用的 `son` 一致 | 对照 `GraphLib/directed/rootedtree.v` | `scc_low_valid_implies_is_low` 证明无法套用该归纳原理 |
| A4 | `pop_scc` 不修改 `dfn`、`low`、`fa`、`visited` 字段 | 查看 `Tarjan_scc.v` / `Tarjan_scc_basics.v` 中 `pop_scc` 的定义或保持性引理 | `pop_scc_keep_scc_low_valid_v` 不成立 |
| A5 | `Tarjan_scc_is_dfn.v` 已完成 `dfn_inv`、`dfn_valid`、`fa_visited` 的完整 Hoare 定理，且形式可直接作为本文件前提使用 | 阅读 `Tarjan_scc_is_dfn.v` 最终定理列表 | `low_pre` / `low_post` 的前提无法组装 |
| A6 | `process_edge` 的回边分支中，`v ∈ visited ∧ v ∈ stack` 蕴含 `fa s v ≠ u` 可由已有不变量证明 | 先尝试证明一个独立引理 | `back_edges_done` 的定义无法在回边分支中满足 |

**早期验证路线**:
1. 创建 `Tarjan_scc_is_low.v` 骨架，写入 `scc_back_edge`、`scc_low_valid_v`、`scc_is_low_v` 等定义；
2. 不进入 Hoare，先证明 `scc_low_tree_decompose` 和 `scc_low_valid_implies_is_low`；
3. 若步骤 2 在 4–6 小时内走不通，优先检查 A1、A3、A6；
4. 步骤 2 走通后，再依次实现 `low_forset_inv`、`preloop_establishes_low_forset_inv`、
   `process_edge_keep_low_forset_inv`。

---

*设计文档版本：2.1*
*最后更新：2026-06-18*
*修订说明：
- 简化 `back_edges_done` 条件为 `fa s v <> u`，并补充等价性说明；
- 明确 `scc_low_valid_v` / `low w` 的历史快照性质，降低 `pop_scc` 保持性证明的语义歧义；
- 新增 6.0 实现前检查清单与 10. 待确认假设，提升可执行性；
- 修正第 9 节主要挑战中 `back_edges_done` 条件的表述。*
