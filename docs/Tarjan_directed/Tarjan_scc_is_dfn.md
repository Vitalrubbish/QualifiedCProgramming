# Tarjan_scc_is_dfn — DFS 编号（dfn）不变式与核心定理

**Author**: Vitalrubbish
**Date**: 2026-06-17

本文档整理 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_dfn.v` 中的所有定义、引理与定理，供后续开发参考。

---

## Context 与依赖

整个文件位于 `Section IS_DFN` 下，共享以下 Context：

```coq
Context {V E: Type}
        `{EqDec V eq}
        (g: OriginalGraphType V E)
        `{OriginalGraph_gvalid g}
        (root: V)
        (g_vvalid_root: original_vvalid g root).
```

依赖的库：

| Import | 用途 |
|--------|------|
| `Coq.Lists.List` | `In`、列表操作 |
| `Coq.Logic.Classical_Prop` | `classic` 排中律 |
| `Coq.Classes.EquivDec` | `equiv_decb` 可判定等价 |
| `Lia` | 线性算术自动化解 |
| `SetsClass.SetsClass` | 集合记法 (`SetsNotation`) |
| `MonadLib.StateRelMonad` | `StateRelBasic`、`StateRelHoare`、`FixpointLib` — Hoare 逻辑基础设施 |
| `GraphLib.graph_basic` | `Graph`、`GValid` 等图类型类基础设施 |
| `GraphLib.Syntax` | `MonadNotation` 单子记法 |
| `GraphLib.examples.tarjan` | `OriginalGraphType` 等图类型定义 |
| `Algorithms.Tarjan_directed.SCC_basic` | 有向图 SCC 数学规格 |
| `Algorithms.Tarjan_directed.Tarjan_scc` | `SCCSt`、基本操作、`tarjan_scc`、`tarjan_scc_all`、`state_to_dfs_tree` |
| `Algorithms.Tarjan_directed.Tarjan_scc_basics` | 83 个 Hoare 基础引理（原语保持性、preloop、process_edge、forset、tarjan_scc 核心保持定理） |

该文件的定位：**Layer 2→1 的第三个证明文件**，位于 `Tarjan_scc_basics.v`（Hoare 基础设施层）之上，负责证明 DFS 编号（dfn）的有效性，并为后续 `Tarjan_scc_is_low.v`、`Tarjan_scc_stack.v`、`SCC_correctness.v` 提供 dfn 相关的核心定理。

---

## 1. 核心定义

### 1.1 `dfn_inv` — 基本 dfn 不变量

```coq
Definition dfn_inv (s: @SCCSt V): Prop :=
  (forall v, v ∈ visited s -> dfn s v < timer s) /\
  (forall v, dfn s v = 0 <-> ~ v ∈ visited s) /\
  0 < timer s.
```

**三个合取项**:
- **分量 1**: 已访问顶点的 dfn 严格小于当前 timer——dfn 保存的是"访问时刻"的时间戳
- **分量 2**: 未访问顶点的 dfn 为 0，且 dfn=0 当且仅当未访问——dfn=0 是"未访问"的标记
- **分量 3**: `0 < timer s`——timer 始终为正（与设计文档的差异：设计文档只规划了两个合取项，实现增加了第三个以简化后续推理）

`dfn_inv` 是证明 `dfn_valid` 的核心前提：树边 `u → v` 要求 `dfn u < dfn v`，而这源于 u 先于 v 被访问。

### 1.2 `dfn_injective` — dfn 单射性辅助定义

```coq
Definition dfn_injective (s: @SCCSt V): Prop :=
  forall x y, x <> y -> x ∈ visited s -> y ∈ visited s -> dfn s x <> dfn s y.
```

已访问的不同顶点的 dfn 值互不相同。这是 `dfn_unique` 的辅助谓词。

### 1.3 `dfn_valid` — 树边 dfn 单调性

```coq
Definition dfn_valid (s: @SCCSt V) (root: V): Prop :=
  forall x y, dg_step (state_to_dfs_tree (V:=V) (E:=E) g s root) x y ->
  dfn s x < dfn s y.
```

DFS 树中每条有向边 `x → y` 满足 `dfn[x] < dfn[y]`——父节点的 dfn 严格小于子节点的 dfn。

### 1.4 `fa_visited` — 树父节点访问性

```coq
Definition fa_visited (s: @SCCSt V): Prop :=
  forall v, fa s v <> v -> fa s v ∈ visited s.
```

对于 DFS 树中每个非根顶点（`fa v ≠ v`），其父节点 `fa v` 在 visited 集中。这是证明 `dfn_valid` 的关键辅助谓词，用于在 `set_fa` 时刻推导 `dfn u < dfn v` 的时序关系。

### 1.5 `dfn_pre` / `dfn_post` — 归纳包装谓词

```coq
Definition dfn_pre (u: V) (s: @SCCSt V) (root: V): Prop :=
  ~ u ∈ visited s /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s.

Definition dfn_post (s: @SCCSt V) (root: V): Prop :=
  dfn_valid s root /\ dfn_inv s.
```

参照桥判定版本的过渡谓词设计，用于支持 `tarjan_scc` 的 Hoare 不动点归纳：
- **`dfn_pre u`**: u 即将被 preloop 处理的前置条件
- **`dfn_post`**: u 已被 `tarjan_scc u` 处理完成的后置条件

---

## 2. `dfn_inv` 保持性证明

### 2.1 初始成立

| 引理 | 语句 | 行号 |
|------|------|------|
| `dfn_inv_init` | `dfn_inv initSt` | 34–40 |

### 2.2 原语操作保持性

| 引理 | 语句 | 行号 |
|------|------|------|
| `set_fa_keep_dfn_inv` | `Hoare (dfn_inv) (set_fa v p) (dfn_inv)` | 42–49 |
| `update_low_keep_dfn_inv` | `Hoare (dfn_inv) (update_low u n) (dfn_inv)` | 51–59 |
| `pop_scc_keep_dfn_inv` | `Hoare (dfn_inv) (pop_scc u) (dfn_inv)` | 61–70 |
| `preloop_keep_dfn_inv` | `Hoare (dfn_inv) (preloop u) (dfn_inv)` | 72–113 |

**证明策略** (`preloop_keep_dfn_inv`): 将 `dfn_inv` 拆分为两个独立的后件，分别证明：
- 分量 1（`dfn v < timer`）: 对 `v = u` 用 `preloop_dfn_set` 推出 `dfn u = old_timer < S old_timer = new_timer`；对 `v ≠ u` 用 `preloop_keep_dfn` + `incr_timer` 只增 timer
- 分量 2+3（`dfn v = 0 ↔ ~ visited` + `timer > 0`）: 类似分情况处理

### 2.3 复合操作保持性

| 引理 | 语句 | 行号 |
|------|------|------|
| `get_low_update_low_keep_dfn_inv` | `Hoare (dfn_inv) (get' low v ;; update_low u lv) (dfn_inv)` | 115–125 |
| `get_dfn_update_low_keep_dfn_inv` | `Hoare (dfn_inv) (get' dfn v ;; update_low u dv) (dfn_inv)` | 127–137 |
| `process_edge_keep_dfn_inv` | 若 `W x` 均保持 `dfn_inv`，则 `process_edge u W v` 也保持 | 139–160 |
| `forset_process_edge_keep_dfn_inv` | 若 `W x` 均保持 `dfn_inv`，则 `forset` 也保持 | 162–177 |

### 2.4 核心递归与外层循环

| 定理 | 语句 | 行号 |
|------|------|------|
| `tarjan_scc_keep_dfn_inv` | `Hoare (dfn_inv) (tarjan_scc g u) (dfn_inv)` | 179–195 |
| `tarjan_scc_all_keep_dfn_inv` | `Hoare (dfn_inv) (tarjan_scc_all g) (dfn_inv)` | 197–212 |

**`tarjan_scc_keep_dfn_inv` 证明策略**: `hoare_fix_nolv_auto` 不动点归纳 + `preloop_keep_dfn_inv` → `forset_process_edge_keep_dfn_inv` → `pop_scc_keep_dfn_inv` 标准三段组合。

---

## 3. `fa_visited` 保持性证明

`fa_visited` 是实际的工程核心，占文件约 500 行（229–731），为 `dfn_valid` 的 Hoare 不动点归纳提供关键的树结构不变量。

### 3.1 初始成立

| 引理 | 语句 | 行号 |
|------|------|------|
| `fa_visited_init` | `fa_visited initSt` | 239–243 |

### 3.2 原语操作保持性

| 引理 | 语句 | 行号 |
|------|------|------|
| `set_fa_keep_fa_visited` | `Hoare (p ∈ visited ∧ fa_visited) (set_fa v p) (fa_visited)` | 247–263 |
| `preloop_keep_fa_visited` | `Hoare (fa_visited) (preloop u) (fa_visited)` | 265–273 |
| `update_low_keep_fa_visited` | `Hoare (fa_visited) (update_low u n) (fa_visited)` | 275–285 |
| `pop_scc_keep_fa_visited` | `Hoare (fa_visited) (pop_scc u) (fa_visited)` | 287–296 |
| `pop_scc_keep_dfn_valid` | `Hoare (dfn_valid root) (pop_scc u) (dfn_valid root)` | 298–312 |

### 3.3 复合操作保持性

| 引理 | 语句 | 行号 |
|------|------|------|
| `get_low_update_low_keep_fa_visited` | 基本复合版本 | 314–324 |
| `get_dfn_update_low_keep_fa_visited` | 基本复合版本 | 326–336 |
| `process_edge_keep_fa_visited` | 基本版本，需要 `u ∈ visited` 前提 | 338–364 |
| `get_low_update_low_keep_fa_visited_rich` | Rich 版本：同时保持 `u ∈ visited ∧ fa_visited` | 371–387 |
| `process_edge_keep_fa_visited_rich` | Rich 版本：回调假设匹配 fixpoint IH 形状 | 392–437 |
| `process_edge_keep_combined` | 通用版本：线程化 `(tracked∈visited ∧ fa_visited) ∧ center∈visited` | 443–516 |
| `forset_process_edge_keep_combined` | 对应的 forset 版本 | 518–538 |
| `forset_process_edge_keep_fa_visited_rich` | forset 保持 `u ∈ visited ∧ fa_visited` | 543–560 |

### 3.4 核心递归定理

| 定理 | 语句 | 行号 |
|------|------|------|
| `tarjan_scc_keep_fa_visited_rich` | `Hoare (u∈visited ∧ fa_visited) (tarjan_scc g u) (u∈visited ∧ fa_visited)` | 570–657 |
| `tarjan_scc_keep_fa_visited` | `Hoare (fa_visited) (tarjan_scc g u) (fa_visited)` | 665–731 |

**证明策略**: 两个定理均使用 `Hoare_fix_logicv_conj`，以 `tarjan_scc_keep_visited` 为辅助性质，将 `fa_visited` 作为主归纳性质。`tarjan_scc_keep_fa_visited_rich` 需要额外线程化 `u ∈ visited`（调用者顶点），因为内部 `forset` 遍历的是当前顶点 `x` 的邻居，其不变量需要 `x ∈ visited`；而外层不动点的归纳假设需要 `u ∈ visited`，两者通过 `process_edge_keep_combined` 桥接。

`tarjan_scc_keep_fa_visited` 是前者的简化版本——不变量仅为 `fa_visited`（不需要 `u ∈ visited`），避免了跟踪顶点不匹配的问题，证明更简洁。

---

## 4. `dfn_valid` 保持性证明

### 4.1 preloop 阶段

| 引理 | 语句 | 行号 |
|------|------|------|
| `preloop_preserves_dfn_valid` | `Hoare (~u∈visited ∧ dfn_valid root ∧ dfn_inv ∧ fa_visited) (preloop u) (u∈visited ∧ dfn_valid root ∧ dfn_inv)` | 737–795 |

**证明策略**: 对 `state_to_dfs_tree` 中的每条树边 `x → y`，分两种情形：
- **情形 1**: `y` 在 preloop 前已访问 → 该树边在 preloop 前已存在，由假设中的 `dfn_valid` 直接得到 `dfn x < dfn y`
- **情形 2**: `y = u`（新树边 `fa s0 u → u`）→ 由 `fa_visited` 知 `x = fa s0 y ∈ visited`，再由 `dfn_inv` 得 `dfn x < timer s0`，而 preloop 后 `dfn u = timer s0`，故 `dfn x < dfn u`

### 4.2 set_fa 阶段 — `dfn_pre` 过渡引理

| 引理 | 语句 | 行号 |
|------|------|------|
| `set_fa_preserves_dfn_pre_child` | 基础版本：从 5 个前提推出 `dfn_pre v s root` | 806–838 |
| `set_fa_preserves_dfn_pre_child_rich` | Rich 版本：同时保持 `u ∈ visited` | 840–856 |
| `set_fa_preserves_dfn_pre_child_full` | Full 版本：同时保持 `u ∈ visited ∧ fa_visited` | 858–903 |

这些引理是 process_edge 树边分支中的关键一步：`set_fa v u` 执行后，`v` 满足 `dfn_pre v`，从而可以调用递归假设 `W v`。

### 4.3 update_low 保持性

| 引理 | 语句 | 行号 |
|------|------|------|
| `update_low_keep_dfn_valid` | `Hoare (dfn_valid root) (update_low u n) (dfn_valid root)` | 905–915 |
| `get_low_update_low_keep_dfn_valid` | 复合版本 | 917–927 |
| `get_dfn_update_low_keep_dfn_valid` | 复合版本 | 929–939 |

### 4.4 process_edge 保持性

| 引理 | 语句 | 行号 |
|------|------|------|
| `process_edge_keep_dfn_valid` | 基础版本 | 941–994 |
| `process_edge_keep_dfn_valid_full` | Full 版本：+ fa_visited | 996–1082 |
| `process_edge_keep_dfn_valid_pre` | Pre 版本：回调假设接收 `dfn_pre x ∧ u∈visited ∧ fa_visited` | 1084–1159 |
| `forset_process_edge_keep_dfn_valid_pre` | 对应的 forset 版本 | 1161–1194 |

**树边分支的证明结构**:
1. `set_fa v u` → 建立 `dfn_pre v`（通过 `set_fa_preserves_dfn_pre_child_*`）
2. `W v`（递归调用）→ 由归纳假设得 `dfn_post`
3. `get' low v ;; update_low u lv` → 保持 `dfn_valid` 和 `dfn_inv`

**回边分支**: `update_low u (dfn s0 v)` 保持 `dfn_valid`（不修改 fa/dfn/visited，只修改 low）。

### 4.5 核心递归定理

| 定理 | 语句 | 行号 |
|------|------|------|
| `tarjan_scc_keep_dfn_valid` | `Hoare (dfn_pre u root) (tarjan_scc g u) (dfn_post root)` | 1196–1302 |

**证明策略**: 使用 `Hoare_fix_logicv_conj` 五参数形式：
- **主性质**: `dfn_pre x s root → dfn_post s root ∧ fa_visited s`
- **辅助性质**: `d ∈ visited s → d ∈ visited s`（由 `tarjan_scc_keep_visited` 提供）
- **证明步骤**:
  1. `preloop x` → 建立 `x∈visited ∧ dfn_valid ∧ dfn_inv ∧ fa_visited`
  2. `forset` 迭代邻居 → 通过 `forset_process_edge_keep_dfn_valid_pre`
  3. `If (low x = dfn x) (pop_scc x)` → `pop_scc_keep_dfn_valid` / 平凡跳过

### 4.6 外层循环定理

| 定理 | 语句 | 行号 |
|------|------|------|
| `tarjan_scc_all_dfn_valid` | `Hoare (dfn_inv ∧ fa_visited ∧ dfn_valid root) (tarjan_scc_all g) (dfn_valid root)` | 1304–1351 |

**证明策略**: `Hoare_forset` 归纳，对每个顶点 `a`：
- 若 `a ∉ visited s0` → 执行 `tarjan_scc a`，由 `tarjan_scc_keep_dfn_inv` + `tarjan_scc_keep_fa_visited` + `tarjan_scc_keep_dfn_valid` 三者组合保持不变量
- 若 `a ∈ visited s0` → 平凡跳过

---

## 5. `dfn_unique` — dfn 单射性

| 引理 | 语句 | 行号 |
|------|------|------|
| `dfn_unique` | `dfn_inv s → dfn_injective s → ∀ x y, dfn s x = dfn s y → x = y ∨ (~x∈visited s ∧ ~y∈visited s)` | 1353–1380 |

**语义**: 在 `dfn_inv` 和 `dfn_injective` 前提下，若两个顶点的 dfn 相等，则要么它们是同一顶点，要么两者都未访问（dfn 均为 0）。

**证明策略**: 使用排中律 (`classic`) 分情况：
- 若 `x = y` → 左分支
- 若 `x ≠ y` → 右分支：证明两者都不能在 visited 中（若一个在 visited 中，由 `dfn_injective` 得 dfn 不等；若一个在 visited 中另一个不在，由 `dfn_inv` 分量 2 得 dfn 分别为非零和零，矛盾）

---

## 6. 定理总结

| 类别 | 数量 | 核心定理 |
|------|------|----------|
| 定义 | 7 | `dfn_inv`, `dfn_injective`, `dfn_valid`, `fa_visited`, `dfn_pre`, `dfn_post` |
| dfn_inv 引理 | 10 | 初始成立 + 各原语/复合/递归/外层循环保持性 |
| fa_visited 引理 | 20 | 初始成立 + 各原语/复合保持性 + 2 个核心递归定理 |
| dfn_valid 引理 | 12 | preloop/set_fa/update_low/process_edge/forset 保持性 + 2 个核心递归/外层循环定理 |
| dfn_unique 引理 | 1 | `dfn_unique` |
| **总计** | **50** | |

---

## 7. 已完成与待完成

### Phase A（已完成 ✅）

- `dfn_inv` — 基本 dfn 不变量及其全套保持性证明
- `dfn_valid` — 树边 dfn 单调性、`dfn_pre`/`dfn_post` 归纳包装、`tarjan_scc_keep_dfn_valid`、`tarjan_scc_all_dfn_valid`
- `dfn_unique` — dfn 单射性
- `fa_visited` — 树父节点访问性（工程中额外发现的核心不变量）及其全套保持性证明

### Phase B（待完成）

以下内容属于 `is_dfn` Record 的剩余字段，计划在独立文件中处理：

- `subtree_segment` — 子树 dfn 区间性质
- `no_cross_edge` — 无交叉边性质
- 完整的 `is_dfn` Record 实例

### 与设计文档的差异

1. **`dfn_inv` 增加了第三合取项 `0 < timer s`** — 简化了后续 `dfn_unique` 和 `preloop` 保持性中的推理
2. **`fa_visited` 谓词** — 设计文档未规划，但在 Hoare 不动点归纳中证明是必需的，占文件最大的代码量（~500 行）
3. **`dfn_injective`** — 设计文档将 `dfn_unique` 的前提直接内嵌在 `dfn_inv` 中，实现将其分离为独立谓词
4. **实际代码量** — ~1382 行（设计估算 210–350 行），超出部分主要为 `fa_visited` 基础设施和多个 "rich/combined" 引理变体

---

*文档版本：1.0*
*最后更新：2026-06-17*
