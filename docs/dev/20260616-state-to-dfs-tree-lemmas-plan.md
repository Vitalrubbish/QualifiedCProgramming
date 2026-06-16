# state_to_dfs_tree 引理补充计划

**Author**: Vitalrubbish
**Date**: 2026-06-16

## 概述

本文档规划在 `Tarjan_scc.v` 中补充 `state_to_dfs_tree` 的结构性引理。
这些引理是后续四个证明文件（`Tarjan_scc_is_dfn.v`、`Tarjan_scc_is_low.v`、
`Tarjan_scc_stack.v`、`SCC_correctness.v`）的共同前置依赖。

---

## 1. 动机：为什么需要这些引理

`state_to_dfs_tree` 被全部后续证明文件引用：

| 后续文件 | 如何使用 |
|---------|---------|
| `Tarjan_scc_is_dfn.v` | `dfn_valid (state_to_dfs_tree s root) (dfn s)` |
| `Tarjan_scc_is_low.v` | `subtree dfs_tree v` = `dg_reachable dfs_tree v`、`children dfs_tree v` = `dg_step dfs_tree v` |
| `Tarjan_scc_stack.v` | `stack_tree_reachable` 用 `offspring dfs_tree u v` |
| `SCC_correctness.v` | `tarjan_scc_invariant` 中 `let dfs_tree := state_to_dfs_tree s in` |

因此，树的结构性质（顶点集、边集刻画、`set_fa` 对树的影响）应作为公共基础设施
放在 `Tarjan_scc.v` 中，避免每个后续文件重复证明。

---

## 2. 分层原则

| 放在 `Tarjan_scc.v` | 不放在 `Tarjan_scc.v` |
|---------------------|----------------------|
| 结构性的、仅依赖 `state_to_dfs_tree` 定义的引理 | 依赖算法不变量（`dfn_inv`、`is_low` 等）的引理 |
| `set_fa` 对树结构的纯函数影响 | `dfn_valid` 实例（需 `timer`/`visited` 关系） |
| 树的顶点集、边集基本刻画 | `RootedTree` Type Class 实例（证明量大，~200 行） |
| 无自环等简单图性质 | `subtree_segment` / `no_cross_edge` / `dfn_unique` |

---

## 3. 第一步：`state_to_dfs_tree` 的 `root` 参数

### 3.1 当前状态

```coq
Definition state_to_dfs_tree (s: SCCSt) (root: V): OriginalGraphType V E :=
  {|
    original_vvalid   := fun v => v ∈ visited s;
    original_step     := fun e =>
      exists v, v ∈ visited s /\ fa s v <> v /\
                original_step_fst g e = fa s v /\
                original_step_snd g e = v;
    original_step_fst := original_step_fst g;
    original_step_snd := original_step_snd g;
    original_listV    := original_listV g;
  |}.
```

`root` 参数在函数体内未使用，但需要保留——后续 `RootedTree` Type Class 实例
（在 `Tarjan_scc_is_dfn.v` 或独立文件中证明）将以 `root` 为树根。

### 3.2 改动

添加注释说明 `root` 参数用途，无需修改函数体。

---

## 4. 第二步：添加结构性质引理

以下 6 个引理描述了 `state_to_dfs_tree` 的基本图性质。

### 引理 1: `state_to_dfs_tree_vvalid`

```coq
Lemma state_to_dfs_tree_vvalid (s: SCCSt) (root v: V):
  original_vvalid (state_to_dfs_tree s root) v <-> v ∈ visited s.
```

**用途**：将树的顶点有效性与算法状态的 `visited` 集关联。
后续所有涉及 `vvalid dfs_tree v` 的前提都可以展开为 `v ∈ visited s`。

**证明**：直接展开 `state_to_dfs_tree` 和 `original_vvalid`，`reflexivity`。

---

### 引理 2: `state_to_dfs_tree_step_char`

```coq
Lemma state_to_dfs_tree_step_char (s: SCCSt) (root x y: V):
  dg_step (state_to_dfs_tree s root) x y <->
  (fa s y = x /\ fa s y <> y /\ y ∈ visited s).
```

**用途**：刻画树中何时存在有向边 `x → y`。
`fa s y <> y` 排除了 `fa` 的默认自环值（`initSt` 中 `fa = fun v => v`）。

**证明**：
- `→` 方向：展开 `dg_step` 和 `original_step`，从 `exists e, ... /\ step_fst = x /\ step_snd = y` 推导 `fa s y = x`、`fa s y <> y`、`y ∈ visited s`。
- `←` 方向：从前提构造 `e` 满足 `original_step` 条件。

---

### 引理 3: `state_to_dfs_tree_step_fa`

```coq
Lemma state_to_dfs_tree_step_fa (s: SCCSt) (root v: V):
  v ∈ visited s -> fa s v <> v ->
  dg_step (state_to_dfs_tree s root) (fa s v) v.
```

**用途**：最常用的正向推理引理——若顶点已访问且 `fa` 被赋值，
则在 DFS 树中存在父节点到该顶点的有向边。

**证明**：由引理 2 的 `←` 方向直接得到。

---

### 引理 4: `state_to_dfs_tree_dg_reachable_refl`

```coq
Lemma state_to_dfs_tree_dg_reachable_refl (s: SCCSt) (root v: V):
  v ∈ visited s ->
  dg_reachable (state_to_dfs_tree s root) v v.
```

**用途**：树中每个已访问顶点自反可达。
`dg_reachable` 是 `clos_refl_trans dg_step` 的包装，
自反性可直接由 `rt_refl` 得到。

**证明**：`apply rt_refl`。

---

### 引理 5: `state_to_dfs_tree_root_visited`

```coq
Lemma state_to_dfs_tree_root_visited (s: SCCSt) (root: V):
  root ∈ visited s ->
  original_vvalid (state_to_dfs_tree s root) root.
```

**用途**：便捷引理——若 root 已访问，则 root 在树中有效。

**证明**：由引理 1 直接得到。

---

### 引理 6: `state_to_dfs_tree_no_self_loop`

```coq
Lemma state_to_dfs_tree_no_self_loop (s: SCCSt) (root v: V):
  ~ dg_step (state_to_dfs_tree s root) v v.
```

**用途**：树中无自环——`fa s v <> v` 条件排除了 `dg_step` 的自环可能。
后续证明树的偏序性质时需要。

**证明**：使用引理 2，若 `dg_step ... v v` 则 `fa s v = v` 且 `fa s v <> v`，矛盾。

---

## 5. 第三步：添加 `set_fa` 保持树结构的引理

以下 3 个引理描述 `set_fa v p` 操作对 DFS 树结构的影响。

### 前置：纯函数版本的 `set_fa`

当前 `Tarjan_scc.v` 中 `set_fa` 是 monadic 操作（`update'`）。
需要额外定义一个纯状态更新函数用于纯逻辑推理：

```coq
Definition set_fa_state (s: SCCSt) (v p: V): SCCSt :=
  s <| fa ::= fun fa0 x => if equiv_decb x v then p else fa0 x |>.
```

这与 `set_fa` 的 `update'` 体一致，只是提取为纯函数。
（若已有等价定义可复用，则跳过此步。）

---

### 引理 7: `set_fa_preserves_tree_vvalid`

```coq
Lemma set_fa_preserves_tree_vvalid (s: SCCSt) (root v p: V):
  original_vvalid (state_to_dfs_tree s root) v ->
  original_vvalid (state_to_dfs_tree (set_fa_state s v p) root) v.
```

**用途**：`set_fa` 不减少树的顶点集（`visited` 不变 → 树顶点集不变）。

**证明**：展开 `set_fa_state`，`visited` 字段未变，由引理 1 得证。

---

### 引理 8: `set_fa_preserves_tree_edges`

```coq
Lemma set_fa_preserves_tree_edges (s: SCCSt) (root v w p: V):
  w <> v ->
  dg_step (state_to_dfs_tree s root) x w ->
  dg_step (state_to_dfs_tree (set_fa_state s v p) root) x w.
```

**用途**：对 `w ≠ v`，已有的树边 `x → w` 不受 `set_fa v p` 影响。

**证明**：使用引理 2，`dg_step` 的充要条件中 `fa s w = x` 且 `w ≠ v`，
`set_fa_state` 只修改 `fa v`，不影响 `fa w`。

---

### 引理 9: `set_fa_adds_tree_edge`

```coq
Lemma set_fa_adds_tree_edge (s: SCCSt) (root v p: V):
  ~ v ∈ visited s -> p <> v ->
  dg_step (state_to_dfs_tree (set_fa_state s v p) root) p v.
```

**用途**：`set_fa v p`（`p ≠ v`）在树中新增一条有向边 `p → v`。
前提 `~ v ∈ visited s` 保证这是一个**新**顶点（树边），
也是 `process_edge` 中树边分支的实际调用场景。

**证明**：`set_fa_state` 后 `fa s' v = p` 且 `p ≠ v`。
还需证明 `v ∈ visited s'`（即 `v ∈ visited s`）。
但前提是 `~ v ∈ visited s`——这意味着此时 `set_fa` 还没有把 `v` 加入 `visited`。
实际流程中 `set_fa v u` 发生在 `process_edge` 树边分支中，
此时 `v ∉ visited` 但 `set_fa` 不修改 `visited`。
因此需要额外的前提 `v ∈ visited (set_fa_state s v p)`，
这通常在 `process_edge` 后的 `W v`（递归 DFS）中由 `preloop` → `visit` 实现。

**设计决策**：此引理的前提可能需要调整为：

```coq
Lemma set_fa_adds_tree_edge (s: SCCSt) (root v p: V):
  p <> v -> v ∈ visited s ->
  dg_step (state_to_dfs_tree (set_fa_state s v p) root) p v.
```

或拆分为两个引理：
- `set_fa_creates_potential_edge`：`fa` 赋值后存在边 `p → v`（不要求 `v ∈ visited`）
- `set_fa_and_visit_creates_tree_edge`：`set_fa` + `visit` 后 `v` 在树中且有入边

**具体采用哪种形式，在实现时根据后续文件的证明需求确定。**

---

## 6. 完整文件结构

```
Tarjan_scc.v
├── 已有内容 (1–284 行，保持不变)
│   ├── Require Import
│   ├── Section TarjanSCC
│   ├── State Record / Settable Instance
│   ├── initSt
│   ├── stack_split_at / pop_scc_state
│   ├── 原语操作 (visit, set_dfn, set_low, set_fa, incr_timer, push_stack, update_low, pop_scc)
│   ├── unfold_op Ltac
│   ├── Main Program (preloop, process_edge, tarjan_scc_f, tarjan_scc)
│   ├── state_to_dfs_tree          ← 添加 root 参数注释
│   ├── mono_cont 证明
│   ├── tarjan_scc_unfold
│   └── tarjan_scc_all
│
└── 新增内容 (~120–180 行)
    ├── (* ================================================================ *)
    ├── (* DFS Tree — Structural Lemmas                                    *)
    ├── (* ================================================================ *)
    ├── set_fa_state 纯函数定义 (~8 行) [条件：若不存在等价定义]
    ├── 引理 1: state_to_dfs_tree_vvalid (~5 行)
    ├── 引理 2: state_to_dfs_tree_step_char (~15 行)
    ├── 引理 3: state_to_dfs_tree_step_fa (~6 行)
    ├── 引理 4: state_to_dfs_tree_dg_reachable_refl (~5 行)
    ├── 引理 5: state_to_dfs_tree_root_visited (~5 行)
    ├── 引理 6: state_to_dfs_tree_no_self_loop (~6 行)
    ├── (* ================================================================ *)
    ├── (* DFS Tree — set_fa Preservation Lemmas                           *)
    ├── (* ================================================================ *)
    ├── 引理 7: set_fa_preserves_tree_vvalid (~6 行)
    ├── 引理 8: set_fa_preserves_tree_edges (~12 行)
    └── 引理 9: set_fa_adds_tree_edge (~12 行)
```

**预估总行数**：284 → ~400–460 行。

---

## 7. 不在 `Tarjan_scc.v` 中证明的内容

| 内容 | 原因 | 归属文件 |
|------|------|---------|
| `dfn_valid (state_to_dfs_tree s root) (dfn s)` | 依赖 `dfn_inv`（需 `dfn v < timer`、`dfn v = 0 ↔ ~ v ∈ visited`） | `Tarjan_scc_is_dfn.v` |
| `RootedTree` Type Class 实例 | 需证 `root_no_edge`、`edge_unique`、`path_exist` 等 7 个条件，涉及 DFS 树的全局结构性质 | `Tarjan_scc_is_dfn.v` 或独立 `Tarjan_scc_dfs_tree.v` |
| `subtree_segment` / `no_cross_edge` | 依赖 `dfn_valid` 和算法完成状态 | `Tarjan_scc_is_dfn.v` |
| `dfn_unique` | 依赖 `dfn_valid` | `Tarjan_scc_is_dfn.v` |
| `offspring` 相关引理 | `offspring = dg_reachable`，直接引用 `GraphLib/directed/rootedtree.v` 的已有引理即可 | 使用时引用 |

---

## 8. 实现顺序

```
1. 添加 set_fa_state 纯函数（若需要）
2. 证明结构引理 1–6（自底向上，无相互依赖）
3. 证明 set_fa 保持引理 7–9（依赖 1–2）
4. coqc 编译验证
5. Commit
```

预估工作量：~2–3 小时。

---

*设计文档版本：1.0*
*最后更新：2026-06-16*
