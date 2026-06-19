# Tarjan_scc_is_dfn — 开发设计与可行性分析

**Author**: Vitalrubbish
**Date**: 2026-06-16

## 概述

本文档分析 `Tarjan_scc_is_dfn.v` 的开发可行性与详细设计。
该文件是 Tarjan SCC 有向图验证体系（Layer 2→1）的第三个证明文件，
位于 `Tarjan_scc_basics.v`（Hoare 基础设施层）之上，
负责证明 DFS 编号（dfn）的有效性并为后续 `is_low`、`stack`、`correctness` 文件提供 dfn 相关的核心定理。

---

## 1. 当前状态

### 1.1 已完成的前置文件

| 文件 | 状态 | 内容 |
|------|------|------|
| `Tarjan_scc.v` | ✅ 已编译 | SCCSt 状态定义、基本操作、`tarjan_scc`/`tarjan_scc_all` 程序定义、`state_to_dfs_tree` 构造、6 个结构引理 + 3 个 `set_fa` 保持引理、`mono_cont` 证明 |
| `SCC_basic.v` | ✅ 已编译 | 有向图 SCC 数学规格（`dg_step`、`is_SCC`、`scc_partition` 等） |
| `Tarjan_scc_basics.v` | ✅ 已编译 | 83 个 Hoare 引理/定理：基本操作保持性、preloop、process_edge、forset 不动点、tarjan_scc 核心保持定理、tarjan_scc_all 外层循环定理 |

### 1.2 后续依赖本文件的模块

```
Tarjan_scc_is_dfn.v  ← 本文件
    ↓
Tarjan_scc_is_low.v  （low 正确性，需要 dfn_valid + dfn_unique）
    ↓
Tarjan_scc_stack.v   （栈不变量 + SCC 弹出定理，需要 dfn 树性质）
    ↓
SCC_correctness.v    （最终功能正确性，需要所有上述模块）
```

### 1.3 `Tarjan_directed/` 中尚未定义的谓词

通过搜索确认，`dfn_inv`、`dfn_valid`、`dfn_unique`、`subtree_segment`、`no_cross_edge` 在当前 `Tarjan_directed/` 中均未定义，需要在 `Tarjan_scc_is_dfn.v` 中全新定义并证明。

---

## 2. 参考文件分析

### 2.1 桥判定版本 `Tarjan_is_dfn.v`

**路径**: `SeparationLogic/algorithms/Tarjan/Tarjan_is_dfn.v`
**规模**: 254 行
**核心成果**: 证明 `tarjan g root` 执行后 `dfn_valid (state_to_rootedtree g root s) s.(dfn)`

**证明策略**:
1. 定义 `dfn_valid_except u dfstree dfn` — dfn 对除 u 外的所有树边有效
2. 定义 `dfn_valid_conj_Pre u s` = `dfn_valid_except u ... ∧ isleaf ... u ∧ (∀v, dfn v < timer)`
3. 定义 `dfn_valid_conj_Post s` = `dfn_valid ... ∧ (∀v, dfn v < timer)`
4. 通过 Hoare 三元组逐操作传递：
   - `preloop u`: 将 Pre(u) 转为 Post（设置 dfn[u] 后树仍未变）
   - `set_tree u v e`: 在叶子 v 处新增树边，从 Post 转回 Pre(v)
   - `post_rec`: 后处理保持 Post
   - `tarjan_f` (Lfix 体): 用 `hoare_fix_nolv_auto` 做不动点归纳
5. 最终 `Tarjan_dfn_valid`: `{s = initSt root} tarjan g root {dfn_valid tree dfn}`

**关键依赖**:
- `Tarjan_set_tree.v` 提供 `add_tree_edge_preserves_dfn_valid_except` 和 `add_tree_edge_creates_leaf`
- `Tarjan_basics.v` 提供 `tree_sub_conj_P`（树子图合取谓词）的保持性

### 2.2 `is_dfn` Record（来自 `dfstree_dfn.v`）

```coq
Record is_dfn {G1 G2 V E: Type} {pg1: Graph G1 V E} {pg2: Graph G2 V E}
              (g: G1) (dfstree: G2) (dfn: V -> nat) := {
    dfn_valid      : forall x y, step dfstree x y -> dfn x < dfn y;
    subtree_segment: forall u v1 v2 x y,
        step dfstree u v1 -> step dfstree u v2 ->
        reachable dfstree v1 x -> reachable dfstree v2 y ->
        dfn v1 < dfn v2 -> dfn x < dfn y;
    no_cross_edge  : forall u v1 v2 x y,
        step dfstree u v1 -> step dfstree u v2 ->
        reachable dfstree v1 x -> reachable dfstree v2 y ->
        dfn v1 < dfn v2 -> ~ step g x y;
    dfn_unique     : forall x y, dfn x = dfn y -> x = y;
}.
```

**Record 本身**不依赖 `RootedTree` Context（定义在 Section 之外），可以在没有 `RootedTree` 实例的情况下构造。
但 `dfstree_dfn.v` 的 `Section DFSTREE` 中的引理（`dfn_valid_offspring` 等）需要 `RootedTree` + `subgraph` 作为 Context。

### 2.3 桥判定 `Tarjan_no_cross_edge.v`

**路径**: `SeparationLogic/algorithms/Tarjan/Tarjan_no_cross_edge.v`
**规模**: 604 行
**核心内容**: 证明 Tarjan 算法的 DFS 树无交叉边（no cross edge）。
使用 `state_to_rootedtree` 并通过 `offspring` 谓词刻画树中可达关系。
**结论**: SCC 版本的 `no_cross_edge` 可能需要类似规模的工作量。

---

## 3. 核心定义设计

### 3.1 `dfn_inv` — 基本 dfn 不变量

```coq
Definition dfn_inv (s: SCCSt): Prop :=
  (forall v, v ∈ visited s -> dfn s v < timer s) /\
  (forall v, dfn s v = 0 <-> ~ v ∈ visited s).
```

**语义**:
- **分量 1**: 已访问顶点的 dfn 严格小于当前 timer——dfn 保存的是"访问时刻"的时间戳
- **分量 2**: 未访问顶点的 dfn 为 0，且 dfn=0 当且仅当未访问——dfn=0 是"未访问"的标记

**为什么需要 `dfn_inv`**:
- `dfn_inv` 是证明 `dfn_valid` 的核心前提：树边 `u → v` 要求 `dfn u < dfn v`，而这源于 u 先于 v 被访问
- `dfn_inv` 提供了 `dfn` 和 `timer` 之间的严格关系
- `dfn_inv` 可以直接从 `Tarjan_scc_basics.v` 的已有引理组合得到

### 3.2 `dfn_valid` — 树边 dfn 单调性

```coq
Definition dfn_valid (s: SCCSt) (root: V): Prop :=
  forall x y, dg_step (state_to_dfs_tree s root) x y -> dfn s x < dfn s y.
```

**语义**: DFS 树中每条有向边 `x → y` 满足 `dfn[x] < dfn[y]`——父节点的 dfn 严格小于子节点的 dfn。这是深度优先遍历的基本性质。

### 3.3 `dfn_unique` — dfn 单射性

```coq
Lemma dfn_unique (s: SCCSt):
  dfn_inv s ->
  forall x y, dfn s x = dfn s y -> x = y \/ (~ x ∈ visited s /\ ~ y ∈ visited s).
```

**语义**: 在 `dfn_inv` 前提下，若两个顶点的 dfn 相等且非零，则它们必须是同一顶点。这是 `is_dfn` Record 四个条件中最容易证明的一个。

### 3.4 归纳友好的包装谓词

参照桥判定版本，定义过渡谓词以支持 Hoare 不动点归纳：

```coq
(* 前置条件：u 即将被 preloop 处理 *)
Definition dfn_pre (u: V) (s: SCCSt) (root: V): Prop :=
  ~ u ∈ visited s /\
  dfn_valid s root /\
  dfn_inv s.

(* 后置条件：u 已被处理完成（tarjan_scc u 返回后） *)
Definition dfn_post (s: SCCSt) (root: V): Prop :=
  dfn_valid s root /\
  dfn_inv s.
```

**与桥判定版本的差异**:
- 桥判定使用 `dfn_valid_except` + `isleaf` 因为树通过 `set_tree'` 逐边构造
- SCC 版本的树通过递归 `tarjan_scc` 整体构造子树的 `dfn_valid`，然后合并到父节点
- 因此 SCC 版本的归纳更"粗粒度"——每次递归调用完成整个子树

---

## 4. 可行性分析

### 4.1 核心证明路径

```
dfn_inv 初始成立 (initSt)
    ↓ [preloop 保持]
dfn_inv 在 preloop 后仍成立，且新访问的 u 满足 dfn[u] < timer
    ↓ [process_edge + tarjan_scc 保持]
子节点 v 被递归访问后，子树满足 dfn_valid
父节点 u 的 dfn_valid 由 dfn_inv + 子树 dfn_valid 组合得到
    ↓ [tarjan_scc_all 保持]
全图所有顶点被访问后，全局 dfn_valid 成立
```

### 4.2 逐项可行性评估

| 子目标 | 复杂度 | 可行性 | 关键前提 |
|--------|--------|--------|----------|
| `dfn_inv` 初始成立 | 低 | ✅ 直接 | initSt 中 visited = ∅, dfn = λ_.0, timer = 0 |
| `preloop` 保持 `dfn_inv` | 低 | ✅ 可行 | `preloop_dfn_set` + `preloop_keep_visited`（已有） |
| `set_fa` 保持 `dfn_inv` | 低 | ✅ 可行 | `set_fa_keep_visited`（已有），不改变 dfn/timer |
| `update_low` 保持 `dfn_inv` | 低 | ✅ 可行 | `update_low_keep_visited` + `update_low_keep_dfn`（已有） |
| `pop_scc` 保持 `dfn_inv` | 低 | ✅ 可行 | `pop_scc_keep_visited` + `pop_scc_keep_dfn`（已有） |
| `process_edge` 保持 `dfn_inv` | 中 | ✅ 可行 | 分情况组合上述引理 |
| `dfn_inv → dfn_valid` 静态推理 | 中 | ✅ 可行 | `state_to_dfs_tree_step_char`（已有）展开树边定义 |
| `tarjan_scc` 保持 `dfn_valid`（Hoare_fix） | **高** | ⚠️ 需仔细设计 | 不动点归纳 + `dfn_pre`/`dfn_post` 包装 |
| `subtree_segment` | **高** | ⚠️ 较大工作量 | 需子树 dfn 区间性质，依赖 DFS 访问顺序 |
| `no_cross_edge` | **高** | ⚠️ 较大工作量 | 需证明非树边都是回边（back edge），无前向边/交叉边 |
| `dfn_unique` | 低 | ✅ 可行 | 从 `dfn_inv` 直接得到 |

### 4.3 主要风险点

#### 风险 1: `state_to_dfs_tree` 的树结构与算法执行轨迹的关联

**问题**: `state_to_dfs_tree s root` 从状态 s 的快照构造 DFS 树，但 `dfn_valid` 的证明需要知道"树边是在算法执行中的哪个时刻创建的"——因为 `dfn u < dfn v` 依赖于"u 在 v 之前被访问"这一时间顺序。

**分析**: 在桥判定版本中，树边通过 `set_tree'` 显式创建，每个 `set_tree'` 调用都携带边证据 `e: E`。SCC 版本中，树边由 `set_fa` + `dg_step g` 隐式定义，但 `set_fa v u` 的调用时刻保证了 u 已被访问而 v 未访问，从而 `dfn u < dfn v`。这个推理可以通过 `dfn_inv` 在 `set_fa` 调用点完成。

**缓解策略**: 在 `process_edge` 的 Hoare 证明中，树边分支 (`~ v ∈ visited`) 处：
1. 前提给出 `u ∈ visited`（来自 preloop 的后件）
2. 前提给出 `~ v ∈ visited`（分支条件）
3. 由 `dfn_inv`: `dfn s u < timer s` 且 `dfn s v = 0`
4. `set_fa v u` 后进入 `tarjan_scc v`
5. `tarjan_scc v` 的归纳假设保证返回后 `v` 的子树满足 `dfn_valid`
6. 返回后 `dfn v` 已被设置为 `≥ timer_at_call`，故 `dfn u < dfn v`
7. 新树边 `u → v` 满足 `dfn_valid`

#### 风险 2: `Hoare_fix` 不动点归纳假设的强度

**问题**: `tarjan_scc` 展开为 `Lfix tarjan_scc_f`，`Hoare_fix` 规则要求归纳假设对"任意已被覆盖的调用"成立。对于 `dfn_valid`，归纳假设需要说：如果某个递归调用 `W v` 在"合适的前提"下执行，则返回后 `dfn_valid` 对新增的子树成立。

**分析**: `Tarjan_scc_basics.v` 已经成功使用 `hoare_fix_nolv_auto` 处理了 `tarjan_scc_keep_visited`、`tarjan_scc_keep_dfn` 等定理。`dfn_valid` 的归纳结构与它们类似——归纳假设要求 `W`（递归体）满足某种 Hoare 规约。

**缓解策略**: 参照 `tarjan_scc_keep_dfn` 的证明模式（`Tarjan_scc_basics.v` 行 1023–1045），使用 `tarjan_scc_unfold` 展开递归，用 `hoare_fix_nolv_auto` 处理 forset 不动点。

#### 风险 3: `subtree_segment` 和 `no_cross_edge` 的工作量被低估

**问题**: 桥判定版本中 `no_cross_edge` 独占 604 行的独立文件。设计文档估算 `Tarjan_scc_is_dfn.v` 为 200-350 行，但若包含完整的 `is_dfn` Record（4 个条件），仅 `subtree_segment` + `no_cross_edge` 就可能需要 400-600 行。

**缓解策略**: 分阶段交付：
- **Phase A** (本文件): `dfn_inv` + `dfn_valid` + `dfn_unique`（~250-400 行）
- **Phase B** (后续或同文件): `subtree_segment` + `no_cross_edge`（~400-600 行）

这保持了与桥判定版本相同的文件拆分粒度（`Tarjan_is_dfn.v` + `Tarjan_no_cross_edge.v`）。

### 4.4 与桥判定版本的关键差异总结

| 维度 | 桥判定 (`Tarjan_is_dfn.v`) | SCC (`Tarjan_scc_is_dfn.v`) |
|------|---------------------------|----------------------------|
| 树构造 | `state_to_rootedtree` — 显式树边列表 | `state_to_dfs_tree` — 从 fa/visited 隐式推导 |
| 边添加 | `set_tree' u v e` — 一次添加一条带证据的树边 | `set_fa v u` + 递归 + 返回 — 子树整体出现 |
| 叶子检测 | `isleaf` 谓词直接可用 | 无直接对应物，需用 `fa v = v`（默认值）判断 |
| 图类型 | 无向图，`step` 对称 | 有向图，`dg_step` 有向 |
| 树根 | `root` 是预设参数，保证在 visited 中 | `root` 在 `tarjan_scc_all` 完成后保证在 visited 中 |
| 核心循环 | `tarjan_f` + `forset` 对边迭代 | `tarjan_scc_f` + `forset` 对邻居迭代（结构类似） |
| 状态类型 | `St`（含 tedge, fa 等） | `SCCSt`（含 dfn, low, stack, sccs 等） |

---

## 5. 详细实现计划

### 5.1 文件结构

```coq
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From GraphLib.directed Require Import dfstree_dfn.
From Algorithms.Tarjan_directed Require Import SCC_basic Tarjan_scc Tarjan_scc_basics.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section IS_DFN.
  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  (* ================================================================ *)
  (* 1. dfn_inv — Basic dfn Invariant                                 *)
  (* ================================================================ *)
  Definition dfn_inv (s: SCCSt): Prop := ...
  Lemma dfn_inv_init: dfn_inv initSt.
  Lemma preloop_keep_dfn_inv: ... Hoare ...
  Lemma process_edge_keep_dfn_inv: ... Hoare ...
  Lemma tarjan_scc_keep_dfn_inv: ... Hoare ...
  Lemma tarjan_scc_all_keep_dfn_inv: ... Hoare ...

  (* ================================================================ *)
  (* 2. dfn_valid — Tree Edge dfn Monotonicity                        *)
  (* ================================================================ *)
  Definition dfn_valid (s: SCCSt): Prop := ...
  (* Induction-friendly wrappers *)
  Definition dfn_pre (u: V) (s: SCCSt): Prop := ...
  Definition dfn_post (s: SCCSt): Prop := ...

  Lemma preloop_establishes_dfn_pre: ... Hoare ...
  Lemma set_fa_preserves_dfn_pre: ... Hoare ...
  Lemma process_edge_keep_dfn_valid: ... Hoare ...
  Lemma forset_process_edge_keep_dfn_valid: ... Hoare ...
  Lemma tarjan_scc_keep_dfn_valid: ... Hoare ...
  Lemma tarjan_scc_all_dfn_valid: ... Hoare ...

  (* ================================================================ *)
  (* 3. dfn_unique — Injectivity of dfn                               *)
  (* ================================================================ *)
  Lemma dfn_unique: dfn_inv s -> forall x y, dfn s x = dfn s y -> ...

  (* ================================================================ *)
  (* 4. is_dfn Record Instance (Phase B — 可延后)                     *)
  (* ================================================================ *)
  (* Lemma dfn_valid_is_dfn: is_dfn g (state_to_dfs_tree s root) (dfn s). *)
  (*   - dfn_valid: from tarjan_scc_all_dfn_valid *)
  (*   - dfn_unique: from dfn_unique lemma *)
  (*   - subtree_segment: ... (Phase B) *)
  (*   - no_cross_edge: ... (Phase B) *)

End IS_DFN.
```

### 5.2 证明步骤分解

#### 步骤 1: `dfn_inv` 的建立与保持 (~60-100 行)

**1a. `dfn_inv` 初始成立**:
```coq
Lemma dfn_inv_init: dfn_inv initSt.
Proof. unfold dfn_inv, initSt; simpl; split; intros; try sets_unfold; lia. Qed.
```

**1b. `preloop` 保持 `dfn_inv`**:
- 前提: `dfn_inv s`
- `set_dfn u timer`: `dfn s' u = timer s`
- `incr_timer`: `timer s'' = S (timer s)`
- `visit u`: `u ∈ visited s'''`
- 结论: `dfn s''' u = timer s < S (timer s) = timer s'''` → `dfn_inv s'''`

**1c. `set_fa` / `update_low` / `pop_scc` 保持 `dfn_inv`**:
- 这些操作不改变 `dfn`、`timer`、`visited` 字段（或仅在已有不变量下做安全修改）
- 使用 `Tarjan_scc_basics.v` 中的保持引理直接组合

**1d. `process_edge` 保持 `dfn_inv`**:
- 三个分支分别处理: 树边、回边（栈中）、交叉边（已出栈）
- 每个分支只使用上述操作，通过 `Hoare_bind` 组合

**1e. `tarjan_scc` 保持 `dfn_inv`** (Hoare_fix 归纳):
- 使用 `tarjan_scc_unfold` 展开
- forset 部分用 `hoare_fix_nolv_auto`
- 归纳假设: `W` 保持 `dfn_inv`

#### 步骤 2: `dfn_valid` 的保持 (~120-200 行)

**2a. 静态引理 — 从 `dfn_inv` + `set_fa` 推导树边 dfn 序**:
```coq
Lemma set_fa_creates_dfn_valid_edge (s: SCCSt) (u v: V):
  dfn_inv s ->
  u ∈ visited s -> ~ v ∈ visited s ->
  set_fa v u 执行后，若后续 v 被访问且 fa v = u ≠ v，
  则新树边 u → v 满足 dfn u < dfn v.
```

**2b. `preloop` 后 `dfn_pre` 成立**:
- `preloop u` 将 u 加入 visited，设置 `dfn u = timer`
- 由于 u 在 preloop 前不在 visited 中，`dfn_valid` 不受影响（无树边涉及 u）

**2c. `process_edge` 树边分支**:
- 前提: `u ∈ visited`, `~ v ∈ visited`, `dfn_valid s root`
- `set_fa v u` → `tarjan_scc v`（归纳假设返回后 `dfn_valid` 对 v 的子树成立）
- `update_low u lv` → 保持 `dfn_valid`（不修改 dfn/fa/visited）
- 新树边 `u → v`: 由步骤 2a 的静态引理保证 `dfn u < dfn v`

**2d. `tarjan_scc` 的 Hoare_fix 归纳**:
- 归纳谓词: `dfn_pre u s` → `dfn_post s`
- 使用 `tarjan_scc_unfold` + `hoare_fix_nolv_auto`
- forset 体中对每个邻居应用 `process_edge` 的保持性

#### 步骤 3: `dfn_unique` (~30-50 行)

从 `dfn_inv` 直接推导：
- 若 `x ≠ y` 且 `x ∈ visited`、`y ∈ visited`，则 `dfn x ≠ dfn y`（因为 timer 每次递增且 dfn 不重复）
- 若 `x ∉ visited`，则 `dfn x = 0`，若 `dfn y = 0` 则 `y ∉ visited`

#### 步骤 4 (Phase B): `subtree_segment` + `no_cross_edge` (~400-600 行)

参照 `Tarjan_no_cross_edge.v` 的证明策略，适配 SCC 的 `state_to_dfs_tree`。

### 5.3 与已有基础设施的衔接

| 需要的引理 | 来源 | 状态 |
|-----------|------|------|
| `state_to_dfs_tree_step_char` | `Tarjan_scc.v` | ✅ 已有 |
| `state_to_dfs_tree_step_fa` | `Tarjan_scc.v` | ✅ 已有 |
| `state_to_dfs_tree_vvalid` | `Tarjan_scc.v` | ✅ 已有 |
| `set_fa_preserves_tree_edges` | `Tarjan_scc.v` | ✅ 已有 |
| `set_fa_adds_tree_edge` | `Tarjan_scc.v` | ✅ 已有 |
| `preloop_keep_visited` | `Tarjan_scc_basics.v` | ✅ 已有 |
| `preloop_dfn_set` | `Tarjan_scc_basics.v` | ✅ 已有 |
| `process_edge_keep_visited` | `Tarjan_scc_basics.v` | ✅ 已有 |
| `process_edge_keep_dfn` | `Tarjan_scc_basics.v` | ✅ 已有 |
| `tarjan_scc_keep_visited` | `Tarjan_scc_basics.v` | ✅ 已有 |
| `tarjan_scc_keep_dfn` | `Tarjan_scc_basics.v` | ✅ 已有 |
| `tarjan_scc_keep_visited_forall` | `Tarjan_scc_basics.v` | ✅ 已有 |
| `tarjan_scc_self_visited` | `Tarjan_scc_basics.v` | ✅ 已有 |
| `tarjan_scc_unfold` | `Tarjan_scc.v` | ✅ 已有 |
| `timer_mono` 定义 | `Tarjan_scc_basics.v` | ✅ 已有 |
| `set_fa_new_fa` | `Tarjan_scc_basics.v` | ✅ 已有 |
| `set_fa_keep_dfn` | `Tarjan_scc_basics.v` | ✅ 已有 |

**结论**: 所有需要的低层引理均已就位，本文件主要负责将它们组装为更高层的不变式证明。

---

## 6. 工作量估算

| 阶段 | 内容 | 预估行数 | 预估时间 | 风险 |
|------|------|---------|---------|------|
| Phase A.1 | `dfn_inv` 定义 + 保持性证明 | 60–100 | 2–4 小时 | 低 |
| Phase A.2 | `dfn_pre`/`dfn_post` + `dfn_valid` Hoare 证明 | 120–200 | 4–8 小时 | 中 |
| Phase A.3 | `dfn_unique` | 30–50 | 1–2 小时 | 低 |
| Phase A.4 | 整体编译验证 + 调试 | — | 1–2 小时 | 低 |
| **Phase A 合计** | | **210–350** | **8–16 小时** | |
| Phase B.1 | `subtree_segment` | 150–250 | 4–8 小时 | 高 |
| Phase B.2 | `no_cross_edge` | 200–350 | 6–12 小时 | 高 |
| **Phase B 合计** | | **350–600** | **10–20 小时** | |
| **总计** | | **560–950** | **18–36 小时** | |

### 6.1 与设计文档估算的对比

原设计文档（`20260614-tarjan-scc-monadic-correctness-design.md`）估算本文件为 200–350 行，1–2 天。
这个估算仅覆盖 Phase A（`dfn_valid` 核心）的范围，是合理的。
Phase B（`subtree_segment` + `no_cross_edge`）实际属于 `is_dfn` Record 的额外字段，
可考虑拆分为独立文件（参照桥判定的 `Tarjan_no_cross_edge.v`），
或在 Phase A 验证通过后再决定是否合并。

---

## 7. 推荐实施策略

### 策略 A: 最小可行交付（推荐）

只交付 Phase A（`dfn_inv` + `dfn_valid` + `dfn_unique`），作为 `is_dfn` Record 的**部分**实例。
`subtree_segment` 和 `no_cross_edge` 留到独立文件处理。

**优点**:
- 与桥判定版本保持相同的文件粒度
- 降低单文件复杂度
- Phase A 交付后 `Tarjan_scc_is_low.v` 即可开始开发（`dfn_valid` 是其主要依赖）

**缺点**:
- `is_dfn` Record 的完整实例需要等到 Phase B 完成

### 策略 B: 完整交付

在一个文件中交付 Phase A + Phase B，构造完整的 `is_dfn` Record 实例。

**优点**:
- 一步到位完成 `is_dfn` 全部四个条件
- 后续文件可以直接使用 `dfstree_dfn.v` 的 Section DFSTREE 引理

**缺点**:
- 工作量大，风险高
- 文件过长（600–1000 行），难以维护
- `no_cross_edge` 可能需要额外的辅助不变量

**建议**: 采用策略 A，先完成 Phase A，在证明过程中积累对 DFS 树结构的理解，
再决定 Phase B 是在同一文件中追加还是拆分为独立文件。

---

## 8. 关键证明草图

### 8.1 `dfn_inv` 的 `preloop` 保持

```coq
Lemma preloop_keep_dfn_inv (u: V):
  Hoare (fun s => dfn_inv s)
        (preloop u)
        (fun _ s => dfn_inv s).
Proof.
  unfold dfn_inv.
  (* 使用 Hoare_conj 分离两个分量 *)
  (* 分量 1: v ∈ visited → dfn v < timer *)
  (*   - 对 v = u: preloop_dfn_set 给出 dfn u = old_timer < S old_timer = new_timer *)
  (*   - 对 v ≠ u: preloop_keep_dfn 保持 dfn v 不变，incr_timer 只增大 timer *)
  (* 分量 2: dfn v = 0 ↔ ~ v ∈ visited *)
  (*   - 对 v = u: preloop 后 u ∈ visited, dfn u = old_timer ≠ 0 *)
  (*   - 对 v ≠ u: preloop_keep_dfn + preloop_keep_visited 保持双向 *)
Qed.
```

### 8.2 `dfn_valid` 的核心归纳

```coq
Lemma tarjan_scc_keep_dfn_valid (u: V):
  Hoare (fun s => dfn_pre u s)
        (tarjan_scc u)
        (fun _ s => dfn_post s).
Proof.
  (* 使用 tarjan_scc_unfold 展开 *)
  rewrite tarjan_scc_unfold.
  unfold tarjan_scc_f.
  (* preloop u: 将 u 加入 visited，设置 dfn[u]，此时无新树边 *)
  eapply Hoare_bind.
  { apply preloop_establishes_dfn_pre. }
  intros _.
  (* forset 迭代邻居 *)
  eapply Hoare_bind.
  { (* 使用 hoare_fix_nolv_auto 处理 forset *)
    hoare_fix_nolv_auto (V -> Prop).
    (* 对每个邻居 v: *)
    (*   树边分支: set_fa v u → IH(v) → update_low *)
    (*   回边分支: update_low (保持 dfn_valid) *)
    (*   跳过分支: 平凡 *)
  }
  intros _.
  (* pop_scc: 保持 dfn_valid *)
  apply pop_scc_keep_dfn_valid.
Qed.
```

### 8.3 `set_fa` + 递归后新树边的 dfn 序

```coq
Lemma new_tree_edge_dfn_order (s s': SCCSt) (u v: V):
  dfn_inv s ->
  u ∈ visited s ->
  ~ v ∈ visited s ->
  (* s' 是 set_fa v u 后经 tarjan_scc v 返回的状态 *)
  v ∈ visited s' ->
  fa s' v = u ->
  dfn s u < dfn s' v.
Proof.
  intros Hinv Hu Hv Hvis' Hfa.
  destruct Hinv as [Hdfn_lt Hdfn_zero].
  (* u 在 s 中已访问 → dfn s u < timer s *)
  apply Hdfn_lt in Hu.
  (* v 在 s 中未访问 → dfn s v = 0 *)
  apply Hdfn_zero in Hv. destruct Hv as [_ Hzero].
  (* tarjan_scc v 不修改 dfn u（u ≠ v，且 u 已访问）*)
  (* 需要额外的保持引理，或使用 tarjan_scc_keep_dfn *)
  (* v 在 tarjan_scc v 的 preloop 中获得 dfn v = timer_at_call *)
  (* timer_at_call ≥ timer s（时间单调）*)
  (* 故 dfn u < timer s ≤ timer_at_call = dfn v *)
  ...
Qed.
```

---

## 9. 依赖关系图

```
Tarjan_scc.v (程序定义 + 结构引理)
    ↓
Tarjan_scc_basics.v (Hoare 基础层)
    ↓
Tarjan_scc_is_dfn.v  ← 本文件
    ├── dfn_inv (dfn 基本不变量)
    ├── dfn_valid (树边 dfn 单调性)
    ├── dfn_unique (dfn 单射性)
    ├── (Phase B) subtree_segment
    └── (Phase B) no_cross_edge
    ↓
Tarjan_scc_is_low.v
    ↓
Tarjan_scc_stack.v
    ↓
SCC_correctness.v
```

---

## 10. 开发环境与编译验证

### 10.1 Opam 环境

```bash
eval $(opam env)          # 切换到 coq-8.20 switch
coqc --version            # 应显示 Rocq 8.20.1
```

### 10.2 编译命令

```bash
cd SeparationLogic/algorithms/Tarjan_directed/
coqc -Q ../../ GraphLib -Q . Algorithms.Tarjan_directed Tarjan_scc_is_dfn.v
```

或在项目根目录使用 `_RocqProject` 配置的构建系统。

### 10.3 交互式证明

使用 `rocq-mcp` 的 `rocq_start` + `rocq_check` + `rocq_step_multi` 进行交互式证明开发。

---

## 11. 结论

**Tarjan_scc_is_dfn.v 的 Phase A（`dfn_inv` + `dfn_valid` + `dfn_unique`）是可行的**，
预计 210–350 行，8–16 小时工作量。

**关键成功因素**:
1. `Tarjan_scc_basics.v` 的 83 个 Hoare 引理提供了充足的低层支撑
2. `Tarjan_scc.v` 的 9 个结构引理提供了树结构推理的基础设施
3. 桥判定 `Tarjan_is_dfn.v`（254 行）提供了成熟的证明策略参考

**主要挑战**:
1. `Hoare_fix` 不动点归纳的谓词设计需要仔细调整
2. `dfn_valid` 的证明需要精确追踪 `set_fa` → 递归 → 返回 的树边构造时序
3. Phase B（`subtree_segment` + `no_cross_edge`）工作量较大，建议拆分为独立文件

**建议**: 采用策略 A，先完成 Phase A 核心交付，积累经验后再规划 Phase B。

---

*设计文档版本：1.0*
*最后更新：2026-06-16*
