# Shared SCC Lib 开发计划

**Author**: Vitalrubbish
**Date**: 2026-06-10

---

## 目录

1. [定位与动机](#1-定位与动机)
2. [总体架构](#2-总体架构)
3. [文件：scc_basic.v — 完整规格](#3-文件scc_basicv--完整规格)
   - [3.1 有向图的具体表示](#31-有向图的具体表示directedgraphtype)
   - [3.2 Type Class 实例化](#32-type-class-实例化)
   - [3.3 相互可达性与 SCC](#33-相互可达性与-scc)
   - [3.4 SCC 划分](#34-scc-划分)
   - [3.5 缩点图](#35-缩点图condensation)
   - [3.6 图反转](#36-图反转graph-reversal)
   - [3.7 完整引理清单](#37-完整引理清单)
4. [Makefile 修改](#4-makefile-修改)
5. [下游接口合同](#5-下游接口合同)
6. [任务拆解与时间估算](#6-任务拆解与时间估算)
7. [风险管理](#7-风险管理)
8. [质量检查清单](#8-质量检查清单)
9. [开工顺序建议](#9-开工顺序建议)

---

## 1. 定位与动机

### 1.1 为什么需要 Shared SCC Lib

当前仓库有两条并行的 SCC 算法验证路线：

| 路线 | 算法 | 负责 |
|------|------|------|
| Tarjan SCC | 单遍 DFS + stack + lowlink，在线弹出 SCC | Vitalrubbish |
| Kosaraju SCC | 两遍 DFS（原图 + 反图），按 finishing time 收集 SCC | 合作者 |

两条路线的**数学目标完全一致**：证明各自算法输出的顶点集合满足强连通分量（SCC）的数学定义。但在原始计划中，SCC 的基础定义分散在了 Tarjan Phase 1 的 `scc_basic.v` 中，合作者无法独立引用。

**Shared SCC Lib** 将 SCC 的数学基础抽取为算法无关的独立阶段，作为两条路线的共同前置依赖。

### 1.2 范围边界

Shared SCC Lib **只包含**：
- 有向图的数学表示和 Type Class 实例
- SCC 的纯数学定义（`is_SCC`、`mutually_reachable`、`scc_partition`）
- 缩点图（condensation）的定义和无环性
- 图反转操作（为 Kosaraju 第二遍 DFS 提供）
- 上述定义的基本性质引理

Shared SCC Lib **不包含**：
- 任何算法的归纳步骤关系
- 任何算法状态（`TarjanState`、`KosarajuState`）
- 任何算法不变量或正确性证明
- 任何 DFS 树生成、low 值计算等算法细节

### 1.3 下游消费者

```
scc_basic.v （本阶段产出）
    ↓
    ├── scc_tarjan.v → scc_tarjan_termination.v → scc_correctness.v  【Tarjan Phase】
    │
    └── kosaraju.v → kosaraju_correctness.v                          【Kosaraju Phase，合作者】
```

---

## 2. 总体架构

本阶段产出 **1 个新文件**：

```
SeparationLogic/GraphLib/examples/
└── scc_basic.v    # 唯一产出：SCC 数学基础
```

**依赖关系**（只读引用，不修改）：

```
graph_basic.v + reachable/*.v + directed/*.v + subgraph/*.v + MaxMinLib/*.v
    ↓
scc_basic.v
```

**设计原则**：

1. **与 GraphLib 风格一致**：使用 Record 表示具体图、Type Classes 参数化、集合谓词（`V -> Prop`）表示顶点集
2. **算法无关**：所有定义和引理不引用任何算法的状态或步骤
3. **使用古典逻辑**：与 tarjan.v 风格一致，使用 `Coq.Logic.Classical`
4. **为两个算法服务**：Tarjan 需要 `is_SCC` 作为 spec 目标，Kosaraju 额外需要 `reverse_directed_graph`
5. **自包含**：本文件可独立编译，不依赖任何尚未创建的文件

---

## 3. 文件：scc_basic.v — 完整规格

**路径**：`SeparationLogic/GraphLib/examples/scc_basic.v`
**预估行数**：700–900 行
**预估时间**：1.5–2 周

### 3.1 导入依赖

```coq
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
```

注意：不需要导入 `MaxMinLib`（本文件不涉及 min/max 操作）或 `directed/` 下的 DFS 树模块（本文件不涉及 DFS）。

---

### 3.2 有向图的具体表示（DirectedGraphType）

现有 `tarjan.v` 中的 `OriginalGraphType` 的 `step_aux` 是无向语义（允许正向或反向解释）。SCC 需要纯粹的有向图。

```coq
(* 有向图：边 e 有确定的方向 source(e) → target(e) *)
Record DirectedGraphType {V E: Type} := {
  dg_vvalid   : V -> Prop;
  dg_evalid   : E -> Prop;
  dg_source   : E -> V;
  dg_target   : E -> V;
  dg_listV    : list V;
}.

Arguments DirectedGraphType _ _ : clear implicits.

(* 良构条件 *)
Record DirectedGraphProp {V E: Type} (dg: DirectedGraphType V E) : Prop := {
  dg_source_valid : forall e, dg_evalid dg e -> dg_vvalid dg (dg_source dg e);
  dg_target_valid : forall e, dg_evalid dg e -> dg_vvalid dg (dg_target dg e);
  dg_finite_v     : forall v, dg_vvalid dg v -> In v (dg_listV dg);
}.

Arguments DirectedGraphProp _ _ : clear implicits.

(* step_aux：严格有向 *)
Record dg_step_aux {V E: Type} (dg: DirectedGraphType V E) (e: E) (x y: V) : Prop := {
  dg_vx  : dg_vvalid dg x;
  dg_vy  : dg_vvalid dg y;
  dg_ve  : dg_evalid dg e;
  dg_dir : dg_source dg e = x /\ dg_target dg e = y;
}.
```

**与 `OriginalGraphType` 的关键差异**：

| 方面 | `OriginalGraphType`（tarjan.v） | `DirectedGraphType`（本文件） |
|------|-------------------------------|---------------------------|
| `step_aux` 方向 | `(x=source /\ y=target) \/ (x=target /\ y=source)` | 严格 `x=source /\ y=target` |
| 图类型 | 无向图 | 有向图 |
| 实例化的 Type Class | `UndirectedGraph`, `StepUniqueUndirected` | 仅 `StepUniqueDirected`，**不**实例化 `UndirectedGraph` |

---

### 3.3 Type Class 实例化

需要在文件中完成以下实例（参考 `tarjan.v` 中对 `OriginalGraphType` 的模式）：

| # | Type Class | 实例名称 | 关键点 |
|---|-----------|---------|--------|
| 1 | `Graph (DirectedGraphType V E) V E` | `DirectedGraph_graph` | `step_aux` 使用 `dg_step_aux`，`vvalid`/`evalid` 委托给 `dg_vvalid`/`dg_evalid` |
| 2 | `GValid (DirectedGraphType V E)` | `DirectedGraph_gvalid` | 直接使用 `DirectedGraphProp` |
| 3 | `StepValid (DirectedGraphType V E) V E` | `DirectedGraph_stepvalid` | 从 `dg_step_aux` 中析构，每条 step 两端均为 valid 顶点 |
| 4 | `NoEmptyEdge (DirectedGraphType V E) V E` | `DirectedGraph_noemptyedge` | 每条有效边提供 source 和 target |
| 5 | `StepUniqueDirected (DirectedGraphType V E) V E` | `DirectedGraph_stepunique` | 每条边有唯一的有向端点对；`dg_dir` 强制单一方向 |
| 6 | `FiniteGraph (DirectedGraphType V E) V E` | `Directed_finitegraph` | 使用 `dg_listV` 作为有限顶点枚举 |

**不实例化的 Type Class**：
- `UndirectedGraph`：SCC 严格有向
- `StepUniqueUndirected`：同上
- `SimpleGraph`：暂不需要（可能后续添加）

---

### 3.4 相互可达性与 SCC

#### 3.4.1 相互可达

```coq
Definition mutually_reachable {G V E: Type} `{Graph G V E} (g: G) (u v: V) : Prop :=
  reachable g u v /\ reachable g v u.
```

**等价关系性质**（三条引理都必须用 `Qed.` 证明）：

```coq
Lemma mutually_reachable_refl : forall g u, vvalid g u -> mutually_reachable g u u.
Lemma mutually_reachable_sym  : forall g u v, mutually_reachable g u v -> mutually_reachable g v u.
Lemma mutually_reachable_trans : forall g u v w,
  mutually_reachable g u v -> mutually_reachable g v w -> mutually_reachable g u w.
```

`refl` 需要 `vvalid g u` 的前提（孤立顶点与自身相互可达）。`trans` 使用 `reachable` 的传递性（`clos_refl_trans` 的传递闭包性质）。

#### 3.4.2 SCC 定义

```coq
Definition is_SCC {G V E: Type} `{Graph G V E} (g: G) (s: V -> Prop) : Prop :=
  (exists v, s v /\ vvalid g v) /\                          (* 非空 *)
  (forall u v, s u -> s v -> mutually_reachable g u v) /\   (* 内部相互可达 *)
  (forall u v, s u -> vvalid g v -> mutually_reachable g u v -> s v). (* 极大性 *)
```

**关键引理**：

```coq
(* SCC 中任意两点的相互可达性蕴含了极大闭包性质 *)
Lemma is_SCC_closed_under_mr : forall g s u v,
  is_SCC g s -> s u -> mutually_reachable g u v -> s v.

(* SCC 不能是真超集 *)
Lemma is_SCC_maximal : forall g s1 s2,
  is_SCC g s1 -> is_SCC g s2 ->
  (forall v, s1 v -> s2 v) -> (forall v, s2 v -> s1 v).

(* 单个顶点的 SCC（自环或无出边入边时） *)
Lemma singleton_is_SCC : forall g v,
  vvalid g v -> (forall u, vvalid g u -> mutually_reachable g v u -> u = v) ->
  is_SCC g (fun w => w = v).
```

---

### 3.5 SCC 划分

```coq
Definition scc_partition {G V E: Type} `{Graph G V E}
  (g: G) (sccs: list (V -> Prop)) : Prop :=
  (forall v, vvalid g v -> exists s, In s sccs /\ s v) /\             (* 覆盖 *)
  (forall s, In s sccs -> is_SCC g s) /\                               (* 每个是 SCC *)
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2). (* 互不相交 *)
```

**核心定理**：

```coq
(* 相互可达的顶点属于同一 SCC *)
Lemma mutually_reachable_same_SCC : forall g u v sccs,
  scc_partition g sccs -> mutually_reachable g u v ->
  exists s, In s sccs /\ s u /\ s v.

(* 划分的唯一性（在集合外延等价意义下） *)
Lemma scc_partition_unique : forall g sccs1 sccs2,
  scc_partition g sccs1 -> scc_partition g sccs2 ->
  (forall s1, In s1 sccs1 -> exists s2, In s2 sccs2 /\
    forall v, s1 v <-> s2 v) /\
  (forall s2, In s2 sccs2 -> exists s1, In s1 sccs1 /\
    forall v, s2 v <-> s1 v).

(* 存在性：每个有限有向图都有 SCC 划分 *)
Theorem scc_partition_exists : forall {V E: Type} (dg: DirectedGraphType V E),
  DirectedGraphProp dg ->
  exists sccs, scc_partition (dg_to_graph dg) sccs.
```

**`scc_partition_exists` 的证明策略**：
1. `mutually_reachable` 是 `dg_vvalid` 上的等价关系（`refl`、`sym`、`trans` 已证）
2. 利用 `dg_listV` 的有限性，通过对顶点列表的归纳构造等价类
3. 每个等价类恰好是一个 `is_SCC`（内部相互可达 + 极大性由等价类定义保证）
4. 等价类集合构成 `scc_partition`
5. 这是一个纯集合论证明，**不依赖任何算法**。

下游算法（Tarjan、Kosaraju）的构造性证明可以替代这个存在性定理，但在 shared lib 中独立证明它有两个好处：
- 确保 `is_SCC` / `scc_partition` 的定义足够强（不自相矛盾）
- 作为算法正确性的 sanity check：算法输出的划分应与这个纯数学构造一致

---

### 3.6 缩点图（Condensation）

```coq
(* 缩点图的边：SCC 间存在原图的有向边 *)
Definition condensation_edge {G V E: Type} `{Graph G V E}
  (g: G) (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ step g u v.

(* 缩点图是 DAG *)
Theorem condensation_is_acyclic : forall {G V E: Type} `{Graph G V E}
  (g: G) (sccs: list (V -> Prop)),
  scc_partition g sccs ->
  ~ exists path_sccs,
    Forall (fun s => In s sccs) path_sccs /\
    length path_sccs >= 2 /\
    (forall i, (S i) < length path_sccs ->
      condensation_edge g sccs (nth i path_sccs (hd nil path_sccs))
                                (nth (S i) path_sccs (hd nil path_sccs))) /\
    hd nil path_sccs = nth (length path_sccs - 1) path_sccs (hd nil path_sccs).
```

**证明策略**（标准反证法）：
1. 假设缩点图中存在环（长度 ≥ 2）
2. 环上相邻 SCC 间存在原图的有向边
3. 通过 `reachable` 的传递性，环上所有 SCC 的顶点相互可达
4. 由 SCC 的极大性，这些 SCC 实际上应该合并为一个 SCC
5. 与 `scc_partition` 的互不相交性质矛盾

#### 等价简化版陈述

为了更实用的引用，同时提供一个简洁版：

```coq
(* 等价简化版：不存在不同 SCC 间的相互可达环 *)
Corollary no_cycle_between_different_SCCs : forall g sccs,
  scc_partition g sccs ->
  ~ exists s1 s2, In s1 sccs -> In s2 sccs -> s1 <> s2 ->
    (exists u1 v1, s1 u1 /\ s2 v1 /\ reachable g u1 v1) /\
    (exists u2 v2, s2 u2 /\ s1 v2 /\ reachable g u2 v2).
```

---

### 3.7 图反转（Graph Reversal）

**新增内容**——原始 Tarjan Phase 1 计划未包含，但 Kosaraju 算法必须依赖。

```coq
(* 图反转：交换每条边的 source 和 target *)
Definition reverse_directed_graph {V E: Type}
  (dg: DirectedGraphType V E) : DirectedGraphType V E :=
  {| dg_vvalid := dg_vvalid dg;
     dg_evalid := dg_evalid dg;
     dg_source := dg_target dg;
     dg_target := dg_source dg;
     dg_listV  := dg_listV dg |}.
```

#### Type Class 实例（反图上自动成立）

反图的实例可以直接从原图实例推导，无需重新证明：

```coq
#[export] Instance ReverseDirected_graph {V E: Type} (dg: DirectedGraphType V E)
  `{Graph (DirectedGraphType V E) V E} :
  Graph (DirectedGraphType V E) V E := ...

#[export] Instance ReverseDirected_gvalid {V E: Type} (dg: DirectedGraphType V E)
  (Hvalid: DirectedGraphProp dg) :
  GValid (reverse_directed_graph dg) := ...

(* StepValid / NoEmptyEdge / StepUniqueDirected / FiniteGraph 同理 *)
```

**关键：每个实例的证明应该只需一行，因为 `reverse_directed_graph` 仅交换 source/target，不影响良构性。**

#### 反图的核心引理

```coq
(* 反转两次恢复原图 *)
Lemma reverse_reverse_id : forall dg,
  reverse_directed_graph (reverse_directed_graph dg) = dg.

(* 反转保持良构性 *)
Lemma reverse_preserves_valid : forall dg,
  DirectedGraphProp dg -> DirectedGraphProp (reverse_directed_graph dg).

(* 相互可达在反转下不变 —— 对 Kosaraju 至关重要 *)
Lemma mutually_reachable_reverse : forall {V E: Type} (dg: DirectedGraphType V E)
  `{DirectedGraphProp dg} (u v: V),
  dg_vvalid dg u -> dg_vvalid dg v ->
  (mutually_reachable (dg_to_graph dg) u v <->
   mutually_reachable (dg_to_graph (reverse_directed_graph dg)) u v).

(* 推论：SCC 在反转下不变 *)
Corollary is_SCC_reverse : forall dg `{DirectedGraphProp dg} s,
  is_SCC (dg_to_graph dg) s <-> is_SCC (dg_to_graph (reverse_directed_graph dg)) s.

(* 推论：SCC 划分在反转下不变 *)
Corollary scc_partition_reverse : forall dg `{DirectedGraphProp dg} sccs,
  scc_partition (dg_to_graph dg) sccs <->
  scc_partition (dg_to_graph (reverse_directed_graph dg)) sccs.
```

**为什么 Kosaraju 需要这些引理**：
- Kosaraju 第二遍在反图上 DFS，收集的每个 DFS 树声称是原图的 SCC
- `mutually_reachable_reverse` 是连接"反图中的 DFS 树"与"原图中的 SCC"的桥梁
- `is_SCC_reverse` 让第二遍 DFS 可以直接使用 `is_SCC` 的定义，不需要重复定义反图版 SCC

---

### 3.8 完整引理清单

| # | 引理 | 复杂度 | 类别 |
|---|------|--------|------|
| D1 | `mutually_reachable_refl` | 低 | 相互可达 |
| D2 | `mutually_reachable_sym` | 低 | 相互可达 |
| D3 | `mutually_reachable_trans` | 中 | 相互可达 |
| D4 | `is_SCC_closed_under_mr` | 低 | SCC 性质 |
| D5 | `is_SCC_maximal` | 中 | SCC 性质 |
| D6 | `singleton_is_SCC` | 低 | SCC 性质 |
| D7 | `mutually_reachable_same_SCC` | 中 | SCC 划分 |
| D8 | `scc_partition_unique` | 中 | SCC 划分 |
| D9 | `scc_partition_exists` | 高 | SCC 划分 |
| D10 | `condensation_is_acyclic` | 中 | 缩点图 |
| D11 | `no_cycle_between_different_SCCs` | 中 | 缩点图 |
| D12 | `reverse_reverse_id` | 低 | 图反转 |
| D13 | `reverse_preserves_valid` | 低 | 图反转 |
| D14 | `mutually_reachable_reverse` | 中 | 图反转 |
| D15 | `is_SCC_reverse` | 低（推论） | 图反转 |
| D16 | `scc_partition_reverse` | 低（推论） | 图反转 |

---

## 4. Makefile 修改

在 `SeparationLogic/GraphLib/Makefile` 中修改 `EXAMPLES_FILES` 行：

```makefile
# 修改前：
EXAMPLES_FILES = examples/floyd.v examples/dijkstra.v examples/prim.v examples/kruskal.v examples/dfs.v examples/tarjan.v

# 修改后：
EXAMPLES_FILES = examples/floyd.v examples/dijkstra.v examples/prim.v examples/kruskal.v examples/dfs.v examples/tarjan.v \
                 examples/scc_basic.v
```

`scc_basic.v` 应在 `tarjan.v` 之后，但不依赖后者。后续 Tarjan Phase 和 Kosaraju Phase 的文件追加到 `scc_basic.v` 之后。

---

## 5. 下游接口合同

下游算法文件（Tarjan、Kosaraju）通过以下方式使用 Shared SCC Lib：

```coq
Require Import GraphLib.examples.scc_basic.
```

### 5.1 下游可以依赖的定义

| 定义 | 类型 | 用途 |
|------|------|------|
| `DirectedGraphType V E` | `Type` | 算法的输入图类型 |
| `DirectedGraphProp dg` | `Prop` | 算法前置条件（图良构） |
| `dg_step_aux dg e x y` | `Prop` | 有向边 step 关系 |
| `mutually_reachable g u v` | `Prop` | 算法正确性的 spec 目标 |
| `is_SCC g s` | `Prop` | 判断算法输出的顶点集合是否为 SCC |
| `scc_partition g sccs` | `Prop` | 判断算法输出的 SCC 列表是否为有效划分 |
| `condensation_edge g sccs s1 s2` | `Prop` | 陈述拓扑序性质 |
| `reverse_directed_graph dg` | `DirectedGraphType V E` | Kosaraju 第二遍的输入图 |
| 全部 16 条引理 | `Lemma`/`Theorem` | 算法证明中可自由引用 |

### 5.2 下游不能依赖的内容

- 任何算法状态、步骤、不变量（不在本文件中）
- DFS 树生成（不在本文件中）
- low 值 / finishing time（不在本文件中）

### 5.3 新增内容的通知机制

如果 shared lib 需要新增定义或修改现有定义，必须在两个下游算法中同步检查影响。但 shared lib 的定位决定了它应该是**稳定接口**——一旦 `scc_basic.v` 编译通过并通过质量检查，下游即可放心依赖。

---

## 6. 任务拆解与时间估算

**总时间估算：1.5–2 周**（单人全职）

### 第 1–3 天：有向图基础 + Type Class 实例

| 天 | 任务 | 产出 |
|----|------|------|
| D1 | 定义 `DirectedGraphType`、`DirectedGraphProp`、`dg_step_aux` | 有向图数据结构 |
| D2 | 实例化 `Graph`、`GValid`、`StepValid`、`StepUniqueDirected` | 前 4 个 Type Class 实例 |
| D3 | 实例化 `NoEmptyEdge`、`FiniteGraph`，整体编译验证 | 全部 6 个 Type Class 实例 |

### 第 4–5 天：相互可达 + SCC 定义

| 天 | 任务 | 产出 |
|----|------|------|
| D4 | 定义 `mutually_reachable`，证明 `refl`、`sym`、`trans` | 等价关系性质 |
| D5 | 定义 `is_SCC`，证明 `closed_under_mr`、`maximal`、`singleton` | SCC 基本性质 |

### 第 6–8 天：SCC 划分 + 缩点图

| 天 | 任务 | 产出 |
|----|------|------|
| D6 | 定义 `scc_partition`，证明 `mutually_reachable_same_SCC` | 覆盖引理 |
| D7 | 证明 `scc_partition_unique`（划分唯一性） | 唯一性定理 |
| D8 | 证明 `scc_partition_exists`（构造等价类） | 存在性定理 |

**D8 是 shared lib 中证明难度最高的一天**，需要：
1. 定义 `equiv_class`（等价类作为 `V -> Prop`）
2. 构造 `list (V -> Prop)` 作为等价类列表
3. 证明每个等价类是 SCC
4. 证明等价类列表是 partition

### 第 9–10 天：缩点图 + 图反转

| 天 | 任务 | 产出 |
|----|------|------|
| D9 | 定义 `condensation_edge`，证明 `condensation_is_acyclic` | 缩点图理论 |
| D10 | 定义 `reverse_directed_graph` + Type Class 实例 + 全部 5 条反图引理 | 图反转操作 |

### 第 11–12 天：Review + 文档

| 天 | 任务 | 产出 |
|----|------|------|
| D11 | 全面 review、补充缺失引理、确保所有证明用 `Qed.` | 完整的 `scc_basic.v` |
| D12 | 编译验证（`coqc` 无错误）、更新 Makefile | 可编译的最终版本 |

---

## 7. 风险管理

| # | 风险 | 可能性 | 影响 | 缓解措施 |
|---|------|--------|------|----------|
| R1 | `scc_partition_exists` 的等价类构造比预期复杂（涉及 quotient 构造） | 中 | 中：可能延迟 2–3 天 | 先用 `Admitted` 占位，后续算法提供构造性证明后回填；或使用 `Coq.Lists.List` 的 `partition` 函数辅助 |
| R2 | `condensation_is_acyclic` 的陈述过于复杂导致难以使用 | 中 | 中：下游算法难以引用 | 提供等价简化版 `no_cycle_between_different_SCCs`。如果 Inductive 路径关系太复杂，先用一阶可达性陈述 |
| R3 | `reverse_directed_graph` 的 Type Class 实例化与现有 GraphLib 实例冲突 | 低 | 高：可能导致编译错误 | 使用 `Existing Instance` 或在实例化时确保参数唯一性。参考 `subgraph.v` 中对多实例的处理方式 |
| R4 | 合作者的 Kosaraju 需要 shared lib 中没有的定义 | 中 | 中：需要修订 shared lib | 在开发早期与合作者对齐需求。如果 Kosaraju 需要额外定义（如 `topological_order`），优先加入 shared lib |
| R5 | 与 `tarjan.v` 中的 `OriginalGraphType` 命名混淆 | 低 | 低 | 明确注释两者差异。`DirectedGraphType` 仅用于 SCC，`OriginalGraphType` 仅用于桥定理 |

---

## 8. 质量检查清单

### 编译
- [ ] `coqc scc_basic.v` 编译无错误
- [ ] Makefile 已更新，`make all` 在 GraphLib 目录下通过

### 有向图基础
- [ ] `DirectedGraphType` 的 5 个字段互不冗余
- [ ] `DirectedGraphProp` 的良构条件充分（source/target valid + finite vertices）
- [ ] 6 个 Type Class 实例化无遗漏、无冲突
- [ ] `DirectedGraphType` 没有实例化 `UndirectedGraph` 或 `StepUniqueUndirected`

### 相互可达 + SCC
- [ ] `mutually_reachable` 的三个等价关系性质全部用 `Qed.` 证明
- [ ] `mutually_reachable_refl` 正确处理孤立顶点（`vvalid g u` 前提）
- [ ] `is_SCC` 的非空、内部可达、极大性三元组自洽
- [ ] 平凡单顶点图满足 `is_SCC` 且 `singleton_is_SCC` 成立

### SCC 划分
- [ ] `scc_partition` 的三条件（覆盖、每个是 SCC、互不相交）自洽
- [ ] `scc_partition_exists` 对所有有限有向图成立
- [ ] `scc_partition_unique` 证明两个划分在外延等价意义下相同
- [ ] `mutually_reachable_same_SCC` 证明相互可达的顶点不能位于不同 SCC

### 缩点图
- [ ] `condensation_is_acyclic` 证明缩点图无环（不含长度 ≥ 2 的环）
- [ ] `no_cycle_between_different_SCCs` 作为等价推论成立

### 图反转
- [ ] `reverse_directed_graph` 定义正确（source/target 交换）
- [ ] `reverse_reverse_id` 成立
- [ ] `reverse_preserves_valid` 成立
- [ ] `mutually_reachable_reverse` 成立（对 Kosaraju 至关重要）
- [ ] 反图的 6 个 Type Class 实例全部编译通过

### 全局
- [ ] 没有遗留 `Admitted`（`scc_partition_exists` 除外，如有必要）
- [ ] 没有引入额外 `Axiom`（除古典逻辑外）
- [ ] 所有依赖为已存在的 GraphLib 文件，不依赖尚未创建的文件

---

## 9. 开工顺序建议

1. **先建骨架**（D1–D3）
   - 定义 `DirectedGraphType` 和 `DirectedGraphProp`
   - 实例化全部 6 个 Type Class
   - 编译通过后再继续——这是降低风险的关键步骤

2. **再写 SCC 数学定义**（D4–D5）
   - `mutually_reachable` + 等价关系
   - `is_SCC` + 基本性质
   - 此时可以 sandbox 测试：用手工构造的小图验证定义是否符合直觉

3. **攻坚划分理论**（D6–D8）
   - 这是证明最密集的部分
   - `scc_partition_exists` 如果卡住超过 2 天，先 `Admitted` 并标注 TODO
   - 后续每个算法的正确性证明都会提供一个构造性实例

4. **缩点图 + 反图**（D9–D10）
   - 这两部分相对独立于划分理论
   - 可以与前几步并行开发

5. **Review + 编译**（D11–D12）
   - 与合作者确认 shared lib 满足 Kosaraju 需求
   - 确保所有证明用 `Qed.` 而非 `Defined.`

### 协作衔接

Shared SCC Lib 完成后：
- Tarjan Phase 的 `scc_tarjan.v` 第一行即是 `Require Import GraphLib.examples.scc_basic.`
- Kosaraju Phase 的 `kosaraju.v` 第一行同样是 `Require Import GraphLib.examples.scc_basic.`
- 两条路线可以**完全并行**推进，互不阻塞

---

*本计划基于 QCP v2.0.2、Rocq 8.20.1、GraphLib 现有版本编写。*
*本文件为 shared_scc_lib 阶段计划，Tarjan SCC 算法验证计划见 `20260610-tarjan-scc-phase1-plan.md`。*
