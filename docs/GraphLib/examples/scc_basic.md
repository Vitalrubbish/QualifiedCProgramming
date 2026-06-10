# scc_basic.v — 有向图强连通分量（SCC）理论

`scc_basic.v` 是 GraphLib 库中关于**有向图强连通分量（Strongly Connected Components, SCC）** 的基础理论文件。它定义了有向图的表示、SCC 的数学性质、SCC 分划的存在性与唯一性、缩点图（condensation）的无环性，以及图反转下 SCC 的不变性——为 Kosaraju 等 SCC 算法的正确性验证提供了严格的数学基础。该文件纯粹在数学层面工作，不涉及具体的命令式实现。

## 文件导入

```coq
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import Lia.
```

该文件依赖 GraphLib 的核心模块（`graph_basic` 提供 Type Class、`reachable_basic` 提供可达性）以及外部库（`SetsClass` 提供集合运算、`Classical` 提供排中律、`Lia` 提供算术判定）。

---

## 文件结构总览

```
scc_basic.v
├── 1. Directed Graph Type — 有向图的数据结构
│   ├── DirectedGraphType（Record 定义）
│   ├── DirectedGraphProp（良构条件）
│   └── dg_step_aux（有向边关系，与 tarjan.v 的关键区别）
│
├── 2. Type Class Instances — 将 DirectedGraphType 嵌入 GraphLib
│   ├── DirectedGraph_graph（Graph 实例）
│   ├── DirectedGraph_gvalid（GValid 实例）
│   ├── DirectedGraph_stepvalid（StepValid 实例）
│   ├── DirectedGraph_noemptyedge（NoEmptyEdge 实例）
│   ├── DirectedGraph_stepunique（StepUniqueDirected 实例）
│   └── Directed_finitegraph（FiniteGraph 实例）
│
├── Section SCC_DEFS — SCC 核心定义与性质
│   ├── 3. Mutually Reachable and SCC
│   │   ├── mutually_reachable（相互可达 = 同属一个 SCC）
│   │   ├── 等价性引理（refl / sym / trans）
│   │   ├── is_SCC（SCC 的三条公理化定义）
│   │   ├── is_SCC_vvalid（SCC 中每个顶点合法）
│   │   ├── is_SCC_closed_under_mr（SCC 在相互可达下封闭）
│   │   ├── is_SCC_maximal（SCC 的极大性引理）
│   │   └── singleton_is_SCC（单点 SCC 的判定条件）
│   │
│   ├── 4. SCC Partition
│   │   ├── scc_partition（分划的三条公理化定义）
│   │   ├── mutually_reachable_same_SCC（相互可达 ⇒ 同属一个 SCC）
│   │   └── scc_partition_unique（SCC 分划的唯一性）
│   │
│   ├── 5. Existence of SCC Partition（古典构造）
│   │   ├── equiv_class（等价类 = 候选 SCC）
│   │   ├── equiv_class_is_SCC（等价类确实是 SCC）
│   │   ├── build_scc_partition_aux（归纳构造分划的辅助引理）
│   │   └── scc_partition_exists（存在性定理）
│   │
│   └── 6. Condensation（缩点图的无环性）
│       ├── condensation_edge（缩点图中的有向边）
│       ├── condensation_reachable（缩点图中 SCC 间的可达性）
│       ├── condensation_reachable_implies_reachable（缩点可达 ⇒ 顶点可达）
│       ├── no_cycle_between_different_SCCs（不同 SCC 间无环）
│       └── condensation_is_acyclic（缩点图是无环的 DAG）
│
└── 7. Graph Reversal（为 Kosaraju 算法准备）
    ├── reverse_directed_graph（反转图定义）
    ├── step_aux_reverse_equiv / step_reverse_equiv / reachable_reverse_equiv
    ├── reverse_reverse_id / reverse_preserves_valid
    ├── mutually_reachable_reverse（相互可达在图反转下不变）
    ├── is_SCC_reverse（SCC 在图反转下不变）
    └── scc_partition_reverse（SCC 分划在图反转下不变）
```

---

## 第一部分：DirectedGraphType — 有向图的数据结构

### 与 tarjan.v 的关键区别

| 维度 | `tarjan.v`（桥算法） | `scc_basic.v`（SCC 理论） |
|------|----------------------|---------------------------|
| 图类型 | `OriginalGraphType`：边列表表示，边方向可以任意解释 | `DirectedGraphType`：有向边，`step_aux` 严格从源到目标 |
| 边的方向 | `step_aux` 允许解释为正向或反向（适合无向图的桥问题） | `dg_step_aux` 强制 `x = source(e)` 且 `y = target(e)` |
| 无向性实例 | 实现了 `UndirectedGraph` 和 `StepUniqueUndirected` | 实现了 `StepUniqueDirected`，不涉及无向性 |
| 应用场景 | Tarjan 桥判定（无向图背景） | SCC 计算（有向图背景，Kosaraju / Tarjan SCC） |

### 数据结构

```coq
Record DirectedGraphType {V E: Type} := {
  dg_vvalid   : V -> Prop;
  dg_evalid   : E -> Prop;
  dg_source   : E -> V;
  dg_target   : E -> V;
  dg_listV    : list V;
}.
```

`DirectedGraphType` 将有向图建模为**源-目标对表示**：
- `dg_source e` 和 `dg_target e` 分别给出边 `e` 的起点和终点；
- `dg_vvalid` / `dg_evalid` 判定顶点/边的有效性；
- `dg_listV` 提供有限的顶点列表。

```coq
Record DirectedGraphProp {V E: Type} (dg: DirectedGraphType V E) : Prop := {
  dg_source_valid : forall e, dg_evalid dg e -> dg_vvalid dg (dg_source dg e);
  dg_target_valid : forall e, dg_evalid dg e -> dg_vvalid dg (dg_target dg e);
  dg_finite_v     : forall v, dg_vvalid dg v -> In v (dg_listV dg);
}.
```

良构条件：
- 每条有效边的两端点都是有效顶点；
- 每个有效顶点都出现在 `dg_listV` 中（有限性）。

### 有向边关系

```coq
Record dg_step_aux {V E: Type} (dg: DirectedGraphType V E) (e: E) (x y: V) : Prop := {
  dg_vx  : dg_vvalid dg x;
  dg_vy  : dg_vvalid dg y;
  dg_ve  : dg_evalid dg e;
  dg_dir : dg_source dg e = x /\ dg_target dg e = y;
}.
```

**关键约束**：`dg_step_aux dg e x y` 要求 `x` 必须是 `source(e)`，`y` 必须是 `target(e)`——边方向严格固定。这与 `tarjan.v` 的 `original_step_aux`（允许正向或反向解释）形成鲜明对比，是 SCC 理论（特别是 Kosaraju 算法需要区分正向图和反向图）的关键基础。

---

## 第二部分：Type Class 实例化

该文件为 `DirectedGraphType` 实例化了 **6 个 Type Class**，使其融入 GraphLib 的通用框架：

| Type Class | 关键证明思路 |
|------------|-------------|
| `Graph` | `vvalid` → `dg_vvalid`，`evalid` → `dg_evalid`，`step_aux` → `dg_step_aux` |
| `GValid` | 直接使用 `DirectedGraphProp` |
| `StepValid` | 从 `dg_step_aux` 的构造直接析取顶点/边的有效性（`dg_vx`、`dg_vy`、`dg_ve`） |
| `NoEmptyEdge` | 每条有效边提供其 `dg_source` 和 `dg_target` 作为端点（依赖 `dg_source_valid` / `dg_target_valid`） |
| `StepUniqueDirected` | 边列表表示保证每条边有唯一的源和目标（`dg_dir` 中的等式直接推导 `source = source ∧ target = target`） |
| `FiniteGraph` | 使用 `dg_listV`（`listV` 字段 → `dg_listV`，`finite_vertices` 字段 → `dg_finite_v`） |

---

## 第三部分：相互可达与 SCC 的定义

### mutually_reachable（相互可达）

```coq
Definition mutually_reachable (u v: V) : Prop :=
  reachable g u v /\ reachable g v u.
```

**直觉**：在有向图中，两个顶点相互可达（即存在 `u →* v` 和 `v →* u` 的路径）等价于它们属于同一个强连通分量。

`mutually_reachable` 是一个**等价关系**：

| 引理 | 内容 | 证明 |
|------|------|------|
| `mutually_reachable_refl` | 若 `vvalid g u`，则 `mutually_reachable u u` | 自反性来自 `reachable` 的自反性（路径长度 0） |
| `mutually_reachable_sym` | `mutually_reachable u v → mutually_reachable v u` | 直接交换 `/\` 的两边 |
| `mutually_reachable_trans` | `mutually_reachable u v → mutually_reachable v w → mutually_reachable u w` | 利用 `reachable` 的传递性（`etransitivity`） |

### is_SCC（强连通分量的公理化定义）

```coq
Definition is_SCC (s: V -> Prop) : Prop :=
  (exists v, s v /\ vvalid g v) /\
  (forall u v, s u -> s v -> mutually_reachable u v) /\
  (forall u v, s u -> vvalid g v -> mutually_reachable u v -> s v).
```

**三个条件**对应 SCC 的三条核心性质：

| 条件 | 含义 | 对应 SCC 性质 |
|------|------|-------------|
| `∃v, s v ∧ vvalid g v` | 非空且至少包含一个有效顶点 | SCC 非空 |
| `∀u v, s u → s v → mutually_reachable u v` | 内部任意两点相互可达 | SCC 的**内部强连通性** |
| `∀u v, s u → vvalid g v → mutually_reachable u v → s v` | 若 SCC 外一点与 SCC 内一点相互可达，则它也被纳入 SCC | SCC 的**极大性（maximality）** |

### SCC 的导出性质

| 引理 | 内容 | 用途 |
|------|------|------|
| `is_SCC_vvalid` | SCC 中每个顶点都是有效顶点（由非空性 + 内部连通性推导） | 后续引理的前置条件 |
| `is_SCC_closed_under_mr` | 若 `s u` 且 `mutually_reachable u v`，则 `s v`（由极大性 + `is_SCC_vvalid` 推导） | SCC 在相互可达下封闭 |
| `is_SCC_maximal` | 若两个 SCC 有包含关系，则它们外延等价 | SCC 的极大性保证相等 |

### 单点 SCC

```coq
Lemma singleton_is_SCC : forall v,
  vvalid g v -> (forall u, vvalid g u -> mutually_reachable v u -> u = v) ->
  is_SCC (fun w => w = v).
```

**条件**：若 `v` 只与自身相互可达（即没有任何其他顶点能到达 `v` 且被 `v` 到达），则单点集 `{v}` 是一个 SCC。这在图的"死胡同"顶点（如 DAG 的汇点）上自然成立。

---

## 第四部分：SCC 分划

### scc_partition（SCC 分划的公理化定义）

```coq
Definition scc_partition (sccs: list (V -> Prop)) : Prop :=
  (forall v, vvalid g v -> exists s, In s sccs /\ s v) /\
  (forall s, In s sccs -> is_SCC s) /\
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2).
```

**三个条件**对应分划的三条性质：

| 条件 | 含义 |
|------|------|
| `Cover` | 每个有效顶点属于某个 SCC（覆盖性） |
| `SCC` | 列表中的每个元素都是一个 SCC（结构性） |
| `Disjoint` | 不同的 SCC 不相交（互斥性，通过"共享顶点 ⇒ 相等"来表述） |

### 相互可达 ⇒ 同属一个 SCC

```coq
Lemma mutually_reachable_same_SCC : forall u v sccs,
  vvalid g u -> scc_partition sccs -> mutually_reachable u v ->
  exists s, In s sccs /\ s u /\ s v.
```

**证明思路**：
1. 由 Cover，`u` 属于某个 SCC `su`。
2. 由 `is_SCC_closed_under_mr`（极大性方向的封闭性），`su` 也包含所有与 `u` 相互可达的顶点。
3. 因此 `su` 同时含有 `u` 和 `v`。

这证明了**一个分划中，相互可达的两个顶点必然属于同一个 SCC**——这是 SCC 分划最核心的语义保证。

### SCC 分划的唯一性

```coq
Lemma scc_partition_unique : forall sccs1 sccs2,
  scc_partition sccs1 -> scc_partition sccs2 ->
  (forall s1, In s1 sccs1 -> exists s2, In s2 sccs2 /\ forall v, s1 v <-> s2 v) /\
  (forall s2, In s2 sccs2 -> exists s1, In s1 sccs1 /\ forall v, s2 v <-> s1 v).
```

**定理**：SCC 分划在**外延等价**意义下唯一——任意两个分划的元素一一对应，且对应的 SCC 具有完全相同的顶点集。

**证明策略**：
- 取 `s1` 中的一个有效顶点 `v`（由非空性保证存在）。
- 在 `sccs2` 中找包含 `v` 的 SCC `s2`（由 Cover 保证）。
- 利用 SCC 的极大性（`is_SCC_closed_under_mr`），证明 `s1` 和 `s2` 包含完全相同的顶点集合。
- 对称地处理另一个方向。

> **注意**：这里的"唯一性"是外延等价意义下的——`s1` 和 `s2` 作为 `V -> Prop` 在数学上相等，但作为列表元素可以有不同顺序或重复。实际实现中可能需要进一步规范化（如排序）。

---

## 第五部分：SCC 分划的存在性（古典构造）

在 `FiniteGraph` 和 `gvalid g` 的附加前提下，本文件构造性地证明了 SCC 分划的存在性。

### equiv_class（等价类）

```coq
Definition equiv_class (v: V) : V -> Prop :=
  fun w => vvalid g w /\ mutually_reachable v w.
```

`equiv_class v` 是所有与 `v` **相互可达**（且在图中有效）的顶点集合。这对应等价关系 `mutually_reachable` 下的等价类。

```coq
Lemma equiv_class_is_SCC : forall v,
  vvalid g v -> is_SCC (equiv_class v).
```

**证明**：需要验证三条 SCC 性质：
1. **非空性**：`v` 自身在 `equiv_class v` 中（自反性）。
2. **内部连通性**：利用 `mutually_reachable` 的传递性和对称性，`equiv_class v` 中任意两点通过 `v` 连接。
3. **极大性**：若 `u ∈ equiv_class v` 且 `w` 与 `u` 相互可达，则 `w` 也与 `v` 相互可达（传递性），因此 `w ∈ equiv_class v`。

### 归纳构造分划

```coq
Lemma build_scc_partition_aux : forall (vertices: list V),
  exists sccs,
    (forall v, vvalid g v -> In v vertices -> exists s, In s sccs /\ s v) /\
    (forall s, In s sccs -> is_SCC s) /\
    (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2).
```

**算法思想**（对顶点列表 `vertices` 的归纳）：

对于当前顶点 `a`：
1. 递归处理剩余顶点 `rest`，得到分划 `sccs_rest`。
2. **情况 A**：`a` 已经被 `sccs_rest` 中的某个 SCC 覆盖 → 直接使用 `sccs_rest`。
   - 这是因为如果 `a` 与某 SCC 中的一点相互可达，则由极大性，`a` 已经被包含。
3. **情况 B**：`a` 未被覆盖而且是有效顶点 → 创建新 SCC `equiv_class a` 并添加到列表最前面。
   - 关键：需要证明新的 `equiv_class a` 不与已有的任何 SCC 相交。这由 `a` 未被覆盖的前提保证——若相交，则 `a` 会通过相互可达性被已有 SCC 覆盖，与前提矛盾。
4. **情况 C**：`a` 不是有效顶点 → 跳过。

**关键证明步骤**（情况 B 的互斥性验证）：
- 若 `equiv_class a` 与已有 SCC `s2` 共享某顶点 `v`，则 `a` 与 `v` 相互可达（`equiv_class a` 的定义）。
- 由 `s2` 的 SCC 性质（极大性），`a` 被吸收进 `s2`。
- 这与 "`a` 未被覆盖" 矛盾，因此 `equiv_class a` 与所有已有 SCC 不相交。

### 存在性定理

```coq
Theorem scc_partition_exists : exists sccs, scc_partition sccs.
```

**证明**：以 `listV g`（`FiniteGraph` 提供的顶点列表）为参数调用 `build_scc_partition_aux`，并对所有有效顶点应用 `listV_contains_valid`（将 `vvalid g v` 转化为 `In v (listV g)`）。

> **经典逻辑依赖**：该构造使用了排中律（`classic`）来判断"是否有已有 SCC 包含 `a`"。这反映了 SCC 分划存在性证明的经典特征——实际算法（如 Kosaraju、Tarjan）会通过 DFS 构造性地生成分划，而非依赖排中律。

---

## 第六部分：缩点图（Condensation）的无环性

缩点图（condensation graph）将每个 SCC 缩为一个"超顶点"，若原图中存在从某个 SCC 到另一个 SCC 的边，则在缩点图中对应的超顶点间连边。SCC 理论的核心结论是：**缩点图一定是 DAG（有向无环图）**。

### condensation_edge（缩点边）

```coq
Definition condensation_edge (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ step g u v.
```

**四个条件**：
1. `s1` 和 `s2` 都在 SCC 分划中；
2. `s1 ≠ s2`（不同的 SCC）；
3. 存在从 `s1` 中某顶点 `u` 到 `s2` 中某顶点 `v` 的原图边。

### condensation_reachable（缩点图可达性）

```coq
Inductive condensation_reachable (sccs: list (V -> Prop)) :
  (V -> Prop) -> (V -> Prop) -> Prop :=
| cr_edge : forall s1 s2, condensation_edge sccs s1 s2 ->
    condensation_reachable sccs s1 s2
| cr_trans : forall s1 s2 s3,
    condensation_reachable sccs s1 s2 ->
    condensation_reachable sccs s2 s3 ->
    condensation_reachable sccs s1 s3.
```

这是 `condensation_edge` 的**传递闭包**。

### 关键引理：缩点可达 ⇒ 顶点可达

```coq
Lemma condensation_reachable_implies_reachable : forall sccs s1 s2,
  scc_partition sccs ->
  condensation_reachable sccs s1 s2 ->
  s1 <> s2 ->
  exists u v, s1 u /\ s2 v /\ reachable g u v.
```

**证明**（对 `condensation_reachable` 的归纳）：

- **Base case**（单条缩点边）：直接从 `condensation_edge` 的构造中取出 `step`，并通过 `step_rt` 转化为 `reachable`。
- **Transitive case**（`s1 → s2 → s3` 的链）：
  - 考虑三种子情况：
    1. `s1 = s2`：路径退化为 `s1(=s2) → s3`，递归应用归纳假设。
    2. `s2 = s3`：路径退化为 `s1 → s2(=s3)`，同上。
    3. 三者均不同：由归纳假设得 `u1 ∈ s1` 到 `v2 ∈ s2` 的路径，以及 `u2 ∈ s2` 到 `v3 ∈ s3` 的路径。`v2` 和 `u2` 都在 `s2` 中，而 `s2` 是 SCC（内部连通），因此存在从 `v2` 到 `u2` 的路径。拼接三段路径得到 `u1 →* v3`。

### 不同 SCC 间无环

```coq
Theorem no_cycle_between_different_SCCs : forall sccs,
  scc_partition sccs ->
  ~ exists s1 s2, In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
    (exists u1 v1, s1 u1 /\ s2 v1 /\ reachable g u1 v1) /\
    (exists u2 v2, s2 u2 /\ s1 v2 /\ reachable g u2 v2).
```

**定理**：不存在两个不同 SCC 之间既有前向路径又有反向路径。

**证明**（反证法）：
1. 假设存在 `s1 ≠ s2`，有前向路径 `u1 →* v1`（`u1 ∈ s1, v1 ∈ s2`）和反向路径 `u2 →* v2`（`u2 ∈ s2, v2 ∈ s1`）。
2. `v1` 和 `u2` 都在 `s2` 中 ⇒ 由 SCC 内部连通性，`v1` 与 `u2` 相互可达。
3. `v2` 和 `u1` 都在 `s1` 中 ⇒ 同理，`v2` 与 `u1` 相互可达。
4. 拼接：`u1 →* v1 ↔* u2 →* v2 ↔* u1` ⇒ `u1` 与 `u2` 相互可达。
5. 由 SCC 极大性，`u2` 必须也在 `s1` 中。
6. 但 `u2 ∈ s2` 且 `s1 ≠ s2`，与分划的互斥性矛盾。

### 缩点图是无环的

```coq
Theorem condensation_is_acyclic : forall sccs s1 s2,
  scc_partition sccs ->
  condensation_edge sccs s1 s2 ->
  ~ condensation_reachable sccs s2 s1.
```

**定理**：若缩点图中存在从 `s1` 到 `s2` 的边，则不存在从 `s2` 回到 `s1` 的缩点路径。即**缩点图是无环的 DAG**。

**证明结构**：
1. 从 `condensation_edge s1 s2` 提取顶点级的前向步 `step g u v`（`u ∈ s1, v ∈ s2`），转化为可达性。
2. 假设存在 `condensation_reachable s2 s1`，通过 `condensation_reachable_implies_reachable` 得到从 `s2` 到 `s1` 的顶点级反向路径。
3. 对顶点 `v ∈ s2` 和反向路径的起点 `u' ∈ s2`：由 SCC 内部连通性，二者相互可达。
4. 对反向路径的终点 `v' ∈ s1` 和 `u ∈ s1`：同理，二者相互可达。
5. 拼接得到 `u` 与 `u'` 相互可达 ⇒ `u' ∈ s1`（极大性）。
6. 但 `u' ∈ s2`，与 `s1 ≠ s2` 且分划互斥矛盾。

---

## 第七部分：图反转（Graph Reversal）

图反转是 **Kosaraju 算法**的理论基础。该算法利用"正向图 SCC = 反向图 SCC"这一性质，通过两次 DFS 计算 SCC。

### reverse_directed_graph（图反转）

```coq
Definition reverse_directed_graph {V E: Type}
  (dg: DirectedGraphType V E) : DirectedGraphType V E :=
  {| dg_vvalid := dg_vvalid dg;
     dg_evalid := dg_evalid dg;
     dg_source := dg_target dg;
     dg_target := dg_source dg;
     dg_listV  := dg_listV dg |}.
```

**定义**：交换每条边的起点和终点。顶点集、边集、顶点列表保持不变。

### 等价性引理

| 引理 | 内容 |
|------|------|
| `step_aux_reverse_equiv` | 反转图中的 `step_aux e x y` ↔ 原图中的 `step_aux e y x` |
| `step_reverse_equiv` | 反转图中的 `step x y` ↔ 原图中的 `step y x` |
| `reachable_reverse_equiv` | 反转图中的 `reachable x y` ↔ 原图中的 `reachable y x` |

`reachable_reverse_equiv` 的证明使用了 `reachable` 的 1-步归纳（`induction_1n`），在归纳步中通过 `step_reverse_equiv` 翻转方向。

### 反转的代数性质

| 引理 | 内容 |
|------|------|
| `reverse_reverse_id` | `reverse(reverse(dg)) = dg`（两次反转变回原图） |
| `reverse_preserves_valid` | 若 `dg` 良构，则 `reverse(dg)` 也良构 |

### SCC 在反转下的不变性（Kosaraju 算法的核心）

```coq
Lemma mutually_reachable_reverse : forall {V E: Type} (dg: DirectedGraphType V E) u v,
  mutually_reachable (g := dg) u v <-> mutually_reachable (g := reverse_directed_graph dg) u v.
```

**定理**：`u` 和 `v` 在原图中相互可达，当且仅当它们在反转图中相互可达。

**直觉**：反转图中从 `u` 到 `v` 的路径对应于原图中从 `v` 到 `u` 的路径，反之亦然。因此"双向都有路径"这一性质在反转下不变。

```coq
Corollary is_SCC_reverse : forall {V E: Type} (dg: DirectedGraphType V E) s,
  is_SCC (g := dg) s <-> is_SCC (g := reverse_directed_graph dg) s.
```

**推论**：`s` 是原图的 SCC ↔ `s` 是反转图的 SCC。证明直接展开 `is_SCC` 的三个条件，并通过 `mutually_reachable_reverse` 桥接两个方向的相互可达。

```coq
Corollary scc_partition_reverse : forall {V E: Type} (dg: DirectedGraphType V E) sccs,
  scc_partition (g := dg) sccs <-> scc_partition (g := reverse_directed_graph dg) sccs.
```

**推论**：SCC 分划在图反转下**不变**。这是 Kosaraju 算法的正确性基础——在反转图上计算 SCC 等价于在原图上计算 SCC。

> **关于 Type Class 实例**：反转图不需要额外的 Type Class 实例声明。因为 `reverse_directed_graph dg` 的结果类型仍然是 `DirectedGraphType V E`，已有的 6 个实例（`Graph`、`GValid`、`StepValid` 等）自动适用。这一设计使得反转操作与 GraphLib 框架无缝集成。

---

## 证明技术分析

### 1. 集合论的公理化风格

SCC 被定义为顶点的集合（`V -> Prop`），而非列表或其他具体表示。`is_SCC` 和 `scc_partition` 的三条公理（非空性、内部连通性、极大性；覆盖性、结构性、互斥性）构成了 SCC 理论的**公理化基础**——所有后续性质（唯一性、DAG 性、反转不变性）都从这些公理推导，不依赖任何具体的 SCC 计算算法。

### 2. 古典逻辑的广泛使用

文件在以下位置使用了 `Coq.Logic.Classical` 提供的排中律：

- `is_SCC_vvalid`：判断 `u = w` 来决定是否从非空 witness 继承 `vvalid`；
- `is_SCC_closed_under_mr`：判断 `u = v` 避免在自反情况重复推导 `vvalid`；
- `build_scc_partition_aux`：判断"已有 SCC 是否覆盖顶点 `a`"以及"`a` 是否有效"；
- `condensation_reachable_implies_reachable`：判断 `s1 = s2` 和 `s2 = s3` 来化简传递路径；
- `scc_partition_exists`：通过 `classic` 判断覆盖关系。

这些使用反映了 SCC 理论本身的**经典特征**——决定一个顶点是否被已有 SCC 覆盖需要判断存在性，而这没有构造性算法（除非给定具体的 SCC 计算过程）。

### 3. 边方向的有向性约束

`dg_step_aux` 强制 `dg_source dg e = x /\ dg_target dg e = y`，确保了边的方向不可逆转。这与 `tarjan.v` 的 `original_step_aux`（`step_fst = x ∧ step_snd = y ∨ step_fst = y ∧ step_snd = x`）形成对比。方向性约束是 SCC 理论的前提——在无向图中，整个连通分量就是一个 SCC，SCC 分划退化为连通分量。

### 4. 缩点图的传递闭包处理

`condensation_reachable` 以归纳谓词（`Inductive`）定义，而非使用 `reachable` 的传递闭包运算。这提供了更强的归纳原理，使 `condensation_reachable_implies_reachable` 的证明可以通过在 `condensation_reachable` 结构上直接归纳来完成。

---

## 与其他模块的关系

| 依赖模块 | 用途 |
|----------|------|
| `graph_basic` | `Graph`、`GValid`、`StepValid`、`NoEmptyEdge`、`StepUniqueDirected`、`FiniteGraph` 等基础 Type Class |
| `reachable_basic` | `reachable`（可达性）、`step`、`step_rt` 等定义 |
| `reachable_restricted` | `reachable_vvalid` 等受限可达性引理 |
| `Syntax` | 图形化记号（`reachable` 的 `etransitivity` / `transitivity_n1` 策略） |
| `SetsClass` | 集合运算记号（详细运算未直接使用，但 `Local Open Scope sets_scope.` 预留了集合论记号） |
| `Classical` | `classic`（排中律）用于多处的存在性/相等性判定 |
| `Lia` | 算术判定（文件仅 `Require Import Lia.`，当前证明中未涉及算术） |

---

## 设计特点

1. **公理化而非算法化**：`is_SCC` 和 `scc_partition` 以三公理形式给出，使得所有后续性质（唯一性、DAG 性、反转不变性）独立于具体的 SCC 计算算法。这支持了**算法无关的 SCC 理论**——无论是 Kosaraju 算法还是 Tarjan SCC 算法，其正确性证明都可以复用这些数学结论。

2. **有向 vs 无向的清晰分离**：`DirectedGraphType` 和 `dg_step_aux` 严格约束边方向，与 GraphLib 中已有的 `OriginalGraphType`（无向语义）互补。两者共享同一套 Type Class 基础设施（`Graph`、`StepValid`、`reachable` 等），但各取所需的附加约束。

3. **缩点图与代数性质**：`condensation_edge`、`condensation_reachable` 和 `condensation_is_acyclic` 构成了缩点图 DAG 的完整理论。这不是一个孤立的性质，而是与顶点级可达性通过 `condensation_reachable_implies_reachable` 紧密相连。

4. **图反转的代数完备性**：通过 `mutually_reachable_reverse` → `is_SCC_reverse` → `scc_partition_reverse`，文件建立了一条完整的**反转不变性传递链**。每个中间引理都是可复用的独立组件。

5. **经典存在性证明**：`scc_partition_exists` 使用静态顶点列表上的递归构造（`build_scc_partition_aux`），产生了与图枚举顺序相关的一个具体分划。这与 Kosaraju 算法（通过 DFS 序构造分划）或 Tarjan SCC 算法（通过 lowlink 值实时输出 SCC）形成理论上的呼应——存在性不依赖具体的构造方式。

---

## 与 tarjan.v 的对比总结

| 维度 | `tarjan.v`（桥判定） | `scc_basic.v`（SCC 理论） |
|------|----------------------|---------------------------|
| **图语义** | 无向图（`UndirectedGraph` 实例） | 有向图（`StepUniqueDirected` 实例） |
| **边方向** | 可反转（`step_sym`） | 严格固定（`dg_dir` 强制 `source/target`） |
| **核心定义** | `is_bridge`、`low` 值、`no_cross_edge` | `mutually_reachable`、`is_SCC`、`scc_partition` |
| **核心定理** | `tarjan：bridge ↔ dfn x < low y` | `condensation_is_acyclic`：缩点图无环 |
| **唯一性** | 无（low 值有唯一性但未形式化） | `scc_partition_unique`：SCC 分划唯一 |
| **图反转** | 不涉及（无向图反转无意义） | 完整的反转代数（`scc_partition_reverse`） |
| **算法应用** | Tarjan 桥算法 | Kosaraju / Tarjan SCC 算法 |
| **经典逻辑** | `classic`、`NNPP` | 主要使用 `classic` |
| **实例数** | 7 个（含 `UndirectedGraph`、`StepUniqueUndirected`） | 6 个（含 `StepUniqueDirected`，无 `UndirectedGraph`） |

---

## 潜在扩展方向

1. **Kosaraju 算法的命令式验证**：`scc_partition_reverse` 直接支持了 Kosaraju 算法的正确性——在反向图上计算 SCC 等价于在原图上计算。下一步可以将 DAST（命令式 DFS）与这些数学定义桥接。

2. **Tarjan SCC 算法的验证**：虽然 `tarjan.v` 处理的是桥判定（无向图背景），但 Tarjan SCC 算法（有向图背景，使用 lowlink 值）需要本文件提供的 SCC 理论基础。将该算法的命令式实现与 `is_SCC` / `scc_partition` 连接是自然的下一个目标。

3. **SCC 分划的构造性版本**：当前的 `scc_partition_exists` 使用排中律，可以进一步证明：若提供具体的 SCC 计算算法（如 Kosaraju 或 Tarjan SCC），则其输出的 SCC 列表确实满足 `scc_partition`。这将消除存在性证明中的经典逻辑依赖。

4. **缩点图的拓扑序**：当前只证明了缩点图是无环的 DAG。可以进一步证明：Kosaraju 算法中第二次 DFS 按照 SCC 的"结束时间"逆序（即拓扑序）遍历——这是许多基于 SCC 的算法（如 2-SAT）所需的关键性质。

5. **2-SAT 的可满足性**：利用 SCC 和缩点图的拓扑序，可以形式化证明 2-SAT 问题的 SCC-based 可满足性判定定理。
