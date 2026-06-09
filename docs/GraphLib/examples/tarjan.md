# tarjan.v — Tarjan 桥算法验证

`tarjan.v` 是 GraphLib 库中一个重要的算法验证示例，用 Coq 形式化了 **Tarjan 算法中利用 DFS 树和 low 值判定桥边** 的核心定理。该文件不涉及具体的命令式实现（如栈操作、while 循环），而是纯粹在数学层面证明：**在 DFS 生成树中，一条树边是原图的桥当且仅当子节点的 low 值大于父节点的 dfn 值**。

## 文件导入

```coq
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.directed.rootedtree.
Require Import GraphLib.directed.dfstree.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.undirected.undirected_basic.
Require Import GraphLib.Syntax.
Require Import MaxMinLib.MaxMin MaxMinLib.Interface.
Require Import SetsClass.SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Arith.Arith.
```

该文件依赖 GraphLib 的多个子模块以及外部库（MaxMinLib 提供最小值语义、SetsClass 提供集合操作、Classical 提供排中律、Lia 提供算术判定）。

---

## 文件结构总览

```
tarjan.v
├── OriginalGraph — 原始图的数据结构与 Type Class 实例
│   ├── OriginalGraphType / OriginalGraphProp（Record 定义）
│   ├── original_step_aux（边的辅助关系）
│   ├── Graph / GValid 实例
│   ├── StepValid / NoEmptyEdge 实例
│   ├── StepUniqueUndirected 实例
│   ├── UndirectedGraph 实例
│   └── FiniteGraph 实例
│
├── RootedTree — DFS 生成树的数据结构与 Type Class 实例
│   ├── RootedTreeType / RootedTreeProp（Record 定义）
│   ├── rt_vvalid / rt_evalid / rt_step_aux（辅助定义）
│   ├── Graph / GValid 实例
│   ├── StepValid / NoEmptyEdge / StepUniqueDirected 实例
│   ├── FiniteGraph 实例
│   ├── RootedTree 实例（核心：证明树满足 RootedTree Type Class）
│   └── SimpleGraph 实例
│
├── Section TARJAN — 主定理及其依赖
│   ├── Context 声明（原图、DFS 树、dfn、low 等）
│   ├── no_cross_edge / reachable_visited 定义
│   │
│   ├── Section LOW — low 值的形式化定义与性质
│   │   ├── step_without_tree / subtree_step / low_tree 定义
│   │   ├── is_low_v / is_low / low_valid_v / low_valid 定义
│   │   ├── low 值的基本引理（low_valid1, low_valid2, low_intros）
│   │   ├── low_witness / low_bound（存在性与下界）
│   │   ├── 分解引理（subtree_decompose, subtree_step_decompose, low_tree_decompose）
│   │   ├── low_valid_induction（归纳关键引理）
│   │   └── low_valid_implies_is_low（low_valid ⇒ is_low）
│   │
│   ├── closed_offspring（封闭性子树引理）
│   ├── father_unreachable（父边不可达引理）
│   ├── tarjan（主定理：bridge ↔ dfn x < low y）
│   ├── tree_path_safe（树路径转化为非树边路径）
│   └── tarjan_trivial（副定理：非树边一定不是桥）
│
└── End TARJAN.
```

---

## 第一部分：OriginalGraph — 原始图的抽象建模

### 数据结构

```coq
Record OriginalGraphType {V E: Type} := {
  original_vvalid : V -> Prop;
  original_step: E -> Prop;
  original_step_fst: E -> V;
  original_step_snd: E -> V;
  original_listV: list V;
}.
```

`OriginalGraphType` 将图建模为一个 **边列表风格的表示**：每条边 `e` 有一个确定的起点 (`step_fst`) 和终点 (`step_snd`)，顶点的有效性由 `vvalid` 谓词判定，且需要提供一个有限的顶点列表 `listV`。

```coq
Record OriginalGraphProp {V E: Type} (origin: OriginalGraphType V E): Prop := {
  original_step_fst_valid: ...;
  original_step_snd_valid: ...;
  original_finite_vertices: ...;
}.
```

`OriginalGraphProp` 定义了良构条件：
- 每条有效边的两端点都是有效顶点；
- 每个有效顶点都出现在 `listV` 中（有限性）。

### Type Class 实例化

该文件为 `OriginalGraphType` 实例化了 **7 个 Type Class**，使其能够融入 GraphLib 的通用框架：

| Type Class | 关键证明思路 |
|------------|-------------|
| `Graph` | `step_aux` 通过 `original_step_aux` 定义，允许无向解释（正向或反向均可） |
| `GValid` | 直接使用 `OriginalGraphProp` |
| `StepValid` | 从 `step_aux` 的构造直接析取顶点/边的有效性 |
| `NoEmptyEdge` | 每条有效边提供其 `step_fst` 和 `step_snd` 作为端点 |
| `StepUniqueUndirected` | 边列表表示保证每条边有唯一的无序端点对 |
| `UndirectedGraph` | `original_step_aux` 的定义天然对称（允许正向/反向两种解释） |
| `FiniteGraph` | 直接使用 `original_listV` |

---

## 第二部分：RootedTree — DFS 生成树的建模

### 数据结构

```coq
Record RootedTreeType {V E: Type} := {
  vset: V -> Prop;
  theroot: V;
  parent: V -> V;
  edge: V -> option E;
  listV: list V;
}.
```

`RootedTreeType` 以 **父指针表示法** 建模有根树：
- `vset`：树中顶点的集合；
- `theroot`：根节点；
- `parent`：每个节点的父节点（根节点的父节点未定义，但 `root_no_edge` 保证了根节点无入边）；
- `edge`：每个节点指向其父节点的边（`option E`，根为 `None`）；
- `listV`：有限的顶点列表。

**记号定义**：

```coq
Notation "tree '.(vset)'" := (vset tree) (at level 1).
Notation "tree '.(root)'" := (theroot tree) (at level 1).
Notation "tree '.(parent)'" := (parent tree) (at level 1).
Notation "tree '.(edge)'" := (edge tree) (at level 1).
```

提供了简洁的成员访问语法。

### 良构条件 (`RootedTreeProp`)

```coq
Record RootedTreeProp {V E: Type} (rt: RootedTreeType V E) := {
  root_no_edge: rt.(edge) (rt.(root)) = None;
  edge_some: forall v, rt.(vset) v -> v <> rt.(root) -> exists e, rt.(edge) v = Some e;
  edge_unique: ...;
  root_valid: rt.(vset) rt.(theroot);
  parent_valid: forall v, rt.(vset) v -> rt.(vset) (rt.(parent) v);
  path_exist: forall v, rt.(vset) v -> clos_refl_trans (fun x y => rt.(parent) y = x) rt.(theroot) v;
  finite_vertices: forall v, rt.(vset) v -> In v rt.(listV);
}.
```

关键约束解读：

| 字段 | 含义 |
|------|------|
| `root_no_edge` | 根节点没有入边 |
| `edge_some` | 非根节点都有指向父节点的边 |
| `edge_unique` | 每条边唯一地标识一个子节点（即每个节点有唯一的入边） |
| `path_exist` | 从根到每个节点存在父指针链（树的连通性） |

### 嵌入 GraphLib 框架

通过三个辅助定义将树的内部表示映射到 GraphLib 的通用接口：

- `rt_vvalid` → `vset g`（树顶点即有效顶点）
- `rt_evalid` → 存在某个节点以该边作为入边
- `rt_step_aux` → 从子节点指向父节点的有向关系（`parent y = x ∧ edge y = Some e`）

> **注意**：在树中，`step_aux tree e x y` 的方向是 **y → x**（y 的父节点是 x）。这与 DFS 树的直觉一致——边从子节点指向父节点，而非从父到子。

**实例化的 Type Class**：

| Type Class | 简要说明 |
|------------|----------|
| `Graph` | 基于 `rt_vvalid`、`rt_evalid`、`rt_step_aux` |
| `GValid` | 使用 `RootedTreeProp` |
| `StepValid` | 从 `rt_step_aux` 构造直接推出 |
| `NoEmptyEdge` | 每条有效边对应一对父子节点 |
| `StepUniqueDirected` | 利用 `edge_unique` 证明每条边有唯一的方向 |
| `FiniteGraph` | 使用 `listV` |
| `RootedTree` | 核心实例，见下文 |
| `SimpleGraph` | 利用 `father_eunique` 和 `no_edge_refl` |

### RootedTree 实例（核心证明）

```coq
#[export]Instance Rootedtree_prop {V E: Type} :
  RootedTree (RootedTreeType V E) V E.
```

该实例为 `RootedTree` Type Class 的四个字段提供证明（`refine {|root := theroot;|}` 提供第 0 个字段 `root`）：

1. **`root_is_valid`**：根节点是有效顶点（直接使用 `RootedTreeProp` 的 `root_valid`）。
2. **`root_is_root`**：从根到每个有效树节点都存在可达路径，即 `vvalid tree x` 蕴含 `reachable tree tree.(root) x`。证明使用了 `path_exist` 提供的 `clos_refl_trans` 链，并在归纳步中通过 `edge_some` 构造 `step`。此步使用了古典逻辑的排中律 (`classic`)。
3. **`root_no_father`**：没有任何边指向根节点（直接使用 `RootedTreeProp` 的 `root_no_edge`，即根节点的 `edge` 为 `None`）。
4. **`father_eunique`**：每个节点有唯一的入边（直接使用 `RootedTreeProp` 的 `edge_unique`）。

---

## 第三部分：Section TARJAN — 算法核心

### Context 声明

```coq
Section TARJAN.
Context {V E: Type}
        (g: OriginalGraphType V E)
        (origin_gvalid: OriginalGraph_gvalid g)
        (dfstree: RootedTreeType V E)
        (tree_valid: Rootedtree_gvalid dfstree)
        (RootedTree_finitegraph: FiniteGraph (RootedTreeType V E) V E) (*hope to derived from sub*)
        (sub: subgraph dfstree g)
        (dfn: V -> nat)
        (dfnv: dfn_valid dfstree dfn)
        (low: V -> nat).
```

**上下文参数解读**：

| 参数 | 类型 | 含义 |
|------|------|------|
| `g` | `OriginalGraphType V E` | 原始无向图 |
| `origin_gvalid` | `OriginalGraph_gvalid g` | 原图是良构的 |
| `dfstree` | `RootedTreeType V E` | DFS 生成树 |
| `tree_valid` | `Rootedtree_gvalid dfstree` | 树是良构的 |
| `RootedTree_finitegraph` | `FiniteGraph (RootedTreeType V E) V E` | 树是有限图（希望可从 subgraph 导出） |
| `sub` | `subgraph dfstree g` | 树是原图的子图 |
| `dfn` | `V -> nat` | DFS 序（每个顶点的发现时间戳） |
| `dfnv` | `dfn_valid dfstree dfn` | dfn 值满足 DFS 性质（祖先的 dfn 小于后代的 dfn） |
| `low` | `V -> nat` | low 函数（待验证其满足 Tarjan 的 low 定义） |

### 关键假设

```coq
Definition no_cross_edge :=
  forall x y, reachable g theroot x -> reachable g theroot y ->
  step g x y -> reachable dfstree x y \/ reachable dfstree y x.

Definition reachable_visited: Prop :=
  forall u, reachable g theroot u -> vvalid dfstree u.

Context {nocross: no_cross_edge}
        {reacheable_is_visited: reachable_visited}.
```

- **`no_cross_edge`**（无横叉边）：在原图中，如果 `x` 和 `y` 都从根可达，且存在边 `x—y`，则在 DFS 树中 `x` 和 `y` 有祖先/后代关系。这是 DFS 生成树的核心性质——DFS 过程中不会出现跨越不同分支的边。
- **`reachable_visited`**：从根可达的每个原图顶点都在 DFS 树中。

---

## Section LOW — low 值的形式化

### 基础定义

```coq
Definition step_without_tree (x y: V): Prop :=
  exists e, step_aux g e x y /\ ~ evalid dfstree e.
```

**非树边**：在原图中存在但在 DFS 树中不存在的边。

```coq
Definition subtree_step (y: V): (V -> Prop) :=
  fun w => exists z, subtree y z /\ step_without_tree z w.
```

**子树外步**：存在 `y` 的后代 `z`，从 `z` 出发有一条非树边到达 `w`。

```coq
Definition low_tree (y: V) : V -> Prop := subtree y ∪ subtree_step y.
```

**low 树**：`y` 的子树中的所有顶点 ∪ 从子树出发通过非树边一步可达的顶点。这对应于 Tarjan 算法中 low 值的候选顶点集合。

### low 值的形式化

```coq
Definition is_low_v (v: V): nat -> Prop :=
  fun lowv => min_value_of_subset Nat.le (low_tree v) dfn lowv.
```

单个顶点 `v` 的 low 值 `lowv` 正确，当且仅当 `lowv` 是集合 `low_tree v` 在 `dfn` 映射下的最小值（使用 `Nat.le` 作为序）。

```coq
Definition is_low (fun_low: V -> nat): Prop :=
  forall v, vvalid dfstree v -> is_low_v v (fun_low v).
```

全局 low 函数正确，当且仅当每个有效树顶点都满足 `is_low_v`。

### 局部 low 有效性与全局 low 有效性的等价

```coq
Definition low_valid_v (v: V) (fun_low: V -> nat): Prop :=
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le (son v) fun_low ∪
     min_value_of_subset Nat.le (step_without_tree v ∪ [v]) dfn)
    (fun x => x) (fun_low v).
```

这是 low 值的 **递归定义**（局部性质），等价于：
```
low[v] = min( min{low[w] | w是v的儿子}, min{dfn[w] | w=v 或 w通过非树边与v相连} )
```

这正是 Tarjan 算法中计算 low 值的标准公式。

```coq
Definition low_valid (fun_low: V -> nat): Prop :=
  forall v, vvalid dfstree v -> low_valid_v v fun_low.
```

### low 值的基本性质

| 引理 | 内容 |
|------|------|
| `low_valid1` | 若 `low` 正确且 `z` 在 `y` 的子树中，则 `low y ≤ dfn z` |
| `low_valid2` | 若 `low` 正确且存在从 `z`（子树内）到 `w` 的非树边，则 `low y ≤ dfn w` |
| `low_intros` | `low y` 的来源只有两种可能：要么来自子树内部（`low y = dfn z`），要么来自一条非树边（`low y = dfn w`） |
| `low_witness` | 若 `n` 是 `w` 的 low 值，则存在 `x` 使得 `dfn x = n` 且 `x ∈ low_tree w` |
| `low_bound` | 若 `n` 是 `w` 的 low 值且 `x ∈ low_tree w`，则 `n ≤ dfn x` |

### 分解引理

```coq
Theorem low_tree_decompose (y: V) (Hvy: vvalid dfstree y):
  low_tree y == [y] ∪ step_without_tree y ∪
  (fun w => exists z, son y z /\ low_tree z w).
```

**`low_tree` 的递归分解**：`y` 的 low 树等于 `{y}` ∪ `y` 的非树边邻居 ∪ 各儿子的 low 树的并集。这是 low 值递归计算的集合论基础。

证明过程分三步：
1. `subtree_decompose`：子树可以分解为 `{y}` ∪（各儿子的子树的并）
2. `subtree_step_decompose`：子树外步可以分解为 `y` 自身的非树边步 ∪ 各儿子的子树外步
3. 将两者组合并调整集合运算次序得到最终结果

### low 值局部定义与全局定义的等价性

```coq
Lemma low_valid_induction (v: V) (fun_low: V -> nat)
  (IHv: forall w, son v w -> is_low_v w (fun_low w)):
  min_value_of_subset Nat.le (son v) fun_low ==
  min_value_of_subset Nat.le ((fun w => exists z, son v z /\ low_tree z w)) dfn.
```

**核心归纳引理**：如果 `fun_low` 在各个儿子上正确（即 `is_low_v w (fun_low w)`），则两边的 min 值等价——一边用 `fun_low` 在儿子上取值，另一边用 `dfn` 在各儿子的 `low_tree` 上取值。

```coq
Lemma low_valid_implies_is_low (fun_low: V -> nat):
  low_valid fun_low -> is_low fun_low.
```

**局部→全局**：利用 `rooted_tree_induction_bottom_up`（自底向上归纳），从 `low_valid`（递归定义）推导出 `is_low`（集合最小值定义）。这是连接两种 low 定义的桥梁。

---

## 主定理：Tarjan 桥判定

### 核心引理：封闭性子树

```coq
Lemma closed_offspring: forall x y z e,
  dfn x < low y ->
  step_aux dfstree e x y ->
  reachable_without g e y z ->
  subtree y z.
```

**含义**：如果 `dfn x < low y`（即 low y 严格大于父节点 x 的 dfn），则从 y 出发不经过边 e 所能到达的所有顶点 z 都仍然在 y 的子树内。这意味着**子树 y 没有通过非树边"逃逸"到子树外部**。

**证明策略**：
1. 对 `reachable_without` 路径进行归纳。
2. 在归纳步中，利用 **无横叉边**（`no_cross_edge`）假设：边 `(z, w)` 只能是前向边或后向边（即 `subtree z w` 或 `subtree w z`）。
3. 若 `subtree z w`（w 是 z 的后代），简单传递即可。
4. 若 `subtree w z`（w 是 z 的祖先），需进一步分析 w 与 y 的关系：
   - 若 `subtree y w`：得证。
   - 否则（y 是 w 的后代）：结合 `dfn x < low y` 和 DFS 性质推出矛盾——若 w→z 是树边则违反树的无环性，若 w→z 是非树边则 `low y ≤ dfn w < dfn x`，与 `dfn x < low y` 矛盾。

### 父边不可达引理

```coq
Lemma father_unreachable: forall x y e,
  dfn x < low y ->
  step_aux dfstree e x y ->
  ~ reachable_without g e y x.
```

**含义**：当 `dfn x < low y` 时，从 y 出发无法不经过边 e 回到 x。这是 `closed_offspring` 的直接推论——如果 y 能回到 x，则 x 在 y 的子树中，违反树的偏序性质（`offspring_partial_order`）。

### 主定理：tarjan

```coq
Lemma tarjan: forall x y e,
  step_aux dfstree e x y ->
  (is_bridge g e <-> dfn x < low y).
```

**定理陈述**：对于 DFS 树中的边 `e = (x, y)`（方向为子→父），**e 是原图的桥当且仅当 `dfn x < low y`**。

这是 Tarjan 算法中最核心的理论结果。

**证明结构**（两个方向）：

#### 方向一（`bridge → dfn x < low y`）

使用反证法 (`NNPP`)。假设 `dfn x ≥ low y`，则根据 `low_intros`，`low y` 有且仅有两类来源：

- **情况 1**：`low y` 来自 y 子树内部某顶点 z 的 dfn。此时 `dfn x ≥ low y = dfn z`，但由 DFS 性质有 `dfn x < dfn z`（x 是祖先），矛盾。

- **情况 2**：`low y` 来自一条非树边 `(z, w)`（z 在 y 子树内，w 有更小的 dfn）。利用 **无横叉边**假设，w 与 z 有祖先/后代关系：
  - 若 w 是 z 的后代：`dfn w ≥ dfn z`，与 `low y ≤ dfn w < dfn z` 矛盾。
  - 若 z 是 w 的后代（即 w 是祖先）：构造不经过 e 的替代路径 `y → ... → z → w → ... → x`，证明 e 不是桥，矛盾。
    - 子情况 2.1（w = x）：回边直接指向 x，形成环。
    - 子情况 2.2（w 是 x 的真祖先）：存在路径绕过 e。

#### 方向二（`dfn x < low y → bridge`）

利用 `father_unreachable` 引理：如果 `dfn x < low y`，则从 y 无法不经过 e 到达 x，因此删除 e 后图不连通，即 e 是桥。结合 `no_multiple_edge`（无重边）和 `step_aux_unique_undirected` 处理边的方向歧义。

---

## 副定理：非树边的桥判定

```coq
Lemma tarjan_trivial: forall e,
  reachable_edge theroot e ->
  reachable_visited ->
  ~ evalid dfstree e ->
  ~ is_bridge g e.
```

**定理陈述**：在 DFS 树中不存在的边（非树边）不可能是桥。

**证明思路**：
```
        root
       /    \
      :      : (tree paths)
      v      v
      x ---- y
         e (non-tree edge)
```

若 e 是桥，则删除 e 后 x 和 y 不连通。但存在绕过 e 的树路径：从 root 到 x 和从 root 到 y 各有一条树路径，连接起来形成了替代路径。使用 `tree_path_safe` 将树路径转化为 `reachable_without` 路径（因为树边都不等于 e）。

---

## 证明技术分析

### 1. 自底向上的树归纳

`low_valid_implies_is_low` 使用了 `rooted_tree_induction_bottom_up`，这是一种针对有根树的归纳原理：先证明叶子节点（无儿子的节点）满足性质，再证明若所有儿子满足性质则父节点也满足。

### 2. 集合论的广泛使用

`SetsClass` 提供了类似集合的表示（`V -> Prop`），配合 `∪`、`==`（外延等价）、`[v]`（单点集）等记号，使得涉及多重集合运算的推导（如 `low_tree_decompose`）直观可读。

### 3. MaxMinLib 的最小值抽象

`min_value_of_subset` 来自 MaxMinLib，提供了在任意集合上定义最小值的抽象接口。这使得 `is_low_v` 和 `low_valid_v` 的定义高度数学化，且与具体的实现细节解耦。

### 4. 古典逻辑的使用

文件在多处使用了 `Coq.Logic.Classical` 提供的排中律 (`classic`) 和双重否定消除 (`NNPP`)。这表明验证采用了经典逻辑而非构造逻辑——这与算法的性质一致（Tarjan 算法本身就是经典的）。

### 5. 边类型参数化

整个证明在 `{V E: Type}` 上参数化，不依赖边的具体类型。这使得证明可以适用于任意边表示（自然数索引、字符串标签等）。

---

## 与其他模块的关系

| 依赖模块 | 用途 |
|----------|------|
| `graph_basic` | `Graph`、`GValid`、`StepValid`、`NoEmptyEdge`、`SimpleGraph`、`FiniteGraph` 等基础 Type Class |
| `reachable_basic` | `reachable`（可达性）、`step`、`reachable_without` 等定义 |
| `reachable_restricted` | `reachable_without_sym`、`reachable_without_step_offspring1/2` 等受限可达性引理 |
| `rootedtree` | `RootedTree` Type Class 及 `rooted_tree_induction_bottom_up` |
| `dfstree` | `dfn_valid` Type Class 及 `dfn_valid_offspring`（dfn 值满足祖先 < 后代） |
| `subgraph` | `subgraph` 关系和 `sub_reachable`、`sub_reachable_without` 引理 |
| `undirected_basic` | `step_sym`（边对称性） |
| `Syntax` | 图形化记号 |
| `MaxMinLib` | `min_value_of_subset` 及相关引理 |
| `SetsClass` | 集合运算记号（`∪`、`==`、`[·]`） |

---

## 设计特点

1. **关注点分离**：`OriginalGraph` 和 `RootedTree` 分别定义了各自的数据结构和良构条件，然后通过 GraphLib 的 Type Class 机制统一接入，使得 TARJAN 部分的证明可以复用 GraphLib 的通用引理。

2. **代数的而非计算的**：该文件不涉及 DFS 的具体执行过程（栈、递归等），而是从 DFS 树必须满足的数学性质（`no_cross_edge`、`dfn_valid`）出发，直接证明 bridge 判定条件。这是 **公理化方法**——给定了 DFS 树的性质，而不关心它是如何生成的。

3. **low 值的两种刻画**：既给出了 low 值的全局/语义定义（`is_low`：集合 dfn 的最小值），也给出了局部/递归定义（`low_valid`：通过儿子递归计算），并证明了二者等价。这既方便了直观理解，又保证了与算法实现的一致性。

4. **严格的桥定义**：`is_bridge` 要求移除边后其端点不连通，证明中精确地构造了替代路径来证明某条边不是桥。

---

## 潜在改进方向

1. **`no_cross_edge` 的生成**：当前 `no_cross_edge` 是作为 Context 假设引入的，而非从 DFS 算法的执行过程推导出来。一个完整的验证应该证明 DFS 算法确实产生满足 `no_cross_edge` 的树。

2. **low 值的计算过程**：类似地，`low` 函数是作为参数传入的，未形式化其具体的计算过程（递归遍历树并取 min）。

3. **命令式实现的验证**：将本文的数学定理桥接到一个具体的 C 语言实现（如 `dfs` 数组和 `low` 数组的更新），完成端到端的验证。
