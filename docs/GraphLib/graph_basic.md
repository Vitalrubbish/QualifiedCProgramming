# graph_basic.v — 图的基础 Type Classes

`graph_basic.v` 是整个 GraphLib 库的基石。它定义了一组相互关联的 Type Classes，以高度抽象的方式刻画了图、顶点、边及其各种结构性质。所有具体实现（邻接表、邻接矩阵等）都通过实例化这些 Type Classes 来接入库的其余部分。

## 文件导入

```coq
Require Import Coq.Lists.List.

Section graph_basic.

(* 所有定义均在此 Section 内 *)

End graph_basic.
```

该文件只依赖 `Coq.Lists.List`，确保基础层足够轻量。

---

## Type Class 层次总览

所有附加 Type Class 均以 `Graph G V E` 和 `GValid G` 为共同前置依赖，彼此之间无代码层面的继承或依赖关系（它们是完全正交的约束，可按需组合声明）：

```
                     Graph G V E          GValid G
                          \                  /
                           └───────┬────────┘
                                   │
      ┌──────────┬──────────┬──────┴──────┬──────────┬──────────┐
      │          │          │             │          │          │
  StepValid  NoEmptyEdge  Undirected   StepUnique  StepUnique  SimpleGraph
                          Graph        Directed    Undirected   FiniteGraph
```

所有依赖 `Graph G V E` 和 `GValid G` 的 Type Class 均声明为：

```coq
`{pg: Graph G V E} `{gv: GValid G}
```

即同时需要图的三要素（顶点、边、步进关系）和图的有效性判定。

> **注意**：虽然代码层面无依赖关系，但在语义上有一些自然的组合约定——例如 `StepUniqueUndirected` 通常与 `UndirectedGraph` 一同使用，`StepUniqueDirected` 适合有向图场景。详见下文[典型组合模式](#典型组合模式)。

---

## 核心 Type Class 详解

### 1. Graph — 图的基本抽象

```coq
Class Graph (G V E: Type) := {
  vvalid : G -> V -> Prop;
  evalid : G -> E -> Prop;
  step_aux : G -> E -> V -> V -> Prop;
}.
```

**类型参数**：

| 参数 | 含义 |
|------|------|
| `G` | 图的类型（任意表示，如邻接表、邻接矩阵等） |
| `V` | 顶点的类型 |
| `E` | 边的类型 |

**字段语义**：

| 字段 | 类型 | 含义 |
|------|------|------|
| `vvalid` | `G -> V -> Prop` | 顶点 `v` 在图 `g` 中是否有效（存在） |
| `evalid` | `G -> E -> Prop` | 边 `e` 在图 `g` 中是否有效（存在） |
| `step_aux` | `G -> E -> V -> V -> Prop` | 边 `e` 连接顶点 `x` 到顶点 `y`（有向） |

**设计要点**：

- `step_aux` 是有向的：`step_aux g e x y` 表示从 `x` 经边 `e` 到达 `y`。
- 将"有效"判定从"连接关系"中分离：`vvalid` / `evalid` 负责成员判断，`step_aux` 负责拓扑结构。两者正交，使得部分图（子图、生长中的图）能自然地表示为：某些顶点/边尚未加入 (`vvalid`/`evalid` 为假) 的状态。

---

### 2. GValid — 图自身有效性

```coq
Class GValid (G: Type) :=
  gvalid : G -> Prop.
```

**类型参数**：仅需 `G`（图的类型），不依赖 `Graph`。

**字段**：

| 字段 | 类型 | 含义 |
|------|------|------|
| `gvalid` | `G -> Prop` | 图 `g` 本身是否满足某种良构性条件 |

**设计意图**：

"图有效"可以表示多种不同级别的约束，例如：
- 所有顶点都在某个范围内（如邻接矩阵的索引不越界）；
- 图满足特定的数据不变量；
- 图已完成了某个初始化阶段。

抽象出 `GValid` 使得后续性质（如 `SimpleGraph`、`FiniteGraph` 等）都能统一地要求"在有效的图上成立"。

---

### 3. StepValid — 步进的有效性约束

```coq
Class StepValid (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  step_vvalid1 : forall g e x y, step_aux g e x y -> vvalid g x;
  step_vvalid2 : forall g e x y, step_aux g e x y -> vvalid g y;
  step_evalid  : forall g e x y, step_aux g e x y -> evalid g e;
}.
```

**三个字段**：

| 字段 | 含义 |
|------|------|
| `step_vvalid1` | 若 `e` 连接 `x→y`，则 `x` 是有效顶点 |
| `step_vvalid2` | 若 `e` 连接 `x→y`，则 `y` 是有效顶点 |
| `step_evalid` | 若 `e` 连接 `x→y`，则 `e` 是有效边 |

**直觉**：一条边只能连接存在的顶点，且边本身必须存在于图中。

`StepValid` 是最基本的"一致性"假设。几乎所有 GraphLib 的其他模块都依赖此约束。不满足 `StepValid` 的图实例（如 `step_aux` 可以引用不存在的顶点）将导致关于可达性、路径等的定理无法成立。

**在项目中的用法**：许多后续证明的上下文都包含 `{stepvalid: StepValid G V E}`，这是最常被引入的约束之一。例如 `rootedtree.v` 中：

```coq
Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}  (* ← 核心前提 *)
        ...
```

---

### 4. NoEmptyEdge — 无空白边

```coq
Class NoEmptyEdge (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  no_empty_edge : forall g e, gvalid g -> evalid g e -> exists x y, step_aux g e x y;
}.
```

**字段**：

| 字段 | 含义 |
|------|------|
| `no_empty_edge` | 在有效图中，每条有效边至少连接一对顶点 |

**直觉**：不存在"孤立"的边——每条边都必须至少连接两个顶点（在有向意义下，即至少有一个 `x` 和一个 `y` 使得 `step_aux g e x y`）。

**注意**：该约束不要求 `x ≠ y`——自环（self-loop）仍然是合法的边，只要它连接某个顶点到自身。

---

### 5. UndirectedGraph — 无向图（对称性）

```coq
Class UndirectedGraph (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  step_sym : forall g e x y, step_aux g e x y -> step_aux g e y x;
}.
```

**字段**：

| 字段 | 含义 |
|------|------|
| `step_sym` | 若边 `e` 连接 `x→y`，则也连接 `y→x` |

**设计要点**：

GraphLib 中的图在 `step_aux` 层面是**天然有向的**。要获得无向图的语义，需要额外声明 `UndirectedGraph` 实例。这样设计的好处：

1. 有向图和无向图共享同一套 `Graph` / `Path` / `StepValid` 基础设施。
2. 无向图的特殊性质（如边对称性导致的路径可逆性）仅在需要时才引入。
3. 无向图中仍有"有向步进"的概念，但 `step_sym` 保证了每步都可以双向走。

**典型用法**：`undirected/` 子目录下的模块（如 `tree.v`、`bigraph.v`）会引入此约束。

---

### 6. StepUniqueDirected — 有向边唯一确定端点

```coq
Class StepUniqueDirected (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  step_aux_unique : forall g e x1 y1 x2 y2,
    gvalid g -> step_aux g e x1 y1 -> step_aux g e x2 y2 ->
    x1 = x2 /\ y1 = y2;
}.
```

**字段**：

| 字段 | 含义 |
|------|------|
| `step_aux_unique` | 在有效图中，每条边 `e` 有唯一的源顶点和唯一的目标顶点 |

**直觉**：一条边不能同时连接 A→B 又连接 C→D。在基于边 ID 的图表示中，这是自然成立的（每条边有唯一的源和目标）。在基于邻接矩阵的表示中，这个约束排除了多重边。

**在项目中的用法**：`RootedTree` 一节中的证明引入了此约束（注意：`RootedTree` 的 Class 定义本身仅依赖 `Graph + GValid`，`StepUniqueDirected` 是在 Section 的 `Context` 中作为证明前提引入的）：

```coq
Context {stepvalid: StepValid G V E}
        {step_aux_unique: StepUniqueDirected G V E}
        {rootedtree: @RootedTree G V E pg gv}
```

有根树中"每个非根节点有唯一父节点"这一性质依赖此约束。

---

### 7. StepUniqueUndirected — 无向边唯一确定端点对（无序）

```coq
Class StepUniqueUndirected (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  step_aux_unique_undirected : forall g e x1 y1 x2 y2,
    gvalid g -> step_aux g e x1 y1 -> step_aux g e x2 y2 ->
    (x1 = x2 /\ y1 = y2) \/ (x1 = y2 /\ x2 = y1);
}.
```

**字段**：

| 字段 | 含义 |
|------|------|
| `step_aux_unique_undirected` | 每条边 `e` 有唯一的**无序**端点对 |

**与 `StepUniqueDirected` 的区别**：

| | `StepUniqueDirected` | `StepUniqueUndirected` |
|---|---|---|
| 允许的歧义 | 无 | 允许方向反转 |
| 结论 | `x1=x2 ∧ y1=y2` | `(x1=x2 ∧ y1=y2) ∨ (x1=y2 ∧ x2=y1)` |
| 适用图类型 | 有向图 | 无向图 |

**直觉**：在无向图中，边 `e` 连接顶点对 `{x, y}`（无序）。因此 `step_aux g e x y` 和 `step_aux g e y x` 描述的是同一条边的两个视角——约束必须允许这种"反转"。

---

### 8. SimpleGraph — 简单图

```coq
Class SimpleGraph (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  no_multiple_edge : forall g e1 e2 x y,
    gvalid g -> step_aux g e1 x y -> step_aux g e2 x y -> e1 = e2;
  no_self_loop : forall g e x,
    gvalid g -> ~ step_aux g e x x;
}.
```

**两个字段**：

| 字段 | 含义 |
|------|------|
| `no_multiple_edge` | 连接同一对顶点 `x→y` 的边至多一条 |
| `no_self_loop` | 不存在从顶点到自身的有向边（自环） |

**直觉**：经典图论中"简单图"的定义——无重边、无自环。在抽象类型表示中，重边是一个重要问题：如果边类型 `E` 可以有两个不同的值 `e1 ≠ e2` 都满足 `step_aux g e1 x y` 和 `step_aux g e2 x y`，则存在重边。

**注意**：`no_self_loop` 禁止的是 `step_aux g e x x`，即通过某条边从 `x` 到 `x`。这自然地排除了长度为 1 的自环。

**组合使用**：一个经典的无向简单图需要同时声明 `UndirectedGraph` 和 `SimpleGraph`（以及可能的 `StepUniqueUndirected`）。

---

### 9. FiniteGraph — 有限图（顶点可枚举）

```coq
Class FiniteGraph (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  listV : G -> list V;
  finite_vertices : forall g, gvalid g -> forall v, vvalid g v -> In v (listV g);
}.
```

**字段**：

| 字段 | 类型 | 含义 |
|------|------|------|
| `listV` | `G -> list V` | 给定图 `g`，返回其所有顶点的列表 |
| `finite_vertices` | `forall g, gvalid g -> forall v, vvalid g v -> In v (listV g)` | 每个有效顶点都出现在 `listV g` 中 |

**设计意图**：

`listV` 提供了顶点的**枚举**。`finite_vertices` 保证枚举是**完备**的（不漏掉任何有效顶点）。这个约束是许多经典算法（如 Dijkstra、Prim）的前提——它们需要遍历所有顶点。

**注意**：该定义仅要求顶点有限，不直接要求边有限。但在 `StepValid` 和 `NoEmptyEdge` 的前提下，可推导出有效边也在某个有限枚举中（每条边对应至少一对顶点）。

---

## Type Class 依赖关系

```coq
(* 无前置依赖 *)
Class GValid (G: Type) := ...

(* Graph 也独立 *)
Class Graph (G V E: Type) := ...

(* 以下均需 Graph + GValid *)
Class StepValid ...         `{pg: Graph G V E} `{gv: GValid G} := ...
Class NoEmptyEdge ...       `{pg: Graph G V E} `{gv: GValid G} := ...
Class UndirectedGraph ...   `{pg: Graph G V E} `{gv: GValid G} := ...
Class StepUniqueDirected ...`{pg: Graph G V E} `{gv: GValid G} := ...
Class StepUniqueUndirected .`{pg: Graph G V E} `{gv: GValid G} := ...
Class SimpleGraph ...       `{pg: Graph G V E} `{gv: GValid G} := ...
Class FiniteGraph ...       `{pg: Graph G V E} `{gv: GValid G} := ...
```

**`Graph` 和 `GValid` 的独立性**：

`Graph` 定义了"什么是图"，`GValid` 定义了"图是否良构"。两者正交——这种分离使得：
- 可以定义多层次的良构条件（宽松的、严格的），分别实现不同的 `GValid` 实例；
- `Graph` 可以独立于特定的良构标准被复用。

**逻辑上相互独立的约束**：

`StepValid`、`UndirectedGraph`、`SimpleGraph`、`FiniteGraph` 等彼此之间没有代码层面的继承或依赖关系（不同于面向对象中的多层继承），可以按需组合声明。

---

## 典型组合模式

### 有向简单图

```coq
Context {G V E: Type}
        `{Graph G V E}
        `{GValid G}
        `{StepValid G V E}
        `{StepUniqueDirected G V E}
        `{NoEmptyEdge G V E}
        `{SimpleGraph G V E}.
```

### 无向简单图

```coq
Context {G V E: Type}
        `{Graph G V E}
        `{GValid G}
        `{StepValid G V E}
        `{UndirectedGraph G V E}
        `{StepUniqueUndirected G V E}
        `{NoEmptyEdge G V E}
        `{SimpleGraph G V E}.
```

### 带有限顶点的图（算法前提）

```coq
Context {G V E: Type}
        `{Graph G V E}
        `{GValid G}
        `{StepValid G V E}
        `{FiniteGraph G V E}.
```

---

## 与 GraphLib 其他模块的关系

- **`Syntax.v`**：基于 `graph_basic.v`，提供 `step` (定义在 `reachable_basic.v` 中) 等语法糖和记号。
- **`reachable/reachable_basic.v`**：基于 `step_aux` 定义可达性 `reachable` 和其性质。
- **`reachable/path.v`**：基于 `vvalid` 和 `step_aux`，定义路径抽象 `Path` Type Class。
- **`directed/rootedtree.v`**：依赖 `Graph`、`GValid`、`StepValid`、`StepUniqueDirected`。
- **`undirected/undirected_basic.v`**：依赖 `Graph`、`GValid`、`UndirectedGraph`。
- **`subgraph/subgraph.v`**：依赖 `Graph`、`GValid`、`StepValid` 等。

所有下游模块通过 `Require Export GraphLib.graph_basic` 导入这些基础定义。

---

## 设计哲学

1. **高度抽象**：`Graph` 只要求三个命题函数，不预设任何具体数据结构。这使得同一个算法证明可以适用于邻接表、邻接矩阵、边列表等任何表示。

2. **约束分层**：不同性质被分解为独立的 Type Class（`StepValid`、`SimpleGraph`、`UndirectedGraph` 等），证明者只需引入实际需要的约束，避免不必要的假设污染上下文。

3. **Coq Type Classes 机制**：利用 `{}` 隐式参数和 `:>` 推导机制，证明中可以省略大量的样板前提。例如，引入 `{stepvalid: StepValid G V E}` 后，`step_vvalid1` 等引理自动可供 `eauto` 使用。

4. **正交性**：`Graph`（结构）、`GValid`（良构）、`StepValid`（一致性）三个维度正交——可以独立地精化或替换每个维度的定义。
