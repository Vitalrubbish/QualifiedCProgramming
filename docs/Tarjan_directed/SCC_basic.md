# SCC_basic — 定义与定理参考

**Author**: Vitalrubbish
**Date**: 2026-06-14

本文档整理 `SeparationLogic/algorithms/Tarjan_directed/SCC_basic.v` 中的所有定义、引理与定理，供后续开发参考。

---

## Context 与依赖

整个文件位于 `Section SCC_DEFS` 下，共享以下 Context：

```coq
Context {V E: Type} (g: OriginalGraphType V E)
        (Hgvalid: OriginalGraphProp V E g)
        (finite_vertices: forall v, original_vvalid g v -> In v (original_listV g)).
```

依赖的库：

| Import | 用途 |
|--------|------|
| `Coq.Lists.List` | `In`、列表操作 |
| `Coq.Logic.Classical_Prop` | `classic` 排中律 |
| `Coq.Logic.ClassicalDescription` | `excluded_middle_informative` |
| `Coq.Logic.PropExtensionality` | `propositional_extensionality` |
| `Coq.Logic.FunctionalExtensionality` | `functional_extensionality` |
| `Coq.Relations.Relations` | `clos_refl_trans` 自反传递闭包 |
| `SetsClass.SetsClass` | 集合记法 |
| `GraphLib.graph_basic` | `OriginalGraphType`, `OriginalGraphProp` 等 |
| `GraphLib.Syntax` | 语法导出 |
| `GraphLib.examples.tarjan` | `original_vvalid`, `original_step`, `original_step_fst`, `original_step_snd`, `original_listV` |

---

## Section 0: dg_step / dg_reachable — 有向图原语

### 定义

#### `dg_step`

```coq
Definition dg_step (g: OriginalGraphType V E) (x y: V): Prop :=
  exists e, original_step g e /\
            original_step_fst g e = x /\
            original_step_snd g e = y.
```

**语义**：存在一条有向边从 `x` 到 `y`。不同于无向 `step`（对称），`dg_step` 是不对称的——仅 `original_step_fst → original_step_snd` 方向。

#### `dg_reachable`

```coq
Definition dg_reachable (g: OriginalGraphType V E) (x y: V): Prop :=
  @Coq.Relations.Relation_Operators.clos_refl_trans V (dg_step g) x y.
```

**语义**：`dg_step` 的自反传递闭包，即存在一条（可能为空的）有向路径从 `x` 到 `y`。

### 引理

#### `dg_reachable_refl`

```coq
Lemma dg_reachable_refl : forall x,
  original_vvalid g x -> dg_reachable g x x.
```

**语义**：有效顶点到自身有向可达（零步路径）。需要顶点有效性前提。

#### `dg_reachable_refl'`

```coq
Lemma dg_reachable_refl' : forall x, dg_reachable g x x.
```

**语义**：无条件自反性——`clos_refl_trans` 对所有顶点（含无效顶点）都自反。用于不需要有效性信息的归纳场景。

#### `dg_reachable_trans`

```coq
Lemma dg_reachable_trans : forall x y z,
  dg_reachable g x y -> dg_reachable g y z -> dg_reachable g x z.
```

**语义**：有向可达的传递性（`clos_refl_trans` 的 `rt_trans`）。

#### `dg_reachable_step`

```coq
Lemma dg_reachable_step : forall x y,
  dg_step g x y -> dg_reachable g x y.
```

**语义**：单步有向边蕴含一步有向可达（`clos_refl_trans` 的 `rt_step`）。

#### `dg_step_vvalid`

```coq
Lemma dg_step_vvalid : forall x y,
  dg_step g x y -> original_vvalid g x /\ original_vvalid g y.
```

**语义**：有向边的两端点都是有效顶点。证明依赖 `Hgvalid` 的 `original_step_fst_valid` 和 `original_step_snd_valid`。

#### `dg_reachable_vvalid`

```coq
Lemma dg_reachable_vvalid : forall x y,
  x <> y -> dg_reachable g x y -> original_vvalid g x /\ original_vvalid g y.
```

**语义**：非平凡有向可达路径的两端点都是有效顶点。`x <> y` 前提是必要的——`clos_refl_trans` 的零步情况对无效顶点也成立。

#### `dg_step_reachable_reachable`

```coq
Lemma dg_step_reachable_reachable : forall x y z,
  dg_step g x y -> dg_reachable g y z -> dg_reachable g x z.
```

**语义**：有向边 + 有向可达 = 有向可达（在 `dg_reachable` 前拼接一步 `dg_step`）。

#### `dg_reachable_step_reachable`

```coq
Lemma dg_reachable_step_reachable : forall x y z,
  dg_reachable g x y -> dg_step g y z -> dg_reachable g x z.
```

**语义**：有向可达 + 有向边 = 有向可达（在 `dg_reachable` 后拼接一步 `dg_step`）。

---

## Section 1: mutually_reachable — 相互可达性

### 定义

#### `mutually_reachable`

```coq
Definition mutually_reachable (g: OriginalGraphType V E) (u v: V) : Prop :=
  dg_reachable g u v /\ dg_reachable g v u.
```

**语义**：两个顶点相互有向可达——即存在从 `u` 到 `v` 的有向路径，也存在从 `v` 到 `u` 的有向路径。这是有效顶点集上的等价关系。

### 引理

#### `mutually_reachable_refl`

```coq
Lemma mutually_reachable_refl : forall u,
  original_vvalid g u -> mutually_reachable g u u.
```

**语义**：有效顶点与自身相互可达。

#### `mutually_reachable_sym`

```coq
Lemma mutually_reachable_sym : forall u v,
  mutually_reachable g u v -> mutually_reachable g v u.
```

**语义**：相互可达的对称性——由定义的合取交换直接得。

#### `mutually_reachable_trans`

```coq
Lemma mutually_reachable_trans : forall u v w,
  mutually_reachable g u v -> mutually_reachable g v w -> mutually_reachable g u w.
```

**语义**：相互可达的传递性——两个方向各用一次 `dg_reachable_trans`。

#### `mutually_reachable_vvalid_l`

```coq
Lemma mutually_reachable_vvalid_l : forall u v,
  u <> v -> mutually_reachable g u v -> original_vvalid g u.
```

**语义**：非平凡相互可达的左端点有效。

#### `mutually_reachable_vvalid_r`

```coq
Lemma mutually_reachable_vvalid_r : forall u v,
  u <> v -> mutually_reachable g u v -> original_vvalid g v.
```

**语义**：非平凡相互可达的右端点有效。

#### `dg_reachable_mutually_reachable`

```coq
Lemma dg_reachable_mutually_reachable : forall u v,
  dg_reachable g u v -> dg_reachable g v u -> mutually_reachable g u v.
```

**语义**：从两个方向的有向可达构造相互可达——`mutually_reachable` 的构造器。

---

## Section 2: is_SCC — SCC 判定谓词

### 定义

#### `is_SCC`

```coq
Definition is_SCC (g: OriginalGraphType V E) (s: V -> Prop) : Prop :=
  (exists v, s v /\ original_vvalid g v) /\
  (forall u v, s u -> s v -> mutually_reachable g u v) /\
  (forall u v, s u -> original_vvalid g v -> mutually_reachable g u v -> s v).
```

**语义**：`s` 是图 `g` 的一个强连通分量（SCC），满足三个条件：

| 条件 | 表述 | 含义 |
|------|------|------|
| 非空性 | `exists v, s v /\ original_vvalid g v` | SCC 至少包含一个有效顶点 |
| 内部 MR | `forall u v, s u -> s v -> mutually_reachable g u v` | SCC 内任意两点相互可达 |
| 极大性 | `forall u v, s u -> original_vvalid g v -> mutually_reachable g u v -> s v` | 任何与 SCC 成员相互可达的有效顶点也在 SCC 内 |

### 引理

#### `is_SCC_vvalid`

```coq
Lemma is_SCC_vvalid : forall s u,
  is_SCC g s -> s u -> original_vvalid g u.
```

**语义**：SCC 中所有顶点都是有效顶点。证明分 `u = v0`（非空性证人）和 `u <> v0`（内部 MR + `mutually_reachable_vvalid_l`）两情况。

#### `is_SCC_closed_under_mr`

```coq
Lemma is_SCC_closed_under_mr : forall s u v,
  is_SCC g s -> s u -> mutually_reachable g u v -> s v.
```

**语义**：SCC 在相互可达下封闭——若 `u` 在 SCC 中且 `u` 与 `v` 相互可达，则 `v` 也在同一 SCC 中。

#### `is_SCC_mutually_reachable_in`

```coq
Lemma is_SCC_mutually_reachable_in : forall s u v,
  is_SCC g s -> s u -> mutually_reachable g u v ->
  s v /\ mutually_reachable g u v.
```

**语义**：若 `u` 在 SCC 中且与 `v` 相互可达，则 `v` 也在 SCC 中，且相互可达关系保持。

#### `is_SCC_maximal`

```coq
Lemma is_SCC_maximal : forall s1 s2,
  is_SCC g s1 -> is_SCC g s2 ->
  (forall v, s1 v -> s2 v) -> (forall v, s2 v -> s1 v).
```

**语义**：SCC 的极大性——若 SCC `s1` 包含于 SCC `s2`（逐点），则两者相等（反向包含也成立）。这是 SCC 唯一性的关键引理。

#### `is_SCC_extensional`

```coq
Lemma is_SCC_extensional : forall s1 s2,
  is_SCC g s1 -> is_SCC g s2 ->
  (forall v, s1 v <-> s2 v) -> (forall v, s1 v = s2 v).
```

**语义**：两个逐点等价的 SCC 是外延相等的（使用 `propositional_extensionality`）。

#### `mutually_reachable_is_SCC`

```coq
Lemma mutually_reachable_is_SCC : forall u,
  original_vvalid g u -> is_SCC g (fun v => mutually_reachable g u v).
```

**语义**：从任意有效顶点 `u` 出发，所有与 `u` 相互可达的顶点构成一个 SCC。这是构造包含指定顶点的唯一 SCC 的基础。

---

## Section 3: scc_partition — SCC 划分

### 定义

#### `scc_partition`

```coq
Definition scc_partition (g: OriginalGraphType V E) (sccs: list (V -> Prop)) : Prop :=
  (forall v, original_vvalid g v -> exists s, In s sccs /\ s v) /\
  (forall s, In s sccs -> is_SCC g s) /\
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v ->
    (forall w, s1 w = s2 w)).
```

**语义**：`sccs` 是图 `g` 的一个有效 SCC 划分，满足三个条件：

| 条件 | 表述 | 含义 |
|------|------|------|
| 覆盖性 | `forall v, original_vvalid g v -> exists s, In s sccs /\ s v` | 每个有效顶点属于某个 SCC |
| 正确性 | `forall s, In s sccs -> is_SCC g s` | 列表中每个集合确实是 SCC |
| 互斥性 | `forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> (forall w, s1 w = s2 w)` | 不同 SCC 不相交——任一公共顶点推出两 SCC 外延相等 |

### 引理

#### `scc_partition_disjoint`

```coq
Lemma scc_partition_disjoint : forall sccs s1 s2,
  scc_partition g sccs -> In s1 sccs -> In s2 sccs -> s1 <> s2 ->
  forall v, ~ (s1 v /\ s2 v).
```

**语义**：不同 SCC 严格不相交——不存在同时属于两个不同 SCC 的顶点。

#### `mutually_reachable_same_SCC`

```coq
Lemma mutually_reachable_same_SCC : forall u v sccs,
  original_vvalid g u -> scc_partition g sccs -> mutually_reachable g u v ->
  exists s, In s sccs /\ s u /\ s v.
```

**语义**：相互可达的两个顶点属于同一个 SCC。证明：由覆盖性得 `u` 属于某 `s`，再用 `is_SCC_closed_under_mr` 推出 `v` 也属于 `s`。

#### `scc_partition_unique_SCC`

```coq
Lemma scc_partition_unique_SCC : forall u sccs,
  original_vvalid g u -> scc_partition g sccs ->
  exists! s, In s sccs /\ s u.
```

**语义**：每个有效顶点属于**唯一**的 SCC。存在性由覆盖性；唯一性由互斥性。

### 定理

#### `scc_partition_exists`

```coq
Theorem scc_partition_exists :
  exists sccs, scc_partition g sccs.
```

**语义**：对任意满足 Context 的有向图，SCC 划分总是存在的（构造性存在证明）。

**证明概要**：

1. 对每个有效顶点 `v`，定义 `scc_of v := fun w => mutually_reachable g v w`；
2. 由 `mutually_reachable_is_SCC`，每个 `scc_of v` 是 SCC；
3. 对 `original_listV g` 做归纳，维护已收集的互不相同的 `scc_of` 列表：
   - 对当前顶点 `x`，用 `excluded_middle_informative` 判定 `original_vvalid g x /\ ~ exists s, In s acc /\ s x`；
   - 若 `x` 有效且未被已收集的 SCC 覆盖，则将 `scc_of x` 加入列表；
4. 验证三个条件：覆盖性（归纳假设 + `finite_vertices`）、正确性（各 `scc_of` 是 SCC）、互斥性（利用 `is_SCC_extensional` 处理重叠情况）。

所需公理：`classic`（排中律）、`excluded_middle_informative`、`propositional_extensionality`、`functional_extensionality`。

---

## Section 4: condensation — 缩点图与 DAG 性质

### 定义

#### `condensation_edge`

```coq
Definition condensation_edge (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ dg_step g u v.
```

**语义**：缩点图中从 SCC `s1` 到 SCC `s2` 存在有向边，当且仅当：
- `s1` 和 `s2` 都是 `sccs` 中的 SCC；
- `s1 ≠ s2`（排除自环——SCC 内部边不产生缩点边）；
- 存在原图中一条有向边从 `s1` 中某顶点指向 `s2` 中某顶点。

#### `condensation_path`

```coq
Inductive condensation_path (sccs: list (V -> Prop)) :
  (V -> Prop) -> (V -> Prop) -> Prop :=
  | cp_edge : forall s1 s2,
      condensation_edge sccs s1 s2 ->
      condensation_path sccs s1 s2
  | cp_trans : forall s1 s2 s3,
      condensation_path sccs s1 s2 ->
      condensation_path sccs s2 s3 ->
      condensation_path sccs s1 s3.
```

**语义**：缩点图中存在从 SCC `s1` 到 SCC `s2` 的路径（至少一步）——即 `condensation_edge` 的传递闭包。使用归纳谓词而非 `clos_refl_trans`，因为缩点图顶点类型为 `V -> Prop`，不是 `OriginalGraphType` 的 `V`。

#### `condensation_reachable`

```coq
Definition condensation_reachable (sccs: list (V -> Prop))
  (s1 s2: V -> Prop) : Prop :=
  s1 = s2 \/ condensation_path sccs s1 s2.
```

**语义**：缩点图中从 SCC `s1` 到 SCC `s2` 的可达性（含零步情况 `s1 = s2`）。

### 引理

#### `dg_step_SCC_classify`

```coq
Lemma dg_step_SCC_classify : forall sccs u v,
  scc_partition g sccs -> dg_step g u v ->
  (exists s, In s sccs /\ s u /\ s v)
  \/
  (exists s1 s2,
    In s1 sccs /\ In s2 sccs /\ s1 u /\ s2 v /\
    condensation_edge sccs s1 s2).
```

**语义**：原图中每条有向边属于以下两种情况之一：
- **同 SCC 内部**：`u` 和 `v` 属于同一个 SCC（不产生缩点边）；
- **跨 SCC**：`u` 和 `v` 属于不同 SCC（产生一条缩点边）。

这是桥接原图结构与缩点图结构的关键引理。

#### `condensation_path_to_dg_reachable`

```coq
Lemma condensation_path_to_dg_reachable : forall sccs s1 s2 u v,
  scc_partition g sccs ->
  condensation_path sccs s1 s2 ->
  s1 u -> s2 v ->
  dg_reachable g u v.
```

**语义**：缩点图中从 `s1` 到 `s2` 的路径蕴含原图中从 `s1` 的任意代表顶点 `u` 到 `s2` 的任意代表顶点 `v` 的有向可达。证明对 `condensation_path` 做归纳：`cp_edge` 情况利用 SCC 内部 MR 在各 SCC 内移动 + `dg_step` 跨 SCC；`cp_trans` 情况利用 SCC 的非空性取中间证人顶点。

#### `condensation_edge_oneway`

```coq
Lemma condensation_edge_oneway : forall sccs s1 s2 u v,
  scc_partition g sccs ->
  condensation_edge sccs s1 s2 ->
  s1 u -> s2 v ->
  dg_reachable g u v /\ ~ mutually_reachable g u v.
```

**语义**：缩点边产生单向可达但**不**产生相互可达——这正是 SCC 划分极大性的体现：若两端点相互可达，则两 SCC 应合并为一个。

### 定理

#### `condensation_is_acyclic`

```coq
Theorem condensation_is_acyclic : forall sccs,
  scc_partition g sccs ->
  forall s1 s2,
    condensation_edge sccs s1 s2 ->
    ~ condensation_reachable sccs s2 s1.
```

**语义**：缩点图是无环的（DAG）——若存在缩点边 `s1 → s2`，则不存在从 `s2` 回到 `s1` 的缩点可达路径。

**证明**：反证法。假设存在 `condensation_edge s1 → s2` 和 `condensation_reachable s2 →* s1`：
- 若 `s2 = s1`：与 `condensation_edge` 的 `s1 <> s2` 矛盾；
- 若存在 `condensation_path s2 →* s1`：取 `u ∈ s1, v ∈ s2`，由 `condensation_path_to_dg_reachable` 得 `dg_reachable g v u`，结合 `dg_step g u v`（从 `condensation_edge` 中的原图边），得 `mutually_reachable g u v`。但 `condensation_edge_oneway` 断言 `~ mutually_reachable g u v`，矛盾。

#### `condensation_no_cycle`

```coq
Theorem condensation_no_cycle : forall sccs,
  scc_partition g sccs ->
  ~ exists s1 s2,
    condensation_edge sccs s1 s2 /\
    condensation_path sccs s2 s1.
```

**语义**：缩点图不存在包含至少一条缩点边的有向环——`condensation_is_acyclic` 的等价表述。

---

## Section 5: reverse_graph — 图反转与 SCC 不变性

### 定义

#### `reverse_graph`

```coq
Definition reverse_graph (g: OriginalGraphType V E) : OriginalGraphType V E :=
  {|
    original_vvalid   := g.(original_vvalid);
    original_step     := g.(original_step);
    original_step_fst := g.(original_step_snd);
    original_step_snd := g.(original_step_fst);
    original_listV    := g.(original_listV);
  |}.
```

**语义**：交换每条边的方向——`original_step_fst` 和 `original_step_snd` 互换。顶点集（`original_vvalid`）、边集（`original_step`）和顶点列表（`original_listV`）保持不变。

### 引理

#### `reverse_graph_gvalid`

```coq
Lemma reverse_graph_gvalid :
  @OriginalGraphProp V E (reverse_graph g).
```

**语义**：反转图仍满足 `OriginalGraphProp`（即仍然是有效图）。证明：`Hgvalid` 中的 `original_step_fst_valid` 和 `original_step_snd_valid` 在交换后仍然成立；`original_finite_vertices` 不变。

#### `dg_step_reverse`

```coq
Lemma dg_step_reverse : forall u v,
  dg_step (reverse_graph g) u v <-> dg_step g v u.
```

**语义**：反转图中的有向边 `u → v` 等价于原图中的有向边 `v → u`。

#### `dg_reachable_reverse`

```coq
Lemma dg_reachable_reverse : forall u v,
  dg_reachable (reverse_graph g) u v <-> dg_reachable g v u.
```

**语义**：反转图中的有向可达 `u →* v` 等价于原图中的有向可达 `v →* u`。证明对 `clos_refl_trans` 做归纳，利用 `dg_step_reverse`。

#### `mutually_reachable_reverse`

```coq
Lemma mutually_reachable_reverse : forall u v,
  mutually_reachable g u v <-> mutually_reachable (reverse_graph g) u v.
```

**语义**：相互可达在图反转下不变——`mutually_reachable g u v` 定义为 `dg_reachable g u v /\ dg_reachable g v u`，反转后两者交换位置但合取不变。

### 推论

#### `is_SCC_reverse`

```coq
Corollary is_SCC_reverse : forall s,
  is_SCC g s <-> is_SCC (reverse_graph g) s.
```

**语义**：SCC 判定在图反转下不变。`is_SCC` 的三个条件中，非空性只涉及 `original_vvalid`（不变），内部 MR 和极大性中的 `mutually_reachable` 由 `mutually_reachable_reverse` 保持。

#### `scc_partition_reverse`

```coq
Corollary scc_partition_reverse : forall sccs,
  scc_partition g sccs <-> scc_partition (reverse_graph g) sccs.
```

**语义**：SCC 划分在图反转下不变。覆盖性只涉及 `original_vvalid`（不变），正确性由 `is_SCC_reverse` 保持，互斥性不变。

---

## 定义与定理清单

### 定义 (7)

| 名称 | 类型 | 行号 |
|------|------|------|
| `dg_step` | `OriginalGraphType V E -> V -> V -> Prop` | 26–29 |
| `dg_reachable` | `OriginalGraphType V E -> V -> V -> Prop` | 34–35 |
| `mutually_reachable` | `OriginalGraphType V E -> V -> V -> Prop` | 117–118 |
| `is_SCC` | `OriginalGraphType V E -> (V -> Prop) -> Prop` | 170–173 |
| `scc_partition` | `OriginalGraphType V E -> list (V -> Prop) -> Prop` | 255–259 |
| `condensation_edge` | `list (V -> Prop) -> (V -> Prop) -> (V -> Prop) -> Prop` | 468–470 |
| `reverse_graph` | `OriginalGraphType V E -> OriginalGraphType V E` | 630–637 |

### 归纳谓词 (1)

| 名称 | 构造子 | 行号 |
|------|--------|------|
| `condensation_path` | `cp_edge`, `cp_trans` | 476–484 |

### 辅助定义 (1)

| 名称 | 类型 | 行号 |
|------|------|------|
| `condensation_reachable` | `list (V -> Prop) -> (V -> Prop) -> (V -> Prop) -> Prop` | 489–491 |

### 引理 (30)

| 名称 | 行号 |
|------|------|
| `dg_reachable_refl` | 37–41 |
| `dg_reachable_refl'` | 46–49 |
| `dg_reachable_trans` | 51–56 |
| `dg_reachable_step` | 58–63 |
| `dg_step_vvalid` | 65–72 |
| `dg_reachable_vvalid` | 74–92 |
| `dg_step_reachable_reachable` | 94–100 |
| `dg_reachable_step_reachable` | 102–108 |
| `mutually_reachable_refl` | 120–124 |
| `mutually_reachable_sym` | 126–130 |
| `mutually_reachable_trans` | 132–137 |
| `mutually_reachable_vvalid_l` | 139–144 |
| `mutually_reachable_vvalid_r` | 146–152 |
| `dg_reachable_mutually_reachable` | 154–158 |
| `is_SCC_vvalid` | 175–184 |
| `is_SCC_closed_under_mr` | 186–195 |
| `is_SCC_mutually_reachable_in` | 197–203 |
| `is_SCC_maximal` | 205–219 |
| `is_SCC_extensional` | 221–229 |
| `mutually_reachable_is_SCC` | 231–244 |
| `scc_partition_disjoint` | 261–268 |
| `mutually_reachable_same_SCC` | 270–278 |
| `scc_partition_unique_SCC` | 280–290 |
| `dg_step_SCC_classify` | 495–524 |
| `condensation_path_to_dg_reachable` | 528–557 |
| `condensation_edge_oneway` | 561–587 |
| `reverse_graph_gvalid` | 640–648 |
| `dg_step_reverse` | 651–664 |
| `dg_reachable_reverse` | 667–683 |
| `mutually_reachable_reverse` | 686–693 |

### 定理 (3)

| 名称 | 行号 |
|------|------|
| `scc_partition_exists` | 294–460 |
| `condensation_is_acyclic` | 591–608 |
| `condensation_no_cycle` | 612–621 |

### 推论 (2)

| 名称 | 行号 |
|------|------|
| `is_SCC_reverse` | 696–712 |
| `scc_partition_reverse` | 716–730 |

**总计**：7 个定义 + 1 个归纳谓词 + 1 个辅助定义 + 20 个引理 + 3 个定理 + 2 个推论 = **34 项**
