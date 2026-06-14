# SCC_basic.v 设计文档

**Author**: Vitalrubbish
**Date**: 2026-06-12

## 概述

本文档给出 `SCC_basic.v` 的完整设计。该文件位于
`SeparationLogic/algorithms/Tarjan_directed/` 下，是 Tarjan **有向图** SCC 验证的
**数学定义层**（Layer 3），独立于任何具体算法。它定义了有向强连通分量（SCC）
的数学概念、SCC 划分的性质、缩点图（condensation graph）的 DAG 性质，
以及图反转下 SCC 的不变性。

**关键设计决策——有向 vs 无向图语义**：

仓库中 `GraphLib/examples/tarjan.v` 的 `OriginalGraphType` 携带方向信息
（`original_step_fst` / `original_step_snd`），但通过 `UndirectedGraph`、
`StepUniqueUndirected` 等 Type Class 实例使 `step_aux` 成为**对称**关系。
因此 `GraphLib/reachable/reachable_basic.v` 中定义的 `step` 和 `reachable`
都是**无向**的——这对已完成的桥判定证明（`algorithms/Tarjan/`）是正确的
（桥是无向概念），但对 SCC 是**错误的**（SCC 是有向概念）。

`SCC_basic.v` 通过定义有向 step（`dg_step`）和有向 reachable（`dg_reachable`），
在 `OriginalGraphType` 上叠加一层薄的有向解释。所有 SCC 相关定义
（`mutually_reachable`、`is_SCC`、`condensation_edge` 等）都基于 `dg_step`/
`dg_reachable`，而非无向 `step`/`reachable`。`Tarjan_directed/` 目录的名称
即是这一语义分歧的直接体现。

本文档必须与以下设计文档协同阅读：
- `docs/plan-tarjan-scc-2sat-verification.md` — 六阶段总计划
- `docs/dev/20260611-kmp-refinement-proof.md` — KMP refinement 全流程——参考其数学层设计、三层解耦模式与 C-Monad 边界拆分决策

**历史记录**：本文档 v1.0（2026-06-12）将文件路径规划为 `algorithms/Tarjan/SCC_basic.v`，
使用无向 `reachable` / `step` 和 `OriginalGraph_gvalid` Context。v2.0（2026-06-14）根据实际落地代码
刷新为 `algorithms/Tarjan_directed/SCC_basic.v`，更新为有向 `dg_step` / `dg_reachable` 语义和
`FiniteGraph` Context。

**验证状态**：本文档中的 `OriginalGraphType` 字段名（`original_step_fst`/`original_step_snd`）、
`Hoare_safeexec_compose` 引理位置（`monadesafe_lib.v:833-848`）、现有桥证明文件行数
（`Tarjan_is_low.v` 2812 行、`Tarjan_basics_ex.v` 2614 行等）均已在
`SeparationLogic/` 代码库中逐文件验证。

---

## 1. 文件定位

### 1.1 在三层架构中的位置

```
Layer 3 (数学规范):  SCC_basic.v                    ← 本文档（已落地）
        ↑ Hoare_safeexec_compose 桥接
Layer 2 (Monad 算法):  SCC_program.v (规划中)       ← 后续 Phase 2
        ↑ safeExec 精化关系
Layer 1 (C 实现):      tarjan_scc_rel.c (规划中)    ← 后续 Phase 4
```

三层解耦模式和 `Hoare_safeexec_compose` 桥接引理的完整说明见
`20260611-kmp-refinement-proof.md`（KMP 案例）和
`20260612-tarjan-scc-abstract-operator-design.md`（Tarjan SCC 方法论）。

`SCC_basic.v` 是**纯数学层**：所有定义和定理只依赖图论基本概念
（`GraphLib.graph_basic.v` 的 `Graph`/`GValid` Type Class 提供的 `vvalid`、`evalid`；
`GraphLib.examples.tarjan.v` 的 `OriginalGraphType` Record 定义及其实例），
以及 Coq 标准库的 `clos_refl_trans`（自反传递闭包）。
不涉及 monad 程序、状态记录、Hoare 逻辑或 C 代码。

### 1.2 文件路径

```
SeparationLogic/algorithms/Tarjan_directed/SCC_basic.v
```

**设计决策：为什么放在 `Tarjan_directed/` 而非 `Tarjan/`？**

`Tarjan_directed/` 与已有的 `Tarjan/`（桥判定）之间存在**图语义**和**证明对象**上的根本分歧：

| 维度 | `Tarjan/`（桥判定） | `Tarjan_directed/`（SCC） |
|------|---------------------|--------------------------|
| 图语义 | **无向**——`OriginalGraphType` 通过 `UndirectedGraph`、`StepUniqueUndirected` 实例使 `step_aux` 对称 | **有向**——必须区分出边和入边 |
| `step` 关系 | `step g x y := exists e, step_aux g e x y`（对称） | `dg_step g x y`（仅前向边 `original_step_fst → original_step_snd`） |
| `reachable` | 无向可达 = `clos_refl_trans (step g)` | 有向可达 = `clos_refl_trans (dg_step g)` |
| 核心输出 | `bridges : list E` | `sccs : list (list V)` |
| 状态记录 | `St`（visited, timer, fa, tedge, dfn, low, bridges） | `SCCSt`（visited, timer, dfn, low, stack, sccs——无 fa/tedge/bridges） |

**关键洞察**：`OriginalGraphType` 同时携带方向信息（`original_step_fst` / `original_step_snd`）
和 `UndirectedGraph` 实例。桥证明利用后者（无向对称性），SCC 证明利用前者（前向有向遍历）。
两者各自在 `OriginalGraphType` 上叠加一个方向解释层——`step` vs `dg_step`。两个目录以此
隔离两套互不兼容的 `reachable`/`mutually_reachable` 语义。

### 1.3 依赖关系

```
GraphLib.graph_basic.v           — Graph, GValid, StepValid, FiniteGraph Type Classes
                                   （提供 vvalid, evalid, step_aux 的接口定义）
GraphLib.examples.tarjan.v       — OriginalGraphType Record, OriginalGraph_gvalid,
                                   Original_finitegraph 实例
GraphLib.Syntax                  — 导出 Coq.Relations
Coq.Relations.Relations          — clos_refl_trans（自反传递闭包）及相关引理
Coq.Logic.Classical_Prop         — classic（scc_partition_exists 证明用）
Coq.Lists.List                   — In, list 操作
SetsClass.SetsClass              — 集合记法
```

`SCC_basic.v` **不依赖**：
- `GraphLib.reachable.reachable_basic.v`——其中定义的 `step` 和 `reachable` 是无向的，SCC_basic 自行定义有向 `dg_step`/`dg_reachable`
- `algorithms/Tarjan/Tarjan.v` 或任何 monadic program 定义
- `MonadLib` / `TraceLib` / `coq-record-update`
- 任何算法相关的概念（`dfn`、`low`、`visited`、`timer`、`stack` 等）
- `GraphLib.directed.rootedtree` / `GraphLib.directed.dfstree`

---

## 2. 有向图原语

### 2.1 动机：为什么不能直接复用 `step` / `reachable`

`GraphLib.reachable.reachable_basic.v` 中定义的：

```coq
Definition step (g: G) (x y: V): Prop :=
  exists e, step_aux g e x y.
```

其中 `step_aux` 来自 `OriginalGraphType` 的实例。但 `OriginalGraphType` 同时声明了
`UndirectedGraph` 实例（`step_sym: step_aux g e x y -> step_aux g e y x`），因此 `step g x y`
和 `reachable g x y` 都是**无向的**。

如果在无向 `reachable` 上定义 `mutually_reachable`，则相互可达退化为"在同一连通分量"——
在有向含义下本应单向的两个顶点会被错误地判为相互可达。因此需要**有向 step**。

### 2.2 有向 step 与有向 reachable

`SCC_basic.v` 在 `OriginalGraphType` 上叠加一层薄的有向解释：

```coq
Definition dg_step (g: OriginalGraphType V E) (x y: V): Prop :=
  exists e, original_step g e /\
            original_step_fst g e = x /\
            original_step_snd g e = y.
```

**语义**：`dg_step g x y` 当且仅当存在一条原图有向边从 x 到 y。

**与无向 `step` 的区别**：
- `step g x y` ←→ `exists e, (e: x→y) \/ (e: y→x)`  —— 对称
- `dg_step g x y` ←→ `exists e, (e: x→y)`             —— 不对称

```coq
Definition dg_reachable (g: OriginalGraphType V E) (x y: V): Prop :=
  clos_refl_trans (dg_step g) x y.
```

**实例**：`dg_reachable` 满足 `reachable_basic.v` 中 `reachable` 的全部传递/自反性质：
```coq
Lemma dg_reachable_refl : forall x, vvalid g x -> dg_reachable g x x.
Lemma dg_reachable_trans : forall x y z,
  dg_reachable g x y -> dg_reachable g y z -> dg_reachable g x z.
Lemma dg_reachable_step : forall x y,
  dg_step g x y -> dg_reachable g x y.
```

### 2.3 基本引理

```coq
Lemma dg_step_vvalid : forall x y,
  dg_step g x y -> vvalid g x /\ vvalid g y.
Lemma dg_reachable_vvalid : forall x y,
  x <> y -> dg_reachable g x y -> vvalid g x /\ vvalid g y.
Lemma dg_step_reachable_reachable : forall x y z,
  dg_step g x y -> dg_reachable g y z -> dg_reachable g x z.
Lemma dg_reachable_step_reachable : forall x y z,
  dg_reachable g x y -> dg_step g y z -> dg_reachable g x z.
```

这些引理是 `reachable_basic.v` 中对应引理的有向版本，证明策略完全一致（`clos_refl_trans` 的归纳）。

---

## 3. 模块结构

`SCC_basic.v` 分为以下 6 个 Section（第 0 节为有向图原语）：

```
Section 0: dg_step / dg_reachable   — 有向图原语（~80 行）
Section 1: mutually_reachable       — 相互可达性与等价关系
Section 2: is_SCC                   — SCC 判定谓词与基本性质
Section 3: scc_partition            — SCC 划分与存在性定理
Section 4: condensation             — 缩点图 DAG 性质
Section 5: reverse_graph            — 图反转与 SCC 不变性
```

每个 Section 使用统一的 Context：

```coq
Context {V E: Type} (g: OriginalGraphType V E)
        `{FiniteGraph (OriginalGraphType V E) V E}.
```

**设计决策——为什么用 `FiniteGraph` 而非 `OriginalGraph_gvalid`**：
`scc_partition_exists` 的构造性证明需要对顶点集进行枚举。
`OriginalGraphType` 通过 `Original_finitegraph` 实例（声明于 `GraphLib.examples.tarjan.v`）
将 `original_listV` 绑定为 `FiniteGraph` 的 `listV` 方法，提供了有限顶点列表。
`FiniteGraph` Type Class 同时蕴含了 `GValid`（有效顶点判定），所以单独声明
`OriginalGraph_gvalid` 是冗余的。若不用 `FiniteGraph` 而要求存在性，则需额外引入选择公理。

---

## 4. Section 1: mutually_reachable — 相互可达性

### 4.1 核心定义

```coq
Definition mutually_reachable (u v: V) : Prop :=
  dg_reachable g u v /\ dg_reachable g v u.
```

**设计说明**：

- 使用 **有向** `dg_reachable`（见 Section 0），而非无向 `reachable`；
- `mutually_reachable` 是 `dg_reachable` 的对称闭包——构成等价关系；
- 使用 `V -> V -> Prop`（纯数学谓词）而非 `list V` 或 `V -> bool`，保持与 `GraphLib` 风格一致且支持古典逻辑推理；
- 对比桥证明中的 `reachable g u v`（无向）——在桥证明中，"可达"即"连通"；在 SCC 中，"可达"是"存在有向路径"。

### 4.2 等价关系引理

```coq
Lemma mutually_reachable_refl : forall u, vvalid g u -> mutually_reachable u u.
Lemma mutually_reachable_sym  : forall u v, mutually_reachable u v -> mutually_reachable v u.
Lemma mutually_reachable_trans : forall u v w,
  mutually_reachable u v -> mutually_reachable v w -> mutually_reachable u w.
```

**证明路线**：

- `refl`：`dg_reachable` 的自反性（`clos_refl_trans` 零步）；
- `sym`：由定义直接得；
- `trans`：`dg_reachable` 的传递性（`clos_refl_trans` 拼接），在两个方向各用一次。

### 4.3 辅助引理

```coq
Lemma mutually_reachable_vvalid_l : forall u v,
  u <> v -> mutually_reachable u v -> vvalid g u.
Lemma mutually_reachable_vvalid_r : forall u v,
  u <> v -> mutually_reachable u v -> vvalid g v.
Lemma dg_reachable_mutually_reachable : forall u v,
  dg_reachable g u v -> dg_reachable g v u -> mutually_reachable u v.
```

**设计要点**：`u <> v` 前提是必要的。因为 `dg_reachable g u u` 由 `clos_refl_trans` 的自反性恒成立，
即使 `~ vvalid g u` 也有 `mutually_reachable u u`。这匹配 `reachable_basic.v` 中
`reachable_vvalid : x <> y -> reachable g x y -> vvalid g x /\ vvalid g y` 的模式。

**用途**：`vvalid_l` / `vvalid_r` 是后续 `is_SCC` 证明中频繁使用的辅助引理——从相互可达推出顶点在图中的有效性。
使用时需先判断 `u = v`：若相等则 `vvalid` 从上下文获得；若不等则用此引理。
`dg_reachable_mutually_reachable` 是构造 `mutually_reachable` 的直接入口。

---

## 5. Section 2: is_SCC — SCC 判定

### 5.1 核心定义

```coq
Definition is_SCC (s: V -> Prop) : Prop :=
  (exists v, s v /\ vvalid g v) /\
  (forall u v, s u -> s v -> mutually_reachable u v) /\
  (forall u v, s u -> vvalid g v -> mutually_reachable u v -> s v).
```

**三个条件的语义**：

| 条件 | 表述 | 语义 |
|------|------|------|
| 非空性 | `exists v, s v /\ vvalid g v` | SCC 至少包含一个有效顶点 |
| 内部 MR | `forall u v, s u -> s v -> mutually_reachable u v` | SCC 内任意两点相互可达 |
| 极大性 | `forall u v, s u -> vvalid g v -> mutually_reachable u v -> s v` | 任何与 SCC 成员相互可达的顶点也在 SCC 内 |

**设计决策：使用 `V -> Prop` 而非 `list V`**：

- `list V` 隐含了顺序和重复性，而 SCC 是**集合**概念；
- `V -> Prop` 直接对应数学定义中的子集，与古典逻辑的量词和等价关系推理无缝衔接；
- 与 `GraphLib` 中 `visited: V -> Prop` 的风格一致；
- `scc_partition` 使用 `list (V -> Prop)` 时，`In s sccs` 提供枚举能力，而 `s v` 提供成员判定。

### 5.2 基本性质引理

```coq
Lemma is_SCC_vvalid : forall s u, is_SCC s -> s u -> vvalid g u.
```

**证明**：由非空性得某个 `v0` 满足 `s v0 /\ vvalid g v0`。分情况：
- 若 `u = v0`：直接得 `vvalid g u`；
- 若 `u <> v0`：内部 MR 给出 `mutually_reachable u v0`，由 `mutually_reachable_vvalid_l`（需 `u <> v0`）得 `vvalid g u`。

```coq
Lemma is_SCC_closed_under_mr : forall s u v,
  is_SCC s -> s u -> mutually_reachable u v -> s v.
```

**证明**：由极大性条件直接实例化。`vvalid g v` 的获取分情况：若 `u = v` 则从 `is_SCC_vvalid s u` 得（`s u` 已知）；若 `u <> v` 则由 `mutually_reachable_vvalid_r` 提供。

```coq
Lemma is_SCC_mutually_reachable_in : forall s u v,
  is_SCC s -> s u -> mutually_reachable u v -> s v /\ mutually_reachable u v.
```

**证明**：`is_SCC_closed_under_mr` + 前提。

```coq
Lemma is_SCC_maximal : forall s1 s2,
  is_SCC s1 -> is_SCC s2 ->
  (forall v, s1 v -> s2 v) -> (forall v, s2 v -> s1 v).
```

**证明**（这是 SCC 唯一性的关键引理）：
设 `s2 v`，由非空性得 `s1 u0`，则 `s2 u0`（假设），内部 MR 得 `mutually_reachable v u0`，再由 s1 极大性得 `s1 v`。

```coq
Lemma is_SCC_extensional : forall s1 s2,
  is_SCC s1 -> is_SCC s2 ->
  (forall v, s1 v <-> s2 v) -> s1 = s2.
```

**证明**：函数外延性 + `is_SCC_maximal`。

```coq
Lemma mutually_reachable_is_SCC : forall u,
  vvalid g u -> is_SCC (fun v => mutually_reachable u v).
```

**证明**（从任意有效顶点构造含它的唯一 SCC）：
- 非空性：u 自身（`vvalid g u` + `mutually_reachable_refl`）；
- 内部 MR：`mutually_reachable` 的对称性和传递性；
- 极大性：定义直接满足。

---

## 6. Section 3: scc_partition — SCC 划分

### 6.1 核心定义

```coq
Definition scc_partition (sccs: list (V -> Prop)) : Prop :=
  (forall v, vvalid g v -> exists s, In s sccs /\ s v) /\
  (forall s, In s sccs -> is_SCC s) /\
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2).
```

**三个条件的语义**：

| 条件 | 表述 | 语义 |
|------|------|------|
| 覆盖性 | `forall v, vvalid g v -> exists s, In s sccs /\ s v` | 每个有效顶点属于某个 SCC |
| 正确性 | `forall s, In s sccs -> is_SCC s` | 列表中的每个集合确实是 SCC |
| 互斥性 | `forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2` | 不同 SCC 不相交（任一公共顶点推出相等） |

**互斥性条件的等价形式**：

```coq
(* 推论：任意两个不同的 SCC 不相交 *)
Lemma scc_partition_disjoint : forall sccs s1 s2,
  scc_partition sccs -> In s1 sccs -> In s2 sccs -> s1 <> s2 ->
  forall v, ~ (s1 v /\ s2 v).
```

### 6.2 核心引理

```coq
Lemma mutually_reachable_same_SCC : forall u v sccs,
  vvalid g u -> scc_partition sccs -> mutually_reachable u v ->
  exists s, In s sccs /\ s u /\ s v.
```

**证明**：

1. 由覆盖性，u 属于某个 `s1`，即 `s1 u`；
2. 由 `mutually_reachable u v` + `is_SCC_closed_under_mr`（s1 是 SCC），得 `s1 v`；
3. 输出 `s1`。

```coq
Lemma scc_partition_unique_SCC : forall u sccs,
  vvalid g u -> scc_partition sccs ->
  exists! s, In s sccs /\ s u.
```

**证明**：存在性由覆盖性；唯一性由互斥性——若 `s1 u` 且 `s2 u`，则互斥性推出 `s1 = s2`。

### 6.3 存在性定理

```coq
Theorem scc_partition_exists : scc_partition (scc_partition_list g).
```

或者更标准的表述：

```coq
Theorem scc_partition_exists : exists sccs, scc_partition sccs.
```

**证明策略**（使用古典逻辑 + `FiniteGraph`）：

1. 对每个有效顶点 `v`，构造 `scc_of v := fun w => mutually_reachable v w`；
2. 由 `mutually_reachable_is_SCC`，每个 `scc_of v` 是 SCC；
3. 收集所有不同的 `scc_of v`（消去重复——由 `is_SCC_extensional`，若 `scc_of u = scc_of w` 则只保留一个）；
4. 验证三个条件：
   - 覆盖性：`v` 在 `scc_of v` 中；
   - 正确性：每个 `scc_of v` 是 SCC；
   - 互斥性：若 `scc_of u` 和 `scc_of w` 有公共顶点 x，则 `mutually_reachable u w`（传递两次），由外延性两集合相等。

**需要的公理**：

- `classic : forall P, P \/ ~ P`（来自 `Coq.Logic.Classical_Prop`）
- `FiniteGraph` 约束（来自 `GraphLib.examples.tarjan`）：顶点集有限，才能对 V 进行枚举构造列表

**注意**：`OriginalGraphType` 的 `original_listV` 字段（通过 `Original_finitegraph` 实例绑定到 `FiniteGraph` 的 `listV` 方法）提供了有限顶点列表，这使得可以遍历所有顶点构造 `scc_partition_list`。若不用 `FiniteGraph` 而要求存在性，则需引入选择公理。当前设计选择依赖 `FiniteGraph`，这与 `GraphLib.examples.tarjan.v` 的设置一致。

### 6.4 存在性构造策略（详情）

```coq
(* 从顶点列表构造 SCC 划分——使用 classic + FiniteGraph *)
(* 策略：对 original_listV 做归纳，维护已收集的代表 SCC 列表。
   对每个有效顶点 u，检查 u 是否与已有代表相互可达：
   - 若是：跳过（u 属于已有的某个 SCC）
   - 若否：将 scc_of u 加入列表 *)
Theorem scc_partition_exists : exists sccs, scc_partition sccs.
Proof.
  (* 对 g.(original_listV) 做 List 归纳，使用 classic 判断
     exists s, In s acc /\ s u，逐步构造满足三个条件的 sccs *)
  ...
Qed.
```

**关键**：由于 `V -> Prop` 的外延等价不可判定，不能直接用 `valid_NoDup_list` 去重。
正确策略是在归纳构造中用 `classic` 判定 `exists s, In s acc /\ s u`
（即 u 是否已属于某个已收集的 SCC）。此判定是 `Prop` 而非 `bool`，依赖排中律。
这与 `graph_basic.v` 中 `valid_NoDup_list` 使用 `excluded_middle_informative` 的模式一致。

---

## 7. Section 4: condensation — 缩点图

### 7.1 核心定义

```coq
(* 缩点图中的有向边 *)
Definition condensation_edge (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ dg_step g u v.
```

**语义**：从 SCC s1 到 SCC s2 存在缩点边，当且仅当存在原图中的一条**有向**边从 s1 中某顶点指向 s2 中某顶点，且 s1 和 s2 是不同的 SCC。

**设计要点**：

- `s1 <> s2` 排除自环——SCC 内部的原图边不产生缩点边；
- 使用 **有向** `dg_step g u v`（见 Section 0），而非无向 `step g u v`——缩点边方向由原图有向边方向决定。

```coq
(* 缩点图中存在从 s1 到 s2 的路径 *)
Inductive condensation_path (sccs: list (V -> Prop)) :
  (V -> Prop) -> (V -> Prop) -> Prop :=
  | cp_edge : forall s1 s2,
      condensation_edge sccs s1 s2 ->
      condensation_path sccs s1 s2
  | cp_trans : forall s1 s2 s3,
      condensation_path sccs s1 s2 ->
      condensation_path sccs s2 s3 ->
      condensation_path sccs s1 s3.

Definition condensation_reachable (sccs: list (V -> Prop))
  (s1 s2: V -> Prop) : Prop :=
  s1 = s2 \/ condensation_path sccs s1 s2.
```

**设计决策：用归纳谓词而非 `clos_refl_trans`**

缩点图的顶点类型是 `V -> Prop`（谓词），不是 `OriginalGraphType` 的 `V`。
`GraphLib` 的 `reachable` 要求 `Graph G V E` 实例，为缩点图构造完整的 `Graph` 实例
（`condensation_edge` 作为 `step_aux`）较重量级。归纳谓词足够证明 DAG 性质，
且证明更透明。

### 7.2 DAG 性质定理

```coq
Theorem condensation_is_acyclic : forall sccs,
  scc_partition sccs ->
  forall s1 s2,
    condensation_edge sccs s1 s2 ->
    ~ condensation_reachable sccs s2 s1.
```

**等价表述**：

```coq
Theorem condensation_no_cycle : forall sccs,
  scc_partition sccs ->
  ~ exists s1 s2,
    condensation_edge sccs s1 s2 /\
    condensation_path sccs s2 s1.
```

**证明路线**：

1. 假设存在 `condensation_edge sccs s1 s2` + `condensation_path sccs s2 s1`；
2. `condensation_edge` 给出 u ∈ s1, v ∈ s2, `dg_step g u v`；
3. `condensation_path s2 →* s1` 的每步对应原图中的 `dg_step`，拼接得到 `dg_reachable g v u`；
4. 于是 `dg_reachable g u v`（`dg_step` 给出）且 `dg_reachable g v u`（缩点路径拼接），即 `mutually_reachable u v`；
5. 但 u ∈ s1, v ∈ s2, `mutually_reachable u v`，由 `scc_partition` 的互斥性推出 `s1 = s2`；
6. 与 `condensation_edge` 的 `s1 <> s2` 矛盾。

**关键子引理**：

```coq
Lemma condensation_edge_oneway : forall sccs s1 s2 u v,
  scc_partition sccs ->
  condensation_edge sccs s1 s2 ->
  s1 u -> s2 v ->
  dg_reachable g u v /\ ~ mutually_reachable u v.
```

这个引理刻画缩点边的本质：连接两个 SCC 的边产生单向可达，且两端顶点**不**相互可达（否则两 SCC 应合并）。

### 7.3 辅助引理

```coq
Lemma dg_step_SCC_classify : forall sccs u v,
  scc_partition sccs -> dg_step g u v ->
  (exists s, In s sccs /\ s u /\ s v)     (* 同 SCC 内部 *)
  \/
  (exists s1 s2,                            (* 跨 SCC *)
    In s1 sccs /\ In s2 sccs /\ s1 u /\ s2 v /\
    condensation_edge sccs s1 s2).
```

**用途**：每条原图有向边要么在同一个 SCC 内部（不产生缩点边），要么连接两个不同 SCC（产生缩点边）。这个引理桥接了原图结构与缩点图结构。

---

## 8. Section 5: reverse_graph — 图反转

### 8.1 核心定义

```coq
Definition reverse_graph (g: OriginalGraphType V E) : OriginalGraphType V E :=
  {|
    original_vvalid   := g.(original_vvalid);
    original_step     := g.(original_step);
    original_step_fst := g.(original_step_snd);   (* 交换 source ↔ target *)
    original_step_snd := g.(original_step_fst);   (* 交换 target ↔ source *)
    original_listV    := g.(original_listV);
  |}.
```

**设计要点**：

- `OriginalGraphType` 的实际字段名来自 `GraphLib/examples/tarjan.v:19-25`：
  `original_vvalid`、`original_step`、`original_step_fst`、`original_step_snd`、`original_listV`；
- 图反转不改变顶点集（`original_vvalid`）和边集（`original_step`），只交换 `original_step_fst` ↔ `original_step_snd`；
- 反转图保持 `gvalid` 性质：

```coq
Lemma reverse_graph_gvalid :
  gvalid g -> gvalid (reverse_graph g).
Proof.
  (* original_step_fst_valid / original_step_snd_valid 交换后仍然成立；
     original_finite_vertices 不变。 *)
  ...
Qed.
```

**设计决策——为什么用 Lemma 而非 Instance**：`FiniteGraph` 实例的构造涉及
`original_listV` 与顶点列表的对应关系，这需要额外的证明（证明反转不改变顶点列表）。
当前 `SCC_basic.v` 中的反转不变性引理（`dg_step_reverse`、`dg_reachable_reverse`、
`mutually_reachable_reverse`、`is_SCC_reverse`、`scc_partition_reverse`）只需要
`gvalid` 保证即可完成，因此用简单的 Lemma 更轻量。若后续阶段（如 Kosaraju 算法）
需要反转图作为完整的 `OriginalGraphType` 实例参与 `FiniteGraph` 推导，届时再补充 Instance。

### 8.2 反转不变性

```coq
Lemma dg_step_reverse : forall u v,
  dg_step (reverse_graph g) u v <-> dg_step g v u.
```

**证明**：`dg_step (reverse_graph g) u v` 展开即 `exists e, original_step g e /\ original_step_snd g e = u /\ original_step_fst g e = v`，即 `dg_step g v u`。

```coq
Lemma dg_reachable_reverse : forall u v,
  dg_reachable (reverse_graph g) u v <-> dg_reachable g v u.
```

**证明**：`clos_refl_trans` 归纳 + `dg_step_reverse`。反转图中从 u 到 v 的有向路径对应原图中从 v 到 u 的有向路径。

```coq
Lemma mutually_reachable_reverse : forall u v,
  mutually_reachable g u v <-> mutually_reachable (reverse_graph g) u v.
```

**证明**：`mutually_reachable` 定义中的两个 `dg_reachable` 在反转下交换位置，但合取交换后等价。

```coq
Corollary is_SCC_reverse : forall s,
  is_SCC g s <-> is_SCC (reverse_graph g) s.
```

**证明**：`is_SCC` 的三个条件中，"非空性"只涉及 `vvalid`（不变），"内部 MR"和"极大性"中的 `mutually_reachable` 由上述引理不变。

```coq
Corollary scc_partition_reverse : forall sccs,
  scc_partition g sccs <-> scc_partition (reverse_graph g) sccs.
```

**证明**：`scc_partition` 的三个条件中，覆盖性只涉及 `vvalid`，正确性由 `is_SCC_reverse`，互斥性不变。

### 8.3 用途

图反转在后续阶段中的用途：

| 场景 | 如何使用 |
|------|----------|
| **Kosaraju 算法** | 第二遍 DFS 在图反转上运行，`is_SCC_reverse` 保证两遍产生的 SCC 一致 |
| **2-SAT 蕴含图** | 蕴含图 `(¬a → b)` 和 `(¬b → a)` 的 SCC 划分在原图和反转图上对称 |
| **缩点图拓扑序** | 反转图的缩点图是原图缩点图的反转，`condensation_is_acyclic` 在反转下保持 |

---

## 9. 证明策略约定

### 9.1 逻辑基础

- 使用 `Coq.Logic.Classical_Prop.classic`（排中律）进行 case 分析；
- 使用 `Coq.micromega.Psatz.lia` 处理算术目标（如果需要 `nat` 相关的序关系证明）；
- 不引入额外的公理（如 `FunctionalChoice` 或 `PropExtensionality`），除非 `scc_partition_exists` 的构造在无 `FiniteGraph` 下需要选择公理。

### 9.2 命名约定

遵循 `GraphLib` 和 `Tarjan.v` 的命名风格：

- 定义：`snake_case`（`mutually_reachable`、`is_SCC`、`scc_partition`）；
- 引理：`subject_condition` 形式（`is_SCC_vvalid`、`condensation_is_acyclic`）；
- 变量命名：u, v, w 用于顶点；s, s1, s2 用于 SCC 谓词；sccs 用于 SCC 列表。

### 9.3 集合记法

使用 `SetsClass.SetsClass` 提供的 `SetsNotation`：
- `[u]` 表示单元素集 `fun x => x = u`
- `u ∈ s` 表示 `s u`
- `s1 ⊆ s2` 表示 `forall v, s1 v -> s2 v`

---

## 10. 文件骨架

```
SCC_basic.v (~320 行，证明全部 Admitted，待补全后预计 ~550 行)
│
├── Require Import (7 行)
│   ├── Coq.Lists.List
│   ├── Coq.Logic.Classical_Prop
│   ├── Coq.Relations.Relations
│   ├── SetsClass.SetsClass
│   ├── GraphLib.graph_basic
│   ├── GraphLib.Syntax
│   └── GraphLib.examples.tarjan
│
├── Local Open Scope sets.
│
├── Section SCC_DEFS
│   └── Context {V E} (g: OriginalGraphType V E)
│               `{FiniteGraph (OriginalGraphType V E) V E}
│
├── Section 0: dg_step / dg_reachable (~80 行)
│   ├── Definition dg_step
│   ├── Definition dg_reachable
│   ├── Lemma dg_reachable_refl
│   ├── Lemma dg_reachable_trans
│   ├── Lemma dg_reachable_step
│   ├── Lemma dg_step_vvalid
│   ├── Lemma dg_reachable_vvalid
│   ├── Lemma dg_step_reachable_reachable
│   └── Lemma dg_reachable_step_reachable
│
├── Section 1: mutually_reachable (~60 行)
│   ├── Definition mutually_reachable
│   ├── Lemma mutually_reachable_refl
│   ├── Lemma mutually_reachable_sym
│   ├── Lemma mutually_reachable_trans
│   ├── Lemma mutually_reachable_vvalid_l
│   ├── Lemma mutually_reachable_vvalid_r
│   └── Lemma dg_reachable_mutually_reachable
│
├── Section 2: is_SCC (~90 行)
│   ├── Definition is_SCC
│   ├── Lemma is_SCC_vvalid
│   ├── Lemma is_SCC_closed_under_mr
│   ├── Lemma is_SCC_mutually_reachable_in
│   ├── Lemma is_SCC_maximal
│   ├── Lemma is_SCC_extensional
│   └── Lemma mutually_reachable_is_SCC
│
├── Section 3: scc_partition (~60 行)
│   ├── Definition scc_partition
│   ├── Lemma scc_partition_disjoint
│   ├── Lemma mutually_reachable_same_SCC
│   ├── Lemma scc_partition_unique_SCC
│   └── Theorem scc_partition_exists
│
├── Section 4: condensation (~60 行)
│   ├── Definition condensation_edge
│   ├── Inductive condensation_path
│   ├── Definition condensation_reachable
│   ├── Lemma dg_step_SCC_classify
│   ├── Lemma condensation_edge_oneway
│   ├── Theorem condensation_is_acyclic
│   └── Theorem condensation_no_cycle
│
├── Section 5: reverse_graph (~50 行)
│   ├── Definition reverse_graph
│   ├── Lemma reverse_graph_gvalid
│   ├── Lemma dg_step_reverse
│   ├── Lemma dg_reachable_reverse
│   ├── Lemma mutually_reachable_reverse
│   ├── Corollary is_SCC_reverse
│   └── Corollary scc_partition_reverse
│
└── End SCC_DEFS.
```

---

## 11. 与后续 Phase 的接口

### 11.1 SCC_program.v 会使用

- `is_SCC` — 在 `pop_scc_component` 的 Hoare 后条件中声明"弹出的顶点集是一个 SCC"
- `scc_partition` — 在 `tarjan_scc_correctness` 的主定理中声明"算法输出一个 SCC 划分"
- `mutually_reachable` — 在栈不变式中连接 low/dfn 值与 SCC 语义（`low[v] = dfn[v]` 是 SCC 根的特征）
- `dg_reachable` — 在 `process_edge` 中表达"沿有向边可达邻居"

### 11.2 SCC_correctness.v 会使用

- 全部 `is_SCC` 性质的引理
- `scc_partition` 的覆盖性、正确性、互斥性引理
- `mutually_reachable_is_SCC`（从单个顶点发出的 SCC 构造）
- `mutually_reachable` 等价关系引理（传递性在证明栈不变量保持时常用）
- `dg_reachable` 的传递性与 `dg_step` 的桥接引理

### 11.3 TwoSAT.v 会使用

- `condensation_is_acyclic` — 2-SAT 赋值构造依赖缩点图的 DAG 性质做拓扑序赋值
- `reverse_graph` + `is_SCC_reverse` — 蕴含图中文字与否定文字在不同 SCC 的判断
- `scc_partition_exists` — 保证任意 2-SAT 实例都存在 SCC 划分

### 11.4 现阶段不实现的内容

| 内容 | 原因 | 归入阶段 |
|------|------|----------|
| `condensation_graph` 构造为 `OriginalGraphType (V -> Prop) E` | 当前 DAG 证明不需要完整图构造，归纳谓词足够 | 阶段五（2-SAT 形式化需要时） |
| `reverse_graph` 的高阶性质（反转两次回到原图等） | 当前用不到 | 阶段五 |
| SCC 与 Tarjan 算法的链接（`scc_stack_invariant`、`low_eq_dfn_marks_scc_root`） | 属于桥接层，应放在 `SCC_correctness.v`（Phase 3 of plan） | Phase 3 |
| Kosaraju 算法相关引理 | Kosaraju 暂不在计划中 | 未来扩展 |

---

## 12. 设计检查清单

### 12.1 定义完整性

- [x] `dg_step` / `dg_reachable` 是否正确定义了有向边和可达性？（使用 `original_step_fst` / `original_step_snd`）— 已落地
- [x] `mutually_reachable` 是否基于 `dg_reachable` 而非无向 `reachable`？— 已落地
- [x] `mutually_reachable` 是否构成等价关系？（自反、对称、传递已声明为 Lemma，待证明）
- [x] `is_SCC` 的三个条件是否互相独立？（非空性不蕴含内部 MR，内部 MR 不蕴含极大性）
- [x] `scc_partition` 的定义是否可判定？（不可判定——`V -> Prop` 的外延等价不可判定，但对古典逻辑推理足够）
- [x] `condensation_edge` 是否使用了 `dg_step`（有向边）？— 已落地
- [x] `condensation_edge` 是否排除了 SCC 自环？（是，`s1 <> s2` 显式排除）
- [x] `reverse_graph` 的字段名是否正确？（`original_step_fst` / `original_step_snd`，非 `original_source` / `original_target`）— 已落地
- [x] `reverse_graph` 是否保持了 `gvalid`？（`Lemma reverse_graph_gvalid : gvalid g -> gvalid (reverse_graph g)` 已声明）

### 12.2 证明可行性

- [x] `scc_partition_exists` 需要什么公理？（古典逻辑 + `FiniteGraph`，均已通过 Context 提供）
- [x] `condensation_is_acyclic` 的证明是否可能因为 `condensation_path` 定义不当而卡住？（用 `dg_reachable` 的传递性 + `mutually_reachable` + `scc_partition` 互斥性推出矛盾）
- [x] 是否有循环依赖？（无——`SCC_basic.v` 是最底层，不依赖任何算法文件）
- [x] `dg_step` / `dg_reachable` 与无向 `step` / `reachable` 是否会混淆？（两者在不同的 namespace，`SCC_basic.v` 内只用 `dg_step` / `dg_reachable`，且不导入 `reachable_basic`）
- [x] `reachable_basic.v` 中对 `reachable` 的引理是否可以迁移到 `dg_reachable`？（大部分可以——`dg_reachable` 也是 `clos_refl_trans`，证明策略相同）

### 12.3 可重用性

- [x] 定义是否足够通用？（使用 `FiniteGraph (OriginalGraphType V E) V E` Context，适用于任意有向图）
- [x] 是否可以复用于 Kosaraju 算法？（`reverse_graph` + `is_SCC_reverse` 保证）
- [x] 是否可以复用于非 Tarjan 的 SCC 算法？（是——所有定义算法无关）
- [x] 与现有桥证明的命名是否冲突？（无——在不同目录 `Tarjan_directed/`，且使用 `dg_` 前缀区分有向/无向）

### 12.4 待完成：证明

所有 Lemma/Theorem 的证明当前均为 `Admitted`。待完成的证明共 30+ 个，
按 Section 分组如下：

| Section | 待证明数 | 关键难点 |
|---------|---------|---------|
| 0: dg_step / dg_reachable | 8 | `clos_refl_trans` 归纳 |
| 1: mutually_reachable | 7 | 等价关系推理 |
| 2: is_SCC | 7 | 极大性传递 |
| 3: scc_partition | 5 | `scc_partition_exists` 构造（classic + FiniteGraph 枚举） |
| 4: condensation | 5 | `condensation_path` 到 `dg_reachable` 的桥接 |
| 5: reverse_graph | 6 | `reverse_graph_gvalid`、`clos_refl_trans` 反转对称 |

---

## 13. 参考文件

| 文件 | 用途 |
|------|------|
| `SeparationLogic/GraphLib/graph_basic.v` | `Graph`, `GValid`, `StepValid`, `step_aux`, `FiniteGraph` Type Classes（~80 行） |
| `SeparationLogic/GraphLib/reachable/reachable_basic.v` | `step` (无向), `reachable` (无向) 定义与引理——`dg_reachable` 的模板（~120 行） |
| `SeparationLogic/GraphLib/examples/tarjan.v` | `OriginalGraphType` Record（`original_vvalid`, `original_step`, `original_step_fst`, `original_step_snd`, `original_listV`）；`OriginalGraph_gvalid`、`Original_finitegraph` 等实例 |
| `SeparationLogic/algorithms/Tarjan_directed/SCC_basic.v` | **本文档的目标文件**——SCC 数学定义层（当前 320 行，证明 Admitted） |
| `SeparationLogic/algorithms/Tarjan/Tarjan.v` | 桥证明的主程序——`St` Record 与 `Lfix` 递归模式（467 行） |
| `SeparationLogic/algorithms/Tarjan/Tarjan_bridge_iff.v` | `Tarjan_bridge_iff_inductive_hypotheses` Record 模式——SCC 归纳假设的模板（493 行） |
| `SeparationLogic/algorithms/Tarjan/Tarjan_is_low.v` | `is_low` 全局性质——SCC_correctness 阶段需适配 stack 语境（2812 行） |
| `SeparationLogic/algorithms/Tarjan/Tarjan_no_cross_edge.v` | 无横叉边引理——DFS 树结构中的路径性质（293 行） |
| `SeparationLogic/MonadLib/Examples/kmp.v` | KMP 数学谓词定义模式——`is_prefix`, `partial_match_result`, `best_partial_match_result` 分层设计 |
| `SeparationLogic/MonadLib/MonadErr/monadesafe_lib.v` | `Hoare_safeexec_compose`（L833-848）——Layer 2 → Layer 3 桥接引理 |
| `docs/dev/20260612-tarjan-scc-abstract-operator-design.md` | 三层精化架构、算子推导方法、执行顺序 |
| `docs/dev/20260612-tarjan-scc-c-monad.md` | C-Monad 边界设计、文件组织、证明结构 |
| `docs/dev/20260611-kmp-refinement-proof.md` | KMP refinement 全流程——参考其数学层设计 |
| `docs/plan-tarjan-scc-2sat-verification.md` | 六阶段总计划 |
