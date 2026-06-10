# Tarjan SCC 算法形式化验证计划

**Author**: Vitalrubbish
**Date**: 2026-06-10

> **前置依赖**：本阶段依赖 Shared SCC Lib（`scc_basic.v`），该文件提供有向图表示、SCC 数学定义、SCC 划分理论和图反转操作。Shared SCC Lib 计划见 `20260610-shared-scc-lib-plan.md`。
>
> **下游说明**：本阶段与 Kosaraju SCC 验证共享同一 `scc_basic.v`，两条路线在 shared lib 完成后可完全并行推进。

---

## 目录

1. [现状分析](#1-现状分析)
2. [与 Shared SCC Lib 的接口](#2-与-shared-scc-lib-的接口)
3. [总体架构](#3-总体架构)
4. [文件一：scc_tarjan.v — Tarjan 算法的数学描述](#4-文件一scc_tarjanv--tarjan-算法的数学描述)
5. [文件二：scc_tarjan_termination.v — 算法终止性与不变量](#5-文件二scc_tarjan_terminationv--算法终止性与不变量)
6. [文件三：scc_correctness.v — 主正确性证明](#6-文件三scc_correctnessv--主正确性证明)
7. [文件清单与 Makefile 修改](#7-文件清单与-makefile-修改)
8. [任务拆解与时间估算](#8-任务拆解与时间估算)
9. [风险管理](#9-风险管理)
10. [质量检查清单](#10-质量检查清单)
11. [开工顺序建议](#11-开工顺序建议)

---

## 1. 现状分析

### 1.1 前置条件

Shared SCC Lib（`scc_basic.v`）提供：

| 模块 | 来源 | 用途 |
|------|------|------|
| `DirectedGraphType` | `scc_basic.v` | 有向图的具体表示 |
| `DirectedGraphProp` | `scc_basic.v` | 图良构条件 |
| `dg_step_aux` | `scc_basic.v` | 有向 step 关系 |
| `mutually_reachable` | `scc_basic.v` | SCC spec：相互可达 |
| `is_SCC` | `scc_basic.v` | SCC spec：SCC 数学定义 |
| `scc_partition` | `scc_basic.v` | SCC spec：SCC 划分定义 |
| `condensation_edge` / `condensation_is_acyclic` | `scc_basic.v` | 缩点图无环 |
| 全部 GraphLib 核心 Type Class | `graph_basic.v` 等 | 图论基础设施 |

### 1.2 tarjan.v（桥定理）已有但不可直接复用

| 方面 | tarjan.v（桥定理） | Tarjan SCC 需要 |
|------|-------------------|-----------------|
| 图的类型 | **无向图**（`UndirectedGraph`、`StepUniqueUndirected`） | **有向图**（使用 `DirectedGraphType`） |
| DFS 树的边方向 | 子→父（`rt_step_aux`：`parent y = x`） | 父→子（有向 DFS 遍历方向） |
| low 值语义 | `low_tree v = subtree v ∪ subtree_step v`（非树边一步可达） | 需考虑**栈中节点**的回边/横叉边 |
| 关键假设 | `no_cross_edge`（无横叉边，DFS 树在无向图中的性质） | 有向 DFS 中**存在横叉边**，需精确分类 |
| 算法状态 | 无栈、无 SCC 输出 | 需要栈、onStack 标记、SCC 列表 |
| 核心结论 | `is_bridge e ↔ dfn x < low y` | `low[v] == dfn[v]` 时栈顶到 v 构成一个 SCC |

### 1.3 可直接复用的 GraphLib 基础设施

以下组件在 Tarjan SCC 证明中直接引用（全部已存在于 GraphLib）：

| 模块 | 文件 | 用途 |
|------|------|------|
| 图基础 Type Classes | `graph_basic.v` | `Graph`、`GValid`、`StepValid`、`StepUniqueDirected`、`NoEmptyEdge`、`FiniteGraph` |
| 可达性 | `reachable/reachable_basic.v` | `step`、`reachable`、连通性 |
| 受限可达性 | `reachable/reachable_restricted.v` | `step_without`、`reachable_without`、`reachable_tl` |
| 有根树 | `directed/rootedtree.v` | `RootedTree` Type Class、`offspring`、树归纳原理（`rooted_tree_induction_bottom_up`） |
| DFS 树 | `directed/dfstree.v` | `dfn_valid` 定义、`dfn_valid_offspring` |
| 子图 | `subgraph/subgraph.v` | 子图关系、`sub_reachable` |
| 最小值抽象 | `MaxMinLib/MaxMin.v` | `min_value_of_subset` 全套引理 |
| 全序实例 | `MaxMinLib/Interface.v` | `NatLe_TotalOrder` 实例、`min_union_iff` |
| 语法糖 | `Syntax.v` | `destruct_equality` 策略、`induction_1n`/`induction_n1` |
| 集合运算 | `SetsClass` | `∪`、`∩`、`==`、`[v]`、`∈` 等集合记号 |

### 1.4 可供参考的证明技巧（从 tarjan.v 学习）

| 技巧 | tarjan.v 中的位置 | SCC 中的适用场景 |
|------|-------------------|-----------------|
| 自底向上的树归纳 | `low_valid_implies_is_low` | low 值递归计算正确性证明 |
| 集合分解引理 | `low_tree_decompose` | `scc_low_candidates` 在有向图中的递归分解 |
| min_value_of_subset 的应用 | `is_low_v`/`low_valid_v` 的定义模式 | SCC low 值的语义定义 |
| 古典逻辑 case analysis | `closed_offspring` | 边分类和路径分析 |
| 反证法 + 低值矛盾 | `tarjan` 方向一 | `low[v] == dfn[v]` 时极大性证明 |

---

## 2. 与 Shared SCC Lib 的接口

### 2.1 导入方式

三个 Tarjan SCC 文件的第一组导入统一为：

```coq
(* Shared SCC Lib — 提供图结构、SCC 数学定义、spec *)
Require Import GraphLib.examples.scc_basic.

(* GraphLib 基础设施 *)
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.directed.rootedtree.
Require Import GraphLib.directed.dfstree.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.Syntax.

(* 外部库 *)
Require Import MaxMinLib.MaxMin MaxMinLib.Interface.
Require Import SetsClass.SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Lia.
```

### 2.2 从 Shared Lib 直接使用的定义

| 定义 | 在 Tarjan 中的用途 |
|------|-------------------|
| `DirectedGraphType V E` | `strongconnect_step` 和 `tarjan_algorithm` 的输入图类型 |
| `DirectedGraphProp dg` | 算法前置条件（图良构） |
| `dg_step_aux dg e x y` | `strongconnect_step` 中各构造子的边条件 |
| `dg_vvalid` / `dg_evalid` / `dg_listV` | 顶点有效性判断、外循环遍历 |
| `mutually_reachable g u v` | 正确性定理的 spec 目标 |
| `is_SCC g s` | `stack_segment_pop_is_scc` 的结论 |
| `scc_partition g sccs` | 主定理结论 |
| `condensation_edge` / `condensation_is_acyclic` | 主定理拓扑序结论 |

### 2.3 本阶段不使用但 Shared Lib 提供的定义

- `reverse_directed_graph` — Tarjan 不需要反图，这是为 Kosaraju 准备的
- `mutually_reachable_reverse` — 同上

Tarjan SCC 文件不需要关心这些定义，只需导入即可。

---

## 3. 总体架构

本阶段产出 **3 个新文件**（`scc_basic.v` 已在 Shared SCC Lib 阶段完成）：

```
scc_basic.v （Shared SCC Lib，前置依赖）
    ↓
scc_tarjan.v ──（算法描述）────────────┐
    ↓                                  │
scc_tarjan_termination.v        scc_correctness.v
（终止性与不变量）              （主正确性证明）
```

**设计原则**：

1. **与 GraphLib 风格一致**：Type Classes 参数化、集合谓词表示顶点集、归纳关系描述算法步骤
2. **与 tarjan.v 互补而非替代**：tarjan.v 专注于无向图桥定理，SCC 文件专注于有向图强连通分量
3. **分阶段可编译**：每个文件应能独立编译
4. **使用古典逻辑**：与 tarjan.v 风格一致
5. **spec 目标引用 `scc_basic.v`**：正确性定理的结论使用 `scc_basic.v` 中的 `is_SCC`、`scc_partition` 等定义

---

## 4. 文件一：scc_tarjan.v — Tarjan 算法的数学描述

**路径**：`SeparationLogic/GraphLib/examples/scc_tarjan.v`
**预估行数**：600–900 行
**预估时间**：2 周

### 4.1 导入依赖

```coq
Require Import GraphLib.examples.scc_basic.          (* Shared SCC Lib *)
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.directed.rootedtree.
Require Import GraphLib.directed.dfstree.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.Syntax.
Require Import MaxMinLib.MaxMin MaxMinLib.Interface.
Require Import SetsClass.SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Lia.
```

### 4.2 算法状态（TarjanState）

```coq
Record TarjanState (V: Type) := {
  ts_index    : V -> option nat;   (* None = 未访问 *)
  ts_lowlink  : V -> option nat;
  ts_onStack  : V -> bool;
  ts_stack    : list V;
  ts_sccs     : list (list V);     (* 已发现的 SCC，每个 SCC 是顶点列表 *)
  ts_nextIdx  : nat;
}.
```

使用 `option nat` 而非 `nat` + 哨兵值：更符合 Coq 惯用法。与 tarjan.v 的 `dfn : V -> nat`（假设所有顶点都有定义）不同，算法状态中大部分顶点尚未被访问。

### 4.3 初始状态

```coq
Definition tarjan_init {V: Type} : TarjanState V :=
  {| ts_index    := fun _ => None;
     ts_lowlink  := fun _ => None;
     ts_onStack  := fun _ => false;
     ts_stack    := nil;
     ts_sccs     := nil;
     ts_nextIdx  := 0 |}.
```

### 4.4 状态良构谓词

```coq
(* 栈中顶点与 onStack 一致，且栈无重复 *)
Definition stack_consistent {V: Type} (s: TarjanState V) : Prop :=
  (forall v, In v s.(ts_stack) <-> s.(ts_onStack) v = true) /\
  NoDup s.(ts_stack).

(* index 被赋值当且仅当顶点已被访问 *)
Definition index_consistent {V: Type} (s: TarjanState V) : Prop :=
  forall v, (s.(ts_index) v <> None) <-> (s.(ts_onStack) v = true \/
            exists scc, In scc s.(ts_sccs) /\ In v scc).

(* 已发现 SCC 的顶点互不相交 *)
Definition sccs_disjoint {V: Type} (s: TarjanState V) : Prop :=
  forall scc1 scc2 v, In scc1 s.(ts_sccs) -> In scc2 s.(ts_sccs) ->
    In v scc1 -> In v scc2 -> scc1 = scc2.
```

### 4.5 有向 DFS 边分类

有向图的 DFS 产生**四类边**：

```coq
Inductive dfs_edge_kind {G V E: Type} `{Graph G V E}
  (dfstree: G) (g: G) (e: E) (x y: V) : Type :=
  | TreeEdge    : step_aux dfstree e x y -> dfs_edge_kind dfstree g e x y
  | BackEdge    : reachable dfstree y x ->
                  ~ step_aux dfstree e x y ->
                  dfs_edge_kind dfstree g e x y
  | ForwardEdge : reachable dfstree x y ->
                  ~ step_aux dfstree e x y ->
                  dfs_edge_kind dfstree g e x y
  | CrossEdge   : ~ reachable dfstree x y ->
                  ~ reachable dfstree y x ->
                  dfs_edge_kind dfstree g e x y.
```

**与 tarjan.v 的关键差异**：
- tarjan.v 处理无向图 DFS 树，无向边只有树边和回边（因此可以假设 `no_cross_edge`）
- 有向图 DFS 存在四类边：树边、回边、前向边、横叉边
- 横叉边的存在是 SCC 算法必须正确处理的核心挑战

### 4.6 Tarjan SCC 的 low 值定义（有向版）

```coq
(* Tarjan SCC 的 low 值语义：
   low[v] = min({dfn[v]} ∪ {dfn[w] | 从 v 的子树有一条指向栈中 w 的边}) *)
Definition scc_low_candidates {V E: Type} `{Graph G V E}
  (dfstree: RootedTreeType V E) (g: DirectedGraphType V E)
  (dfn: V -> nat) (stack_set: V -> Prop) (v: V) : V -> Prop :=
  fun w =>
    (w = v) \/  (* v 自身 *)
    (exists u, offspring dfstree v u /\ step g u w /\ stack_set w).

Definition is_scc_low_v {V E: Type} `{Graph G V E}
  (dfstree: RootedTreeType V E) (g: DirectedGraphType V E)
  (dfn: V -> nat) (stack_set: V -> Prop) (v: V) (lv: nat) : Prop :=
  min_value_of_subset Nat.le (scc_low_candidates dfstree g dfn stack_set v) dfn lv.
```

**与 tarjan.v 中 `is_low_v` 的区别**：

| 方面 | tarjan.v (`is_low_v`) | SCC (`is_scc_low_v`) |
|------|----------------------|---------------------|
| 候选顶点集合 | `low_tree v = subtree v ∪ subtree_step v` | `scc_low_candidates = {v} ∪ {w \| ∃u∈subtree(v), u→w, w∈stack}` |
| 是否包含 `v` 自身 | 不直接包含（通过 subtree 间接） | 显式包含（对应算法中 `low[v]` 初始化为 `dfn[v]`） |
| 非树边的目标约束 | 无约束（`step_without_tree` 即可） | 必须**仍在栈中**（`stack_set w`） |
| 边的方向 | 无向（对称） | 严格有向 |

### 4.7 strongconnect 步骤的归纳定义

```coq
Inductive strongconnect_step {V E: Type}
  (g: DirectedGraphType V E) (gvalid: DirectedGraphProp g)
  : TarjanState V -> V -> TarjanState V -> Prop :=

  (* 初始化：分配编号并入栈 *)
  | sc_init : forall s v,
      ts_index s v = None ->
      let s1 := update_enter s v in  (* index[v]=lowlink[v]=nextIdx; nextIdx++; 入栈 *)
      (* 遍历 v 的所有出边邻居...需要递归/迭代 *)
      ...
      strongconnect_step g gvalid s v s_final

  (* 处理邻居 w：若 w 未访问则递归 *)
  | sc_recurse : forall s s1 s2 v w,
      step g v w ->
      ts_index s1 w = None ->
      strongconnect_step g gvalid s1 w s2 ->
      let s3 := update_lowlink_min s2 v w in
      strongconnect_step g gvalid s v s3

  (* 处理邻居 w：若 w 在栈中则用 dfn[w] 更新 lowlink[v] *)
  | sc_back_edge : forall s s' v w,
      step g v w ->
      ts_onStack s w = true ->
      ts_lowlink s' v > ts_index s' w ->
      let s'' := set_lowlink s' v (unwrap (ts_index s' w)) in
      strongconnect_step g gvalid s v s''

  (* 回溯完成：若 low[v] == dfn[v]，弹出 SCC *)
  | sc_pop_scc : forall s v,
      ts_lowlink s v = ts_index s v ->
      let '(popped, stack') := span (fun x => x <> v) s.(ts_stack) in
      let s' := {| ts_index    := s.(ts_index);
                   ts_lowlink  := s.(ts_lowlink);
                   ts_onStack  := mark_false s.(ts_onStack) (v :: popped);
                   ts_stack    := stack';
                   ts_sccs     := (v :: popped) :: s.(ts_sccs);
                   ts_nextIdx  := s.(ts_nextIdx) |} in
      strongconnect_step g gvalid s v s'

  (* 步骤的传递闭包 *)
  | sc_trans : forall s1 s2 s3 v,
      strongconnect_step g gvalid s1 v s2 ->
      strongconnect_step g gvalid s2 v s3 ->
      strongconnect_step g gvalid s1 v s3.
```

### 4.8 完整算法步骤

```coq
Inductive tarjan_algorithm {V E: Type}
  (g: DirectedGraphType V E) (gvalid: DirectedGraphProp g)
  : list V -> TarjanState V -> TarjanState V -> Prop :=
  | ta_nil : forall s,
      tarjan_algorithm g gvalid nil s s
  | ta_visited : forall v vs s s',
      ts_index s v <> None ->
      tarjan_algorithm g gvalid vs s s' ->
      tarjan_algorithm g gvalid (v :: vs) s s'
  | ta_unvisited : forall v vs s s1 s',
      ts_index s v = None ->
      strongconnect_step g gvalid s v s1 ->
      tarjan_algorithm g gvalid vs s1 s' ->
      tarjan_algorithm g gvalid (v :: vs) s s'.
```

### 4.9 主正确性定理陈述

```coq
Theorem tarjan_scc_correctness_goal {V E: Type}
  (g: DirectedGraphType V E) (gvalid: DirectedGraphProp g) :
  forall (s_final: TarjanState V),
    tarjan_algorithm g gvalid (dg_listV g) (tarjan_init) s_final ->
    (* 1. 算法终止（所有顶点被访问且没有剩余栈中顶点） *)
    (forall v, dg_vvalid g v -> ts_index s_final v <> None) /\
    ts_stack s_final = nil /\
    (* 2. SCC 划分正确（使用 scc_basic.v 的 scc_partition） *)
    scc_partition (dg_to_graph g) (map list_to_set s_final.(ts_sccs)) /\
    (* 3. 顶点到 SCC 的归属关系与相互可达一致（使用 scc_basic.v 的 mutually_reachable） *)
    (forall u v, dg_vvalid g u -> dg_vvalid g v ->
      mutually_reachable (dg_to_graph g) u v <->
      exists scc, In scc s_final.(ts_sccs) /\ In u scc /\ In v scc) /\
    (* 4. SCC 顺序与缩点图拓扑序一致（使用 scc_basic.v 的 condensation_edge） *)
    topological_order (condensation (dg_to_graph g) (map list_to_set s_final.(ts_sccs)))
                      (map list_to_set s_final.(ts_sccs)).
```

**注意**：结论 (2)(3) 中的 `scc_partition` 和 `mutually_reachable` 来自 `scc_basic.v`。这确保了 Tarjan 算法的 spec 与 Kosaraju 一致——两者都在证明"我的算法输出满足 `scc_basic.v` 定义的 `scc_partition`"。

---

## 5. 文件二：scc_tarjan_termination.v — 算法终止性与不变量

**路径**：`SeparationLogic/GraphLib/examples/scc_tarjan_termination.v`
**预估行数**：500–800 行
**预估时间**：2 周

### 5.1 导入依赖

```coq
Require Import GraphLib.examples.scc_basic.
Require Import GraphLib.examples.scc_tarjan.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.directed.rootedtree.
Require Import GraphLib.directed.dfstree.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.Syntax.
Require Import MaxMinLib.MaxMin MaxMinLib.Interface.
Require Import SetsClass.SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Lia.
```

### 5.2 核心不变量

```coq
Record tarjan_invariant {V E: Type}
  (g: DirectedGraphType V E) (gvalid: DirectedGraphProp g)
  (s: TarjanState V) : Prop := {

  (* 1. 栈内部一致性 *)
  ti_stack_cons : stack_consistent s;

  (* 2. index 与顶点状态一致 *)
  ti_index_cons : index_consistent s;

  (* 3. lowlink 仅对已访问顶点有定义 *)
  ti_lowlink_def : forall v, ts_index s v <> None <-> ts_lowlink s v <> None;

  (* 4. lowlink[v] <= index[v] *)
  ti_lowlink_le : forall v, ts_index s v <> None ->
    option_nat_le (ts_lowlink s v) (ts_index s v);

  (* 5. 已发现的 SCC 都正确（使用 scc_basic.v 的 is_SCC） *)
  ti_sccs_valid : forall scc, In scc s.(ts_sccs) ->
    is_SCC (dg_to_graph g) (fun v => In v scc);

  (* 6. SCC 间顶点互不相交 *)
  ti_sccs_disjoint : sccs_disjoint s;

  (* 7. SCC 顶点 + 栈中顶点 = 所有已访问顶点 *)
  ti_sccs_stack_cover : forall v, ts_index s v <> None ->
    (exists scc, In scc s.(ts_sccs) /\ In v scc) \/
    ts_onStack s v = true;

  (* 8. 已出 SCC 的顶点不在栈中 *)
  ti_sccs_not_on_stack : forall v scc,
    In scc s.(ts_sccs) -> In v scc -> ts_onStack s v = false;
}.
```

**注意**：不变量 (5) 直接引用 `scc_basic.v` 的 `is_SCC`。这确保算法在中间步骤中已输出的 SCC 满足 SCC 的数学定义。

### 5.3 strongconnect 保持不变量

```coq
Lemma strongconnect_step_preserves_invariant {V E: Type}
  (g: DirectedGraphType V E) (gvalid: DirectedGraphProp g) :
  forall s v s',
    tarjan_invariant g gvalid s ->
    strongconnect_step g gvalid s v s' ->
    tarjan_invariant g gvalid s'.
```

**证明策略**：对 `strongconnect_step` 的每个构造子分别证明。最复杂的 cases：
- `sc_init`：需要证明 index/lowlink 赋值和入栈操作保持一致性
- `sc_recurse`：需要利用递归调用的归纳假设
- `sc_pop_scc`：需要证明弹出操作产生的顶点集合是一个 SCC（引用 `scc_basic.v` 的 `is_SCC` 定义）

### 5.4 有限性论证 — 终止证明

参考 `rootedtree.v` 中 `parent_relation_is_well_founded` 的技术：

```coq
(* 度量函数：未访问顶点数 + 栈中顶点数 *)
Definition tarjan_progress_measure {V: Type} (g: DirectedGraphType V E) (s: TarjanState V) : nat :=
  let unvisited := length (filter (fun v => ts_index s v = None ?) (dg_listV g)) in
  let stack_len := length (ts_stack s) in
  unvisited + stack_len.

Lemma strongconnect_step_decreases_or_stacks_shrink :
  forall g gvalid s v s',
    strongconnect_step g gvalid s v s' ->
    tarjan_progress_measure g s' < tarjan_progress_measure g s \/
    length (ts_stack s') < length (ts_stack s).

Theorem tarjan_algorithm_terminates :
  forall g gvalid,
    exists s_final, tarjan_algorithm g gvalid (dg_listV g) (tarjan_init) s_final /\
    is_final_state g s_final.
```

### 5.5 关键子引理清单

| # | 引理 | 说明 |
|---|------|------|
| T1 | `init_preserves_invariant` | 初始状态满足不变量 |
| T2 | `stack_push_preserves_consistency` | 入栈保持 `stack_consistent` |
| T3 | `stack_pop_segment_preserves_consistency` | 弹出一段保持 `stack_consistent` |
| T4 | `lowlink_update_preserves_le` | 用更小的值更新 lowlink 保持 `lowlink_le` |
| T5 | `unvisited_count_decreases` | 每次 `sc_init` 减少未访问顶点计数 |
| T6 | `stack_shrinks_in_pop` | `sc_pop_scc` 至少弹出 1 个顶点 |

---

## 6. 文件三：scc_correctness.v — 主正确性证明

**路径**：`SeparationLogic/GraphLib/examples/scc_correctness.v`
**预估行数**：1000–1500 行
**预估时间**：4 周

这是最核心也是工作量最大的文件。

### 6.1 证明结构总览

```
                         tarjan_scc_correctness
                                │
                ┌───────────────┼───────────────┐
                │               │               │
    Lemma 1:    │    Lemma 2:   │    Lemma 3:   │
    栈弹出子段  │    low 值     │    完备性      │
    恰好是 SCC  │    正确性     │               │
    (Soundness) │               │               │
```

### 6.2 Lemma 1（Soundness）：`low[v] == dfn[v]` 时弹出的栈段构成 SCC

```coq
Lemma stack_segment_pop_is_scc {V E: Type}
  (g: DirectedGraphType V E) (gvalid: DirectedGraphProp g)
  (s: TarjanState V) (v: V)
  (Hinv: tarjan_invariant g gvalid s)
  (Hlow_eq_idx : ts_lowlink s v = ts_index s v)
  (Hv_on_stack : ts_onStack s v = true) :
  let seg := stack_segment_above s v in
  (* 使用 scc_basic.v 的 is_SCC 作为结论 *)
  is_SCC (dg_to_graph g) (fun w => In w seg).
```

**证明关键步骤**：

1. **内部相互可达**：
   - 对栈段中任两个顶点 a, b，通过 low 值的语义定义证明存在路径
   - 关键子引理：栈段中 v 以上的每个顶点 w 都可以到达 v，且 v 可以到达 w
   - 第一方向（w → v）：利用 low[w] ≤ dfn[v] 的性质（因为 w 在 v 以上入栈，dfn 更大），结合 low 值的语义
   - 第二方向（v → w）：利用 DFS 树的子树性质（v 是 w 的祖先）

2. **极大性**：
   - 反证法：假设存在栈外顶点 u 与 v 相互可达
   - 若 u 已被分配到某个 SCC：矛盾，因为 u 应该随 v 一起被弹出
   - 若 u 尚未访问：矛盾，因为 u 可达 v 意味着 DFS 应该先访问 u

### 6.3 Lemma 2（Low Correctness）：算法计算的 lowlink 满足 `is_scc_low_v`

使用自底向上的树归纳。

```coq
(* 基于有向 DFS 树的 low 值的局部/递归定义 *)
Definition scc_low_valid_v {V E: Type} `{Graph G V E}
  (dfstree: RootedTreeType V E) (dfn: V -> nat) (stack_set: V -> Prop)
  (low: V -> nat) (v: V) : Prop :=
  min_value_of_subset Nat.le
    (Sets.singleton v ∪
     (fun w => step g v w /\ stack_set w) ∪
     (fun u => exists e, step_aux dfstree e v u))
    (fun x => match x with
             | inl (inl v') => dfn v'
             | inl (inr w) => dfn w
             | inr u => low u
             end)
    (low v).

(* 递归定义 ⇔ 语义定义 *)
Lemma scc_low_valid_implies_is_scc_low {V E: Type} `{Graph G V E}
  (dfstree: RootedTreeType V E) (dfn: V -> nat) (stack_set: V -> Prop)
  (low: V -> nat) :
  scc_low_valid dfstree dfn stack_set low ->
  (forall v, vvalid dfstree v -> is_scc_low_v dfstree dfn stack_set v (low v)).
```

**证明策略**：参考 tarjan.v 中 `low_valid_implies_is_low` 的模式。
1. 使用 `rooted_tree_induction_bottom_up` 自底向上归纳
2. 在归纳步中，利用类比 `low_tree_decompose` 的引理对 `scc_low_candidates` 进行递归分解
3. 关键引理：`scc_low_candidates_decompose`（`scc_low_candidates` 可递归分解）

### 6.4 Lemma 3（Completeness）：算法发现所有 SCC

```coq
Lemma tarjan_complete {V E: Type}
  (g: DirectedGraphType V E) (gvalid: DirectedGraphProp g)
  (s_final: TarjanState V)
  (Halg: tarjan_algorithm g gvalid (dg_listV g) (tarjan_init) s_final) :
  forall scc, is_SCC (dg_to_graph g) scc ->     (* 使用 scc_basic.v 的 is_SCC *)
  exists scc_list, In scc_list s_final.(ts_sccs) /\
    (forall v, scc v <-> In v scc_list).
```

**证明关键步骤**：
1. 对每个原图 SCC，证明其在算法执行过程中恰好被完整弹出一次
2. 利用不变量：当 SCC 的"根"（dfn 最小的顶点）的 `strongconnect_step` 完成时，整个 SCC 被弹出
3. 反证法：假设某 SCC 未被完整弹出或分散在多个 ts_sccs 中

### 6.5 关键子引理清单

| # | 引理 | 复杂度 | 说明 |
|---|------|--------|------|
| L1 | `stack_segment_above_defined` | 低 | 从栈中定位 v 以上的连续段的函数定义 |
| L2 | `lowlink_monotonic_on_stack` | 中 | 栈中 lowlink 值从底到顶 non-decreasing |
| L3 | `subtree_reachability_preserved` | 中 | v 子树中的顶点可以到达 v（通过树边） |
| L4 | `back_edge_implies_low_update` | 中 | 回边→lowlink 被正确更新 |
| L5 | `cross_edge_target_on_stack_or_done` | 高 | 横叉边的目标要么在栈中，要么已在完成的 SCC 中 |
| L6 | `dfs_reachability_through_low` | 高 | 若 low[w] = dfn[v] ≤ dfn[w]，则 w 可达 v |
| L7 | `stack_segment_closed` | 高 | 当 `low[v] = dfn[v]` 时，v 以上的栈段是"封闭的" |
| L8 | `scc_root_has_low_eq_index` | 中 | SCC 中 dfn 最小的顶点满足 `low[v] = dfn[v]` |
| L9 | `condensation_topological_order` | 高 | ts_sccs 的顺序与缩点图的拓扑序一致（引用 `scc_basic.v` 的 `condensation_edge`） |
| L10 | `scc_low_candidates_decompose` | 中 | `scc_low_candidates` 的递归分解引理 |

### 6.6 证明技术指南

1. **自底向上的树归纳**：复用 `rooted_tree_induction_bottom_up` 处理 DFS 树上 low 值的性质。

2. **集合论与 min 操作**：大量使用 `SetsClass` 的集合运算和 `MaxMinLib` 的 `min_value_of_subset` 引理。`min_union_iff`（`Interface.v` 中）是处理 min 值递归定义的利器。

3. **古典逻辑**：对于存在性论证（如"存在一条回边使得 low 值等于某 dfn"），使用 `classic` 做 case analysis。

4. **Well-founded 归纳**：参考 `rootedtree.v` 中 `parent_relation_is_well_founded` 的技术，用于证明算法终止。

5. **与 tarjan.v 的差异**：虽然概念相关（low 值、dfn），但有向图的 SCC 使得几乎所有核心引理都需要重新证明。可以**参考** tarjan.v 的证明技巧，但必须独立写证明。

---

## 7. 文件清单与 Makefile 修改

### 7.1 新增文件清单

```
SeparationLogic/GraphLib/examples/
├── scc_basic.v                   # Shared SCC Lib 阶段（前置依赖）
├── scc_tarjan.v                  # Tarjan Phase：Tarjan 算法的数学描述
├── scc_tarjan_termination.v      # Tarjan Phase：算法终止性与不变量
└── scc_correctness.v             # Tarjan Phase：主正确性证明
```

### 7.2 Makefile 修改

在 `SeparationLogic/GraphLib/Makefile` 中修改 `EXAMPLES_FILES` 行：

```makefile
# 修改前：
EXAMPLES_FILES = examples/floyd.v examples/dijkstra.v examples/prim.v examples/kruskal.v examples/dfs.v examples/tarjan.v

# Shared SCC Lib 完成后：
EXAMPLES_FILES = examples/floyd.v examples/dijkstra.v examples/prim.v examples/kruskal.v examples/dfs.v examples/tarjan.v \
                 examples/scc_basic.v

# Tarjan Phase 完成后：
EXAMPLES_FILES = examples/floyd.v examples/dijkstra.v examples/prim.v examples/kruskal.v examples/dfs.v examples/tarjan.v \
                 examples/scc_basic.v \
                 examples/scc_tarjan.v examples/scc_tarjan_termination.v examples/scc_correctness.v
```

依赖顺序：`scc_basic.v` → `scc_tarjan.v` → `scc_tarjan_termination.v` / `scc_correctness.v`。`coqdep` 会自动解析依赖，但 Makefile 中显式顺序有助于可读性。

### 7.3 不修改的已有文件

| 文件 | 原因 |
|------|------|
| `SeparationLogic/GraphLib/graph_basic.v` | 只读引用基础 Type Classes |
| `SeparationLogic/GraphLib/reachable/*.v` | 只读引用可达性定义 |
| `SeparationLogic/GraphLib/directed/*.v` | 只读引用树结构和 dfn 定义 |
| `SeparationLogic/GraphLib/subgraph/subgraph.v` | 只读引用子图关系 |
| `SeparationLogic/GraphLib/examples/tarjan.v` | 只读引用桥定理证明（不修改） |
| `SeparationLogic/GraphLib/examples/scc_basic.v` | Shared SCC Lib 产出，只读引用 |
| `SeparationLogic/MaxMinLib/*.v` | 只读引用 min/max 抽象 |
| 所有 Type Class 实例 | 均不修改 |

---

## 8. 任务拆解与时间估算

**总时间估算：8 周**（单人全职，不含 Shared SCC Lib 的 1.5–2 周）

### 第 1–2 周：scc_tarjan.v

| 天 | 任务 | 产出 |
|----|------|------|
| D1–D2 | 定义 `TarjanState`、`tarjan_init`、状态良构谓词 | `stack_consistent`、`index_consistent`、`sccs_disjoint` |
| D3–D4 | 定义 `dfs_edge_kind`（四类边）和分类引理 | 有向图 DFS 边分类 |
| D5–D6 | 定义 `scc_low_candidates`、`is_scc_low_v` | 有向图 low 值的语义定义 |
| D7–D9 | 定义 `strongconnect_step` 的 4–5 个构造子 | 算法步骤的归纳关系 |
| D10–D11 | 定义 `tarjan_algorithm`（3 个构造子）和基础性质 | 完整算法关系 |
| D12–D14 | 陈述主正确性定理、`is_scc_low` 的基本性质 | 完整 `scc_tarjan.v` |

### 第 3–4 周：scc_tarjan_termination.v

| 天 | 任务 | 产出 |
|----|------|------|
| D15–D16 | 定义 `tarjan_invariant`（8 个字段） | 核心不变量 record |
| D17–D18 | 证明初始状态满足不变量 | `init_preserves_invariant` |
| D19–D22 | 证明 `strongconnect_step` 每个构造子保持不变量 | `strongconnect_step_preserves_invariant` |
| D23–D25 | 定义度量函数，证明每一步度量递减 | 终止性论证 |
| D26–D28 | 组合证明主终止定理 + review | 完整的 `scc_tarjan_termination.v` |

### 第 5–8 周：scc_correctness.v（最关键）

| 天 | 任务 | 产出 |
|----|------|------|
| D29–D32 | Lemma 1：`stack_segment_pop_is_scc`（Soundness） | 弹出 SCC 正确性（~200 行） |
| D33–D36 | Lemma 2 辅助：`scc_low_candidates_decompose`（集合分解） | low 值集合的递归分解 |
| D37–D42 | Lemma 2 主体：`scc_low_valid_implies_is_scc_low`（Low Correctness） | low 值递归计算 ⇔ 语义定义（~300 行） |
| D43–D46 | Lemma 3 辅助：stack 和 low 的单调性引理 | L2、L4、L5 |
| D47–D50 | Lemma 3 主体：`tarjan_complete`（Completeness） | 完备性（~250 行） |
| D51–D54 | 组装主定理 `tarjan_scc_correctness_goal` | 最终正确性证明（~200 行） |
| D55–D56 | 全面 review、调试、编译验证 | 完整的 `scc_correctness.v` |

---

## 9. 风险管理

| # | 风险 | 可能性 | 影响 | 缓解措施 |
|---|------|--------|------|----------|
| R1 | `strongconnect_step` 的归纳定义不够表达递归语义（对邻居的遍历） | 中 | 高 | 先用简单的"全序处理邻居"模型；若不够，引入 `Forall` 对出边列表的约束；最坏情况：使用 `Relation_Operators.rtclosure` |
| R2 | 有向 DFS 森林的 `dfs_edge_kind` 分类比预期复杂 | 高 | 中 | 先简化：假设 DFS 树是单棵树（图强连通），再泛化到森林 |
| R3 | `is_scc_low_v` 的语义定义与算法 `lowlink` 的等价性证明过长 | 高 | 中 | 分两层：先定义 `scc_low_semantic` 和 `scc_low_algorithmic`，再证明等价性 |
| R4 | `scc_low_candidates_decompose` 的集合分解引理有向图版比无向图版复杂 | 中 | 中 | 先证明不含栈条件（`stack_set := fun _ => True`）的简化版，再泛化 |
| R5 | `condensation_topological_order` 证明需要深层组合论证 | 中 | 中 | 先证明 SCC 弹出顺序是缩点图的反拓扑序（不含环性质），再用循环性矛盾论证 |
| R6 | Shared SCC Lib 的 `scc_basic.v` 在 Tarjan 开发过程中需要修改 | 中 | 中 | Shared lib 应为稳定接口；若需要修改，必须同步更新 Tarjan 和 Kosaraju 两侧 |
| R7 | 证明文件过大导致 Coq 编译时间过长 | 中 | 低 | 若 `scc_correctness.v` 超过 2000 行，拆分为 `scc_correctness_part1.v` / `part2.v` |

---

## 10. 质量检查清单

### scc_tarjan.v
- [ ] `coqc` 编译无错误
- [ ] `TarjanState` 的定义包含所有必要字段
- [ ] `stack_consistent`、`index_consistent`、`sccs_disjoint` 定义自洽
- [ ] `dfs_edge_kind` 的四类边互斥且完备（每条有向边恰好属于一类）
- [ ] `is_scc_low_v` 的定义正确刻画 Tarjan 的 low 值语义
- [ ] `strongconnect_step` 关系是确定的（每一步产生唯一后继状态）
- [ ] `tarjan_algorithm` 关系能表达"对所有顶点依次处理"
- [ ] 主定理陈述类型正确（`Check tarjan_scc_correctness_goal` 通过）
- [ ] 主定理结论使用 `scc_basic.v` 的 `scc_partition` 和 `mutually_reachable`

### scc_tarjan_termination.v
- [ ] `coqc` 编译无错误
- [ ] `tarjan_invariant` 的 8 个字段是互不冗余的最小集合
- [ ] 初始状态满足不变量
- [ ] 每个 `strongconnect_step` 构造子保持不变量
- [ ] 不变量 (5) 引用 `scc_basic.v` 的 `is_SCC`
- [ ] 对任意有限有向图，`tarjan_algorithm_terminates` 成立
- [ ] 终止度量函数的值严格递减

### scc_correctness.v
- [ ] `coqc` 编译无错误
- [ ] Lemma 1（Soundness）：`stack_segment_pop_is_scc` 证明通过，结论为 `is_SCC`
- [ ] Lemma 2（Low Correctness）：`scc_low_valid_implies_is_scc_low` 证明通过
- [ ] Lemma 3（Completeness）：`tarjan_complete` 证明通过
- [ ] `tarjan_scc_correctness_goal` 全部 4 个子目标均被证明
- [ ] 没有遗留 `Admitted`
- [ ] 没有引入额外的 `Axiom`（除古典逻辑的 `classic` 外）

### 全局
- [ ] 全部 3 个文件均能通过 `coqc` 编译
- [ ] Makefile 已更新，`make all` 在 GraphLib 目录下通过
- [ ] 文件依赖顺序正确（scc_basic → scc_tarjan → termination / correctness）
- [ ] 没有修改 Shared SCC Lib 的冻结前缀

---

## 11. 开工顺序建议

### 11.1 前置条件

本阶段必须在 **Shared SCC Lib（`scc_basic.v`）编译通过** 之后才能开始。

### 11.2 推荐执行顺序

1. **先在 Shared SCC Lib 完成验证后再开始**
   - 确保 `DirectedGraphType`、`is_SCC`、`scc_partition` 的定义稳定
   - 在同一轮 Rocq 会话中测试 `scc_basic.v` 的 `Require Import` 可通过

2. **在骨架层面写 `scc_tarjan.v`**（第 1–2 周）
   - 先把 `TarjanState`、`strongconnect_step`、`tarjan_algorithm` 和主定理陈述写出来
   - 主定理证明可以先 `Admitted` 占位
   - 目标：确认定义与 `scc_basic.v` 的接口对齐

3. **然后写 `scc_tarjan_termination.v`**（第 3–4 周）
   - 终止性证明相对独立（只需要不变量，不需要完整正确性）
   - 先完成这部分可以建立对不变量定义的信心

4. **最后攻坚 `scc_correctness.v`**（第 5–8 周）
   - 核心正确性证明是最大的难点
   - 按 Lemma 1 → Lemma 2 → Lemma 3 → 组装主定理的顺序推进

### 11.3 开发方法建议

- **在 Rocq 中交互式探索**：遇到复杂子证明时，使用 `rocq-mcp` 交互式开发
- **阶段性 commit**：每完成一个文件的编译，立即 commit
- **参考但不照搬 tarjan.v**：tarjan.v 提供优秀的证明模式（树归纳、集合分解、min 值操作），但 SCC 的有向性意味着需要独立写证明
- **遇到困难时回退到简化版**：如果某个引理卡住超过 2 天，考虑先证明简化版本，再逐步泛化
- **保持与 Shared SCC Lib 的接口稳定**：如果需要修改 `scc_basic.v`，先与合作者同步

### 11.4 协作衔接

- 本阶段与 Kosaraju SCC 验证**完全并行**——两者都依赖 `scc_basic.v`，但互不依赖
- 如果合作者在 Kosaraju 开发中发现 `scc_basic.v` 需要补充定义或引理，应先修改 shared lib，再同步更新双方
- 两个算法的主定理都指向同一个 `scc_partition` spec，这是交叉验证的基础

---

*本计划基于 QCP v2.0.2、Rocq 8.20.1、GraphLib 现有版本编写。*
*前置依赖：Shared SCC Lib 计划见 `20260610-shared-scc-lib-plan.md`。*
*本文件描述 Tarjan SCC 算法形式化验证（原 Phase 1 的算法部分），SCC 数学定义已抽离至 Shared SCC Lib。*
