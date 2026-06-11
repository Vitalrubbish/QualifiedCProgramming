# 使用 QCP 框架证明 Tarjan SCC 算法正确性并用于 2-SAT 的全过程计划

> **当前架构状态 (2026-06-11 更新)**
>
> 本计划已根据仓库最新架构全面刷新。关键变更：
> - Tarjan 算法形式化已位于 `SeparationLogic/algorithms/Tarjan/`（11 文件，8911 行），使用 monadic Hoare logic + TraceLib
> - 仓库新增 `algorithms/DFS/`、`tracelib/`、`coq-record-update/` 等基础设施
> - 图表示统一使用 `OriginalGraphType`（来自 `GraphLib/examples/tarjan.v`），不再使用自建的 `DirectedGraphType`
> - SCC 数学定义（`mutually_reachable`、`is_SCC`、`scc_partition`、`condensation`）尚未在新架构中实现——这是阶段一的核心待办
> - 原 `GraphLib/examples/scc_basic.v` 已删除，阶段一的 SCC 基础层应在 `algorithms/Tarjan/` 下重建

## 目录

1. [项目背景与 QCP 框架概述](#1-项目背景与-qcp-框架概述)
2. [现有基础设施分析](#2-现有基础设施分析)
3. [总体路线图](#3-总体路线图)
4. [阶段一：Rocq 中 SCC 数学基础与算法规格](#4-阶段一rocq-中-scc-数学基础与算法规格)
5. [阶段二：C 语言的 Tarjan SCC 实现与标注](#5-阶段二c-语言的-tarjan-scc-实现与标注)
6. [阶段三：符号执行与 VC 生成](#6-阶段三符号执行与-vc-生成)
7. [阶段四：验证条件的证明](#7-阶段四验证条件的证明)
8. [阶段五：2-SAT 问题形式化与归约](#8-阶段五2-sat-问题形式化与归约)
9. [阶段六：集成与最终验证](#9-阶段六集成与最终验证)
10. [文件结构与交付物](#10-文件结构与交付物)
11. [工作量估算与风险评估](#11-工作量估算与风险评估)
12. [执行建议](#12-执行建议)

---

## 1. 项目背景与 QCP 框架概述

### 1.1 QCP 是什么

QCP（Qualified C Programming）是一个基于分离逻辑的 C 程序验证工具。它的核心工作流程为：

1. **编写带标注的 C 程序**
   - 前置条件（`Require`）和后置条件（`Ensure`）
   - 循环不变量（`Inv Assert`）
   - 中间断言（`Assert`）
   - 函数的逻辑变量声明（`With`）
   - 所有标注均使用分离逻辑断言语言编写

2. **运行符号执行**（`symexec` 命令行工具）
   - 逐条语句执行符号计算
   - 在每个标注点生成蕴含条件（entailment）
   - 输出三个 Rocq 文件：
     - `*_goal.v`：全部需要证明的验证条件（VC）
     - `*_proof_auto.v`：工具自动证明的 VC
     - `*_proof_manual.v`：需要人工补全证明的 VC

3. **在 Rocq 中证明验证条件**
   - 使用分离逻辑专用策略：`Intros`、`Exists`、`entailer!`、`sep_apply`、`prop_apply` 等
   - 结合标准 Coq 策略：`intros`、`destruct`、`induction`、`lia` 等
   - 证明目标形式为 `P |-- Q`（分离逻辑蕴含）

4. **最终检查**
   - 编译 Rocq 文件确保无 `Admitted` 或额外 `Axiom`
   - 验证 `*_goal_check.v` 通过
   - 清理临时文件

### 1.2 Agent 验证工作流

QCP 仓库支持结构化的 agent 验证工作流（详见 `AGENTS.md`），状态机如下：

```
intake → annotation → goal-frozen → vc-checking → vc-proving → final-check → done
```

- **主 agent**：独占 phase 切换、符号执行、Rocq 编译、最终检查
- **`annotation-subagent`**：在隔离 scratch 上迭代标注和 spec 定义，每轮标注后必须通过 `annotation-checking` 质量门
- **`vc-checking-subagent`**：对 manual VC 进行语义分类，给出 proof group 分组建议
- **`vc-proving-subagent`**：执行脚本化并发 worker 流水线证明 manual VC
- **`final-check`**：结构审计、Rocq 编译、`Admitted`/额外 `Axiom` 审查

### 1.3 分离逻辑断言语言速览

| 说明 | Rocq 写法 | C 标注写法 |
|------|-----------|------------|
| 分离合取 | `P ** Q` | `P * Q` |
| 存在量词 | `EX` | `exists` |
| 纯命题 | `[| P |]` | `P` |
| 4字节整数存储 | `p # Int \|-> v` | `data_at(p, int, v)` |
| 指针存储 | `p # Ptr \|-> v` | `data_at(p, int *, v)` |
| 结构体字段访问 | `x # "A" ->ₛ "f"` | `x -> f` |

---

## 2. 现有基础设施分析

### 2.1 仓库总体架构

当前仓库的 Rocq 形式化部分组织如下：

```
SeparationLogic/
├── GraphLib/             # 图论核心库（Type Classes、有根树、可达性、子图）
│   ├── graph_basic.v     # Graph/GValid/StepValid/reachable 等核心定义
│   ├── directed/         # rootettree.v, dfstree.v
│   ├── reachable/        # reachable_basic.v, epath.v, bfs_dist.v 等
│   ├── subgraph/         # subgraph.v
│   ├── undirected/       # undirected_basic.v, tree.v
│   └── examples/         # floyd.v, dijkstra.v, prim.v, kruskal.v, tarjan.v
├── algorithms/           # 算法形式化（monadic/trace-based 风格）
│   ├── BFS/              # BFS.v, BFS_path.v, Go.v
│   ├── DFS/              # DFS.v, DFS_traditional.v, C10909_MonadProg_DFS.v
│   ├── Tarjan/           # Tarjan SCC 算法（11 文件，8911 行）
│   ├── Dijkstra/         # Dijkstra.v, Dijkstra_trace.v
│   ├── Floyd/            # Floyd.v
│   ├── Kruskal/          # Kruskal.v
│   └── Prim/             # Prim.v
├── MonadLib/             # Monad 库（StateRelMonad, MonadErr）
├── tracelib/             # Trace 推理库（ghost code, trace logic）
├── MaxMinLib/            # 最小值/最大值语义
├── listlib/              # 列表引理库
├── SeparationLogic/      # 分离逻辑核心
├── coq-record-update/    # Record 字段更新宏（第三方）
└── examples/             # QCP 验证案例（QCP_demos_LLM, LLM_bench, Applications_human）
```

### 2.2 `algorithms/Tarjan/` — Tarjan 算法形式化

这是阶段一最重要的现有资产。当前 11 个文件覆盖了 Tarjan 算法的操作语义验证：

| 文件 | 行数 | 内容 |
|------|------|------|
| `Tarjan.v` | 467 | 主程序定义（monadic `program St unit`）、`Tarjan_DFS_rel` 定理、`Tarjan_visited_reachable` |
| `Tarjan_basics.v` | 1577 | 基本不变量：visited/dfn/low/offspring/step_aux 保持性 |
| `Tarjan_basics_ex.v` | 2614 | 扩展不变量：树性质、low 正确性 |
| `Tarjan_is_low.v` | 2812 | `is_low` 定义与全局 low 性质的归纳证明 |
| `Tarjan_is_dfn.v` | 253 | dfn 编号性质 |
| `Tarjan_bridge_iff.v` | 493 | 桥 ↔ (low > dfn) 等价定理 |
| `Tarjan_no_cross_edge.v` | 293 | 无横叉边条件下的路径分析 |
| `Tarjan_set_tree.v` | 252 | DFS 树设置操作的引理 |
| `Tarjan_tactics.v` | 91 | 自定义策略 |
| `Tarjan_tarjan.v` | 59 | 顶层模块聚合 |

**关键依赖链**：
```
GraphLib (graph_basic, tarjan, GraphLib)
    ↓
algorithms/DFS (DFS.v, DFS_traditional.v)
    ↓
algorithms/Tarjan/Tarjan.v  ←  tracelib (TraceBasic, TraceLogic, GhostCode, ...)
    ↓                        ←  MonadLib (StateRelHoare, FixpointLib, safeexec_lib)
algorithms/Tarjan/Tarjan_basics.v  ←  coq-record-update
    ↓
Tarjan_basics_ex.v → Tarjan_is_low.v → Tarjan_bridge_iff.v
```

**编程风格**：使用 `MonadLib.StateRelMonad` 的 `program St unit` monad 和非确定性 choice/`forset` 组合子，配合 `TraceLib` 的 ghost code 和 trace logic 进行规约。

**已验证的核心定理**：
- `Tarjan_visited_reachable`：Tarjan 访问的顶点恰好是从 root 可达的顶点
- `Tarjan_DFS_rel`：Tarjan 的 visited 行为等价于标准 DFS
- 桥判定定理（`Tarjan_bridge_iff.v`）
- `is_low` 的全局归纳性质
- dfn/low 序的不变量

**尚未完成的关键部分**：
- **SCC 数学定义**（`mutually_reachable`、`is_SCC`、`scc_partition`）——不存在
- **SCC 正确性定理**：Tarjan 弹出操作产生的顶点集满足 `is_SCC`
- **缩点图 DAG 性质**（`condensation_is_acyclic`）
- **图反转操作**（Kosaraju 算法需要）

### 2.3 `GraphLib/examples/tarjan.v` — 桥定理

这是 Tarjan 算法的早期数学风格版本（区别于 `algorithms/Tarjan/` 的操作风格）：

- 定义了 `OriginalGraphType`（Record 含 `original_vvalid`/`original_evalid`/`original_source`/`original_target`）
- 类型类实例：`Graph`、`GValid`、`StepValid`、`StepUniqueUndirected`、`FiniteGraph`
- Type Class：`RootedTree`、`DFSTree`、`dfn_valid`、`is_low`、`low_valid_implies_is_low`
- 核心定理：树边是桥 ↔ `low[child] > dfn[parent]`

**与 `algorithms/Tarjan/` 的关系**：`algorithms/Tarjan/` import `GraphLib.examples.tarjan`，重用了 `OriginalGraphType`、`St` Record 结构、`RootedTree` Type Class 等定义。两者共享相同的图表示。

### 2.4 `algorithms/DFS/` — DFS 参考实现

| 文件 | 内容 |
|------|------|
| `DFS.v` | 标准 DFS 的 monadic 实现与正确性证明（`DFS_visited_reachable`） |
| `DFS_traditional.v` | DFS 的传统 Hoare 风格验证 |
| `C10909_MonadProg_DFS.v` | DFS 的扩展正确性引理 |

`Tarjan.v` 中 `Tarjan_DFS_rel` 的证明依赖 `DFS.v` 的 `DFS_visited_reachable` 定理。

### 2.5 新增基础设施库

| 库 | 路径 | 用途 |
|----|------|------|
| **TraceLib** | `tracelib/` | Ghost code、trace logic、trace 递归/循环推理。`Tarjan.v` 使用 trace call 机制将纯程序提升为 trace 程序 |
| **coq-record-update** | `coq-record-update/` | Record 字段更新的 `settable!` 宏。Tarjan 程序用 `` s <| visited ::= ... |> `` 语法更新状态字段 |
| **MonadLib 更新** | `MonadLib/` | `MonadErrHoarePartial.v` 新增、`FixpointLib.v` 扩展、`safeexec_lib.v` 更新 |

### 2.6 现有示例参考

根据 `AGENTS.md`，只参考 `QCP_demos_LLM` 版本的示例：

- `sll_insert_sort.c`：展示了多函数、复杂循环不变量、函数调用
- `fme/fme.c`：展示了嵌套循环、复杂数据结构、多文件组织
- `kmp_rel.c` / `int_array_merge_rel.c`：展示了 refinement proof 模式
- `glibc_slist_rel/*.c`（新增 17 个案例）：C refines monad 的 refinement 模式参考

---

## 3. 总体路线图

本计划分六个阶段推进，各阶段之间存在依赖关系：

```
阶段一：SCC 数学定义 + Tarjan SCC 正确性定理（在 algorithms/Tarjan/ 下）
    ↓
阶段二：C 语言的 Tarjan SCC 实现与标注
    ↓
阶段三：符号执行与 VC 生成
    ↓
阶段四：验证条件的证明
    ↓
阶段五：2-SAT 的形式化与实现
    ↓
阶段六：集成与最终验证
```

当前进度：阶段一的**算法操作语义部分**（Tarjan 程序定义 + visited/dfn/low 不变量 + 桥定理）已基本完成。**SCC 数学规格层**和**SCC 正确性定理**尚未开始。

---

## 4. 阶段一：Rocq 中 SCC 数学基础与算法规格

### 4.1 现状与缺口

当前 `algorithms/Tarjan/` 中的定理聚焦于**操作层面**（程序执行了什么），但缺少**规格层面**的定义（程序的数学目标是什么）。具体缺口：

| 缺失项 | 用途 |
|--------|------|
| `mutually_reachable` (on `OriginalGraphType`) | SCC 的数学定义：两点相互可达 |
| `is_SCC` | 顶点集合是否为 SCC 的判定谓词 |
| `scc_partition` | 整个图的 SCC 划分定义 |
| `scc_partition_exists` | SCC 划分的存在性证明 |
| `condensation_edge` / `condensation_is_acyclic` | 缩点图 DAG 性质 |
| `reverse_graph` (for `OriginalGraphType`) | 图反转（Kosaraju 和 2-SAT 蕴含图需要） |
| Tarjan SCC 正确性定理 | 连接操作语义与 SCC 规格 |

### 4.2 新建文件：`algorithms/Tarjan/SCC_basic.v`

定义 SCC 的数学基础（图类型使用 `OriginalGraphType`）：

#### 4.2.1 相互可达性与 SCC

```coq
Require Import GraphLib.GraphLib.
Require Import GraphLib.examples.tarjan.

Section SCC_DEFS.

Context {V E: Type} (g: OriginalGraphType V E) `{OriginalGraph_gvalid g}.

(* 相互可达性 *)
Definition mutually_reachable (u v: V) : Prop :=
  reachable g u v /\ reachable g v u.

(* 等价关系性质 *)
Lemma mutually_reachable_refl : forall u, vvalid g u -> mutually_reachable u u.
Lemma mutually_reachable_sym : forall u v, mutually_reachable u v -> mutually_reachable v u.
Lemma mutually_reachable_trans : forall u v w,
  mutually_reachable u v -> mutually_reachable v w -> mutually_reachable u w.

(* SCC 定义：非空 + 内部相互可达 + 极大 *)
Definition is_SCC (s: V -> Prop) : Prop :=
  (exists v, s v /\ vvalid g v) /\
  (forall u v, s u -> s v -> mutually_reachable u v) /\
  (forall u v, s u -> vvalid g v -> mutually_reachable u v -> s v).

(* SCC 的基本性质 *)
Lemma is_SCC_vvalid : forall s u, is_SCC s -> s u -> vvalid g u.
Lemma is_SCC_closed_under_mr : forall s u v,
  is_SCC s -> s u -> mutually_reachable u v -> s v.
Lemma is_SCC_maximal : forall s1 s2,
  is_SCC s1 -> is_SCC s2 ->
  (forall v, s1 v -> s2 v) -> (forall v, s2 v -> s1 v).
```

#### 4.2.2 SCC 划分

```coq
(* SCC 划分：覆盖 + 每个是 SCC + 互不相交 *)
Definition scc_partition (sccs: list (V -> Prop)) : Prop :=
  (forall v, vvalid g v -> exists s, In s sccs /\ s v) /\
  (forall s, In s sccs -> is_SCC s) /\
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2).

(* 相互可达的顶点在同一 SCC 中 *)
Lemma mutually_reachable_same_SCC : forall u v sccs,
  vvalid g u -> scc_partition sccs -> mutually_reachable u v ->
  exists s, In s sccs /\ s u /\ s v.

(* SCC 划分存在性（使用 FiniteGraph + 古典逻辑） *)
Theorem scc_partition_exists : exists sccs, scc_partition sccs.
```

#### 4.2.3 缩点图（Condensation DAG）

```coq
(* 缩点图边：从 SCC s1 到不同 SCC s2 存在原图边 *)
Definition condensation_edge (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ step g u v.

(* 缩点图无环 *)
Theorem condensation_is_acyclic : forall sccs s1 s2,
  scc_partition sccs ->
  condensation_edge sccs s1 s2 ->
  ~ condensation_reachable sccs s2 s1.
```

#### 4.2.4 图反转

```coq
(* OriginalGraphType 的反转：交换 source/target *)
Definition reverse_graph (g: OriginalGraphType V E) : OriginalGraphType V E := ...

(* mutually_reachable 和 is_SCC 在图反转下不变 *)
Lemma mutually_reachable_reverse : forall u v,
  mutually_reachable g u v <-> mutually_reachable (reverse_graph g) u v.
Corollary is_SCC_reverse : forall s,
  is_SCC g s <-> is_SCC (reverse_graph g) s.
Corollary scc_partition_reverse : forall sccs,
  scc_partition g sccs <-> scc_partition (reverse_graph g) sccs.
```

**设计要点**：
- 使用 `OriginalGraphType`（与 `tarjan.v` 和 `algorithms/Tarjan/` 一致）
- 不引入新的 `DirectedGraphType`——`OriginalGraphType` 已包含 `original_source`/`original_target`
- 所有定义对任意 `OriginalGraphType` 有效（算法无关）
- 图反转在 Kosaraju 和 2-SAT 蕴含图构造时需要

### 4.3 新建文件：`algorithms/Tarjan/SCC_correctness.v`

将 Tarjan 算法的操作语义与 SCC 数学规格连接：

```coq
Require Import GraphLib.GraphLib.
Require Import GraphLib.examples.tarjan.
Require Import Algorithms.Tarjan.Tarjan.
Require Import Algorithms.Tarjan.SCC_basic.

Section SCC_CORRECTNESS.

Context {V E: Type} `{EqDec V eq} (g: OriginalGraphType V E)
        `{OriginalGraph_gvalid g} (root: V) `{vvalid g root}.

(* 核心不变式：已弹出的 SCC 都是正确的 *)
Definition scc_stack_invariant (s: St) (dfstree: DFSTreeType V E) : Prop :=
  (* 栈中顶点按 low 值分组对应 SCC *)
  ...

(* 主正确性定理 *)
Theorem tarjan_scc_correctness :
  Hoare (fun s => s = initSt)
        (tarjan g root)
        (fun _ s =>
          exists sccs,
            scc_partition g sccs /\
            (* sccs 中的每个 SCC 对应 Tarjan 算法弹出的一组顶点 *)
            ...).

(* 推论：每个被弹出的顶点组是一个 SCC *)
Corollary tarjan_pop_is_scc : forall s s' v popped,
  (* s --[tarjan g root]--> s' 且在某步中弹出 popped *)
  ...
  is_SCC g (fun w => In w popped).
```

**关键依赖**：
- `Tarjan_is_low.v` 的 `is_low` 全局性质
- `Tarjan_basics.v` / `Tarjan_basics_ex.v` 的 visited/dfn/low/offspring 不变式
- `Tarjan_bridge_iff.v` 的无横叉边条件下的路径引理

### 4.4 阶段一产出物

| 文件 | 预估行数 | 内容 |
|------|---------|------|
| `algorithms/Tarjan/SCC_basic.v` | 500–700 | SCC 数学定义、划分、缩点图、图反转 |
| `algorithms/Tarjan/SCC_correctness.v` | 800–1200 | Tarjan 弹出操作的 SCC 正确性证明 |

两个文件放在 `algorithms/Tarjan/` 下，与现有文件同级，`Require Import` 路径为 `From Algorithms Require Import Tarjan.SCC_basic.`

---

## 5. 阶段二：C 语言的 Tarjan SCC 实现与标注

### 5.1 目录结构

```
QCP_examples/Applications_human/tarjan_scc/
├── tarjan_scc.c           # Tarjan SCC 算法实现
├── tarjan_scc_def.h       # C 结构体定义
├── tarjan_scc_lib.v       # common_case_formal_lib
├── common.strategies      # 通用策略文件（如需要）
└── tarjan_scc.strategies  # SCC 专用策略（如需要）
```

### 5.2 C 数据结构定义

```c
/* tarjan_scc_def.h */

// 邻接表的边节点
struct EdgeNode {
    int to;                   // 目标顶点编号
    struct EdgeNode *next;    // 下一条边
};

// 有向图：邻接表表示
struct Graph {
    int numVertices;
    struct EdgeNode **adj;    // 链表头指针数组
};

// Tarjan 算法的运行时状态
struct TarjanContext {
    int *index;               // DFS 编号数组，-1 表示未访问
    int *lowlink;             // low 值数组
    int *stack;               // 顶点栈
    int stackTop;             // 栈顶指针
    bool *onStack;            // 顶点是否在栈中
    int *sccIds;              // 每个顶点所属的 SCC ID
    int nextIndex;            // 下一个 DFS 编号
    int sccCount;             // 已发现的 SCC 数量
};
```

### 5.3 对应 Rocq 表示谓词（写入 `tarjan_scc_lib.v`）

```coq
(* 边链表表示谓词 *)
Fixpoint EdgeList_rep (x: addr) (edges: list Z): Assertion :=
  match edges with
  | nil => [| x = NULL |] && emp
  | to :: edges' =>
      [| x <> NULL |] &&
      EX next: addr,
        &(x # "EdgeNode" ->ₛ "to") # Int |-> to **
        &(x # "EdgeNode" ->ₛ "next") # Ptr |-> next **
        EdgeList_rep next edges'
  end.

(* 邻接数组表示谓词 *)
Fixpoint AdjArray_rep (arr: addr) (n: nat) (adj: list (list Z)): Assertion :=
  match n, adj with
  | O, nil => emp
  | S n', edges :: adj' =>
      EX head: addr,
        (arr # Ptr |-> head) **
        EdgeList_rep head edges **
        AdjArray_rep (arr +ₚ 4) n' adj'
  | _, _ => [| False |]
  end.

(* 图的完整表示 *)
Definition Graph_rep (g: addr) (adj: list (list Z)): Assertion :=
  EX numV: Z, EX adjPtr: addr,
    &(g # "Graph" ->ₛ "numVertices") # Int |-> numV **
    &(g # "Graph" ->ₛ "adj") # Ptr |-> adjPtr **
    AdjArray_rep adjPtr (Z.to_nat numV) adj.

(* Tarjan 上下文的表示 *)
Definition TarjanContext_rep (ctx: addr) (n: nat)
    (index lowlink: list Z) (stack: list Z) (stackTop: Z)
    (onStack: list bool) (sccIds: list Z)
    (nextIndex sccCount: Z): Assertion :=
  EX idxPtr llPtr stkPtr osPtr sccPtr: addr,
    &(ctx # "TarjanContext" ->ₛ "index") # Ptr |-> idxPtr **
    &(ctx # "TarjanContext" ->ₛ "lowlink") # Ptr |-> llPtr **
    &(ctx # "TarjanContext" ->ₛ "stack") # Ptr |-> stkPtr **
    &(ctx # "TarjanContext" ->ₛ "stackTop") # Int |-> stackTop **
    &(ctx # "TarjanContext" ->ₛ "onStack") # Ptr |-> osPtr **
    &(ctx # "TarjanContext" ->ₛ "sccIds") # Ptr |-> sccPtr **
    &(ctx # "TarjanContext" ->ₛ "nextIndex") # Int |-> nextIndex **
    &(ctx # "TarjanContext" ->ₛ "sccCount") # Int |-> sccCount **
    IntArray_rep idxPtr n index **
    IntArray_rep llPtr n lowlink **
    IntArray_rep stkPtr n stack **
    BoolArray_rep osPtr n onStack **
    IntArray_rep sccPtr n sccIds.
```

### 5.4 核心函数：`strongconnect` 的标注

```c
void strongconnect(struct Graph *graph, int v, struct TarjanContext *ctx)
  /*@ With (adj: list (list Z)) (n: Z)
             (index lowlink: list Z) (stack: list Z) (stackTop: Z)
             (onStack: list bool) (sccIds: list Z)
             (nextIndex sccCount: Z)
             (G: OriginalGraphType Z Z)
      Require n == Zlength adj /\
              n <= INT_MAX /\
              0 <= v /\
              v < n /\
              graph_well_formed G adj /\
              Znth v index = -1 /\
              tarjan_invariant_partial G adj v index lowlink
                                       stack stackTop onStack sccIds
                                       nextIndex sccCount /\
              Graph_rep(graph, adj) *
              TarjanContext_rep(ctx, n, index, lowlink, stack,
                                stackTop, onStack, sccIds,
                                nextIndex, sccCount)
      Ensure exists index' lowlink' stack' stackTop' onStack' sccIds'
                    nextIndex' sccCount',
             Zlength index' == n /\
             Znth v index' != -1 /\
             (* 包含 v 的 SCC 已正确识别并出栈 *)
             scc_completed_at G adj v sccIds' sccCount' /\
             Graph_rep(graph, adj) *
             TarjanContext_rep(ctx, n, index', lowlink', stack',
                               stackTop', onStack', sccIds',
                               nextIndex', sccCount')
  */
{
    // DFS 进入：分配编号，入栈
    ctx->index[v] = ctx->nextIndex;
    ctx->lowlink[v] = ctx->nextIndex;
    ctx->nextIndex++;
    ctx->stack[ctx->stackTop] = v;
    ctx->stackTop++;
    ctx->onStack[v] = true;

    // 遍历 v 的所有邻居
    struct EdgeNode *e = graph->adj[v];
    /*@ Inv
        exists e_ptr index2 lowlink2 stack2 stackTop2 onStack2
               sccIds2 nextIndex2 sccCount2 processed,
        forall w, In w processed ->
          update_lowlink_correct G dfstree dfn index2 lowlink2 v w /\
          ...
        EdgeList_seg(graph->adj[v], e, e_ptr, processed, adj_nth adj v) *
        TarjanContext_rep(ctx, n, index2, lowlink2, stack2,
                          stackTop2, onStack2, sccIds2,
                          nextIndex2, sccCount2)
    */
    while (e != NULL) {
        int w = e->to;

        if (ctx->index[w] == -1) {
            /* w 未访问，递归调用 */
            strongconnect(graph, w, ctx);
            if (ctx->lowlink[w] < ctx->lowlink[v]) {
                ctx->lowlink[v] = ctx->lowlink[w];
            }
        } else if (ctx->onStack[w]) {
            /* w 在当前栈中（回边） */
            if (ctx->index[w] < ctx->lowlink[v]) {
                ctx->lowlink[v] = ctx->index[w];
            }
        }

        e = e->next;
    }

    /* 弹出 SCC */
    if (ctx->lowlink[v] == ctx->index[v]) {
        int w;
        do {
            ctx->stackTop--;
            w = ctx->stack[ctx->stackTop];
            ctx->onStack[w] = false;
            ctx->sccIds[w] = ctx->sccCount;
        } while (w != v);
        ctx->sccCount++;
    }
}
```

### 5.5 主函数：`tarjan_scc` 的标注

```c
void tarjan_scc(struct Graph *graph, struct TarjanContext *ctx)
  /*@ With (adj: list (list Z)) (n: Z) (G: OriginalGraphType Z Z)
      Require n == Zlength adj /\
              n <= INT_MAX /\
              graph_well_formed G adj /\
              Graph_rep(graph, adj) *
              TarjanContext_init(ctx, n)
      Ensure exists sccIds sccCount,
             Zlength sccIds == n /\
             (forall i j, 0 <= i < n -> 0 <= j < n ->
               Znth i sccIds == Znth j sccIds <->
               mutually_reachable G (Z.to_nat i) (Z.to_nat j)) /\
             Graph_rep(graph, adj) *
             TarjanContext_rep_final(ctx, n, sccIds, sccCount)
  */
{
    int v;

    /*@ Inv
        exists index lowlink stack stackTop onStack sccIds nextIndex sccCount,
        (forall i, 0 <= i < v ->
           Znth i index != -1 ->
           scc_assigned G adj i sccIds sccCount) /\
        (forall i, v <= i < n -> Znth i index == -1) /\
        Graph_rep(graph, adj) *
        TarjanContext_rep(ctx, n, index, lowlink, stack,
                          stackTop, onStack, sccIds,
                          nextIndex, sccCount)
    */
    for (v = 0; v < graph->numVertices; v++) {
        if (ctx->index[v] == -1) {
            strongconnect(graph, v, ctx);
        }
    }
}
```

### 5.6 关键标注挑战与应对

| 挑战 | 应对策略 |
|------|----------|
| `strongconnect` 是递归函数 | 使用 QCP 的函数规约机制。在调用点通过前置条件匹配来实例化逻辑变量 |
| 对数组的细粒度更新 | 使用 ArrayLib 谓词（`IntArray_rep`、`BoolArray_rep`），标注中显式声明每次数组访问的权限 |
| 递归调用中的栈帧 | 递归函数的逻辑变量在每次调用时独立量化 |
| DFS 树结构与 C 迭代过程的对应 | 在 `tarjan_scc_lib.v` 中证明引理：C 访问顺序产生合法 DFS 树 |
| 结构体字段访问的权限展开 | 使用 `Assert` + `which implies` 语法手动展开谓词获得 `data_at` 权限 |

---

## 6. 阶段三：符号执行与 VC 生成

### 6.1 运行符号执行

```bash
linux-binary/symexec \
  --input-file=QCP_examples/Applications_human/tarjan_scc/tarjan_scc.c \
  --goal-file=SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_goal.v \
  --proof-auto-file=SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_proof_manual.v \
  --coq-logic-path=SimpleC.EE.Applications_human.tarjan_scc \
  -slp QCP_examples/Applications_human/ SimpleC.EE.Applications_human \
  -IQCP_examples/QCP_demos_LLM/ \
  -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM \
  --no-exec-info
```

### 6.2 迭代调试流程

```
编写/修改 C 标注
    → 运行 symexec
    → 检查错误输出（缺失权限、无法实例化等）
    → 分析生成的 goal 文件中哪个 VC 失败
    → 回到标注修正
    → 重复直到 symexec 成功到达文件尾
```

使用 `qcp-mcp` 进行**交互式增量检查**可以大幅加速此过程。

### 6.3 预期的 VC 分类

**A 类：直接内存布局 VC（预期 40%+ 自动解决）**
- 结构体字段访问权限（`e->to`、`e->next`）
- 数组读写权限（`index[v]`、`lowlink[v]`）
- 栈入栈出权限（`stack[stackTop]`）

**B 类：函数调用参数实例化 VC（预期 20% 策略解决）**
- `strongconnect(graph, w, ctx)` 调用处：匹配前置条件、分离内存帧

**C 类：循环不变量维护 VC（预期 25% 需要手动证明）**
- 外层循环：v 的增加保持不变量
- 邻居遍历循环：e 的移动保持不变量
- SCC 弹出循环：栈收缩保持不变量

**D 类：纯数学命题 VC（预期 15% 需要深入手动证明）**
- `lowlink` 更新保持 `is_low` 性质
- 栈弹出子序列构成 SCC（依赖 `SCC_correctness.v`）
- 后置条件中的 `mutually_reachable` 等价性

### 6.4 策略文件

如需要自定义策略，创建 `QCP_examples/Applications_human/tarjan_scc/tarjan_scc.strategies`：

```
# 用于分离 Graph_rep 和 TarjanContext_rep 的策略
pattern: Graph_rep(g, adj) * TarjanContext_rep(ctx, ...) |-- Graph_rep(g, adj)
action: cancel Graph_rep

pattern: IntArray_rep(arr, n, l) |-- data_at(arr + offset, Int, v)
action: ...
```

---

## 7. 阶段四：验证条件的证明

### 7.1 设置证明环境

在 `SeparationLogic/examples/Applications_human/tarjan_scc/tarjan_scc_lib.v` 中：

- 导入 GraphLib（`graph_basic`、`tarjan`）
- 导入 `Algorithms.Tarjan`（`Tarjan`、`SCC_basic`、`SCC_correctness`）
- 导入分离逻辑策略库
- 定义阶段二中的所有表示谓词
- 陈述辅助引理：`graph_rep_open`、`edge_list_read`、`int_array_read`/`int_array_write`、`tarjan_context_frame`
- 记录 `lib_frozen_prefix_end_line` 和 `lib_frozen_prefix_snapshot`

### 7.2 VC 检查阶段（`vc-checking`）

| Proof Group | 描述 | 估计数量 | 策略 |
|-------------|------|---------|------|
| Group 1 | 直接 entailer 可解 | ~30% | `entailer!` 一步完成 |
| Group 2 | 需要简单引理 | ~25% | 应用 `sep_apply` 再 `entailer!` |
| Group 3 | 需要 low/dfn 性质 | ~20% | 引用 `Tarjan_is_low.v`、`Tarjan_basics.v` |
| Group 4 | 深度数学（SCC 正确性） | ~15% | 结合 `SCC_correctness.v` 的复杂证明 |
| Group 5 | 可能语义不可证 | ~10% | 回到 annotation 阶段修正 |

### 7.3 VC 证明阶段（`vc-proving`）

使用 `vc-proving` 技能的脚本化并发 worker 流水线：Split → Prepare → Run → Validate → Migrate。

#### Group 3 证明示例

```coq
Lemma neighbor_processed_preserves_invariant:
  forall G dfstree dfn low index lowlink stack ...,
  ...
  |--
  EX index' lowlink' ..., ... ** TarjanContext_rep ...
Proof.
  intros. Intros.
  sep_apply lowlink_update_preserves_is_low.
  { ... }
  entailer!.
Qed.
```

#### Group 4 证明示例（核心困难 VC）

```coq
Lemma pop_scc_when_low_equals_index:
  forall G dfstree dfn low stack stack' v popped,
  dfn_valid dfstree dfn ->
  is_low G dfstree dfn low ->
  low v = dfn v ->
  pop_until_stack stack v = Some (popped, stack') ->
  ...
  |--
  is_SCC G (fun w => In w popped).
Proof.
  intros.
  (* 引用阶段一的 SCC_correctness.v 主定理 *)
  apply SCC_correctness.tarjan_pop_is_scc with (g := G) (dfstree := dfstree); auto.
  - apply build_dfstree_from_tarjan_trace; auto.
  - apply lowlink_implies_is_low; auto.
Qed.
```

### 7.4 分离逻辑策略参考

| 策略 | 用途 |
|------|------|
| `Intros` | 将前提中的纯命题移入 Coq 上下文 |
| `Intros x` | 实例化前提中的存在量词为 `x` |
| `Exists x` | 用 `x` 填充结论中的存在量词 |
| `Exists_l x` | 用 `x` 填充前提中的全称量词 |
| `entailer!` | 自动尝试消除分离逻辑目标 |
| `sep_apply H` | 应用引理 `H` 转换前提（`P * Q \|-- R` 形式） |
| `prop_apply H` | 应用引理 `H` 添加纯命题 |
| `csimpl` | 简化记号 |

---

## 8. 阶段五：2-SAT 问题形式化与归约

### 8.1 新建文件：`algorithms/TwoSAT/TwoSAT.v`

（或在 `algorithms/Tarjan/` 下新增 `TwoSAT.v`，因为 2-SAT 归约直接依赖 Tarjan SCC）

```coq
Require Import GraphLib.GraphLib.
Require Import GraphLib.examples.tarjan.
Require Import Algorithms.Tarjan.SCC_basic.

(* 文字：变量编号 + 极性 *)
Definition literal := (Z * bool).
Definition negate (l: literal): literal := (fst l, negb (snd l)).

(* 子句和公式 *)
Definition clause := (literal * literal).
Definition formula := list clause.
Definition assignment := Z -> bool.

(* 可满足性 *)
Definition satisfies (a: assignment) (f: formula): Prop :=
  forall c, In c f ->
    (eval_literal a (fst c) = true \/ eval_literal a (snd c) = true).

Definition satisfiable (f: formula): Prop := exists a, satisfies a f.

(* 蕴含图构造 *)
Definition implication_graph (f: formula) (numVars: Z): OriginalGraphType Z Z := ...

(* 2-SAT 主定理：公式可满足 ↔ 没有变量与其否定在同一 SCC *)
Theorem two_sat_characterization:
  forall f numVars,
  (forall c, In c f -> valid_clause c numVars) ->
  (satisfiable f <->
   forall v, 1 <= v <= numVars ->
     ~ same_SCC (implication_graph f numVars) (v, true) (v, false)).
```

### 8.2 C 语言的 2-SAT 实现

```c
int two_sat(int numVars, int *clauseA, int *clauseB, int numClauses,
            int *assignment)
  /*@ With (f: formula) (nv nc: Z)
      Require nv == numVars /\
              formula_from_arrays clauseA clauseB numClauses f /\
              int_array_rep(clauseA, nc, ...) *
              int_array_rep(clauseB, nc, ...) *
              int_array_undef(assignment, nv)
      Ensure exists a,
             ((__return == 1 && satisfies a f &&
               assignment_holds(assignment, nv, a)) ||
              (__return == 0 && ~ satisfiable f)) /\
             int_array_rep(assignment, nv, ...)
  */
{
    int n = 2 * numVars;
    struct Graph *graph = build_implication_graph(clauseA, clauseB,
                                                   numClauses, numVars);
    struct TarjanContext ctx;
    allocate_tarjan_context(&ctx, n);

    tarjan_scc(graph, &ctx);

    for (int v = 0; v < numVars; v++) {
        if (ctx.sccIds[2 * v] == ctx.sccIds[2 * v + 1]) {
            free_graph(graph);
            free_tarjan_context(&ctx);
            return 0;
        }
    }

    for (int v = 0; v < numVars; v++) {
        assignment[v] = (ctx.sccIds[2 * v + 1] < ctx.sccIds[2 * v]) ? 1 : 0;
    }

    free_graph(graph);
    free_tarjan_context(&ctx);
    return 1;
}
```

### 8.3 2-SAT 的 VC 证明策略

| C 实现 | 对应的 Coq 定理 |
|--------|----------------|
| `build_implication_graph` | `implication_graph` 构造 |
| `tarjan_scc` 调用 | `tarjan_scc_correctness`（阶段四的产出） |
| `sccIds[2*v] == sccIds[2*v+1]` 检查 | `same_scc_implies_contradiction` |
| 按 SCC 序赋值 | `build_assignment_from_scc_order` |

---

## 9. 阶段六：集成与最终验证

### 9.1 文件编译依赖

```
GraphLib/graph_basic.v → reachable/*.v, directed/*.v
    ↓
GraphLib/examples/tarjan.v（已有，桥定理）
    ↓
algorithms/DFS/DFS.v（已有，DFS 正确性）
    ↓
algorithms/Tarjan/Tarjan.v → Tarjan_basics.v → Tarjan_basics_ex.v  （已有，操作语义）
    ↓                         ↓
algorithms/Tarjan/Tarjan_is_low.v → Tarjan_bridge_iff.v             （已有）
    ↓
algorithms/Tarjan/SCC_basic.v（新增，SCC 数学定义）
    ↓
algorithms/Tarjan/SCC_correctness.v（新增，SCC 正确性定理）
    ↓
algorithms/TwoSAT/TwoSAT.v（新增，2-SAT 归约）
    ↓
examples/Applications_human/tarjan_scc/tarjan_scc_lib.v（common_case_formal_lib）
    ↓
tarjan_scc_goal.v / tarjan_scc_proof_auto.v / tarjan_scc_proof_manual.v
two_sat_goal.v / two_sat_proof_auto.v / two_sat_proof_manual.v
```

### 9.2 Final-Check 检查清单

1. **符号执行**：已到达文件尾，生成文件是最新的
2. **手动 VC**：所有 manual VC 都已完成证明（无 `Admitted`）
3. **Goal check**：`*_goal_check.v` 编译通过
4. **Proof manual 审计**：只含 witness proofs，无 helper lemmas，无 forbidden top-level 定义，无 forbidden lemma
5. **Common lib 审计**：spec 定义不是算法镜像，冻结前缀未被改写，helper imports 经审计
6. **Rocq 编译**：全量编译通过
7. **清理**：`.tmp` 文件、`.aux` 文件、临时 scratch 删除完毕

### 9.3 最终编译命令

```bash
cd SeparationLogic

# 编译核心库
make depend-core && make core

# 编译 GraphLib
cd GraphLib && make && cd ..

# 编译 algorithms（包括新增的 SCC_basic、SCC_correctness）
cd algorithms && make && cd ..

# 编译 tarjan_scc 案例
make depend-examples-applications && make examples-applications
```

---

## 10. 文件结构与交付物

### 10.1 新增文件清单

```
SeparationLogic/algorithms/Tarjan/
├── SCC_basic.v                   # 新增：SCC 数学定义、划分、缩点图、图反转
└── SCC_correctness.v             # 新增：Tarjan 弹出操作的 SCC 正确性证明

SeparationLogic/algorithms/TwoSAT/
└── TwoSAT.v                      # 新增：2-SAT 归约的形式化与正确性定理

QCP_examples/Applications_human/tarjan_scc/
├── tarjan_scc_def.h              # C 结构体定义
├── tarjan_scc.c                  # Tarjan SCC 实现（带标注）
├── two_sat.c                     # 2-SAT 求解器（带标注）
├── common.strategies             # 通用策略（如需要）
├── tarjan_scc.strategies         # SCC 专用策略（如需要）
└── two_sat.strategies            # 2-SAT 专用策略（如需要）

SeparationLogic/examples/Applications_human/tarjan_scc/
├── tarjan_scc_goal.v             # 生成的：SCC 验证条件
├── tarjan_scc_proof_auto.v       # 生成的：自动证明
├── tarjan_scc_proof_manual.v     # 人工证明（最终所有 VC 被证明）
├── tarjan_scc_goal_check.v       # 生成的：一致性检查
├── two_sat_goal.v                # 生成的：2-SAT 验证条件
├── two_sat_proof_auto.v          # 生成的：自动证明
├── two_sat_proof_manual.v        # 人工证明（最终所有 VC 被证明）
├── two_sat_goal_check.v          # 生成的：一致性检查
└── tarjan_scc_lib.v              # common_case_formal_lib（两个 C 文件共用）
```

### 10.2 已有的只读依赖（不修改）

- `SeparationLogic/GraphLib/**/*.v`（核心图论库）
- `SeparationLogic/algorithms/Tarjan/Tarjan*.v`（Tarjan 操作语义，11 文件）
- `SeparationLogic/algorithms/DFS/*.v`（DFS 参考实现）
- `SeparationLogic/tracelib/*.v`（Trace 推理库）
- `SeparationLogic/MonadLib/**/*.v`（Monad 库）
- `SeparationLogic/SeparationLogic/*.v`（分离逻辑库）
- `SeparationLogic/coq-record-update/`（Record 更新宏）

---

## 11. 工作量估算与风险评估

### 11.1 工作量估算

| 阶段 | 子任务 | 预估人周 | 关键交付物 | 备注 |
|------|--------|---------|-----------|------|
| **一** | SCC 数学基础 + 正确性定理 | **3–5 周** | `SCC_basic.v`, `SCC_correctness.v` | 操作语义已有，聚焦规格层 |
| | 1.1 SCC 数学定义与性质 | 1–1.5 周 | `SCC_basic.v` | 可复用之前 scc_basic.v 的证明思路 |
| | 1.2 Tarjan SCC 正确性证明 | 2–3.5 周 | `SCC_correctness.v` | 核心难点，连接 low/dfn 理论与 SCC |
| **二** | C 实现与标注 | **4–5 周** | `tarjan_scc.c`, `two_sat.c`, `tarjan_scc_lib.v` |
| | 2.1 表示谓词定义 | 0.5 周 | `tarjan_scc_lib.v` |
| | 2.2 `strongconnect` 标注 | 2–3 周 | 核心递归函数标注 |
| | 2.3 `tarjan_scc` 主函数标注 | 1 周 | 外层循环标注 |
| | 2.4 `two_sat` 标注 | 0.5 周 | 调用已验证的 tarjan_scc |
| **三** | 符号执行迭代 | **1–2 周** | `*_goal.v`, `*_proof_*.v` |
| **四** | VC 证明 | **3–5 周** | 全部 VC 被证明 |
| | 4.1 Group 1–2 VC（简单） | 0.5 周 | entailer! 一步解决 |
| | 4.2 Group 3 VC（中等） | 1–1.5 周 | low/dfn 性质 |
| | 4.3 Group 4 VC（困难） | 1.5–2 周 | SCC 正确性 |
| | 4.4 迭代修正 | 0.5–1 周 | 标注与证明往返 |
| **五** | 2-SAT 形式化 + C 实现 | **1–2 周** | `TwoSAT.v` + 证明 |
| **六** | 集成与 final-check | **1 周** | 编译通过，checklist 完成 |
| **总计** | | **13–20 周** | |

- **单人总预估**：约 4–5 个月（阶段一已有操作语义基础，节省 1–2 周）
- **两人团队**：约 2.5–3 个月

### 11.2 风险矩阵

| 风险 | 可能性 | 影响 | 缓解措施 |
|------|--------|------|----------|
| `SCC_correctness.v` 中 low/dfn → SCC 的桥梁证明比预期更深 | 中 | 高 | 充分利用已有的 `Tarjan_is_low.v`（2812 行）和 `Tarjan_basics_ex.v`（2614 行）；从单 SCC 弹出操作开始逐步泛化 |
| `OriginalGraphType` 的 step 关系对 SCC 定义不适合（无向 step） | 低 | 中 | `OriginalGraphType` 已有 `original_source`/`original_target`；SCC 规格层可定义有向 step 关系 `dg_step_aux`，证明与 `original_step_aux` 的包含关系 |
| `strongconnect` 递归函数规约在 QCP 中不被充分支持 | 中 | 高 | 尽早用最小递归示例测试；准备迭代版本作为备选 |
| 标注调试循环耗时过长 | 高 | 中 | 使用 `qcp-mcp` 交互式验证做增量检查；从最简单标注开始逐步细化 |
| 数组/栈操作的细粒度权限在符号执行中产生 VC 爆炸 | 中 | 中 | 使用高层聚合谓词，通过引理展开而非在标注中展开 |
| 2-SAT 蕴含图构造与 Tarjan SCC 之间接口不匹配 | 低 | 中 | 确保 Tarjan 适用于任意 `OriginalGraphType`；2-SAT 图以 `V = E = Z` 构造 |

---

## 12. 执行建议

### 12.1 推荐执行顺序

1. **首先完成 SCC 数学定义（阶段一 1.1）**
   - 在 `algorithms/Tarjan/SCC_basic.v` 中定义 `mutually_reachable`、`is_SCC`、`scc_partition`
   - 使用 `OriginalGraphType`（与现有 `algorithms/Tarjan/` 一致）
   - 可参考已删除的 `GraphLib/examples/scc_basic.v` 中的证明思路（但图类型需调整）
   - 这是**最低风险的第一步**——如果 SCC 数学定义无法在 Rocq 中建立，后续所有工作都无从谈起

2. **然后证明 Tarjan SCC 正确性（阶段一 1.2）**
   - 充分利用 `algorithms/Tarjan/` 已有的操作语义（`Tarjan.v`、`Tarjan_is_low.v` 等）
   - 核心挑战：将 `is_low` 全局性质连接到 `is_SCC` 判定
   - 关键引理：`low[v] = dfn[v]` 时，v 子树中 low ≥ dfn[v] 的顶点构成一个 SCC

3. **在两个方向上逐步推进 C 验证**
   - 先用最简标注（只有函数规约）运行 `symexec`，确认基本内存操作无误
   - 再逐步细化循环不变量和内部断言
   - 每次迭代使用 `qcp-mcp` 做交互式检查

4. **将 2-SAT 作为独立案例**
   - Tarjan SCC 通过 `final-check` 后，2-SAT 就是"调用已验证的 Tarjan + 归约证明"
   - 2-SAT 的难度集中在蕴含图构造保持语义的引理上

5. **遵循 Agent 工作流纪律**
   - 不要在 main 线程做 sub agent 的工作
   - annotation 使用 scratch + 质量门机制
   - vc-proving 先让 `vc-checking-subagent` 分类，再并发证明

6. **参考现有资产**
   - `algorithms/Tarjan/Tarjan.v` 的 monadic Hoare 证明风格（`Tarjan_DFS_rel` 的模式可复用）
   - `algorithms/DFS/DFS.v` 的 DFS 正确性证明（`Tarjan.v` 已引用）
   - `glibc_slist_rel/` 的 refinement 模式（阶段四 VC 证明可参考）
   - 只参考 `QCP_demos_LLM`（不参考 `QCP_demos_human`）

---

*计划文档版本：2.0*
*最后更新：2026-06-11*
*本计划基于 QCP v2.0.2、Rocq 8.20.1、algorithms/Tarjan/ (8911 lines) 现有版本编写*
*历史版本 v1.0 (2026-06-05) 基于旧 GraphLib/examples/ 架构，已归档*
