# Tarjan SCC Monadic Correctness 设计文档

**Author**: Vitalrubbish  
**Date**: 2026-06-14

## 概述

本文档给出 Direction B（refinement proof）中 **Layer 2（Monad 算法层）** 的完整设计。
目标是在 `SeparationLogic/algorithms/Tarjan_directed/` 下构建一个 monadic Tarjan SCC 程序，
并证明其输出满足 `SCC_basic.v` 中的数学规格（`is_SCC`、`scc_partition`）。

当前 `Tarjan_directed/` 下仅有 Layer 3（数学规格层）的 `SCC_basic.v`（732 行，全部 Qed）。
Layer 2 需要从零构建。

本文档应与以下文档协同阅读：
- `docs/plan-tarjan-scc-2sat-verification.md` — 六阶段总计划
- `docs/dev/20260612-scc-basic-design.md` — SCC_basic.v 设计文档（Layer 3）
- `docs/Tarjan_directed/SCC_basic.md` — SCC_basic.v 定义/定理参考
- `docs/dev/20260611-kmp-refinement-proof.md` — KMP refinement 全流程（参考其三層解耦模式）

**注意**：`Tarjan_directed/` 与 `algorithms/Tarjan/`（桥判定）完全独立。
两者使用相同的共享基础设施（`MonadLib`、`GraphLib`、`algorithms/DFS/`），
但图语义（有向 vs 无向）、State Record、核心逻辑、最终定理均不同。

---

## 1. 三层架构

```
Layer 3 (数学规格):  SCC_basic.v                           ✅ 已完成
        ↑ Hoare 后条件: scc_partition g s.(sccs)
Layer 2 (Monad 算法): Tarjan_scc.v + 证明文件               🆕 本文档设计
        ↑ safeExec 精化（Phase 2）
Layer 1 (C 实现):     tarjan_directed.c                     🆕 Phase 2
```

Layer 2 的工作又分为两层子任务：

```
Layer 2a (Monad 程序):   Tarjan_scc.v                       — State Record + Lfix 程序
Layer 2b (正确性证明):    Tarjan_scc_basics.v                — 基本不变量
                         Tarjan_scc_is_dfn.v                — dfn 有效性
                        Tarjan_scc_is_low.v                — 有向 low 正确性
                         Tarjan_scc_stack.v                 — 栈不变量 + low=dfn → SCC
                         SCC_correctness.v                  — 主正确性定理
                         Tarjan_scc_tarjan.v                — 聚合
```

---

## 2. State Record

### 2.1 字段设计

```coq
Record SCCSt: Type := mkSCCSt {
  visited : V -> Prop;       (* DFS 已访问顶点集 *)
  timer   : nat;             (* 全局 DFS 编号计数器 *)
  fa      : V -> V;          (* DFS 父节点（偏函数，未赋值时取默认值） *)
  dfn     : V -> nat;        (* DFS 发现编号 *)
  low     : V -> nat;        (* lowlink 值 *)
  stack   : list V;          (* Tarjan 算法顶点栈 *)
  sccs    : list (V -> Prop);(* 已收集的 SCC（集合谓词列表） *)
}.
```

### 2.2 字段对比（vs 桥判定 `Tarjan/`）

| 字段 | 桥判定 | SCC | 原因 |
|------|--------|-----|------|
| `visited` | ✅ | ✅ | DFS 搜索状态 |
| `timer` | ✅ | ✅ | 全局编号 |
| `fa` | ✅ | ✅ | DFS 树结构（`dfn_valid`、`is_low` 需要） |
| `tedge` | ✅ | ❌ | 桥判定需要记录树边来源；SCC 不需要 |
| `dfn` | ✅ | ✅ | 发现编号 |
| `low` | ✅ | ✅ | lowlink 值 |
| `bridges` | ✅ | ❌ | 桥判定输出；SCC 输出 sccs |
| `stack` | ❌ | ✅ | Tarjan SCC 核心栈 |
| `sccs` | ❌ | ✅ | SCC 收集输出 |

### 2.3 Settable 实例

```coq
Instance: Settable SCCSt := settable! mkSCCSt
  <visited; timer; fa; dfn; low; stack; sccs>.
```

### 2.4 初始状态

```coq
Definition initSt: SCCSt :=
  mkSCCSt (fun _ => False) 0 (fun v => v) (fun _ => 0) (fun _ => 0) nil nil.
```

其中 `fa` 默认值取 `fun v => v`（顶点到自身），`dfn`/`low` 默认取 0。

---

## 3. Monadic 程序

### 3.1 依赖

```coq
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From Algorithms.Tarjan_directed Require Import SCC_basic.
Import MonadNotation.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope monad.
```

### 3.2 可复用基础设施

以下来自 `MonadLib/StateRelMonad/StateRelBasic.v` 的算子可直接使用：

| 算子 | 类型 | 用途 |
|------|------|------|
| `get' f` | `program Σ (f 的返回类型)` | 读取状态投影 `f(s)` |
| `update' f` | `program Σ unit` | 纯函数更新状态 |
| `If cond c` | `program Σ unit` | guard 条件，成立则执行 c |
| `if_else cond c1 c2` | `program Σ A` | 条件分支 |
| `forset universe body` | `program Σ unit` | 迭代 universe 中每个元素执行 body |
| `Lfix F` | `program Σ A` | 最小不动点（递归） |

**注意**：DFS.v 使用 `whileP`（条件驱动的 while 循环），而桥判定 `Tarjan/` 使用 `forset`（遍历边集合）。
对于 Tarjan SCC，边遍历应使用 `whileP` 或 `forset` 均可，此处选用 `whileP`（与 DFS.v 一致，更直接）。

### 3.3 原语操作

```coq
Section TARJAN_SCC.
  Context {V E: Type} (g: OriginalGraphType V E)
          `{EqDec V eq}
          `{OriginalGraph_gvalid g}.

  Definition visit (v: V): program SCCSt unit :=
    update' (fun s => s <| visited ::= visited s ∪ [v] |>).

  Definition set_dfn (v: V) (n: nat): program SCCSt unit :=
    update' (fun s => s <| dfn ::= fun x => if x == v then n else dfn s x |>).

  Definition set_low (v: V) (n: nat): program SCCSt unit :=
    update' (fun s => s <| low ::= fun x => if x == v then n else low s x |>).

  Definition set_fa (v: V) (p: V): program SCCSt unit :=
    update' (fun s => s <| fa ::= fun x => if x == v then p else fa s x |>).

  Definition incr_timer: program SCCSt unit :=
    update' (fun s => s <| timer ::= S (timer s) |>).

  Definition push_stack (v: V): program SCCSt unit :=
    update' (fun s => s <| stack ::= v :: stack s |>).

  Definition pop_stack: program SCCSt (option V) :=
    get' (fun s => match stack s with nil => None | v :: _ => Some v end);;
    update' (fun s => s <| stack ::= match stack s with nil => nil | _ :: st' => st' end |>).

  Definition update_low (u: V) (n: nat): program SCCSt unit :=
    lu <- get' (fun s => low s u);;
    If (fun s => n < low s u) (set_low u n).
```

### 3.4 主程序

```coq
  (* 进入顶点：分配 dfn/low，入栈，标记 visited *)
  Definition preloop (u: V): program SCCSt unit :=
    t <- get' (fun s => timer s);;
    set_dfn u t;; set_low u t;; incr_timer;;
    push_stack u;; visit u.

  (* 遍历 u 的每条出边 *)
  Definition process_edge (u: V) (W: V -> program SCCSt unit) (v: V): program SCCSt unit :=
    if_else (fun s => ~ v ∈ visited s)
      (* 树边：v 未访问 *)
      (set_fa v u;; W v;;
       lv <- get' (fun s => low s v);;
       update_low u lv)
      (* v 已访问 — 检查是否在栈中 *)
      (If (fun s => In v (stack s))
         (dv <- get' (fun s => dfn s v);;
          update_low u dv)).

  (* 从栈中弹出直到遇到 u（含），将弹出顶点收集为一个 SCC *)
  Definition pop_scc_state (s: SCCSt) (u: V): SCCSt :=
    let (popped, rest) := stack_split_at (stack s) u in
    s <| stack ::= rest |>
      <| sccs ::= (fun v => In v popped) :: sccs s |>.

  (* 边遍历完毕后，弹出 SCC（若 low[u] = dfn[u]） *)
  Definition pop_scc (u: V): program SCCSt unit :=
    update' (fun s => pop_scc_state s u).

  (* 单次 DFS 步骤 *)
  Definition tarjan_scc_f (W: V -> program SCCSt unit) (u: V): program SCCSt unit :=
    preloop u;;
    whileP (fun s => exists v, dg_step g u v /\ ~ v ∈ visited s)
      (v <- get (fun s v => dg_step g u v /\ ~ v ∈ visited s);; process_edge u W v);;
    If (fun s => low s u = dfn s u)
       (pop_scc u).

  (* Tarjan SCC 主程序 *)
  Definition tarjan_scc (u: V): program SCCSt unit :=
    Lfix tarjan_scc_f u.
```

### 3.5 单调性证明

需要证明 `tarjan_scc_f` 是 `mono_cont`，以便 `Lfix` 有良定义的不动点语义：

```coq
  Lemma tarjan_scc_f_mono_cont: mono_cont tarjan_scc_f.
  Proof.
    unfold tarjan_scc_f.
    (* 需要展开 whileP, whileP_f, if_else, If, preloop 等组合子 *)
    unfold whileP, whileP_f, if_else, If, preloop.
    mono_cont_auto.
    (* mono_cont_auto 会自动分解 bind / choice / const / Lfix 等结构 *)
  Qed.

  Lemma tarjan_scc_unfold (u: V):
    tarjan_scc u == tarjan_scc_f tarjan_scc u.
  Proof.
    apply Lfix_fixpoint'. apply tarjan_scc_f_mono_cont.
  Qed.
```

**注意**：若 `mono_cont_auto` 在展开上述组合子后仍无法完成证明
（例如 `get`/`get'` 的组合可能需要额外引理），
可以回退到手动应用 `mono_cont_bind`、`mono_cont_const`、`mono_cont_choice`、`mono_cont_Lfix` 等引理。
参考 DFS.v 的 `DFS_mono_cont` 证明（该文件仅需展开 `whileP_f` 即可由 `mono_cont_auto` 完成）。

### 3.6 辅助函数：`stack_split_at`

```coq
  (* 从栈中弹出直到遇到目标顶点 u（含）。
     返回 (popped, rest)，其中 popped = 从栈顶到 u（含）的顶点列表。 *)
  Fixpoint stack_split_at (stk: list V) (u: V): list V * list V :=
    match stk with
    | nil => (nil, nil)
    | x :: xs =>
        if x == u
        then (x :: nil, xs)
        else let (popped, rest) := stack_split_at xs u in
             (x :: popped, rest)
    end.
```

### 3.7 构造 DFS 树：`state_to_dfs_tree`

`is_low`、`dfn_valid`、`stack_tree_reachable` 等核心定义
都依赖一个 `dfs_tree: OriginalGraphType V E` 参数。
它需要从 `SCCSt` 的 `fa`/`dfn`/`visited` 字段中构造，
并满足 `RootedTree` Type Class 和 `is_dfn` Record 的要求。

```coq
(* 从算法状态构造 DFS 树。
   dfs_tree 的顶点集为 visited s，边集为 {(fa[v], v) | v ∈ visited s, fa[v] ≠ v}。
   注意：fa 默认值为 fun v => v（自环），在构造 DFS 树时需要排除。 *)
Definition state_to_dfs_tree (s: SCCSt): OriginalGraphType V E :=
  {| original_vvalid := fun v => v ∈ visited s;
     original_step  := fun e => (* 从 fa 关系中选取有向边 e *)
       exists v, v ∈ visited s /\ fa s v <> v /\
                 original_step_fst g e = fa s v /\
                 original_step_snd g e = v;
     original_step_fst := original_step_fst g;
     original_step_snd := original_step_snd g;
     original_listV  := original_listV g;
  |}.

(* DFS 树需要满足如下 Type Class 实例：
   - RootedTree: 以 root 为根，offspring = dg_reachable dfs_tree
   - is_dfn: dfn_valid + subtree_segment + no_cross_edge + dfn_unique *)
```

**关键引理**（参考 `Tarjan_set_tree.v` 的模式）：

| 引理 | 内容 |
|------|------|
| `state_to_dfs_tree_root` | root 是 DFS 树的根 |
| `state_to_dfs_tree_fa_valid` | 若 `fa[v] ≠ v`，则 `dg_step dfs_tree (fa[v]) v` |
| `state_to_dfs_tree_offspring` | `offspring dfs_tree u v ↔ dg_reachable dfs_tree u v` |
| `state_to_dfs_tree_dfn_valid` | `dfn_valid dfs_tree (dfn s)` — 树边方向 dfn 严格递增 |
| `state_to_dfs_tree_subtree_segment` | DFS 编号的子树分段性质 |
| `state_to_dfs_tree_no_cross_edge` | 在有向图 DFS 树中，不存在横叉边（不同子树之间没有有向边） |
| `state_to_dfs_tree_dfn_unique` | `dfn` 值在不同顶点之间互不相同 |

这些引理的证明策略与 `Tarjan_set_tree.v`（252 行）类似，
但 SCC 版本不需要 `tedge` 字段，且 `set_fa` 是独立操作
（桥判定中 `set_tree` 同时设置 `visited`、`fa`、`tedge`）。

**`fa` 默认值处理**：`initSt` 中 `fa` 的初始值为 `fun v => v`（自环）。
由于 `RootedTree` 的 `Forest` 要求 `no_reachable_back_edge`，
在构造 DFS 树时必须通过 `fa s v <> v` 条件排除未赋值顶点。
桥判定的 `initSt` 采用同样的默认值策略，已验证可行。

---

## 4. 证明文件规划

### 4.1 `Tarjan_scc_basics.v` — 基本不变量

**Context 风格说明**：

Layer 2 证明文件统一使用 typeclass 风格的 Context：
```coq
Context {V E: Type} (g: OriginalGraphType V E)
        `{EqDec V eq}
        `{OriginalGraph_gvalid g}.
```

而 Layer 3 (`SCC_basic.v`) 使用显式假设风格：
```coq
Context {V E: Type} (g: OriginalGraphType V E)
        (Hgvalid: OriginalGraphProp V E g)
        (finite_vertices: forall v, original_vvalid g v -> In v (original_listV g)).
```

两种风格在语义上等价：`OriginalGraph_gvalid` 是通过 `OriginalGraphProp` 定义的
Type Class 实例（见 `GraphLib/examples/tarjan.v` line 53）。
Layer 2 采用 typeclass 风格与 MonadLib/DFS.v/桥判定保持一致，
在 `Require Import SCC_basic` 后需要确认 `finite_vertices` 可从
`OriginalGraph_gvalid` + `Original_finitegraph` 实例中推导。

**Context**：

```coq
Context {V E: Type} (g: OriginalGraphType V E)
        `{EqDec V eq}
        `{OriginalGraph_gvalid g}.
```

**关键不变量**：

```coq
(* visited 单调增 *)
Definition visited_mono (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> v ∈ visited s2.

(* dfn 值持久 — 已在 visited 中的顶点，其 dfn 不变 *)
Definition dfn_persist (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> dfn s1 v = dfn s2 v.

(* low 值持久 *)
Definition low_persist (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> low s1 v = low s2 v.

(* 栈不变量 — 栈中顶点均在 visited 中 *)
Definition stack_in_visited (s: SCCSt): Prop :=
  forall v, In v (stack s) -> v ∈ visited s.

(* sccs 单调增 — 已收集的 SCC 不丢失 *)
Definition sccs_mono (s1 s2: SCCSt): Prop :=
  forall scc, In scc (sccs s1) -> In scc (sccs s2).
```

**核心引理**：

| 引理 | 内容 |
|------|------|
| `Tarjan_keep_visited_inv` | 每个原语操作保持 `visited_mono` |
| `Tarjan_keep_dfn_inv` | `set_dfn` 只赋值未 visited 顶点的 dfn |
| `Tarjan_keep_low_inv` | `update_low` 只修改 visited 顶点的 low |
| `Tarjan_keep_stack_inv` | `push_stack`/`pop_scc` 保持 `stack_in_visited` |
| `Tarjan_keep_sccs_inv` | `pop_scc` 保持 `sccs_mono` 且新增 SCC 是 `is_SCC` |
| `Tarjan_preloop_preserves` | `preloop` 保持所有不变量 |
| `Tarjan_process_edge_preserves` | `process_edge` 保持所有不变量 |
| `Tarjan_tarjan_scc_preserves` | `tarjan_scc`（Lfix）保持所有不变量 |

### 4.2 `Tarjan_scc_is_dfn.v` — dfn 有效性

**核心定义**：

```coq
Definition dfn_valid (dfs_tree: OriginalGraphType V E) (dfn: V -> nat): Prop :=
  forall x y, original_step dfs_tree x y -> dfn x < dfn y.
```

**关键不变量**：

```coq
Definition dfn_inv (s: SCCSt): Prop :=
  (forall v, v ∈ visited s -> dfn s v < timer s) /\
  (forall v, dfn s v = 0 <-> ~ v ∈ visited s).
```

**核心引理**：

| 引理 | 内容 |
|------|------|
| `Tarjan_dfn_timer_inv` | `preloop` 后 `dfn v < timer` |
| `Tarjan_dfn_zero_unvisited` | 未 visited 顶点的 dfn 为 0 |
| `Tarjan_dfn_tree_increasing` | 从 DFS 树边提取 `dfn_valid`：父节点 dfn < 子节点 dfn |

**复用性**：此文件约 50% 的证明策略与 `Tarjan_is_dfn.v`（桥判定）相同，核心差异在于 `dfn_valid` 构造的树来自 `set_fa` 操作而非 `set_tree`。

### 4.3 `Tarjan_scc_is_low.v` — 有向 low 正确性

**这是 Layer 2 的核心难点。** 需要定义有向图版本的 `is_low`，并证明算法维护了 low 的数学语义。

**核心定义**：

```coq
(* 从 x 沿有向边一步可达 y *)
Definition dg_step (g: OriginalGraphType V E) (x y: V): Prop :=
  exists e, original_step g e /\
            original_step_fst g e = x /\
            original_step_snd g e = y.

(* low_tree[v] = v 的 DFS 子树中的所有顶点
  （沿 dfs_tree 边有向可达的顶点） *)
Definition subtree (dfs_tree: OriginalGraphType V E) (v: V): V -> Prop :=
  fun w => dg_reachable dfs_tree v w.

(* 从子树出发沿一条原图有向边可达的顶点 *)
Definition subtree_step (g dfs_tree: OriginalGraphType V E) (v: V): V -> Prop :=
  fun w => exists u, subtree dfs_tree v u /\ dg_step g u w.

(* low_tree[v] = v 的子树 ∪ 子树一步出边可达顶点 *)
Definition low_tree (g dfs_tree: OriginalGraphType V E) (v: V): V -> Prop :=
  subtree dfs_tree v ∪ subtree_step g dfs_tree v.

(* is_low: low[v] = min { dfn[w] | w ∈ low_tree[v] ∧ w 在栈中 } *)
Definition is_low (g dfs_tree: OriginalGraphType V E)
                 (dfn low: V -> nat) (stack: list V): Prop :=
  forall v, v ∈ visited ->
    low v = min_dfn_of_set g dfn
            (low_tree g dfs_tree v ∩ (fun w => In w stack)).
```

**关于 `subtree_step` 中 `dg_step` 包含树边的说明**：

桥判定版本的 `subtree_step` 使用 `step_without_tree`（排除树边），
而 SCC 版本的 `subtree_step` 直接使用 `dg_step`（包含所有有向边，包括树边）。
在有向图中这不是问题：
- 树边子节点 v 已在 `subtree dfs_tree v u` 中（v 属于 u 的子树），不会被重复计入 min
- `process_edge` 中树边走 `visited` 检查分支，子节点递归完成后通过 `update_low u lv` 更新
- `dg_step` 包含树边不会导致 `low[u]` 被自身的 dfn 重复影响（`subtree_step` 的 min 运算天然去重）

因此 SCC 版本无需 `step_without_tree`，简化了定义且避免了需要 `evalid dfs_tree` 判定。

#### 4.3.1 归纳版 low 不变量（用于 `Hoare_fix` 归纳）

**关键设计说明**：`Hoare_fix` 的归纳假设要求一个「对递归调用 W 成立的 low 性质」。
全局 `is_low`（以整个 `dfs_tree` 和全部 `visited` 顶点为域）不能直接作为归纳假设：
递归调用 W 只处理了 u 的子节点（尚未覆盖完整 DFS 树）。

需要额外定义一个归纳版 low 不变量，参考桥判定 `Tarjan_is_low.v`（2812 行）
中 `low_valid_v_inv_with_eset` / `low_valid_loop_inv` 的模式。

```coq
(* 辅助记号：栈集合 *)
Notation stack_set := (fun w => In w (stack s)).

(* 辅助记号：DFS 树中 v 的直接后继（子节点）集合。
   对应 GraphLib/examples/tarjan.v 中的 `son v`。
   定义为：step dfs_tree v w（v 到 w 有树边） *)
Definition children (dfs_tree: OriginalGraphType V E) (v: V): V -> Prop :=
  fun w => dg_step dfs_tree v w.

(* low_valid_v v fun_low:
   low[v] 的值由两个候选值取 min 得到：
   - min_dfn_of_subtree: v 的子树出发一步有向边可达的、仍在栈中的顶点的最小 dfn
   - min_low_of_children: v 的所有子节点的 low 值的最小值 *)
Definition low_valid_v (v: V) (dfn fun_low: V -> nat)
                      (stack: list V): Prop :=
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le
       (subtree_step g dfs_tree v ∩ fun w => In w stack) dfn ∪
     min_value_of_subset Nat.le (children dfs_tree v) fun_low)
    (fun x => x) (fun_low v).

(* low_valid: 对 DFS 树中所有有效顶点成立 *)
Definition low_valid (dfn fun_low: V -> nat) (stack: list V): Prop :=
  forall v, vvalid dfs_tree v -> low_valid_v v dfn fun_low stack.

(* 与全局 is_low 的关系：当算法终止时两者等价 *)
Lemma low_valid_implies_is_low: forall s,
  stack_is_unassigned s ->
  low_valid (dfn s) (low s) (stack s) ->
  is_low g dfs_tree (dfn s) (low s) (stack s).
```

**`min_dfn_of_set` vs `min_value_of_subset` 说明**：

设计文档 §4.3 主定义中使用 `min_dfn_of_set`（自定义），
而此处归纳版使用桥判定已有的 `min_value_of_subset`。
两个方案均可；最终实现建议统一使用 `min_value_of_subset Nat.le`，
原因：
- 桥判定已有成熟的 `min_value_of_subset` 引理库
- `min_value_of_subset` 支持任意的 `relation`（此处用 `Nat.le`）
- 栈过滤 `(∩ stack_set s)` 可以通过 set intersection 表达，无需自定义函数

**关键引理**：

| 引理 | 内容 |
|------|------|
| `is_low_preserved_by_update_low` | `update_low u lv`（`lv = low child`）保持 `is_low` |
| `is_low_preserved_by_update_low_dfn` | `update_low u dv`（`dv = dfn back_edge_target`）保持 `is_low` |
| `is_low_initial` | `preloop u` 后 `is_low` 对 u 成立（low = dfn，low_tree 仅含 u 自身） |
| `is_low_inductive` | 若递归调用返回后 child 的 `low_valid` 成立，则父节点 u 的 `low_valid` 经 `update_low` 后仍成立 |
| `low_valid_preserved_by_process_edge` | `process_edge` 处理单条边后保持 `low_valid` |
| `low_valid_preserved_by_whileP` | 边遍历循环（`whileP`）保持 `low_valid` |
| `low_valid_preserved_by_tarjan_scc` | 递归程序（`Lfix`）保持 `low_valid` — 使用 `Hoare_fix` 规则 |

**核心差异（vs 桥判定无向 `is_low`）**：

| 维度 | 桥判定 (Tarjan_is_low.v) | SCC (Tarjan_scc_is_low.v) |
|------|--------------------------|---------------------------|
| 步关系 | `step g x y`（无向，对称） | `dg_step g x y`（有向，`fst→snd`） |
| `subtree_step` | 子树 + 一条无向非树边 | 子树 + 一条有向边（出边方向） |
| 目标过滤 | 无过滤 | 目标必须在栈中（`In w stack`） |
| `no_cross_edge` | 需要（无向图中区分 back edge vs cross edge） | 不需要 — 有向图中 `dg_step` 天然区分方向 |

**为什么栈过滤是必须的**：Tarjan SCC 的 lowlink 只考虑仍在当前 DFS 搜索路径上的祖先节点。
如果一个顶点已被弹出 SCC（不在栈中），它属于另一个已完成的 SCC，lowlink 不应被其 dfn 影响。

### 4.4 `Tarjan_scc_stack.v` — 栈不变量与 SCC 弹出定理

**这是连接操作语义到 SCC 数学定义的关键桥梁。**

**核心不变量**：

```coq
(* 辅助定义：u 在栈中位于 v 下方（u 先于 v 入栈）。
   即存在将栈分割为 front ++ [u] ++ mid ++ [v] ++ back 的方式 *)
Definition below_in_stack (stk: list V) (u v: V): Prop :=
  exists front mid back,
    stk = front ++ u :: mid ++ v :: back.

(* 栈中顶点按 dfn 递增排列（栈底 dfn 最小，栈顶 dfn 最大）。
   使用 In 谓词避免 nth 的偏函数问题。 *)
Definition stack_dfn_ordered (s: SCCSt): Prop :=
  forall u v, In u (stack s) -> In v (stack s) ->
    (* 若 u 在 v 之前入栈（即 dfn[u] < dfn[v]），则 u 在栈中位于 v 下方 *)
    dfn s u < dfn s v ->
    below_in_stack (stack s) u v.

(* 栈中顶点恰好是已 visited 但尚未分配到 SCC 的顶点 *)
Definition stack_is_unassigned (s: SCCSt): Prop :=
  forall v, In v (stack s) <->
    (v ∈ visited s /\ forall scc, In scc (sccs s) -> ~ scc v).

(* 若 u 在栈中位于 v 下方（dfn[u] < dfn[v]），则 v 属于 u 的 DFS 子树。
   即 u 沿 DFS 树有向边可达 v（树边可达）。
   注：dfs_tree = state_to_dfs_tree s，即当前状态 s 中已记录的 DFS 树。 *)
Definition stack_tree_reachable (dfs_tree: OriginalGraphType V E) (s: SCCSt): Prop :=
  forall u v, In u (stack s) -> In v (stack s) ->
    dfn s u < dfn s v ->
    offspring dfs_tree u v.

(* 若 v 属于 u 的子树，且原图中存在从 v 的子树指向 u 的有向边（回边），
   则 u 和 v 的 low 值都会被更新，最终 low[u] <= dfn[u]。
   栈中 low 值向栈底方向不增（即越靠近栈底 low 值越小或相等）。 *)
Definition stack_low_nonincreasing (s: SCCSt): Prop :=
  forall u v, In u (stack s) -> In v (stack s) ->
    dfn s u < dfn s v ->
    low s v <= low s u.
```

**核心弹出定理**：

```coq
(* 当 low[u] = dfn[u] 时，从栈顶到 u（含）的顶点集合构成一个 SCC *)
Lemma low_eq_dfn_marks_scc_root: forall (dfs_tree: OriginalGraphType V E) s u,
  visited_inv s ->
  dfn_inv s ->
  stack_dfn_ordered s ->
  stack_tree_reachable dfs_tree s ->
  stack_is_unassigned s ->
  is_low g dfs_tree (dfn s) (low s) (stack s) ->
  low s u = dfn s u ->
  In u (stack s) ->
  let popped := fst (stack_split_at (stack s) u) in
  is_SCC g (fun v => In v popped).
```

**关键辅助引理** — `stack_split_at` 的规约：

```coq
(* popped 包含 u 且恰好是从栈顶到 u（含）的所有顶点。
   需要传入 dfn 函数以表达"rest 中顶点的 dfn 均小于 popped 中顶点的 dfn"。 *)
Lemma stack_split_at_spec (stk: list V) (u: V) (dfn: V -> nat) :
  In u stk ->
  let (popped, rest) := stack_split_at stk u in
  (* 分割正确：popped ++ rest = stk（保持顺序） *)
  popped ++ rest = stk /\
  (* popped 非空且以 u 结尾 *)
  exists front, popped = front ++ [u] /\
  (* popped 中的所有元素都不在 rest 中 *)
  (forall v, In v popped -> ~ In v rest) /\
  (* rest 的 dfn 值全部小于 popped 中任意元素的 dfn（popped = 当前 SCC） *)
  (forall v w, In v popped -> In w rest -> dfn w < dfn v).
```

**证明结构**（三个条件的独立证明）：

1. **非空性**：`popped` 至少包含 u（由 `stack_split_at_spec`），且 `visited_inv` + `stack_is_unassigned` → `u ∈ visited`，保证 `vvalid g u`。

2. **内部相互可达性**：对 `popped` 中任意两个顶点 x, y，需要证明 `mutually_reachable g x y`，即 `dg_reachable g x y /\ dg_reachable g y x`。
   - 由于 x, y 都在 popped 中且 popped = 从栈顶到 u，有 `dfn[u] ≤ dfn[x]` 和 `dfn[u] ≤ dfn[y]`
   - 由 `stack_tree_reachable`，u 沿 DFS 树可达 x 和 y：`offspring dfs_tree u x` 且 `offspring dfs_tree u y`
   - 因此 `dg_reachable g u x` 且 `dg_reachable g u y`（树边蕴含原图有向边）
   - 由 `is_low` 定义，`low[x] = dfn[u]`（因为 low[x] 的最小值来自 u 或 u 的祖先，但 `dfn[u] = low[u]` 是最小值）
   - 因此存在从 x 出发沿有向边到达 dfn = low[x] = dfn[u] 的顶点的路径 → `dg_reachable g x u`
   - 同理 `dg_reachable g y u`
   - 拼接：x →* u →* y，y →* u →* x，得 `mutually_reachable g x y`

3. **极大性**：若 x ∈ `popped`，`vvalid g w`，`mutually_reachable g x w`，则 w 也在 `popped` 中。
   - 由 `mutually_reachable g x w`，存在路径 x →* w 和 w →* x
   - 由 (2) 知 x →* u，因此 w →* x →* u 得 w 可达 u
   - 由 `stack_is_unassigned`，w 在栈中（否则 w 属于已完成的 SCC，与 x 在栈中且 x ↔ w 矛盾）
   - 若 w 不在 `popped` 中，则 w 在 `rest` 中（栈中 u 的下方）→ `dfn[w] < dfn[u]`
   - 但由 `is_low` 定义和 `low[u] = dfn[u]`，w 可达 u → `dfn[w] < dfn[u] = low[u]`，与 `is_low` 的极小性矛盾
   - 因此 w 也在 `popped` 中

```coq
(* 弹出操作保持 scc_partition 不变量（pop_scc_state 定义见 §3.4） *)
Lemma pop_scc_preserves_sccs_inv: forall (dfs_tree: OriginalGraphType V E) s u,
  visited_inv s ->
  dfn_inv s ->
  stack_dfn_ordered s ->
  stack_tree_reachable dfs_tree s ->
  stack_is_unassigned s ->
  is_low g dfs_tree (dfn s) (low s) (stack s) ->
  low s u = dfn s u ->
  In u (stack s) ->
  (forall scc, In scc (sccs s) -> is_SCC g scc) ->
  let s' := pop_scc_state s u in
  (forall scc, In scc (sccs s') -> is_SCC g scc).
```

### 4.5 `SCC_correctness.v` — 主正确性定理

```coq
Require Import Algorithms.Tarjan_directed.Tarjan_scc.
Require Import Algorithms.Tarjan_directed.Tarjan_scc_basics.
Require Import Algorithms.Tarjan_directed.Tarjan_scc_is_dfn.
Require Import Algorithms.Tarjan_directed.Tarjan_scc_is_low.
Require Import Algorithms.Tarjan_directed.Tarjan_scc_stack.
Require Import Algorithms.Tarjan_directed.SCC_basic.

Section SCC_CORRECTNESS.
  Context {V E: Type} (g: OriginalGraphType V E)
          `{EqDec V eq}
          `{OriginalGraph_gvalid g}.

  (* 完整不变量（汇总所有子模块的不变量） *)
  Definition tarjan_scc_invariant (s: SCCSt): Prop :=
    let dfs_tree := state_to_dfs_tree s in
    (* 来自 Tarjan_scc_basics.v *)
    visited_mono s /\
    dfn_persist s /\
    low_persist s /\
    stack_in_visited s /\
    sccs_mono s /\
    (* 来自 Tarjan_scc_is_dfn.v *)
    dfn_inv s /\
    (* 来自 Tarjan_scc_is_low.v *)
    is_low g dfs_tree (dfn s) (low s) (stack s) /\
    (* 来自 Tarjan_scc_stack.v *)
    stack_dfn_ordered s /\
    stack_is_unassigned s /\
    stack_tree_reachable dfs_tree s /\
    stack_low_nonincreasing s /\
    (* sccs 中每个元素都是 is_SCC *)
    (forall scc, In scc (sccs s) -> is_SCC g scc).

  (* 主定理 *)
  Theorem tarjan_scc_correctness: forall root,
    vvalid g root ->
    Hoare (fun s => s = initSt)
          (tarjan_scc root)
          (fun _ s =>
            scc_partition g (sccs s) /\
            (forall v, v ∈ visited s <-> dg_reachable g root v)).
```

**证明策略**：

1. 由 `Lfix` 的 `Hoare_fix` 规则，对递归程序使用归纳假设
2. 在每个原语操作后应用对应的保持性引理：
   - 基本不变量保持性来自 `Tarjan_scc_basics.v`
   - `dfn_inv` 保持性来自 `Tarjan_scc_is_dfn.v`
   - `low_valid` 保持性来自 `Tarjan_scc_is_low.v`（使用归纳版 `low_valid` + `Hoare_fix`）
3. 在 `pop_scc` 后应用 `pop_scc_preserves_sccs_inv`（来自 `Tarjan_scc_stack.v`）
   以及 `low_valid_implies_is_low`（来自 `Tarjan_scc_is_low.v`）得到 `is_SCC`
4. 最终组装三个条件（覆盖性、正确性、互斥性）得到 `scc_partition`
   - **覆盖性**：DFS 访问了所有从 root 有向可达的顶点，每个 visited 顶点在某次 `pop_scc` 中被收集
   - **正确性**：由 `pop_scc_preserves_sccs_inv`，每次 `pop_scc` 都产生一个 `is_SCC`
   - **互斥性**：一个顶点只能被弹出一次（`pop_scc` 修改 `stack`，且 `stack_is_unassigned` 保证已弹出顶点不再入栈）

#### 4.5.1 外层循环（处理非连通图）

`tarjan_scc root` 只处理从单个 root 出发的 DFS。
完整的 Tarjan SCC 算法需要遍历所有顶点，
对每个未 visited 的顶点启动一次 `tarjan_scc`。

外层循环有两种实现方案：

**方案 A（推荐）：在 Layer 2 中实现 `tarjan_scc_all`**

```coq
Definition tarjan_scc_all: program SCCSt unit :=
  forset (fun v => original_vvalid g v)
         (fun v => If (fun s => ~ v ∈ visited s) (tarjan_scc v)).

Theorem tarjan_scc_all_correctness:
  Hoare (fun s => s = initSt)
        tarjan_scc_all
        (fun _ s =>
          scc_partition g (sccs s) /\
          (forall v, original_vvalid g v -> v ∈ visited s)).
```

**方案 B：推迟到 Layer 1（C 代码）**

C 代码 `tarjan_directed.c` 中由调用者循环：
```c
for (v = 0; v < n; v++)
  if (!visited[v]) tarjan(v);
```

**选择**：采用方案 A。
- `forset` 已支持遍历顶点全集（`original_vvalid g`）
- `Hoare_forset` 规则可直接组合单次 `tarjan_scc_correctness`
- Layer 1 的 C 代码直接对应 `tarjan_scc_all`，简化 refinement proof

### 4.6 `Tarjan_scc_tarjan.v` — 聚合模块

```coq
Require Import Algorithms.Tarjan_directed.Tarjan_scc.
Require Import Algorithms.Tarjan_directed.Tarjan_scc_basics.
Require Import Algorithms.Tarjan_directed.Tarjan_scc_is_dfn.
Require Import Algorithms.Tarjan_directed.Tarjan_scc_is_low.
Require Import Algorithms.Tarjan_directed.Tarjan_scc_stack.
Require Import Algorithms.Tarjan_directed.SCC_correctness.
(* 重新导出所有公共定义和定理 *)
```

参考 `Tarjan_tarjan.v`（桥判定）的聚合模式。

---

## 5. 文件清单

```
SeparationLogic/algorithms/Tarjan_directed/
├── SCC_basic.v                ✅ 已完成    — Layer 3 数学规格
├── Tarjan_scc.v               🆕 200-300 行 — State Record + monadic 程序 + DFS 树构造
├── Tarjan_scc_basics.v        🆕 400-600 行 — 基本不变量 + 栈不变量
├── Tarjan_scc_is_dfn.v        🆕 200-350 行 — dfn 有效性 + `is_dfn` Record 实例证明
├── Tarjan_scc_is_low.v        🆕 800-1500 行 — 有向 low 正确性（含归纳版 low 不变量，核心难点）
├── Tarjan_scc_stack.v         🆕 500-900 行 — 栈不变量 + `low_eq_dfn_marks_scc_root` + `stack_split_at` 规约
├── SCC_correctness.v          🆕 400-700 行 — 主正确性定理 + `tarjan_scc_all` 外层循环
└── Tarjan_scc_tarjan.v        🆕 30-50 行   — 聚合
```

预估总行数：~2500–4000 行（不含 `SCC_basic.v`）。

**行数校准依据**：桥判定对应文件的实测行数 —
`Tarjan_is_low.v` 2812 行（含 `no_cross_edge` 的推理），
`Tarjan_basics.v` 1577 行，
`Tarjan_basics_ex.v` 2614 行。
SCC 版本不需要 `no_cross_edge`（有向图天然区分方向），
但需要栈过滤和更强的不变量交互，预计总行数与桥判定在同一量级。

---

## 6. 不变量的依赖关系

```
visited_inv ──┐
              ├──> stack_is_unassigned ──┐
dfn_inv ──────┤                          │
              ├──> stack_dfn_ordered ────┤
              │                          ├──> low_eq_dfn_marks_scc_root ──┐
              ├──> stack_tree_reachable ─┤                               │
              │                          │                               │
              └──> is_low_inv ───────────┘                               │
                                                                         │
                                                         ┌───────────────┘
                                                         v
                                                  scc_partition g s.(sccs)
```

- `visited_inv` + `dfn_inv` → `stack_is_unassigned`（栈中顶点有有效 dfn 且未分配 SCC）
- `dfn_inv` → `stack_dfn_ordered`（栈序与 dfn 序一致）
- `dfn_inv` + DFS 树构造 → `stack_tree_reachable`（祖先沿树边可达到后代）
- `is_low_inv` + `stack_dfn_ordered` + `stack_tree_reachable` + `stack_is_unassigned` → `low_eq_dfn_marks_scc_root`
- 所有不变量 → `SCC_correctness.v` 的主定理

---

## 7. 推荐执行顺序

| 步骤 | 文件 | 预估工作量 | 产出标准 |
|------|------|-----------|---------|
| 1 | `Tarjan_scc.v` | 1–2 天 | 程序定义 + `mono_cont` + `Lfix_unfold` + DFS 树构造，编译通过 |
| 2 | `Tarjan_scc_basics.v` | 2–3 天 | 基本不变量 + 栈不变量保持性引理，全部 Qed |
| 3 | `Tarjan_scc_is_dfn.v` | 1–2 天 | `dfn_inv` 保持性 + `is_dfn` Record 实例证明，全部 Qed |
| 4 | `Tarjan_scc_is_low.v` | 3–7 天 | 有向 `is_low` 全局定义 + `low_valid` 归纳版 + `low_valid` → `is_low` 等价性，全部 Qed |
| 5 | `Tarjan_scc_stack.v` | 4–7 天 | `stack_split_at` 规约 + `low_eq_dfn_marks_scc_root` + `pop_scc_preserves_sccs_inv`，全部 Qed |
| 6 | `SCC_correctness.v` | 3–6 天 | 主定理 `tarjan_scc_correctness` + `tarjan_scc_all_correctness`，全部 Qed |
| 7 | `Tarjan_scc_tarjan.v` | 0.5 天 | 聚合，编译通过 |

总预估：~15–28 天。

**注意**：
- 步骤 4 和步骤 5 是两个核心难点，之间有依赖（步骤 5 引用步骤 4 的 `is_low`/`low_valid` 定义）
- 步骤 2–3 可以并行推进（`basics` 和 `dfn` 之间无依赖）
- 步骤 4 中的归纳版 `low_valid` 是 `Hoare_fix` 规则能使用的关键，建议先在纸上完成 `low_valid` → `is_low` 的等价性证明草图
- 行数校准：桥判定 `Tarjan_is_low.v` 实测 2812 行；SCC 版本虽无需 `no_cross_edge`，但栈过滤逻辑增加了额外复杂度

---

## 8. 关键设计决策

| # | 决策 | 选择 | 理由 |
|---|------|------|------|
| 1 | 边遍历循环 | `whileP` | 与 DFS.v 一致，mono_cont 策略成熟 |
| 2 | 出边集合 | `dg_step g u v`（来自 `SCC_basic.v`） | 有向边语义，与 `SCC_basic.v` 一致 |
| 3 | 父节点字段 | `fa: V -> V`（使用默认值） | 用于构造 DFS 树；配合 `set_fa` 操作逐步记录父子关系，最终用于 `RootedTree` 和 `is_dfn` Record 实例构造 |
| 4 | DFS 树 Type Class | `RootedTree` + `is_dfn` Record | 代码库中不存在单独的 `DFSTree` Type Class；实际使用 `directed/rootedtree.v` 的 `RootedTree` Class + `directed/dfstree_dfn.v` 的 `is_dfn` Record |
| 5 | TraceLib | **暂不引入** | 先直接证明，trace 增加大量复杂度；若后续发现需要（如 cross-edge 推理需要事件序），再引入 |
| 6 | `SCC_correctness.v` 的目标 | `scc_partition g s.(sccs)` + `visited = dg_reachable g root` | 完整规格：被访问的顶点 = 从 root 出发有向可达的顶点，且 sccs 是这些顶点的 SCC 划分 |
| 7 | 证明风格 | `Hoare` 三元组 + `mono_cont` + `Lfix_fixpoint'` | 与 DFS.v 和桥判定一致 |

---

## 9. 风险与缓解

| 风险 | 可能性 | 影响 | 缓解措施 |
|------|--------|------|----------|
| `is_low` 在栈过滤下的归纳证明比预期复杂 | **高** | 高 | 先在纸上完成 `low_eq_dfn_marks_scc_root` 的证明草图，确认核心论证无误后再开始 Rocq 编码；桥判定 `Tarjan_is_low.v` 实测 2812 行，栈过滤可能增加额外复杂度 |
| 归纳版 `low_valid` 与全局 `is_low` 的等价性证明出现循环依赖 | 中 | 高 | 严格分层：先在 `Tarjan_scc_is_low.v` 中只证明 `low_valid` 的保持性和 `low_valid` → `is_low`（引入全部栈不变量后），避免在 `Lfix` 归纳中直接使用全局 `is_low` |
| `whileP` 与 `forset` 的不变式规则不同 | 低 | 中 | DFS.v 已有成熟的 `whileP` + `Hoare_whileP` 模式，直接参考 |
| DFS 树构造（`state_to_dfs_tree` → `RootedTree` + `is_dfn` 实例）比预期复杂 | 中 | 高 | 桥判定 `Tarjan_set_tree.v`（252 行）提供了 `RootedTree` 构造的标准模式；SCC 版本需额外适配 `set_fa` 操作（无 `tedge`）、排除 `fa` 自环默认值 |
| `stack_split_at` 规约引理的归纳证明有边界情况 | 中 | 中 | 先写出完整的 `stack_split_at_spec` 引理及其纸面证明；特别注意 `In u stk` 前提和 `x == u` 的 `EqDec` 可判定性 |
| 栈弹出操作的历史信息丢失 | 低 | 中 | `sccs` 字段直接记录已弹出 SCC，不需要从历史栈状态重建 |
| `scc_partition_exists`（`SCC_basic.v`）与算法输出的 `sccs` 之间关系不清 | 低 | 低 | `scc_partition_exists` 是纯数学存在性定理；算法输出是对该存在的构造性实现，两者通过 `scc_partition` 谓词统一 |
| Context 风格不兼容导致 `SCC_basic.v` 引理无法直接引用 | 低 | 中 | Layer 2 采用 typeclass 风格（与 MonadLib 一致）；`SCC_basic.v` 使用显式假设；确认 typeclass 实例可从显式 `OriginalGraphProp` 构造 |

---

## 10. 后续 Phase 接口

Layer 2 完成后，进入 Phase 2（C 标注 + 符号执行）时：

- `common_case_formal_lib` 需导入 `Tarjan_scc_tarjan.v`（获取 `tarjan_scc` 程序和 `tarjan_scc_correctness` 定理）
- C 函数 `tarjan()` 的 `Ensure` 后置条件引用 `scc_partition g s.(sccs)`
- `refinement proof` 模式下，C annotation 中的逻辑变量 `With (G: OriginalGraphType Z Z)` 将 C 内存状态映射到 `SCCSt`，VC 生成 `safeExec` 精化目标

---

## 11. 参考文件

| 文件 | 用途 |
|------|------|
| `SeparationLogic/algorithms/Tarjan_directed/SCC_basic.v` | Layer 3 数学规格 — 所有 SCC 定义和定理 |
| `SeparationLogic/algorithms/DFS/DFS.v` | DFS monadic 程序 — `whileP`、`Lfix`、`mono_cont` 模式 |
| `SeparationLogic/MonadLib/StateRelMonad/StateRelBasic.v` | `program Σ A` 定义 + 所有算子 |
| `SeparationLogic/MonadLib/StateRelMonad/StateRelHoare.v` | `Hoare` 三元组 + `Hoare_bind`/`Hoare_get`/`Hoare_update` 等规则 |
| `SeparationLogic/MonadLib/StateRelMonad/FixpointLib.v` | `Lfix`、`mono_cont`、`Lfix_fixpoint'` |
| `SeparationLogic/GraphLib/examples/tarjan.v` | `OriginalGraphType`、`OriginalGraphProp`、`RootedTreeType`、`no_cross_edge` |
| `SeparationLogic/GraphLib/directed/rootedtree.v` | `RootedTree` Type Class、`Forest`、`offspring`、子树引理 |
| `SeparationLogic/GraphLib/directed/dfstree.v` | 简单版 `dfn_valid` 谓词（`step dfs_tree x y -> dfn x < dfn y`） |
| `SeparationLogic/GraphLib/directed/dfstree_dfn.v` | `is_dfn` Record（包含 `dfn_valid`、`subtree_segment`、`no_cross_edge`、`dfn_unique` 四个条件） |
| `SeparationLogic/MonadLib/Examples/kmp.v` | KMP 数学规格层的分层设计模式（参考） |
| `docs/dev/20260612-scc-basic-design.md` | SCC_basic.v 设计文档 |
| `docs/dev/20260611-kmp-refinement-proof.md` | KMP refinement 三層架构参考 |
| `docs/plan-tarjan-scc-2sat-verification.md` | 六阶段总计划 |
