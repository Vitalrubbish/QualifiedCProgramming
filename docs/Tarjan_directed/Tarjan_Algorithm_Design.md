# Tarjan 强连通分量算法 — 形式化验证设计

**Author**: Vitalrubbish
**Date**: 2026-06-24

## 概述

本文档给出 Tarjan 有向图强连通分量（SCC）算法的形式化验证的**完整设计**。参照 Kosaraju 算法的验证架构（`docs/Kosaraju/Kosaraju.md`），将验证分解为清晰的分层结构：图论基础设施 → 单子程序定义 → 基本不变式 → dfn 不变式 → low-link 正确性 → 全局 SCC 正确性。

与 Kosaraju 的两趟 DFS 不同，Tarjan 算法仅需**一趟 DFS**，通过维护 `low`（low-link）值来实时识别 SCC 根节点。这使得其不变式设计更加精细，但整体验证架构仍然遵循相同的分层模式。

---

## 1. 图模型

### 有向图原语

在 `OriginalGraphType V E` 的基础上定义有向图原语：

```coq
(* 有向边：存在原始边 e 从 x 指向 y *)
Definition dg_step (g: OriginalGraphType V E) (x y: V): Prop :=
  exists e, original_step g e /\
            original_step_fst g e = x /\
            original_step_snd g e = y.

(* 有向可达：dg_step 的自反传递闭包 *)
Definition dg_reachable (g: OriginalGraphType V E) (x y: V): Prop :=
  clos_refl_trans (dg_step g) x y.

(* 相互可达 *)
Definition mutually_reachable (g: OriginalGraphType V E) (u v: V): Prop :=
  dg_reachable g u v /\ dg_reachable g v u.
```

### SCC 数学定义

```coq
(* s 是图 g 的一个 SCC *)
Definition is_SCC (g: OriginalGraphType V E) (s: V -> Prop): Prop :=
  (exists v, s v /\ original_vvalid g v) /\                      (* 非空 *)
  (forall u v, s u -> s v -> mutually_reachable g u v) /\         (* 内部连通 *)
  (forall u v, s u -> original_vvalid g v ->
     mutually_reachable g u v -> s v).                            (* 极大性 *)

(* sccs 是图 g 的一个 SCC 划分 *)
Definition scc_partition (g: OriginalGraphType V E) (sccs: list (V -> Prop)): Prop :=
  (forall v, original_vvalid g v -> exists s, In s sccs /\ s v) /\  (* 覆盖 *)
  (forall s, In s sccs -> is_SCC g s) /\                             (* 正确 *)
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v ->       (* 互斥 *)
     forall w, s1 w = s2 w).
```

### 缩点图 DAG 性质

```coq
(* 缩点边：从 SCC s1 到 SCC s2（s1 ≠ s2）存在原图有向边 *)
Definition condensation_edge (sccs: list (V -> Prop)) (s1 s2: V -> Prop): Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ dg_step g u v.

(* 缩点图无环 *)
Theorem condensation_is_acyclic: forall sccs,
  scc_partition g sccs ->
  forall s1 s2, condensation_edge sccs s1 s2 ->
  ~ condensation_reachable sccs s2 s1.
```

这些图论基础设施与 Kosaraju 共享同一架构，但使用有向边 `dg_step` 替代无向 `step`。

---

## 2. 程序状态

```coq
Record SCCSt: Type := mkSCCSt {
  visited : V -> Prop;    (* 已访问顶点集 *)
  timer   : nat;          (* DFS 时间戳计数器，单调递增 *)
  fa      : V -> V;       (* DFS 父节点映射；根的父节点为自身 *)
  dfn     : V -> nat;     (* DFS 发现时间；0 表示未访问 *)
  low     : V -> nat;     (* low-link 值 *)
  stack   : list V;       (* Tarjan 栈，存储当前 DFS 路径上的顶点 *)
  sccs    : list (V -> Prop); (* 已输出的 SCC 列表 *)
}.
```

**初始状态**：
```coq
Definition initSt: SCCSt :=
  mkSCCSt (fun _ => False) 1 (fun v => v) (fun _ => 0) (fun _ => 0) nil nil.
```

关键设计选择：
- `fa v = v` 作为"根节点/未赋值"的哨兵值，与 Kosaraju 一致
- `dfn v = 0` 作为"未访问"的哨兵值——此编码简化了"dfn=0 iff unvisited"这一核心引理
- `timer` 从 1 开始（而非 0），使 Sentinel 值 0 有清晰的语义

---

## 3. 程序定义

### 3.1 基本操作

```coq
Definition visit (v: V): program SCCSt unit :=
  update' (fun s => s <| visited ::= fun x => x ∪ [v] |>).

Definition set_dfn (v: V) (n: nat): program SCCSt unit :=
  update' (fun s => s <| dfn ::= fun dfn0 x =>
    if equiv_decb x v then n else dfn0 x |>).

Definition set_low (v: V) (n: nat): program SCCSt unit :=
  update' (fun s => s <| low ::= fun low0 x =>
    if equiv_decb x v then n else low0 x |>).

Definition set_fa (v: V) (p: V): program SCCSt unit :=
  update' (fun s => s <| fa ::= fun fa0 x =>
    if equiv_decb x v then p else fa0 x |>).

Definition incr_timer: program SCCSt unit :=
  update' (fun s => s <| timer ::= fun t => S t |>).

Definition push_stack (v: V): program SCCSt unit :=
  update' (fun s => s <| stack ::= fun stk => v :: stk |>).

(* 仅当 n < low[u] 时才更新 *)
Definition update_low (u: V) (n: nat): program SCCSt unit :=
  lu <- get' (fun s => low s u);;
  If (fun s => n < low s u) (set_low u n).

(* 弹出以 u 为栈底的 SCC *)
Definition pop_scc (u: V): program SCCSt unit :=
  update' (fun s => pop_scc_state s u).
```

其中 `pop_scc_state` 将栈在 `u` 处分割为 `(popped, rest)`，`popped` 为从栈顶到 `u`（含）的顶点列表，作为新 SCC 加入 `sccs`。

### 3.2 主程序

```coq
(* DFS 进入顶点 u 的前置处理 *)
Definition preloop (u: V): program SCCSt unit :=
  t <- get (fun s t => t = s.(timer));;
  set_dfn u t;;
  set_low u t;;
  incr_timer;;
  push_stack u;;
  visit u.

(* 处理从 u 到 v 的一条有向边；W 是递归体 *)
Definition process_edge (u: V) (W: V -> program SCCSt unit) (v: V): program SCCSt unit :=
  if_else (fun s => ~ v ∈ visited s)
    (* 树边 (tree edge): v 未被访问 *)
    (set_fa v u;; W v;;
     lv <- get' (fun s => low s v);;
     update_low u lv)
    (* 非树边 *)
    (If (fun s => In v (stack s))
       (* 回边 (back edge): v 在栈中 → 同一 SCC *)
       (dv <- get' (fun s => dfn s v);;
        update_low u dv)).

(* Tarjan 单步函数体，W 为递归占位参数 *)
Definition tarjan_scc_f (W: V -> program SCCSt unit) (u: V): program SCCSt unit :=
  preloop u;;
  forset (fun v => dg_step g u v) (process_edge u W);;
  If (fun s => low s u = dfn s u) (pop_scc u).

(* 最小不动点递归 *)
Definition tarjan_scc (u: V): program SCCSt unit :=
  Lfix tarjan_scc_f u.

(* 外层循环：遍历所有有效顶点 *)
Definition tarjan_scc_all: program SCCSt unit :=
  forset (fun v => original_vvalid g v)
         (fun v => If (fun s => ~ v ∈ visited s) (tarjan_scc v)).
```

### 3.3 单调性

```coq
Lemma tarjan_scc_f_mono_cont: mono_cont tarjan_scc_f.
Lemma tarjan_scc_unfold (u: V):
  tarjan_scc u == tarjan_scc_f tarjan_scc u.
```

`mono_cont` 保证最小不动点的存在性和展开性质，是后续 Lfix 归纳证明的基础。

---

## 4. DFS 树构造

从算法状态提取 DFS 树的结构化视图：

```coq
Definition state_to_dfs_tree (s: SCCSt) (root: V): OriginalGraphType V E :=
  {|
    original_vvalid := fun v => v ∈ visited s;
    original_step   := fun e => exists v, v ∈ visited s /\ fa s v <> v /\
                                original_step_fst g e = fa s v /\
                                original_step_snd g e = v;
    (* 其他字段从 g 继承 *)
  |}.
```

DFS 树的核心性质：
- **顶点集** = `visited s`
- **边** = `fa s v → v`（其中 `fa s v ≠ v`，即排除根节点自指）
- 边的方向与原始图一致（从父到子）

### DFS 树结构引理

```coq
(* 正向：树边 → fa/visited 条件 *)
Lemma tree_step_char: dg_step (dfs_tree s root) x y ->
  fa s y = x /\ fa s y <> y /\ y ∈ visited s.

(* 反向：状态条件 + 原图边 → 树边 *)
Lemma tree_step_char_backward: dg_step g x y ->
  fa s y = x -> fa s y <> y -> y ∈ visited s ->
  dg_step (dfs_tree s root) x y.
```

这些引理构成了连接算法状态（`fa`、`visited`）与纯图论概念（`dg_step`、`dg_reachable`）的桥梁。

---

## 5. 不变式分层架构

验证按以下层次组织，每层在前一层基础上构建：

```
Layer 0: 图论基础设施 (SCC_basic)
  dg_step, dg_reachable, mutually_reachable, is_SCC, scc_partition,
  condensation_edge, condensation_is_acyclic

Layer 1: 基本单调不变式
  visited_mono, dfn_persist, low_nonincreasing, fa_persist,
  timer_mono, stack_in_visited

Layer 2: dfn 不变式
  dfn_inv, dfn_valid, fa_visited, dfn_injective, stack_dfn_order

Layer 3: Low-link 局部正确性
  scc_low_tree, scc_low_valid_v, scc_is_low_v,
  forset_low_inv (forset 迭代不变式)

Layer 4: Low-link 全局正确性
  tarjan_scc_keep_low_valid（单顶点）
  tarjan_scc_all_scc_is_low（全图）

Layer 5: SCC 划分正确性
  tarjan_scc_correct（最终定理）
```

---

## 6. Layer 1 — 基本单调不变式

```coq
Definition visited_mono (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> v ∈ visited s2.

Definition dfn_persist (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> dfn s1 v = dfn s2 v.

Definition low_nonincreasing (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> low s2 v <= low s1 v.

Definition fa_persist (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> fa s1 v = fa s2 v.

Definition timer_mono (s1 s2: SCCSt): Prop :=
  timer s1 <= timer s2.

Definition stack_in_visited (s: SCCSt): Prop :=
  forall v, In v (stack s) -> v ∈ visited s.
```

这些是 Tarjan 算法最基础的双状态不变式，每个基本操作和组合操作都必须保持。它们打包为：

```coq
Definition basics_invariant (s1 s2: SCCSt): Prop :=
  visited_mono s1 s2 /\ dfn_persist s1 s2 /\ low_nonincreasing s1 s2 /\
  fa_persist s1 s2 /\ timer_mono s1 s2 /\ stack_in_visited s2.
```

### 核心保持引理

对每个基本操作 `op`，证明形如：
```coq
Lemma op_keep_visited: Hoare (fun s => v ∈ visited s) (op ...) (fun _ s => v ∈ visited s).
Lemma op_keep_dfn: Hoare (fun s => ...) (op ...) (fun _ s => dfn s v = n).
(* ... 对 fa, low, timer, stack_in_visited 同理 *)
```

对组合操作（`preloop`、`process_edge`、`tarjan_scc`），通过 Hoare 组合规则将基本保持引理组合为复合保持引理。

---

## 7. Layer 2 — dfn 不变式

### 7.1 `dfn_inv` — dfn 基本不变式

```coq
Definition dfn_inv (s: SCCSt): Prop :=
  (forall v, v ∈ visited s -> dfn s v < timer s) /\    (* (A) 已访问的 dfn < timer *)
  (forall v, dfn s v = 0 <-> ~ v ∈ visited s) /\       (* (B) dfn=0 iff 未访问 *)
  0 < timer s.                                          (* (C) timer 始终为正 *)
```

**语义**：
- (A) 保证已分配 dfn 的值小于当前 timer（分配后 timer 已递增）
- (B) 利用 dfn=0 作为"未访问"的哨兵标记——这个编码使得很多引理的表述更简洁
- (C) 保证 timer 从 1 开始（初始值），从而 dfn 值从 1 开始

**关键引理**：`preloop u` 从 `dfn_inv s /\ ~u ∈ visited s` 出发，分配 `dfn[u] := timer`，然后递增 timer，最终恢复完整 `dfn_inv`。

### 7.2 `dfn_valid` — 树边 dfn 单调性

```coq
Definition dfn_valid (s: SCCSt) (root: V): Prop :=
  forall x y, dg_step (state_to_dfs_tree g s root) x y -> dfn s x < dfn s y.
```

**语义**：DFS 树中每条父→子边满足 `dfn[父] < dfn[子]`——即父节点的发现时间严格早于子节点。

**证明策略**：`dfn_valid` 仅在 `preloop u` 执行后（分配 `dfn[u] := timer`）才对新树边 `parent → u` 成立。在 `set_fa v u` 后、`preloop v` 前，新树边 `u → v` 的 dfn 关系尚未建立——此"pending tree edge"状态由 `dfn_pre` 刻画：

```coq
Definition dfn_pre (u: V) (s: SCCSt) (root: V): Prop :=
  ~ u ∈ visited s /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s.
```

`preloop` 从 `dfn_pre u` 恢复到完整 `dfn_valid`（含新边 `parent → u`）。

### 7.3 `dfn_injective` — dfn 单射性

```coq
Definition dfn_injective (s: SCCSt): Prop :=
  forall x y, x <> y -> x ∈ visited s -> y ∈ visited s -> dfn s x <> dfn s y.
```

**语义**：不同已访问顶点的 dfn 值互不相同。这来源于每次分配 dfn 时 timer 递增且永不回退。

### 7.4 `fa_visited` — 父节点已访问

```coq
Definition fa_visited (s: SCCSt): Prop :=
  forall v, fa s v <> v -> fa s v ∈ visited s.
```

**语义**：每个非根顶点的父节点在 visited 集中。此性质在 `set_fa v u` 时由 `u ∈ visited` 前提保证。

### 7.5 `stack_dfn_order` — 栈中 dfn 有序

```coq
Definition stack_dfn_order (s: SCCSt): Prop :=
  forall x y l1 l2, stack s = l1 ++ x :: l2 -> In y l2 -> dfn s x <= dfn s y.
```

**语义**：栈中顶点按 dfn 非递减排列（栈底 dfn 小，栈顶 dfn 大）。该性质源于顶点按 preloop 顺序入栈，且每次 preloop 分配的 dfn 严格递增。

### 7.6 `settled_closed` — 已沉降顶点闭合

```coq
Definition settled_closed (s: SCCSt): Prop :=
  forall v w, v ∈ visited s -> ~ In v (stack s) ->
    dg_reachable g v w -> w ∈ visited s.
```

**语义**：已被弹出栈（已确定 SCC 归属）的顶点，其所有前向可达顶点也都已访问。这是 Kosaraju 中 `ReachRevClosed` 的 Tarjan 对应物——它保证"已完成的 SCC 不会通过前向可达路径连到未访问顶点"，从而封锁 cross-subtree 中"old→new"的病理情况。

**为什么需要这个不变式**：
1. 在证明 `pop_scc` 的极大性时，需要排除弹出集合外存在与集合内顶点相互可达的顶点
2. `settled_closed` 保证这种"外部相互可达顶点"不可能存在——若存在路径从已弹出 SCC 回到当前栈中顶点，则违反缩点图无环性

**保持性**：`visit`、`push_stack`、`pop_scc`（移除顶点出栈）均保持此性质。关键在于 `pop_scc u`（当 `low[u]=dfn[u]`）弹出的是完整 SCC，不会产生新的"已沉降但前向可达未访问顶点"的情况。

### 7.7 `wf_scc_state` — 整体良构状态

```coq
Definition wf_scc_state (s: SCCSt): Prop :=
  stack_in_visited s /\ dfn_inv s /\ dfn_valid g s root /\
  fa_visited s /\ settled_closed s.
```

`wf_scc_state` 打包了 Layer 2 的全部全局不变式，作为 Layer 3（low-link 正确性）的**前置条件**。所有修改状态的操作都需证明保持 `wf_scc_state`。

---

## 8. Layer 3 — Low-link 局部正确性

这是 Tarjan 验证的核心。

### 8.1 核心定义

```coq
(* 回边：从 x 到 y 的原图有向边，y 仍在栈中，但不是 DFS 树边 *)
Definition scc_back_edge (s: SCCSt) (x y: V): Prop :=
  dg_step g x y /\ In y (stack s) /\
  ~ dg_step (state_to_dfs_tree g s root) x y.

(* scc_low_reachable: 从 x 出发，沿树边下行 + 至多一条回边可达 y *)
Definition scc_low_reachable (s: SCCSt) (x y: V): Prop :=
  exists z, dg_reachable (state_to_dfs_tree g s root) x z /\
            (z = y \/ scc_back_edge s z y).

(* scc_low_tree: x 的 low-link 可达集 *)
Definition scc_low_tree (s: SCCSt) (x: V): V -> Prop :=
  fun y => scc_low_reachable s x y.

(* low-link 正确性：low[u] = min { dfn[v] | v ∈ scc_low_tree s u } *)
Definition scc_is_low_v (s: SCCSt) (u: V): Prop :=
  (forall v, scc_low_tree s u v -> low s u <= dfn s v) /\
  exists v, scc_low_tree s u v /\ low s u = dfn s v.
```

**直觉**：`scc_low_tree s root u` 是从 `u` 出发，沿 DFS 树向下走任意多步树边，再走**至多一条**回边（到栈中顶点，即 DFS 祖先方向）所到达的所有顶点。`scc_is_low_v` 断言 `low[u]` 恰好等于这些顶点的 dfn 的最小值。

**SCC 根的充要条件**：当 `low[u] = dfn[u]`，意味着从 u 的子树无法通过回边到达任何 dfn 小于 dfn[u] 的顶点——u 就是其 SCC 在 DFS 树中的"最高点"（根）。

### 8.2 可选辅助定义

实现中可选择使用 `min_value_of_subset`（来自 MaxMinLib）定义 `scc_low_valid_v`，并证明 `scc_low_valid_v s root u ↔ scc_is_low_v s root u`。这将"low = min over scc_low_tree"的高层语义与"low = min(own dfn, children's low, back edges' dfn)"的递归计算语义桥接。但核心证明不应依赖此等价性——forset 不变式直接用不等式约束（见 8.3），`scc_is_low_v` 直接从 forset 完成引理和子节点 IH 推出。

### 8.3 Forset 迭代不变式（不等式版本）

**设计决策**：在 forset 逐边迭代期间，**不**追踪 `low[u]` 的精确等式（精确等式在 forset 完成后单独证明），而是维护一个纯不等式约束的不变式。这避免了 `partial_low_tree` 因栈非单调变化（顶点被弹出时从 back-edge 分支消失）而导致的递推断裂。

```coq
(* Forset 迭代不变式：low[u] 是已处理邻居的 dfn 下界 *)
Definition forset_inv (u: V) (done: V -> Prop) (s: SCCSt): Prop :=
  wf_scc_state s /\
  u ∈ visited s /\
  In u (stack s) /\
  low s u <= dfn s u /\
  (forall v, done v -> dg_step g u v ->
    (* 树子节点：low[u] 不超过其 low *)
    (fa s v = u -> low s u <= low s v) /\
    (* 回边目标（在栈中）：low[u] 不超过其 dfn *)
    (In v (stack s) -> low s u <= dfn s v)).
```

**为什么这个不变式是单调的**：
- `low[u]` 只降不升（`update_low` 取 min），所以旧的不等式约束在 `low[u]` 更新后依然成立
- 当 `done` 扩张（加入新邻居 v），只需为 v 建立新的不等式约束
- 当回边目标因被其他 child 的 pop_scc 弹出时，`In v (stack s)` 前提变为 false，对应约束 vacuously true——不需要更新

**为何不需要精确等式**：`update_low` 的 min 语义保证了 `low[u]` 最终等于所有比较过的候选值中的最小值。forset 完成时的精确等号由单独引理证明（见 8.5）。

### 8.4 迭代步骤

对每条边 `u → v`：

**情况 1 — 树边（`v` 未访问）**：
```
set_fa v u;           (* 建立父子关系 *)
W v;                  (* 递归 DFS，由 IH: W v 满足 tarjan_scc_post v *)
lv <- get' low v;     (* 获取 low[v] *)
update_low u lv       (* low[u] := min(low[u], low[v]) *)
```
`W v`（即 `tarjan_scc g v`）执行后，由 Lfix 归纳假设（IH），`tarjan_scc_post v` 保证：
- `wf_scc_state` 保持
- `scc_is_low_v s' v`（low[v] 正确）
- `u` 仍在栈中（由 `stack_dfn_order` + `dfn[u] < dfn[v]`：u 在栈底方向，v 的 pop_scc 只弹栈顶方向）
- `done` 中顶点的相关性质不变（由 `settled_closed` + dfn 不等式）

之后 `update_low u (low v)` 将 `low[u]` 与 `low[v]` 比较并取 min。由于 IH 保证 `low[v] = min_{w ∈ scc_low_tree v} dfn[w]`，此步正确地将 v 子树的贡献纳入了 `low[u]` 的上界。

**情况 2 — 回边（`v` 已访问且在栈中）**：
```
dv <- get' dfn v;     (* 获取 dfn[v] *)
update_low u dv       (* low[u] := min(low[u], dfn[v]) *)
```
`update_low u (dfn v)` 将回边目标 dfn 纳入 `low[u]` 的不等式上界。

**情况 3 — 交叉边（`v` 已访问且不在栈中）**：`skip`——`v` 属于已弹出的 SCC（由 `settled_closed`，其所有前向可达顶点已访问），与当前 SCC 无关。

**祖先保持（关键跨层论证）**：树边分支中 `W v` 不破坏 `u` 的 `forset_inv`，因为：
1. `dfn[u] < dfn[v]`（树边 dfn 单调性）
2. `stack_dfn_order` 保证 u 在 v 下方（栈底方向）
3. `W v` 内的 `pop_scc` 只可能弹出 dfn ≥ dfn[v] 的顶点（栈顶方向），不会触及 u
4. `settled_closed` 保证 `W v` 不会引入"从已沉降 SCC 到未访问顶点"的边

### 8.5 Forset 完成后的等号引理

当 `forset` 遍历完 `u` 的所有出边邻居后，`done = dg_step g u`。此时需从不等式不变式 `forset_inv` 推出精确等号 `scc_is_low_v s u`。分两步：

**步骤 A — 下界（low[u] 不小于 scc_low_tree 中所有 dfn）**：

引理 `forset_complete_lower_bound`：
```coq
Lemma forset_complete_lower_bound (u: V) (s: SCCSt):
  wf_scc_state s ->
  (forall v, dg_step g u v ->
    (fa s v = u -> low s u <= low s v) /\
    (In v (stack s) -> low s u <= dfn s v)) ->
  low s u <= dfn s u ->
  (forall w, scc_low_tree s u w -> low s u <= dfn s w).
```
证明：对 `scc_low_tree s u w` 的推导做归纳——w 要么是 u 自身（trivial），要么通过树子节点可达（由 child low 不等式 + IH(child) 传递），要么是回边目标（直接由不等式）。

**步骤 B — 上界（low[u] 等于某个 dfn，即最小值被达到）**：

引理 `low_u_equals_some_candidate`：
```coq
Lemma low_u_equals_some_candidate (u: V) (s: SCCSt):
  wf_scc_state s -> u ∈ visited s ->
  low s u = dfn s u \/
  (exists v, dg_step g u v /\ fa s v = u /\ low s u = low s v) \/
  (exists v, dg_step g u v /\ In v (stack s) /\ low s u = dfn s v).
```
证明：追踪 `low[u]` 的更新历史——初始值为 `dfn[u]`（preloop 设置），每次 `update_low` 将其替换为当前值与新候选值的 min。经过有限次更新后，`low[u]` 恰好等于某个候选值。

**步骤 C — 组合**：

引理 `forset_end_implies_scc_low_valid_v`：
```coq
Lemma forset_end_implies_scc_low_valid_v (u: V) (s: SCCSt):
  wf_scc_state s ->
  (forall v, dg_step g u v ->
    (fa s v = u -> scc_is_low_v s v /\ low s u <= low s v) /\
    (In v (stack s) -> low s u <= dfn s v)) ->
  low s u <= dfn s u ->
  scc_is_low_v s u.
```
证明：由步骤 A 得下界（`∀w ∈ scc_low_tree, low[u] ≤ dfn[w]`）。由步骤 B 得 `low[u]` 等于某个候选值 c。若 c = dfn[u]，则 u ∈ scc_low_tree s u 满足等号。若 c = low[v]（child），由 child 的 `scc_is_low_v s v` 得 `low[v] = dfn[w]` 对某 w ∈ scc_low_tree s v，而 scc_low_tree s v ⊆ scc_low_tree s u（树传递），故 w ∈ scc_low_tree s u。若 c = dfn[v]（回边），则 v ∈ scc_low_tree s u（回边支）。综上，存在 w ∈ scc_low_tree s u 使 `low[u] = dfn[w]`。

### 8.6 `tarjan_scc` 的复合后置条件

参照 Kosaraju 的 `Q_phase1` 模式（11 个合取项，显式区分 old/new），为 `tarjan_scc u` 定义复合后置条件。关键设计：**显式区分旧顶点（保持性质）和新顶点（建立性质）**。

```coq
Definition tarjan_scc_post (u: V) (s0 s': SCCSt) (root: V): Prop :=
  (* === 旧顶点（在 s0 中已访问）的保持性质 === *)
  (* O1. 基本单调性 *)
  visited_mono s0 s' /\
  dfn_persist s0 s' /\
  fa_persist s0 s' /\
  timer_mono s0 s' /\
  (* O2. 全局不变式保持 *)
  wf_scc_state s' /\
  stack_dfn_order s' /\
  dfn_injective s' /\
  (* O3. 旧顶点的 scc_is_low_v 保持 *)
  (forall v, v ∈ visited s0 -> scc_is_low_v s0 v -> scc_is_low_v s' v) /\
  (* O4. 旧顶点的 low 值不增 *)
  (forall v, v ∈ visited s0 -> low s' v <= low s0 v) /\

  (* === 新顶点（在 s' 中新访问）的建立性质 === *)
  (* N1. u 自身 *)
  u ∈ visited s' /\
  scc_is_low_v s' u /\
  (* N2. 新顶点都是 u 的 DFS 树后代 *)
  (forall v, v ∈ visited s' -> ~ v ∈ visited s0 ->
    dg_reachable (state_to_dfs_tree g s' root) u v) /\
  (* N3. 新顶点的 dfn ≥ dfn[u] *)
  (forall v, v ∈ visited s' -> ~ v ∈ visited s0 ->
    dfn s' u <= dfn s' v) /\
  (* N4. 新顶点的 low ≥ low[u]（low[u] 是子树最小 dfn） *)
  (forall v, v ∈ visited s' -> ~ v ∈ visited s0 ->
    low s' u <= low s' v) /\

  (* === 栈状态 === *)
  (* S1. u 在栈中 iff u 的 SCC 未被弹出 *)
  (In u (stack s') <-> low s' u <> dfn s' u) /\
  (* S2. SCC 列表单调 *)
  (forall scc, In scc (sccs s0) -> In scc (sccs s')).
```

**与 Kosaraju `Q_phase1` 的对应**：

| Kosaraju Q_phase1 | Tarjan tarjan_scc_post |
|---|---|
| `visited1 s0' ⊆ visited1 s'` | O1. `visited_mono` |
| `visited1 s' u'` | N1. `u ∈ visited s'` |
| `step_rev v w → visited1 s' w` (new) | (蕴含于 `wf_scc_state`) |
| `reachable_rev u' v` (new) | N2. 新顶点是 u 的树后代 |
| `finish s' u' < timer s'` | (Tarjan 无 finish 概念；对应 `low ≤ dfn` 关系) |
| old finish preserved | O4. old low 不增 |
| `timer s0' <= timer s'` | O1. `timer_mono` |
| `finish v < finish u'` (new, non-root) | N3. `dfn[u] ≤ dfn[v]` |
| `timer s0' <= finish v` (new) | (Tarjan 的 timer 语义不同) |
| `R_non_closed u'` preserved | (由 `settled_closed` 替代) |
| Phase1_Order disjunctive | N1+N4. `scc_is_low_v` 建立 |

### 8.7 核心定理性引理

```coq
(* 单顶点 low-link 正确性 *)
Lemma tarjan_scc_keep_low_valid (u: V) (root: V):
  original_vvalid g u ->
  Hoare (fun s => wf_scc_state s /\ ~ u ∈ visited s)
        (tarjan_scc g u)
        (fun _ s' => exists s0, tarjan_scc_post u s0 s' root).
```

**证明策略**（与 Kosaraju `DFS_finish_phase1` 同模式）：

1. 使用 `Hoare_normal_LFix`（而非 product-type `Hoare_fix`），以 `tarjan_scc_post` 为 Q 做不动点归纳——这避免了现有实现中 "fixpoint bridging" 的结构性 admit

2. 展开 `tarjan_scc_f W u`：
   - **`preloop u`**：从 `wf_scc_state /\ ~u ∈ visited` 出发
     - 分配 `dfn[u] = low[u] = timer`，递增 timer，压栈，标记 visited
     - 结束后：`wf_scc_state` 恢复，`u ∈ visited`，`In u (stack s)`，`low[u] = dfn[u]`
     - `forset_inv u ∅` 成立（done 为空时，forall 约束 vacuously true）

   - **`forset (dg_step g u) (process_edge u W)`**：核心迭代
     - 使用 `Hoare_forset` 配合不变式 `P(done) := forset_inv u done`
     - **树边分支**：
       ```
       set_fa v u;              (* 建立 fa[v]=u；保持 wf_scc_state_pre v *)
       W v;                     (* IH: tarjan_scc_post v，含 scc_is_low_v s' v *)
       lv <- get' low v;       (* 获取 low[v] *)
       update_low u lv          (* low[u] := min(low[u], low[v]) *)
       ```
       关键：`W v` 的 IH 保证 `low[v] = min_{w ∈ scc_low_tree v} dfn[w]` 且 `dfn[u] < dfn[v]`。
       `stack_dfn_order` + dfn 不等式保证 u 在 `W v` 期间不会被弹出。`settled_closed` 保证
       `W v` 不会引入从已沉降 SCC 到未访问顶点的边。

     - **回边分支**：`update_low u (dfn v)`，直接更新不等式上界

     - **Properness**：`forset_inv` 对 `done` 的集合等价是 Proper 的（仅含 `done v` 前提的 forall 和 implication）

   - **完成 forset 后**：`done = dg_step g u`，由引理 `forset_end_implies_scc_low_valid_v` 得 `scc_is_low_v s u`

   - **`If low[u] = dfn[u] then pop_scc u`**：
     - 若 `low[u] = dfn[u]`：`pop_scc u` 弹出 u 的 SCC。`wf_scc_state` 保持（`pop_scc_preserves_wf_scc_state`）。u 离开栈（`In u (stack s')` 变为 false），满足 S1。
     - 若 `low[u] ≠ dfn[u]`：skip。u 保留在栈中（由定义 `low ≠ dfn` 蕴含仍有机会被更大 SCC 包含）。

3. 最终 `tarjan_scc_post u s0 s' root` 全部 16 个合取项由上述步骤的组合建立

---

## 9. Layer 4 — Low-link 全局正确性

### 9.1 跨子树保持

`tarjan_scc g a` 执行后，不仅 `a` 自身获得 `scc_is_low_v`，还需保证**已访问顶点的 scc_is_low_v 不被破坏**。

关键引理——祖先不变式保持：

```coq
(* tarjan_scc g v 保持祖先 u 的 forset_low_inv *)
Lemma tarjan_scc_preserves_ancestor_low_inv (u v: V) (done: V -> Prop):
  dg_step g u v ->                                        (* v 是 u 的邻居 *)
  ~ v ∈ visited s ->                                      (* v 尚未访问 *)
  Hoare (fun s => forset_low_inv u done s /\
                  In u (stack s) /\
                  (forall w, done w -> In w (stack s) -> dfn s w < dfn s u))
        (tarjan_scc g v)
        (fun _ s => forset_low_inv u done s /\
                    In u (stack s) /\
                    (forall w, done w -> In w (stack s) -> dfn s w < dfn s u)).
```

**核心论证**：`tarjan_scc g v` 内部的 `pop_scc` 仅弹出 dfn ≥ dfn[v] 的顶点（它们位于栈顶方向）。由于 `dfn[u] < dfn[v]`（树边 dfn 单调性）且 `done` 中顶点的 dfn < dfn[u]（由前提），它们都在栈底方向，不会被弹出。

### 9.2 全局建立

```coq
(* 全局 low-link 正确性 *)
Theorem tarjan_scc_all_scc_is_low:
  Hoare (fun s => wf_scc_state s)
        (tarjan_scc_all g)
        (fun _ s => forall v, original_vvalid g v -> scc_is_low_v s v).
```

**证明策略**：
1. `tarjan_scc_all` = `forset` over all original vertices
2. 使用 `Hoare_forset` 配合不变式：
   ```
   P(done) s := (forall v, original_vvalid g v -> done v -> scc_is_low_v s v) /\
               wf_scc_state s
   ```
3. 对每个顶点 `a`：
   - 若 `a ∈ visited`：skip，`P` 不变
   - 若 `a ∉ visited`：由 `tarjan_scc_keep_low_valid` 得到 `scc_is_low_v s a`；由祖先保持引理，`done` 中已有顶点的 `scc_is_low_v` 不被破坏
4. 循环结束后 `done = original_vvalid g`，故所有原图顶点满足 `scc_is_low_v`

---

## 10. Layer 5 — SCC 划分正确性（最终定理）

这是验证的最终目标——证明 Tarjan 算法输出的 `sccs` 构成合法的 SCC 划分。

### 10.1 回边链到根引理

这是整个验证中最精巧的引理之一：证明当 `low[u] = dfn[u]` 时，栈上 u 及以上的每个顶点都能通过有向路径回到 u。

```coq
Lemma back_edge_chain_to_root (u x: V) (s: SCCSt) (root: V):
  wf_scc_state s ->
  scc_is_low_v s u ->
  scc_is_low_v s x ->
  low s u = dfn s u ->
  In x (stack s) ->
  dg_reachable (state_to_dfs_tree g s root) u x ->
  dg_reachable g x u.
```

**证明**（对 `dfn s x` 做良基归纳）：

1. 若 `dfn s x = dfn s u`，由 `dfn_injective` 得 `x = u`，trivial（零步可达）。

2. 若 `dfn s u < dfn s x`：
   - 由 `scc_is_low_v s x`，存在 `w ∈ scc_low_tree s x` 使 `low s x = dfn s w`
   - 由 `scc_low_tree` 定义，存在 z 使 `dg_reachable(dfs_tree) x z` 且 (`z = w` 或 `scc_back_edge s z w`)
   - **若 `z = w`**：`dg_reachable(dfs_tree) x w`。若 `w = x` 则 `low s x = dfn s x`，结合 `low s u = dfn s u` 和 dfn 不等式推出矛盾。故 `w ≠ x`，从而 `dfn s w < dfn s x`（树边 dfn 严格递减）。由 `dg_reachable_vvalid` 和树边性质知原图中 `dg_reachable g x w`。
   - **若 `scc_back_edge s z w`**：回边 `dg_step g z w` 给出 `dg_reachable g x z → z → w`，且 `dfn s w < dfn s z ≤ dfn s x`（回边指向 dfn 更小的栈中顶点）。
   - 两种情况均有 `dfn s w < dfn s x`
   - 现在需要 `scc_is_low_v s w`：若 `w = u`，由前提得；若 `w ≠ u`，w 在栈中（由 `scc_back_edge` 或树边性质）且 `dfn[w] ≥ dfn[u]`（否则 `low[u]` 不是最小），且 w 已访问，由 `tarjan_scc_post` 的 O3 保持性质知 `scc_is_low_v s w`
   - 还需 `dg_reachable(dfs_tree) u w`：由 `dg_reachable(dfs_tree) u x`（前提）+ `dg_reachable(dfs_tree) x w`（上述推导）+ 树传递性
   - 由归纳假设（`dfn s w < dfn s x`），`dg_reachable g w u`
   - 结合 `dg_reachable g x w`（上述），得 `dg_reachable g x u`

3. 若 `dfn s x < dfn s u`：由 `stack_dfn_order` 和 `In x (stack s)`，x 在 u 下方。但 `dg_reachable(dfs_tree) u x` 表示从 u 沿树边向下可达 x，这要求 `dfn[u] < dfn[x]`（树边 dfn 递增），矛盾。此情况不可能。

### 10.2 `pop_scc` 产生合法 SCC

```coq
Lemma pop_scc_is_SCC (u: V) (s: SCCSt) (root: V):
  wf_scc_state s ->
  scc_is_low_v s u ->
  low s u = dfn s u ->
  In u (stack s) ->
  let '(popped, rest) := stack_split_at (stack s) u in
  is_SCC g (fun v => In v popped).
```

**证明**：

**非空性**：`stack_split_at` 的定义保证 `u ∈ popped`，且 `u ∈ visited s`（由 `wf_scc_state`），故 `original_vvalid g u` 成立（由 `state_to_dfs_tree_vvalid` + `dg_reachable_vvalid`）。

**内部 MR（∀x,y ∈ popped, mutually_reachable g x y）**：
- 由 `stack_split_at_partition`，popped 中顶点恰为栈上从 u 到栈顶的所有顶点
- 由 `stack_dfn_order`，`dfn[u] ≤ dfn[x]` 对所有 x ∈ popped
- 对任意 x ∈ popped：
  - `dg_reachable(dfs_tree) u x`（x 是 u 的树后代，由 DFS 结构和 `dfn[u] ≤ dfn[x]`）
  - 由 `back_edge_chain_to_root`，`dg_reachable g x u`
- 因此对任意 x,y ∈ popped：`dg_reachable g x u` → `dg_reachable(dfs_tree) u y`（树路径） → `dg_reachable g x y`（原图路径拼接）
- 同理 `dg_reachable g y x`
- 故 `mutually_reachable g x y`

**极大性**（∀x ∈ popped, original_vvalid g y, mutually_reachable g x y → y ∈ popped）：
- 设 x ∈ popped，`original_vvalid g y`，`mutually_reachable g x y`
- 反设 `y ∉ popped`
- 由 `stack_split_at_partition`，y 要么在 `rest` 中（栈上 u 下方），要么已不在栈上
- **若 y 在 rest 中**：`dfn[y] < dfn[u]`（stack_dfn_order，y 在 u 下方）
  由 `mutually_reachable g x y` 得 `dg_reachable g y x`
  由 `settled_closed`（y 在栈中 → 未沉降），不产生矛盾。需进一步论证。
  由 `dg_reachable g y x` 且 `dfn[y] < dfn[u] ≤ dfn[x]`，结合缩点图无环性和 `scc_is_low_v` 的性质，推出 `low[u] < dfn[u]`，与前提冲突。
- **若 y 不在栈上**：y 已被弹出（在之前的 SCC 中）
  由 `settled_closed`，`∀w, dg_reachable g y w → w ∈ visited s`
  由 `mutually_reachable g x y` 得 `dg_reachable g y x`
  故 `x ∈ visited s`（成立）。但 y 不在栈上且与栈中顶点 x 相互可达，这要求 x 也在 y 的 SCC 中——但 y 的 SCC 已被弹出，矛盾（除非 x 和 y 在同一 SCC 中且同时被弹出）。
  更严谨论证：由 `condensation_is_acyclic`，若 x 和 y 在不同 SCC 中，则不能同时有 `dg_reachable g y x` 和（由 `dg_reachable(dfs_tree) u x` 等导出的）`dg_reachable g x y` 经过不同 SCC。实际两者在同一 SCC 中，故 y 应与 x 一起被弹出（在 `pop_scc u` 中）。

### 10.3 最终定理

```coq
Theorem tarjan_scc_correct (root: V):
  original_vvalid g root ->
  Hoare (fun s => s = initSt)
        (tarjan_scc_all g)
        (fun _ s => scc_partition g (sccs s) /\
                    (forall v, original_vvalid g v -> v ∈ visited s)).
```

**证明**：
1. `initSt` 满足 `wf_scc_state`（由各初始值的定义）
2. `tarjan_scc_all` 后，由 Layer 4 的 `tarjan_scc_all_scc_is_low` 得 `∀v, scc_is_low_v s v`
3. 由 Layer 1 的基本不变式，所有原图顶点均被访问
4. 算法执行期间，每次 `pop_scc u`（仅当 `low[u] = dfn[u]` 时调用）弹出一个 SCC（引理 10.2）
5. 不同 `pop_scc` 弹出的顶点集互不相交（弹栈操作物理移除顶点）
6. 覆盖性：每个原图顶点恰在一次 `pop_scc` 中被弹出（DFS 遍历完全性 + `settled_closed`）

---

## 11. 与 Kosaraju 验证架构的对比

| 维度 | Kosaraju | Tarjan |
|------|----------|--------|
| **DFS 趟数** | 2 趟（反向 + 正向） | 1 趟 |
| **关键值** | `finish` (完成时间) | `low` (low-link) |
| **状态字段数** | 6 个 (`timer`, `finish`, `visited1`, `visited2`, `scc_id`, `scc_next`) | 7 个 (`visited`, `timer`, `fa`, `dfn`, `low`, `stack`, `sccs`) |
| **递归结构** | `DFS_finish` + `DFS_scc`（两个独立的 Lfix） | `tarjan_scc`（单个 Lfix） |
| **迭代方式** | `repeat_break`（重复取边直到所有边处理完） | `forset`（遍历出边邻居集） |
| **核心不变式** | `Phase1_Order`（finish 排序）+ `ForwardReachClosed` + `R` | `scc_is_low_v`（low-link 正确性）+ `stack_dfn_order` |
| **Phase 1 证明模式** | 11 合取 `Q_phase1` + 析取 P_loop | 单复合后置条件 + forset 迭代不变式 |
| **外层循环** | `Hoare_normal_LFix_closed` with Inv | `Hoare_forset` with P(done) |
| **SCC 根识别** | 取最大 finish 的未访问顶点作新根 | `low[u] = dfn[u]` 自动识别 |
| **最终定理** | `scc_id u = scc_id v ↔ mutually_reachable u v` | `scc_partition g (sccs s)` |

### 关键差异

1. **Kosaraju 的两趟结构**使得每趟的不变式相对独立；Tarjan 的单趟结构要求 low-link 不变式和栈不变式紧密耦合。

2. **Tarjan 的额外复杂度**在于 `stack`——必须精确刻画栈上顶点的 dfn 顺序和哪些操作会弹出哪些顶点，这增加了约 30% 的辅助引理。

3. **两种算法共享** SCC 图论基础设施（`mutually_reachable`、`is_SCC`、`scc_partition`、`condensation_is_acyclic`）。Kosaraju 使用无向 `step`/`reachable`，Tarjan 使用有向 `dg_step`/`dg_reachable`——但最终定理中都归结为 `mutually_reachable` 和 `scc_partition`。

---

## 12. 文件组织

```
SeparationLogic/algorithms/Tarjan_directed/
├── SCC_basic.v            (* Layer 0: 有向图 SCC 图论基础设施 *)
├── Tarjan_scc.v           (* 程序定义 + 单调性 + DFS 树构造 *)
├── Tarjan_scc_basics.v    (* Layer 1: 基本单调不变式 *)
├── Tarjan_scc_is_dfn.v    (* Layer 2: dfn 不变式 *)
├── Tarjan_scc_is_low.v    (* Layer 3+4: low-link 正确性 *)
└── Tarjan_scc_correct.v   (* Layer 5: SCC 划分正确性（最终定理）*)
```

**依赖关系**：
```
SCC_basic
  ↓
Tarjan_scc
  ↓
Tarjan_scc_basics
  ↓
Tarjan_scc_is_dfn
  ↓
Tarjan_scc_is_low
  ↓
Tarjan_scc_correct
```

---

## 13. 总结

Tarjan SCC 算法的形式化验证遵循与 Kosaraju 相同的分层架构，但由于其单趟 DFS 的特性，核心复杂度集中在 **low-link 正确性**（Layer 3+4）。关键设计决策包括：

1. **`wf_scc_state` 打包全局不变式**——简化高层证明中的前提传递
2. **`scc_low_tree` 刻画 low-link 语义**——连接递归计算（children's low + back edges' dfn）与图论语义（tree edges + one back edge reachable set）
3. **`forset_low_inv` 作为迭代不变式**——精确刻画 `low[u]` 在逐边处理中的逐步更新
4. **`stack_dfn_order` 作为关键辅助不变式**——保证祖先顶点在子树 DFS 期间不被弹出
5. **`tarjan_scc_post` 复合后置条件**——参照 Kosaraju `Q_phase1` 模式，将单次 `tarjan_scc u` 的所有效果打包为一个可组合的后置条件

最终定理 `tarjan_scc_correct` 将从 low-link 正确性和缩点图 DAG 性质推出输出的 `sccs` 构成合法的 SCC 划分。
