# Tarjan_scc — Monadic Tarjan SCC 程序定义与定理参考

**Author**: Vitalrubbish
**Date**: 2026-06-15

本文档整理 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc.v` 中的所有定义、引理与定理，供后续开发参考。

---

## Context 与依赖

整个文件位于 `Section TarjanSCC` 下，共享以下 Context：

```coq
Context {V E: Type}
        `{EqDec V eq}
        (g: OriginalGraphType V E)
        `{OriginalGraph_gvalid g}.
```

依赖的库：

| Import | 用途 |
|--------|------|
| `Coq.Lists.List` | `In`、列表操作 |
| `Coq.Classes.Morphisms` | 态射类型类 |
| `Coq.Logic.Classical_Prop` | `classic` 排中律 |
| `Coq.Classes.EquivDec` | `equiv_decb` 可判定等价 |
| `Coq.Relations.Relations` | `clos_refl_trans`、`rt_refl` 等关系运算 |
| `SetsClass.SetsClass` | 集合记法 (`SetsNotation`) |
| `MonadLib.StateRelMonad` | `StateRelBasic`、`StateRelHoare`、`FixpointLib` — 状态关系单子基础设施 |
| `RecordUpdate` | `settable!` 宏、Record update 语法 `<| field ::= f |>` |
| `GraphLib.graph_basic` | `OriginalGraphType`、`OriginalGraphProp` |
| `GraphLib.Syntax` | `MonadNotation` 单子记法 |
| `GraphLib.examples.tarjan` | `dg_step`、有向图相关导出 |
| `Algorithms.Tarjan_directed.SCC_basic` | SCC 数学规格 (`is_SCC`、`scc_partition` 等) |

---

## 1. State Record — `SCCSt`

### 定义

```coq
Record SCCSt: Type := mkSCCSt {
  visited : V -> Prop;
  timer   : nat;
  fa      : V -> V;
  dfn     : V -> nat;
  low     : V -> nat;
  stack   : list V;
  sccs    : list (V -> Prop);
}.
```

**语义**：Tarjan SCC 算法的完整状态记录，包含七个字段：

| 字段 | 类型 | 含义 |
|------|------|------|
| `visited` | `V -> Prop` | 已访问顶点集 |
| `timer` | `nat` | DFS 时间戳计数器 |
| `fa` | `V -> V` | DFS 树中的父节点映射（根节点的父节点为自己） |
| `dfn` | `V -> nat` | 顶点的 DFS 发现时间（Discovery/DFS Number） |
| `low` | `V -> nat` | 顶点的 low-link 值：能通过至多一条回边到达的最小 dfn |
| `stack` | `list V` | Tarjan 算法维护的栈，存储当前 DFS 路径上的顶点 |
| `sccs` | `list (V -> Prop)` | 已发现并弹出的 SCC 列表，每个 SCC 表示为顶点集 |

### Record Update 实例

```coq
Instance: Settable SCCSt := settable! mkSCCSt
  <visited; timer; fa; dfn; low; stack; sccs>.
```

**语义**：通过 `RecordUpdate` 库使 `SCCSt` 支持 `<| field ::= f |>` 语法进行字段级更新。

---

## 2. Initial State — `initSt`

### 定义

```coq
Definition initSt: SCCSt :=
  mkSCCSt (fun _ => False) 0 (fun v => v) (fun _ => 0) (fun _ => 0) nil nil.
```

**语义**：算法初始状态：

| 字段 | 初始值 | 含义 |
|------|--------|------|
| `visited` | `∅` | 无已访问顶点 |
| `timer` | `0` | 时间戳从 0 开始 |
| `fa` | `id` | 每个顶点初始的父节点为自己 |
| `dfn` | `λ_. 0` | 所有顶点 dfn 初始为 0 |
| `low` | `λ_. 0` | 所有顶点 low 初始为 0 |
| `stack` | `[]` | 栈为空 |
| `sccs` | `[]` | 尚未发现任何 SCC |

---

## 3. Helper Function — `stack_split_at`

### 定义

```coq
Fixpoint stack_split_at (stk: list V) (u: V): list V * list V :=
  match stk with
  | nil => (nil, nil)
  | x :: xs =>
      if equiv_decb x u
      then (x :: nil, xs)
      else let (popped, rest) := stack_split_at xs u in
           (x :: popped, rest)
  end.
```

**语义**：递归地将栈 `stk` 在顶点 `u`（包含）处分割为两部分：
- 返回值 `(popped, rest)`：`popped` 是从栈顶到 `u`（含）的所有顶点，`rest` 是剩余部分。
- 当 `u` 不在栈中时返回 `(nil, nil)`（实际使用中保证 `u` 一定在栈中）。

---

## 4. Pure Function — `pop_scc_state`

### 定义

```coq
Definition pop_scc_state (s: SCCSt) (u: V): SCCSt :=
  let '(popped, rest) := stack_split_at (stack s) u in
  s <| stack ::= fun _ => rest |>
    <| sccs ::= fun sccs0 => (fun v => In v popped) :: sccs0 |>.
```

**语义**：纯函数——从状态 `s` 的栈中弹出以 `u` 为栈底的 SCC：
1. 调用 `stack_split_at` 将栈在 `u` 处分隔
2. 更新 `stack` 为 `rest`（移除 `popped` 部分）
3. 将 `popped` 中的顶点集作为新的 SCC 添加到 `sccs` 列表头部

---

## 5. Primitive Operations — 基本单子操作

所有操作类型均为 `program SCCSt unit`，即状态变换单子程序。

### `visit`

```coq
Definition visit (v: V): program SCCSt unit :=
  update' (fun s => s <| visited ::= fun x => x ∪ [v] |>).
```

**语义**：将顶点 `v` 加入 `visited` 集合。

### `set_dfn`

```coq
Definition set_dfn (v: V) (n: nat): program SCCSt unit :=
  update' (fun s => s <| dfn ::= fun dfn0 x =>
    if equiv_decb x v then n else dfn0 x |>).
```

**语义**：将顶点 `v` 的 `dfn` 设置为 `n`，其他顶点保持不变。

### `set_low`

```coq
Definition set_low (v: V) (n: nat): program SCCSt unit :=
  update' (fun s => s <| low ::= fun low0 x =>
    if equiv_decb x v then n else low0 x |>).
```

**语义**：将顶点 `v` 的 `low` 值设置为 `n`。

### `set_fa`

```coq
Definition set_fa (v: V) (p: V): program SCCSt unit :=
  update' (fun s => s <| fa ::= fun fa0 x =>
    if equiv_decb x v then p else fa0 x |>).
```

**语义**：将顶点 `v` 的父节点设置为 `p`。

### `set_fa_state` — 纯函数版本

```coq
Definition set_fa_state (s: SCCSt) (v p: V): SCCSt :=
  s <| fa ::= fun fa0 x => if equiv_decb x v then p else fa0 x |>.
```

**语义**：与 `set_fa` 相同的行为，但作为纯状态函数暴露。用于 `state_to_dfs_tree` 的结构性引理中，描述 `set_fa` 对 DFS 树结构的影响（`set_fa_preserves_tree_edges` 等），不涉及 monadic Hoare 推理。

### `incr_timer`

```coq
Definition incr_timer: program SCCSt unit :=
  update' (fun s => s <| timer ::= fun t => S t |>).
```

**语义**：将 `timer` 计数器加一。

### `push_stack`

```coq
Definition push_stack (v: V): program SCCSt unit :=
  update' (fun s => s <| stack ::= fun stk => v :: stk |>).
```

**语义**：将顶点 `v` 压入栈顶。

### `update_low`

```coq
Definition update_low (u: V) (n: nat): program SCCSt unit :=
  lu <- get' (fun s => low s u);;
  If (fun s => n < low s u) (set_low u n).
```

**语义**：仅当 `n` 严格小于 `u` 的当前 `low` 值时，才将 `low[u]` 更新为 `n`。即取两者中的较小值。

### `pop_scc`

```coq
Definition pop_scc (u: V): program SCCSt unit :=
  update' (fun s => pop_scc_state s u).
```

**语义**：调用 `pop_scc_state` 弹出以 `u` 为栈底的 SCC。

### Ltac: `unfold_op`

```coq
Ltac unfold_op :=
  unfold visit, set_dfn, set_low, set_fa, incr_timer,
         push_stack, update_low, pop_scc.
```

**语义**：战术宏，一次性展开所有基本操作的定义，用于 monotonicity 证明中简化目标。

---

## 6. Main Program — 主程序

### `preloop`

```coq
Definition preloop (u: V): program SCCSt unit :=
  t <- get (fun s t => t = s.(timer));;
  set_dfn u t;;
  set_low u t;;
  incr_timer;;
  push_stack u;;
  visit u.
```

**语义**：DFS 进入顶点 `u` 时的前置处理——标准 Tarjan 算法的 "preorder" 阶段：
1. 读取当前 `timer` 值 `t`
2. 设 `dfn[u] := t`
3. 设 `low[u] := t`（初始 low 等于 dfn）
4. `timer` 加一
5. 将 `u` 压入栈
6. 标记 `u` 为已访问

### `process_edge`

```coq
Definition process_edge (u: V) (W: V -> program SCCSt unit) (v: V): program SCCSt unit :=
  if_else (fun s => ~ v ∈ visited s)
    (* Tree edge: v is unvisited *)
    (set_fa v u;; W v;;
     lv <- get' (fun s => low s v);;
     update_low u lv)
    (* v is already visited — check if it's still in the stack *)
    (If (fun s => In v (stack s))
       (dv <- get' (fun s => dfn s v);;
        update_low u dv)).
```

**语义**：处理从 `u` 到 `v` 的一条有向边。`W` 是当前递归体（即 `tarjan_scc` 自身）。

分两种情况：
- **树边 (Tree edge)**：`v` 未被访问
  1. 设 `fa[v] := u`（建立父子关系）
  2. 递归调用 `W v`（深度优先探索 `v`）
  3. 读取 `low[v]` 并用它更新 `low[u]`（取较小值）
- **非树边 (Non-tree edge)**：`v` 已被访问
  - 若 `v` 仍在栈中（即 `v` 是 `u` 在 DFS 树中的祖先——回边/交叉边且仍在当前 SCC 内）
    1. 读取 `dfn[v]`
    2. 用 `dfn[v]` 更新 `low[u]`

### `tarjan_scc_f`

```coq
Definition tarjan_scc_f (W: V -> program SCCSt unit) (u: V): program SCCSt unit :=
  preloop u;;
  forset (fun v => dg_step g u v) (process_edge u W);;
  If (fun s => low s u = dfn s u) (pop_scc u).
```

**语义**：Tarjan SCC 算法的单步函数体（以 `W` 为递归占位参数）：
1. 执行 `preloop u`——DFS 进入 `u`
2. 对 `u` 的所有出边邻居 `v`（满足 `dg_step g u v`）执行 `process_edge u W v`
3. 若 `low[u] = dfn[u]`（即 `u` 是当前 SCC 的根），则弹出以 `u` 为栈底的 SCC

### `tarjan_scc`

```coq
Definition tarjan_scc (u: V): program SCCSt unit :=
  Lfix tarjan_scc_f u.
```

**语义**：`tarjan_scc_f` 的最小不动点（least fixpoint），即从顶点 `u` 开始的完整 Tarjan SCC 递归 DFS。

---

## 7. DFS Tree Construction — `state_to_dfs_tree`

### 定义

```coq
(** [state_to_dfs_tree s root] constructs the DFS tree from the algorithm
    state [s].  The [root] parameter is the DFS traversal root vertex; it
    is not used in the tree structure itself but is required by the
    [RootedTree] Type Class instance (proved in a separate file) which
    takes [root] as the tree root. *)
Definition state_to_dfs_tree (s: SCCSt) (root: V): OriginalGraphType V E :=
  {|
    original_vvalid   := fun v => v ∈ visited s;
    original_step     := fun e =>
      exists v, v ∈ visited s /\ fa s v <> v /\
                original_step_fst g e = fa s v /\
                original_step_snd g e = v;
    original_step_fst := original_step_fst g;
    original_step_snd := original_step_snd g;
    original_listV    := original_listV g;
  |}.
```

**语义**：从算法状态 `s` 构造 DFS 树图：
- `root` 参数是 DFS 遍历的根顶点，函数体未使用，但为 `RootedTree` Type Class 实例（在 `Tarjan_scc_is_dfn.v` 中证明）保留，以 `root` 作为树根。
- **有效顶点**：所有在 `visited s` 中的顶点
- **边**：从父节点 `fa[v]` 到子节点 `v` 的树边（要求 `fa[v] ≠ v`，即排除根节点自指）
- 边的方向与原始图保持一致

---

## 8. Monotonicity — 单调性引理

本部分证明 `tarjan_scc_f` 是 `mono_cont`（单调且连续），从而保证最小不动点 `Lfix` 的存在性和展开性质。

### 背景：为何需要 `mono_cont`？

Tarjan SCC 算法的递归结构通过 `Lfix`（最小不动点）定义：

```coq
tarjan_scc := Lfix tarjan_scc_f
```

这意味着 `tarjan_scc` 是递归方程 `X = tarjan_scc_f X` 的最小解。然而并非所有函数都有良定义的最小不动点——需要函数满足一定的序理论条件。

在程序语义学中，程序 `program SCCSt unit` 可视为状态变换关系（前置状态 `σ` 到后置状态 `σ'` 的二元关系）。这些关系按包含性 (`⊆`) 构成偏序，且该偏序是完备的（存在任意上确界）。在此结构下：

- **单调性 (`mono`)**：若递归体 `W₁ ⊑ W₂`（`W₂` 的行为包含了 `W₁`），则 `f W₁ ⊑ f W₂`。即"更好的递归体不会使程序变差"。
- **连续性 (`cont`)**：对任意递增链 `W₁ ⊑ W₂ ⊑ …`，`f (supᵢ Wᵢ) = supᵢ f Wᵢ`。即程序对递归体的行为是"连续的"——极限点的行为由所有有限近似决定。
- **`mono_cont`**：单调且连续。这是 Kleene–Knaster–Tarski 不动点理论的标准条件：满足该条件的函数存在最小不动点，且可通过迭代 `∅, f ∅, f² ∅, …` 的链上确界构造。

### 递归参数 `W` 在图上的含义

在解释每个引理之前，必须先理解 **`W : V → program SCCSt unit` 到底是什么**。

从类型签名看，`W` 是一个函数：给定一个顶点 `v`，返回一个在 `SCCSt` 状态上运行的程序。在图论中，`W v` 就是**从顶点 `v` 出发、沿着有向边做 DFS 探索并发现 SCC 的"引擎"**。

关键在于，`tarjan_scc_f` 本身并不直接完成完整的 DFS——它只执行**一层**（当前顶点 `u`），而把更深层的探索委托给参数 `W`：

```
tarjan_scc_f W u =
    preloop u;;                           (* 本层: 标记 u *)
    forset (dg_step g u)                  (* 本层: 遍历 u 的出边 *)
           (process_edge u W);;           (*       遇到树边时，调用 W v 做深一层 DFS *)
    If low[u] = dfn[u] pop_scc u         (* 本层: 判断 / 弹出 SCC *)
```

可见，`W` 是 `tarjan_scc_f` 内部递归调用的**占位符**：`process_edge u W v` 在 `v` 未访问时执行 `W v`，就等价于"递归进入 `v` 继续 DFS"。

那么 `W` 的"好坏"是什么意思？在序理论中，`W` 的类型 `V → program SCCSt unit` 按逐点包含关系 `⊑` 构成偏序：

```
W₁ ⊑ W₂  ≜  ∀v. W₁ v ⊑ W₂ v
```

即对每个顶点 `v`，引擎 `W₂ v` 的行为包含了 `W₁ v` 的行为——它可能访问更多顶点、探索更深的 DFS 子树、发现更多的 SCC。

`Lfix tarjan_scc_f` 的构造过程可以理解为**逐层逼近**：

```
第 0 步: W₀ = ⊥                       (什么都不探索的空引擎)
第 1 步: W₁ = tarjan_scc_f W₀         (只能处理单层——无递归调用)
第 2 步: W₂ = tarjan_scc_f W₁         (能处理两层——递归调用一次 W₁)
第 3 步: W₃ = tarjan_scc_f W₂         (三层)
...
极限:    tarjan_scc = supᵢ Wᵢ         (能处理任意深度的 DFS 树)
```

**图例——考虑一条简单的链 `a → b → c`**：

| 迭代 | `W(a)` 的行为 | `W(b)` 的行为 |
|------|--------------|--------------|
| `W₀` | 无 | 无 |
| `W₁` | 标记 a，遍历 a 的邻居 b——但调用 `W₀ b` 无效果 | 标记 b，遍历 b 的邻居 c——调用 `W₀ c` 无效果 |
| `W₂` | 标记 a，调用 `W₁ b` 可以标记 b，再通过 `W₁ b` 访问 c | 标记 b，调用 `W₁ c` 可以标记 c |
| `W₃` | 与 `W₂` 一致（链深 2，已全覆盖） | 一致 |

最终的不动点 `tarjan_scc` 对任意深度的 DFS 树都能完整处理——从 `a` 出发会发现链上三个顶点同属一个 SCC（根据有向图结构可能不同，此处示意 DFS 探索深度）。

单调性 (`mono`) 保证了每一步逼近不会"退化"——`W₁ ⊑ W₂ ⊑ W₃ ⊑ …` 严格递增（或驻留）；连续 (`cont`) 则保证了极限点的行为恰好是所有有限步行为的并集——不会在极限处突然"冒出"某个只在无限深度才出现的行为。

下面结合这个理解，逐一解释每个引理在图上的意义。

---

### Lemma `process_edge_mono_cont`

```coq
Lemma process_edge_mono_cont (u v: V):
  mono_cont (fun (W: V -> program SCCSt unit) => process_edge u W v).
```

**图上解释**：

`process_edge u W v` 处理从顶点 `u` 到 `v` 的一条有向边 `u→v`。它只在一种情况下使用递归参数 `W`：当 `v` 尚未被访问时（树边情况），它执行 `W v` 从 `v` 开始递归 DFS。

因此 `process_edge u W v` 在 `W` 上的单调性反映了以下直觉：若我们有一个"更强"的 DFS 递归体 `W₂`（即 `W₂` 对每个起始顶点的行为包含了 `W₁` 的行为），那么：
- 对于树边，`W₂ v` 会探索 `v` 的整个可达子图，其结果（访问的顶点、形成的 SCC 等）包含了 `W₁ v` 的结果。进而，`process_edge u W₂ v` 产生的状态（如 `low[u]` 通过 `W₂` 递归后的 `low[v]` 更新）也包含或改进了 `process_edge u W₁ v` 的结果。
- 对于非树边（回边），`W` 根本不被调用——边处理与递归体无关，单调性平凡成立。

**证明思路**：展开 `process_edge` 和 `if_else` 定义后，使用 `mono_cont_auto` 自动化完成。

---

### Lemma `forset_body_mono_cont`

```coq
Lemma forset_body_mono_cont (u: V)
      (W0: (V -> Prop) -> program SCCSt unit) (universe': V -> Prop):
  mono_cont (fun (W: V -> program SCCSt unit) =>
    choice
      (a <- get (fun (_: SCCSt) (a: V) => a ∈ universe');;
       process_edge u W a;;
       W0 (fun x => x ∈ universe' /\ x <> a))
      (assume!! (universe' == ∅);; skip)).
```

**图上解释**：

这是 `forset_f` 的核心——对顶点 `u` 的**邻域进行迭代**的每一步。给定 `u` 的剩余未处理的邻居集合 `universe'`：

1. **非空分支**：从 `universe'` 中**任选**一个邻居 `a`（`get` 读出满足 `a ∈ universe'` 的任意元素），处理边 `u→a`（通过 `process_edge u W a`），然后对**剩余邻居集合** `{x | x ∈ universe' ∧ x ≠ a}` 调用递归体 `W0`。
2. **空分支**：所有邻居已处理完毕，`skip` 终止。

单调性在此的含义是：若 DFS 递归体 `W` 变强了（探索能力增加了），那么处理 `u` 的一条出边 `u→a` 的效果也变强了（由 `process_edge_mono_cont` 保证），进而**整个邻域迭代**的结果也变强了——`u` 可能访问更多顶点、发现更多 SCC、更新更准确的 low-link 值。

**证明思路**：由 `mono_cont_choice` 处理两分支的单调性，非空分支由 `mono_cont_bind` 串接；其中 `process_edge` 的单调性来自上一条引理，`W0` 部分为常量。

---

### Lemma `mono_cont_apply`

```coq
Lemma mono_cont_apply (s: V -> Prop):
  mono_cont (fun (W: (V -> Prop) -> program SCCSt unit) => W s).
```

**图上解释**：

这个引理看似平凡但其作用关键：它允许 `forset_f` 将**自身递归调用**视为 `W` 上的单调连续函数。在 `forset_f` 的定义中，递归调用 `W (fun x => x ∈ universe' /\ x <> a)` 是对递归参数 `W` 的实例化——用"剩余邻居集合"替代了原始的全邻域集合。

从图论角度看：`forset_f` 在遍历 `u` 的邻居时，每处理一条边就缩小剩余的邻居集合。递归调用 `W s`（其中 `s` 是缩小后的邻居集）必须对这种缩小保持单调性——即若外层的 `W` 对**所有可能的集合参数**都变强了，那它对**特定集合 `s`** 的行为自然也跟着变强。

**证明思路**：`mono` 部分直接由偏序定义展开；`cont` 部分由集合上确界的逐点性质得证。

---

### Lemma `forset_f_mono_cont_body`

```coq
Lemma forset_f_mono_cont_body (body: V -> program SCCSt unit):
  mono_cont (forset_f body).
```

**图上解释**：

当 `process_edge u W v` 中的 `W` 被特化为一个**固定的**递归体 `body`（不依赖外部参数）时，`forset_f body` 变成了一个标准的迭代程序：对于给定的顶点 `u` 和其邻居集合，逐一遍历所有邻居 `v` 并执行 `body v`。

在图论上，这意味着**DFS 树中的逐邻域处理本身就是单调连续的**：`forset_f` 接收一个参数 `W0 : (V -> Prop) -> program SCCSt unit` 代表"剩余邻居的处理"，以及一个参数 `universe` 代表"待处理的邻居集合"。如果 `W0` 更强（能更好地处理剩余的邻居集合），那么整个 `forset_f` 的结果也更强。这保证了 `forset_f` 自身的递归结构是良定义的。

这个引理是最终 `tarjan_scc_f_mono_cont` 证明中的关键环节——它保证了对**每个顶点**的邻域迭代的最小不动点 `Lfix (forset_f body)` 是良定义的。

**证明思路**：使用 `mono_cont_intro` 引入内部参数 `W0`，然后 `mono_cont_choice` + `mono_cont_bind` 串接，其中递归调用的单调性由 `mono_cont_apply` 处理。

---

### Lemma `tarjan_scc_f_mono_cont`

```coq
Lemma tarjan_scc_f_mono_cont: mono_cont tarjan_scc_f.
```

**图上解释**：

这是整个单调性证明的**终极目标**。`tarjan_scc_f` 是 Tarjan 算法的单步函数体（以 `W` 为递归参数）：

```
tarjan_scc_f W u =
  preloop u;;                    (* 步骤 1: DFS 进入标记 *)
  forset (dg_step g u)           (* 步骤 2: 遍历 u 的所有出边邻居 *)
         (process_edge u W);;    (* 对每条边，用 W 递归处理 *)
  If low[u] = dfn[u]             (* 步骤 3: 判断是否为 SCC 根 *)
    pop_scc u
```

在图论中，该引理断言：**整个 Tarjan 单步的语义在递归体 `W` 上是单调连续的**。具体而言：

1. **`preloop`**：写入 `dfn[u]`、`low[u]`，压栈，标记 visited——这些操作与 `W` 无关，是常量的。
2. **邻域迭代**：`forset (dg_step g u) (process_edge u W)` 对 `u` 的出边集 `{v | u→v}` 迭代执行 `process_edge u W`。`process_edge u W` 在 `W` 上是 `mono_cont`，而 `forset`（即 `Lfix (forset_f …)`）由 `mono_cont_Lfix` + `forset_f_mono_cont_body` + `forset_body_mono_cont` 保证也应是 `mono_cont`。
3. **`pop_scc`**：条件判断与弹出操作——与 `W` 无关，常量的。

这三部分通过单子 `bind` 串接，由于每个阶段在 `W` 上都是 `mono_cont`，整个流水线也是 `mono_cont`。

**图论意义**：这意味着 Tarjan 算法从顶点的递归 DFS 在实际执行中的行为是最小不动点给出的——即算法执行的是"最少必需"的探索：只访问从给定顶点可达的那些顶点，只发现那些确实存在的 SCC。不会有"幽灵探索"或"多余 SCC"。

**证明结构**：
1. 使用 `mono_cont_intro` 处理参数 `u`
2. `preloop` 后 `bind` 两个阶段
3. 内层 `forset` 使用 `mono_cont_Lfix` 结合 `forset_f_mono_cont_body` 和 `forset_body_mono_cont` 证明——前者处理 `body` 固定时的 `forset_f`，后者处理 `body`（即 `process_edge u W`）依赖 `W` 时的逐步单调性
4. 最后的 `If ... pop_scc` 是常量

---

### Lemma `tarjan_scc_unfold`

```coq
Lemma tarjan_scc_unfold (u: V):
  tarjan_scc u == tarjan_scc_f tarjan_scc u.
```

**图上解释**：

这是 `tarjan_scc_f_mono_cont` 的**直接推论**：由于 `tarjan_scc_f` 满足 `mono_cont`，Kleene–Knaster–Tarski 不动点定理保证最小不动点 `tarjan_scc = Lfix tarjan_scc_f` 确实是不动点，即：

```
tarjan_scc u == tarjan_scc_f tarjan_scc u
```

展开右侧，得到 Tarjan 算法的**递归展开形式**：

```
tarjan_scc u ==
  preloop u;;
  forset (dg_step g u) (process_edge u tarjan_scc);;
  If low[u] = dfn[u] then pop_scc u
```

在图论上，这意味着：**从顶点 `u` 开始执行 Tarjan 算法**，等价于：
1. 标记 `u` 的 DFS 序（`dfn`、`low`、入栈、visited）
2. 对 `u` 的**每条**出边 `u→v`：
   - 若 `v` 未被访问：递归执行 `tarjan_scc v`（形成 DFS 树的子树），然后用 `low[v]` 更新 `low[u]`
   - 若 `v` 已被访问且在栈中：用 `dfn[v]` 更新 `low[u]`（回边/交叉边）
3. 若 `low[u] = dfn[u]`（`u` 是当前 SCC 在 DFS 树中的根），弹出以 `u` 为栈底的 SCC。

这个展开引理是后续**正确性证明**的基础——它允许我们在证明中将递归调用替换为它的定义展开，从而对 DFS 树的结构做归纳论证。

---

## 9. DFS Tree — Structural Lemmas

本部分包含 `state_to_dfs_tree` 的 6 个结构性引理，描述 DFS 树的顶点集、边集基本性质。这些引理是后续四个证明文件（`Tarjan_scc_is_dfn.v`、`Tarjan_scc_is_low.v`、`Tarjan_scc_stack.v`、`SCC_correctness.v`）的共同前置依赖。

### 分层原则

| 放在 `Tarjan_scc.v` | 不放在 `Tarjan_scc.v` |
|---------------------|----------------------|
| 结构性的、仅依赖 `state_to_dfs_tree` 定义的引理 | 依赖算法不变量（`dfn_inv`、`is_low` 等）的引理 |
| `set_fa` 对树结构的纯函数影响 | `dfn_valid` 实例（需 `timer`/`visited` 关系） |
| 树的顶点集、边集基本刻画 | `RootedTree` Type Class 实例（~200 行，在 `Tarjan_scc_is_dfn.v` 中证明） |
| 无自环等简单图性质 | `subtree_segment` / `no_cross_edge` / `dfn_unique` |

### 设计决策：`dg_step` 的反向刻画与边存在条件

`state_to_dfs_tree` 构造的 DFS 树图的 `original_step` 定义为：

```coq
original_step (state_to_dfs_tree s root) e :=
  exists v, v ∈ visited s /\ fa s v <> v /\
            original_step_fst g e = fa s v /\
            original_step_snd g e = v
```

`dg_step` 要求提供一条边 `e : E` 作为存在证据。当需要证明 `dg_step (state_to_dfs_tree ...) x y` 时，必须构造一个 `e` 使得 `original_step_fst g e = x` 且 `original_step_snd g e = y`。由于类型 `E` 是任意的（无构造子保证），这个存在性无法从 `fa s y = x` 等纯状态条件推出。

在算法实际运行时，`fa s y = x` 仅在 `process_edge` 的树边分支中被 `set_fa y x` 设置，而该分支受 `dg_step g x y` 守卫——因此 `fa s y = x` 总是伴随 `dg_step g x y` 出现，后者恰好提供了所需的边 `e`。因此，含 `dg_step g` 前提的引理在实际使用中总是可实例化的。

### Lemma `state_to_dfs_tree_vvalid`

```coq
Lemma state_to_dfs_tree_vvalid (s: SCCSt) (root v: V):
  original_vvalid (state_to_dfs_tree s root) v <-> v ∈ visited s.
```

**用途**：将树的顶点有效性与算法状态的 `visited` 集关联。后续所有涉及 `vvalid dfs_tree v` 的前提都可展开为 `v ∈ visited s`。

**证明**：直接展开 `state_to_dfs_tree` 和 `original_vvalid`，`reflexivity`。

### Lemma `state_to_dfs_tree_step_char` (→ 方向)

```coq
Lemma state_to_dfs_tree_step_char (s: SCCSt) (root x y: V):
  dg_step (state_to_dfs_tree s root) x y ->
  fa s y = x /\ fa s y <> y /\ y ∈ visited s.
```

**用途**：从 DFS 树中存在边 `x → y` 推出状态中的 `fa` 和 `visited` 条件。这是正向推理的核心引理。

**证明**：展开 `dg_step` 和 `original_step`，提取内部 `exists v` 的证据，通过 `step_fst`/`step_snd` 的等式重写统一 `v` 与 `y`。

### Lemma `state_to_dfs_tree_step_char_backward` (← 方向，带边条件)

```coq
Lemma state_to_dfs_tree_step_char_backward (s: SCCSt) (root x y: V):
  dg_step g x y ->
  fa s y = x -> fa s y <> y -> y ∈ visited s ->
  dg_step (state_to_dfs_tree s root) x y.
```

**用途**：反向构造 DFS 树中的边。`dg_step g x y` 前提提供原始图中的边 `e`，该边恰好满足树边条件。在算法运行时，该条件由 `process_edge` 树边分支中的 `dg_step g u v` 守卫提供。

### Lemma `state_to_dfs_tree_step_fa`

```coq
Lemma state_to_dfs_tree_step_fa (s: SCCSt) (root v: V):
  dg_step g (fa s v) v ->
  v ∈ visited s -> fa s v <> v ->
  dg_step (state_to_dfs_tree s root) (fa s v) v.
```

**用途**：最常用的正向推理引理——若顶点已访问且 `fa` 被赋值（且存在对应的原始图边），则在 DFS 树中存在父节点到该顶点的有向边。

### Lemma `state_to_dfs_tree_dg_reachable_refl`

```coq
Lemma state_to_dfs_tree_dg_reachable_refl (s: SCCSt) (root v: V):
  v ∈ visited s ->
  dg_reachable (state_to_dfs_tree s root) v v.
```

**用途**：树中每个已访问顶点自反可达。`dg_reachable` 是 `clos_refl_trans dg_step` 的包装，自反性直接由 `rt_refl` 得到。

### Lemma `state_to_dfs_tree_root_visited`

```coq
Lemma state_to_dfs_tree_root_visited (s: SCCSt) (root: V):
  root ∈ visited s ->
  original_vvalid (state_to_dfs_tree s root) root.
```

**用途**：便捷引理——若 root 已访问，则 root 在树中有效。由 `state_to_dfs_tree_vvalid` 直接得到。

### Lemma `state_to_dfs_tree_no_self_loop`

```coq
Lemma state_to_dfs_tree_no_self_loop (s: SCCSt) (root v: V):
  ~ dg_step (state_to_dfs_tree s root) v v.
```

**用途**：树中无自环——`fa s v ≠ v` 条件排除了 `dg_step` 的自环可能。由 `state_to_dfs_tree_step_char` 推出矛盾。

---

## 10. DFS Tree — set_fa Preservation Lemmas

以下 3 个引理描述 `set_fa_state v p`（纯函数版本的 `set_fa`）操作对 DFS 树结构的影响。

### Lemma `set_fa_preserves_tree_vvalid`

```coq
Lemma set_fa_preserves_tree_vvalid (s: SCCSt) (root v p: V):
  original_vvalid (state_to_dfs_tree s root) v ->
  original_vvalid (state_to_dfs_tree (set_fa_state s v p) root) v.
```

**用途**：`set_fa` 不修改 `visited`，故不减少树的顶点集。由直接展开得证。

### Lemma `set_fa_preserves_tree_edges`

```coq
Lemma set_fa_preserves_tree_edges (s: SCCSt) (root v x w p: V):
  w <> v ->
  dg_step (state_to_dfs_tree s root) x w ->
  dg_step (state_to_dfs_tree (set_fa_state s v p) root) x w.
```

**用途**：对 `w ≠ v`，已有的树边 `x → w` 不受 `set_fa v p` 影响。证明复用原始树 `dg_step` 中的边证据 `e`，因为 `w ≠ v` 时 `fa s' w = fa s w`。此引理**不需要** `dg_step g` 条件——边证据直接来自已有树边。

### Lemma `set_fa_adds_tree_edge`

```coq
Lemma set_fa_adds_tree_edge (s: SCCSt) (root v p: V):
  dg_step g p v ->
  p <> v -> v ∈ visited s ->
  dg_step (state_to_dfs_tree (set_fa_state s v p) root) p v.
```

**用途**：`set_fa v p`（`p ≠ v`，`v` 已访问）在树中新增一条有向边 `p → v`。`dg_step g p v` 前提提供边证据；`v ∈ visited s` 反映算法中 `visit v`（递归 `tarjan_scc v` 内部）之后的实际状态。

---

## 11. Outer Loop — `tarjan_scc_all`

### 定义

```coq
Definition tarjan_scc_all: program SCCSt unit :=
  forset (fun v => original_vvalid g v)
         (fun v => If (fun s => ~ v ∈ visited s) (tarjan_scc v)).
```

**语义**：对图中所有有效顶点（`original_vvalid g v`）迭代：
- 若顶点 `v` 尚未被访问，则从 `v` 启动 Tarjan SCC DFS
- 已访问的顶点跳过（它们已在之前的 DFS 中处理）

这是完整的 Tarjan SCC 算法入口——保证覆盖图中所有顶点。

---

## 定义与定理清单

### 定义 (Definitions/Fixpoints)

| 名称 | 类型 | 行号 | 摘要 |
|------|------|------|------|
| `SCCSt` | `Record` | 28 | 算法状态记录，含 7 个字段 |
| `initSt` | `SCCSt` | 45 | 算法初始状态 |
| `stack_split_at` | `list V → V → list V * list V` | 52 | 在顶点 `u` 处分割栈 |
| `pop_scc_state` | `SCCSt → V → SCCSt` | 66 | 纯函数：弹出以 `u` 为栈底的 SCC |
| `visit` | `V → program SCCSt unit` | 75 | 标记已访问 |
| `set_dfn` | `V → nat → program SCCSt unit` | 78 | 设置 dfn 值 |
| `set_low` | `V → nat → program SCCSt unit` | 81 | 设置 low 值 |
| `set_fa` | `V → V → program SCCSt unit` | 84 | 设置父节点 |
| `incr_timer` | `program SCCSt unit` | 87 | timer 自增 |
| `push_stack` | `V → program SCCSt unit` | 90 | 压栈 |
| `update_low` | `V → nat → program SCCSt unit` | 93 | 条件更新 low（取较小值） |
| `pop_scc` | `V → program SCCSt unit` | 97 | 弹出 SCC |
| `preloop` | `V → program SCCSt unit` | 108 | DFS 进入预处理 |
| `process_edge` | `V → (V → program SCCSt unit) → V → program SCCSt unit` | 116 | 处理单条有向边 |
| `tarjan_scc_f` | `(V → program SCCSt unit) → V → program SCCSt unit` | 127 | Tarjan 单步函数体 |
| `tarjan_scc` | `V → program SCCSt unit` | 132 | 最小不动点递归 |
| `set_fa_state` | `SCCSt → V → V → SCCSt` | — | `set_fa` 的纯函数版本 |
| `state_to_dfs_tree` | `SCCSt → V → OriginalGraphType V E` | — | 从状态构造 DFS 树 |
| `tarjan_scc_all` | `program SCCSt unit` | — | 外层循环：覆盖全图 |

### 引理与定理 (Lemmas)

| 名称 | 摘要 |
|------|------|
| `process_edge_mono_cont` | `process_edge` 在 `W` 参数上单调连续 |
| `forset_body_mono_cont` | `forset_f` 循环体在 `W` 上单调连续 |
| `mono_cont_apply` | 函数应用 `W s` 对固定 `s` 单调连续 |
| `forset_f_mono_cont_body` | 常量 `body` 下 `forset_f` 单调连续 |
| `tarjan_scc_f_mono_cont` | `tarjan_scc_f` 单调连续（核心） |
| `tarjan_scc_unfold` | 不动点展开：`tarjan_scc u == tarjan_scc_f tarjan_scc u` |
| `state_to_dfs_tree_vvalid` | 树的顶点有效性与 `visited` 集等价 (`iff`) |
| `state_to_dfs_tree_step_char` | 树边 → `fa s y = x` 等状态条件 (→ 方向) |
| `state_to_dfs_tree_step_char_backward` | 反向构造树边，需 `dg_step g x y` 前提 |
| `state_to_dfs_tree_step_fa` | `fa s v` 到 `v` 的树边，需 `dg_step g (fa s v) v` |
| `state_to_dfs_tree_dg_reachable_refl` | 已访问顶点在树中自反可达 |
| `state_to_dfs_tree_root_visited` | 已访问的 root 在树中有效 |
| `state_to_dfs_tree_no_self_loop` | DFS 树中无自环 |
| `set_fa_preserves_tree_vvalid` | `set_fa` 不改变树顶点集 |
| `set_fa_preserves_tree_edges` | 对 `w ≠ v`，已有树边 `x → w` 不变 |
| `set_fa_adds_tree_edge` | `set_fa v p` 后新增树边 `p → v`，需 `dg_step g p v` |

### Ltac

| 名称 | 行号 | 摘要 |
|------|------|------|
| `unfold_op` | 100 | 展开所有基本操作定义 |

---

## 与 SCC_basic.v 的关系

`Tarjan_scc.v` 是 **Layer 2（Monad 算法层）** 的实现，依赖 `SCC_basic.v` 作为 **Layer 3（数学规格层）**。

- `SCC_basic.v` 定义了纯数学概念：`dg_step`、`dg_reachable`、`mutually_reachable`、`is_SCC`、`scc_partition`、`condensation_edge` 等
- `Tarjan_scc.v` 使用这些概念：
  - `dg_step g u v` 用于 `tarjan_scc_f` 中 `forset` 的邻域迭代——确定顶点的出边邻居集合，供遍历时调用 `process_edge`
  - 最终目标是证明 `tarjan_scc_all` 输出的 `sccs` 满足 `scc_partition g sccs`

## 数据流概览

```
initSt
  │
  ▼
tarjan_scc_all ──► forset (遍历所有有效顶点)
  │                   │
  │                   ▼
  │              tarjan_scc v (若 v 未访问)
  │                   │
  │                   ▼
  │              preloop v (设置 dfn/low, 入栈, 标记 visited)
  │                   │
  │                   ▼
  │              forset (遍历 v 的出边邻居)
  │                   │
  │                   ▼
  │              process_edge v W w
  │                ├── 树边: 递归 W w 后更新 low[v]
  │                └── 回边: 用 dfn[w] 更新 low[v]
  │                   │
  │                   ▼
  │              If low[v] = dfn[v] → pop_scc v (弹出 SCC)
  │
  ▼
最终状态: (sccs = [...]) 应满足 scc_partition g sccs
```
