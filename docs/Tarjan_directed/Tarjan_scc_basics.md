# Tarjan_scc_basics — 不变式与 Hoare 基础定理

**Author**: Vitalrubbish
**Date**: 2026-06-16

本文档整理 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_basics.v` 中的所有定义、引理与定理，供后续开发参考。

---

## Context 与依赖

整个文件位于 `Section BASICS` 下，共享以下 Context：

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
| `Coq.Logic.Classical_Prop` | `classic` 排中律 |
| `Coq.Classes.Morphisms` | 态射类型类 |
| `Coq.Classes.EquivDec` | `equiv_decb` 可判定等价 |
| `Coq.Arith.PeanoNat` | `Nat` 运算 |
| `Lia` | 线性算术自动化解 |
| `SetsClass.SetsClass` | 集合记法 (`SetsNotation`) |
| `MonadLib.StateRelMonad` | `StateRelBasic`、`StateRelHoare`、`FixpointLib` — 状态关系单子与 Hoare 逻辑基础设施 |
| `GraphLib.graph_basic` | `Graph`、`GValid` 等图类型类基础设施 |
| `GraphLib.Syntax` | `MonadNotation` 单子记法 |
| `GraphLib.examples.tarjan` | `OriginalGraphType`、`OriginalGraphProp` 等图类型定义与基础设施 |
| `Algorithms.Tarjan_directed.SCC_basic` | `dg_step`、`dg_reachable` 等有向图原语与 SCC 数学规格 |
| `Algorithms.Tarjan_directed.Tarjan_scc` | `SCCSt`、基本操作、`tarjan_scc`、`tarjan_scc_all` 定义 |

该文件的定位：**Layer 2.5（不变式与 Hoare 基础层）**，处于 `Tarjan_scc.v`（Layer 2，程序定义）和后续正确性证明之间的桥梁。它定义了 Tarjan 算法程序应当满足的不变式框架，并对每个基本操作、组合操作、递归调用和外层循环证明 Hoare 风格的前后条件保持性质。

---

## 1. Tactic Definitions — 战术定义

### `unfold_op`

```coq
Ltac unfold_op :=
  unfold visit, set_dfn, set_low, set_fa, incr_timer,
         push_stack, update_low, pop_scc.
```

**语义**：一次性展开所有基本操作的定义，用于 Hoare 证明中简化目标。

### `my_destruct`

```coq
Ltac my_destruct H := destruct H as [? [? ?]].
```

**语义**：将形如 `A /\ B /\ C` 的合取假设一次展开为三个成分。

### `hoare_bind''`

```coq
Tactic Notation "hoare_bind''" uconstr(H) :=
  eapply Hoare_bind; [ | intros; eapply H]; intros.
```

**语义**：`eapply Hoare_bind` 的简化语法糖——将当前目标分解为两部分：第一部分用第一个子目标证明，第二部分直接应用引理 `H`。用于处理 `bind` 后后件自然传递的模式。

---

## 2. Invariant Definitions — 不变式定义

Tarjan 算法的核心性质是：从状态 `s1` 到状态 `s2` 的任意执行片段保持一系列单调/保持性质。下面的定义逐项给出这些性质，再打包为 `basics_invariant`。

### `visited_mono`

```coq
Definition visited_mono (s1 s2: @SCCSt V): Prop :=
  forall v, v ∈ visited s1 -> v ∈ visited s2.
```

**语义**：`visited` 集合单调递增——已访问过的顶点不会从 `visited` 中消失。

### `dfn_persist`

```coq
Definition dfn_persist (s1 s2: @SCCSt V): Prop :=
  forall v, v ∈ visited s1 -> dfn s1 v = dfn s2 v.
```

**语义**：已访问顶点的 `dfn` 值持久不变——一旦某个顶点被访问并分配了 DFS 编号，该编号不会在后续操作中改变。

### `low_nonincreasing`

```coq
Definition low_nonincreasing (s1 s2: @SCCSt V): Prop :=
  forall v, v ∈ visited s1 -> low s2 v <= low s1 v.
```

**语义**：已访问顶点的 `low` 值非增——`low[v]` 只能被更新为更小的值（通过回边发现更早的祖先），不能增大。

### `fa_persist`

```coq
Definition fa_persist (s1 s2: @SCCSt V): Prop :=
  forall v, v ∈ visited s1 -> fa s1 v = fa s2 v.
```

**语义**：已访问顶点的父节点关系持久不变——DFS 树一旦建立，后续操作不会改变已确定父子关系。

### `stack_in_visited`

```coq
Definition stack_in_visited (s: @SCCSt V): Prop :=
  forall v, In v (stack s) -> v ∈ visited s.
```

**语义**：栈中的所有顶点都已被访问——这是 Tarjan 算法的不变式：栈只包含当前 DFS 路径上的顶点，这些都是已访问的。

### `sccs_mono`

```coq
Definition sccs_mono (s1 s2: @SCCSt V): Prop :=
  forall scc, In scc (sccs s1) -> In scc (sccs s2).
```

**语义**：已发现的 SCC 列表单调递增——弹出并记录的 SCC 不会在后续操作中丢失。

### `timer_mono`

```coq
Definition timer_mono (s1 s2: @SCCSt V): Prop :=
  timer s1 <= timer s2.
```

**语义**：DFS 时间戳计数器单调递增——`timer` 只增不减。

### `basics_invariant`

```coq
Definition basics_invariant (s1 s2: @SCCSt V): Prop :=
  visited_mono s1 s2 /\
  dfn_persist s1 s2 /\
  low_nonincreasing s1 s2 /\
  fa_persist s1 s2 /\
  timer_mono s1 s2 /\
  stack_in_visited s2 /\
  sccs_mono s1 s2.
```

**语义**：总不变式——将上述七个性质打包为一个合取谓词。如果 `basics_invariant s1 s2` 成立，则意味着从状态 `s1` 到 `s2` 的执行路径保持了所有 Tarjan 算法的核心单调/保持性质。

---

## 3. Primitive Operation Lemmas — 基本操作引理

对每个基本操作（`visit`、`set_dfn`、`set_low`、`set_fa`、`incr_timer`、`push_stack`、`update_low`、`pop_scc`），文件提供两类 Hoare 引理：

1. **保持 visited**：操作不减少 `visited` 集合
2. **设置/保持字段**：操作正确设置目标字段，同时保持其他顶点或字段不变

### `visit`

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `visit_keep_visited` | `{w ∈ visited} visit v {w ∈ visited}` | `visit v` 不将任何已访问顶点从 `visited` 中移除 |

### `set_dfn`

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `set_dfn_keep_visited` | `{w ∈ visited} set_dfn v n {w ∈ visited}` | 设置 dfn 保持 visited |
| `set_dfn_new_dfn` | `{~ v ∈ visited} set_dfn v n {dfn v = n}` | 若 v 未访问，设置后 `dfn v = n` |
| `set_dfn_keep_other_dfn` | `{v ≠ w ∧ dfn w = dfnw} set_dfn v n {dfn w = dfnw}` | 设置 v 的 dfn 不影响 w ≠ v 的 dfn 值 |

### `set_low`

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `set_low_keep_visited` | `{w ∈ visited} set_low v n {w ∈ visited}` | 设置 low 保持 visited |
| `set_low_new_low` | `{True} set_low v n {low v = n}` | 无条件设置 `low v = n` |
| `set_low_keep_other_low` | `{v ≠ w ∧ low w = loww} set_low v n {low w = loww}` | 设置 v 的 low 不影响 w ≠ v 的 low 值 |

### `set_fa`

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `set_fa_keep_visited` | `{w ∈ visited} set_fa v p {w ∈ visited}` | 设置 fa 保持 visited |
| `set_fa_new_fa` | `{True} set_fa v p {fa v = p}` | 无条件设置 `fa v = p` |
| `set_fa_keep_other_fa` | `{v ≠ w ∧ fa w = faw} set_fa v p {fa w = faw}` | 设置 v 的 fa 不影响 w ≠ v 的 fa 值 |
| `set_fa_keep_dfn` | `{dfn w = dfnw} set_fa v p {dfn w = dfnw}` | 设置 fa 不影响任何顶点的 dfn |
| `set_fa_keep_low` | `{low w = loww} set_fa v p {low w = loww}` | 设置 fa 不影响任何顶点的 low |

### `incr_timer`

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `incr_timer_keep_visited` | `{w ∈ visited} incr_timer {w ∈ visited}` | 递增 timer 保持 visited |

### `push_stack`

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `push_stack_keep_visited` | `{w ∈ visited} push_stack v {w ∈ visited}` | 压栈保持 visited |
| `push_stack_in_stack` | `{True} push_stack v {In v (stack s)}` | 压栈后 v 成为栈顶元素（由 `cons` 实现保证 `In` 成立） |

### `update_low`

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `update_low_keep_visited` | `{w ∈ visited} update_low u n {w ∈ visited}` | 条件更新 low 保持 visited |
| `update_low_nonincreasing` | `{low u = old_low} update_low u n {low u <= old_low}` | low 更新后非增——仅当 n 更小时才更新 |
| `update_low_keep_dfn` | `{dfn w = dfnw} update_low u n {dfn w = dfnw}` | 更新 low 不影响任何顶点的 dfn |

### `pop_scc`

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `pop_scc_keep_visited` | `{w ∈ visited} pop_scc u {w ∈ visited}` | 弹出 SCC 保持 visited |
| `pop_scc_keep_dfn` | `{dfn w = dfnw} pop_scc u {dfn w = dfnw}` | 弹出 SCC 不影响 dfn |
| `pop_scc_keep_low` | `{low w = loww} pop_scc u {low w = loww}` | 弹出 SCC 不影响 low |
| `pop_scc_keep_fa` | `{fa w = faw} pop_scc u {fa w = faw}` | 弹出 SCC 不影响 fa |

**证明模式**：所有基本操作引理的证明均使用相同的模式：
1. `unfold <operation>. intro_state. hoare_auto_s.` 展开操作并应用 Hoare 自动化
2. `subst s. simpl.` 化简状态代换
3. 对涉及特定顶点更新的引理，展开 `equiv_decb` 分支，使用 `reflexivity` 或 `exfalso` 处理等价/不等价情况

---

## 4. Composite Operation Lemmas — preloop

`preloop u` 是 DFS 进入顶点 `u` 的前置处理序列：读取 `timer` → 设置 `dfn` 和 `low` → 递增 `timer` → 压栈 → 标记 `visited`。

### 保持性质

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `preloop_keep_visited` | `{w ∈ visited} preloop u {w ∈ visited}` | preloop 不减少 visited |
| `preloop_self_visited` | `{True} preloop u {u ∈ visited}` | preloop 后 u 在 visited 中 |
| `preloop_in_stack` | `{True} preloop u {In u (stack s)}` | preloop 后 u 在栈中 |

### 字段设置性质

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `preloop_dfn_set` | `{timer = t} preloop u {dfn u = t}` | `dfn[u]` 设为当前 timer 值 |
| `preloop_low_set` | `{timer = t} preloop u {low u = t}` | `low[u]` 初始设为当前 timer 值 |

### 对其他顶点的保持性质

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `preloop_keep_dfn` | `{u ≠ v ∧ v ∈ visited ∧ dfn v = dfnv} preloop u {u ≠ v ∧ v ∈ visited ∧ dfn v = dfnv}` | 对已访问的 v ≠ u，dfn 保持不变 |
| `preloop_keep_low` | `{u ≠ v ∧ v ∈ visited ∧ low v = lowv} preloop u {u ≠ v ∧ v ∈ visited ∧ low v = lowv}` | 对已访问的 v ≠ u，low 保持不变 |
| `preloop_keep_fa` | `{u ≠ v ∧ v ∈ visited ∧ fa v = fav} preloop u {u ≠ v ∧ v ∈ visited ∧ fa v = fav}` | 对已访问的 v ≠ u，fa 保持不变 |

这些引理的关键前提是 `u ≠ v ∧ v ∈ visited`：`preloop u` 会设置 `dfn[u]` 和 `low[u]`，但不会改变其他已访问顶点的对应字段。

---

## 5. Composite Operation Lemmas — process_edge helpers

这两个引理是 `process_edge` 证明中的辅助步骤，处理 `get'` + `update_low` 的组合：

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `get_low_update_low_keep_visited` | `{w ∈ visited} lv ← get' (low v);; update_low u lv {w ∈ visited}` | 读 low[v] 后更新 low[u]，保持 visited |
| `get_dfn_update_low_keep_visited` | `{w ∈ visited} dv ← get' (dfn v);; update_low u dv {w ∈ visited}` | 读 dfn[v] 后更新 low[u]，保持 visited |

---

## 6. Composite Operation Lemmas — process_edge

`process_edge u W v` 是 Tarjan 算法中处理单条边 `u → v` 的操作。它对 `W`（代表递归 DFS 体）有依赖，因此其引理也以 `W` 的保持性质为前提。

### `process_edge_keep_visited`

```coq
Lemma process_edge_keep_visited (u v w: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => w ∈ visited s) (W x) (fun _ s => w ∈ visited s)) ->
  Hoare (fun s => w ∈ visited s) (process_edge u W v) (fun _ s => w ∈ visited s).
```

**语义**：若递归体 `W` 对所有参数保持 visited，则 `process_edge` 也保持 visited。

**分情况证明**：
- **树边**（v 未访问）：执行 `set_fa v u` → `W v`（递归 DFS）→ `get' (low v)` → `update_low u lv`。每步保持 visited。
- **非树边**（v 已访问且在栈中）：执行 `get' (dfn v)` → `update_low u dv`。每步保持 visited。
- **非树边**（v 已访问且不在栈中）：`skip`，平凡保持。

---

## 7. Composite Operation Lemmas — process_edge_fa

这一组引理关注 `fa` 字段在 `process_edge` 中的保持性质。

### 辅助引理

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `set_fa_keep_not_visited` | `{~ v ∈ visited} set_fa w p {~ v ∈ visited}` | 设置 fa 不改变 visited，故未访问的顶点保持未访问 |
| `update_low_keep_fa` | `{fa w = faw} update_low u n {fa w = faw}` | 更新 low 不影响任何顶点的 fa |
| `update_low_keep_visited_fa` | `{w ∈ visited ∧ fa w = faw} update_low u n {w ∈ visited ∧ fa w = faw}` | 合取引用：更新 low 同时保持 visited 和 fa |

### `process_edge_keep_fa`

```coq
Lemma process_edge_keep_fa (u v w: V) (W: V -> program (@SCCSt V) unit) (faw: V):
  (forall x, Hoare (fun s => x <> w /\ w ∈ visited s /\ fa s w = faw)
                  (W x)
                  (fun _ s => w ∈ visited s /\ fa s w = faw)) ->
  Hoare (fun s => w ∈ visited s /\ fa s w = faw)
        (process_edge u W v)
        (fun _ s => w ∈ visited s /\ fa s w = faw).
```

**语义**：若 `W` 对不同顶点保持 fa 值，则 `process_edge` 对指定顶点 `w` 也保持 fa 值。

**树边分支的关键推理**：`set_fa v u` 设置的是 `fa[v]`，而非 `fa[w]`。因此只要 `v ≠ w`（通过 `~ v ∈ visited` + `w ∈ visited` 保证），`fa[w]` 不受影响。后续的 `W v` 和 `update_low` 也都保持 `fa[w]`。

---

## 8. Composite Operation Lemmas — process_edge (dfn/low variants)

这组引理为 `process_edge` 提供了 dfn 和 low 的保持版本。它们与 `process_edge_keep_fa` 结构类似但关注不同字段。

### 辅助引理

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `update_low_keep_other_low` | `{u ≠ w ∧ low w = loww} update_low u n {low w = loww}` | 不同顶点间的 low 不互相干扰 |
| `update_low_keep_other_dfn` | `{u ≠ w ∧ dfn w = dfnw} update_low u n {dfn w = dfnw}` | 更新 low 不影响任何顶点的 dfn |
| `set_fa_keep_nv_visited_dfn` | `{~ v ∈ visited ∧ w ∈ visited ∧ dfn w = dfnw} set_fa v u {~ v ∈ visited ∧ w ∈ visited ∧ dfn w = dfnw}` | 合并保持——set_fa 不修改 visited 和 dfn |
| `set_fa_keep_nv_visited_low` | 同上（low 替代 dfn） | 合并保持——set_fa 不修改 visited 和 low |
| `set_fa_keep_visited_dfn` | `{w ∈ visited ∧ dfn w = dfnw} set_fa v u {w ∈ visited ∧ dfn w = dfnw}` | 通过 `Hoare_conj` 从 `set_fa_keep_visited` 和 `set_fa_keep_dfn` 组合 |
| `set_fa_keep_visited_low` | 同上（low 替代 dfn） | 通过 `Hoare_conj` 组合 |
| `update_low_keep_visited_dfn` | `{w ∈ visited ∧ dfn w = dfnw} update_low u n {w ∈ visited ∧ dfn w = dfnw}` | 通过 `Hoare_conj` 组合 |
| `get_low_update_low_keep_visited_dfn` | `{w ∈ visited ∧ dfn w = dfnw} lv ← get' (low v);; update_low u lv {w ∈ visited ∧ dfn w = dfnw}` | `get'` + `update_low` 的 dfn 保持版本 |
| `get_dfn_update_low_keep_visited_dfn` | 同上（读 dfn v） | `get'` + `update_low` 的 dfn 保持版本 |

### `process_edge_keep_dfn`

```coq
Lemma process_edge_keep_dfn (u v w: V) (W: V -> program (@SCCSt V) unit) (dfnw: nat):
  (forall x, Hoare (fun s => x <> w /\ w ∈ visited s /\ dfn s w = dfnw)
                  (W x)
                  (fun _ s => w ∈ visited s /\ dfn s w = dfnw)) ->
  Hoare (fun s => u <> w /\ w ∈ visited s /\ dfn s w = dfnw)
        (process_edge u W v)
        (fun _ s => w ∈ visited s /\ dfn s w = dfnw).
```

**语义**：若 `W` 对不同顶点保持 dfn，则 `process_edge` 保持 dfn。前提中 `u ≠ w` 由外层不动点归纳传递而来——它源于 `tarjan_scc_keep_dfn` 中 `preloop u` 会设置 `dfn[u]` 的事实，因此 `u` 自身的 dfn 不能声称被保持；`update_low` 本身不修改任何顶点的 dfn。

### `process_edge_keep_low`

```coq
Lemma process_edge_keep_low (u v w: V) (W: V -> program (@SCCSt V) unit) (loww: nat):
  (forall x, Hoare (fun s => x <> w /\ w ∈ visited s /\ low s w = loww)
                  (W x)
                  (fun _ s => w ∈ visited s /\ low s w = loww)) ->
  Hoare (fun s => u <> w /\ w ∈ visited s /\ low s w = loww)
        (process_edge u W v)
        (fun _ s => w ∈ visited s /\ low s w = loww).
```

**语义**：与 dfn 版本不同，low 版本中 `u ≠ w` 是关键——`update_low u n` 会修改 `low[u]`，若 `u = w` 则 `low[w]` 会改变；但对于 `u ≠ w`，`low[w]` 保持不变。

---

## 9. Forall Variants — visited 的全称量化版本

这些引理将逐点的 visited 保持性质提升为全称量化的版本，用一个谓词 `done` 标记"已确认在 visited 中"的顶点集。

### 基本 forall 保持

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `set_fa_keep_visited_forall` | `{∀w, done w → w ∈ visited} set_fa v p {∀w, done w → w ∈ visited}` | forall 版本的 fa-visited 保持 |
| `update_low_keep_visited_forall` | `{∀w, done w → w ∈ visited} update_low u n {∀w, done w → w ∈ visited}` | forall 版本的 low-visited 保持 |
| `get_low_update_low_keep_visited_forall` | 同上（get' + update_low） | forall 版本的 get_low + update_low |
| `get_dfn_update_low_keep_visited_forall` | 同上（get' + update_low） | forall 版本的 get_dfn + update_low |
| `preloop_keep_visited_forall` | `{∀w, done w → w ∈ visited} preloop u {∀w, done w → w ∈ visited}` | forall 版本的 preloop visited 保持 |
| `pop_scc_keep_visited_forall` | `{∀w, done w → w ∈ visited} pop_scc u {∀w, done w → w ∈ visited}` | forall 版本的 pop_scc visited 保持 |

### 复合引理

| 引理 | Hoare 三元组 | 含义 |
|------|-------------|------|
| `process_edge_keep_visited_forall` | `(∀x, {∀w, done w → w ∈ visited} W x {…}) → {∀w, done w → w ∈ visited} process_edge u W v {…}` | forall 版本的 process_edge visited 保持 |
| `forset_process_edge_keep_visited_forall` | 同上扩展到 forset | forall 版本的 forset 迭代 visited 保持 |

后者是关键的归纳桥梁：它将 `process_edge` 的 forall 保持性质通过 `forset` 不动点结构提升为整个邻域迭代的 forall 保持性质。

---

## 10. Core Hoare Fixpoint Theorems — tarjan_scc

这一组定理是文件的**核心成果**：证明 Tarjan SCC 递归 DFS（`tarjan_scc u`）保持各种字段性质。

### forset 不动点辅助引理

在证明主定理之前，需要先证明 `forset` (对 `u` 的出边邻居的迭代) 保持各种字段：

| 引理 | 含义 |
|------|------|
| `forset_process_edge_keep_visited` | `forset (dg_step g u) (process_edge u W)` 保持 visited |
| `forset_process_edge_keep_dfn` | 同上，保持 dfn（前提 `u ≠ v`） |
| `forset_process_edge_keep_low` | 同上，保持 low（前提 `u ≠ v`） |
| `forset_process_edge_keep_fa` | 同上，保持 fa |

这些引理使用 `hoare_fix_nolv_auto` 处理 `forset` 的最小不动点结构。证明模式为：
1. 展开 `forset` 为 `Lfix (forset_f body) universe`
2. 使用 `hoare_fix_nolv_auto` 引入归纳假设 `IH0`
3. 对 `forset_f` 的分支分别处理
4. 非空分支：`process_edge` + 归纳假设组合
5. 空分支：前提到后件的平凡推理

---

### 主定理

#### `tarjan_scc_keep_visited`

```coq
Theorem tarjan_scc_keep_visited (u v: V):
  Hoare (fun s => v ∈ visited s)
        (tarjan_scc g u)
        (fun _ s => v ∈ visited s).
```

**语义**：Tarjan SCC 递归 DFS 从 `u` 出发，不会将任何已访问顶点从 `visited` 中移除。这是最基本的不变式保持定理。

**证明**：对 `tarjan_scc` 的不动点做归纳：
1. `preloop` 保持 visited（`preloop_keep_visited`）
2. `forset` 迭代保持 visited（`forset_process_edge_keep_visited` + 归纳假设）
3. `pop_scc` 保持 visited（`pop_scc_keep_visited`）

#### `tarjan_scc_keep_dfn`

```coq
Theorem tarjan_scc_keep_dfn (u v: V) (dfnv: nat):
  Hoare (fun s => u <> v /\ v ∈ visited s /\ dfn s v = dfnv)
        (tarjan_scc g u)
        (fun _ s => v ∈ visited s /\ dfn s v = dfnv).
```

**语义**：若 `v ≠ u` 且 `v` 在调用前已访问（有已知 dfn 值），则 `tarjan_scc u` 递归 DFS 不会改变 `dfn[v]` 的值。

**关键前提 `u ≠ v`**：`preloop u` 会设置 `dfn[u]`，所以 `u` 自身的 dfn 当然会变。但对其他顶点保持。

#### `tarjan_scc_keep_low`

```coq
Theorem tarjan_scc_keep_low (u v: V) (lowv: nat):
  Hoare (fun s => u <> v /\ v ∈ visited s /\ low s v = lowv)
        (tarjan_scc g u)
        (fun _ s => v ∈ visited s /\ low s v = lowv).
```

**语义**：与 dfn 版本类似但针对 low 字段。其中 `u ≠ v` 更为关键——`process_edge` 中对邻居的 `update_low u lv` 会更新 `low[u]`。但对于 `v ≠ u`，`low[v]` 保持不变。

#### `tarjan_scc_keep_fa`

```coq
Theorem tarjan_scc_keep_fa (u v: V) (fav: V):
  Hoare (fun s => u <> v /\ v ∈ visited s /\ fa s v = fav)
        (tarjan_scc g u)
        (fun _ s => v ∈ visited s /\ fa s v = fav).
```

**语义**：递归 DFS 不改变已访问顶点 `v ≠ u` 的父节点关系。

#### `tarjan_scc_self_visited`

```coq
Theorem tarjan_scc_self_visited (u: V):
  Hoare (fun s => True)
        (tarjan_scc g u)
        (fun _ s => u ∈ visited s).
```

**语义**：从 `u` 出发的 Tarjan DFS 完成后，`u` 一定在 `visited` 中——递归必定访问了起始顶点。

**证明策略**：使用 `tarjan_scc_unfold` 将 `tarjan_scc u` 展开为 `tarjan_scc_f tarjan_scc u`：
1. `preloop` 后 `u ∈ visited`（`preloop_self_visited`）
2. `forset` 迭代保持 visited（`tarjan_scc_keep_visited` 作归纳）
3. `pop_scc` 保持 visited

#### `tarjan_scc_keep_visited_forall`

```coq
Theorem tarjan_scc_keep_visited_forall (u: V) (done: V -> Prop):
  Hoare (fun s => forall v, done v -> v ∈ visited s)
        (tarjan_scc g u)
        (fun _ s => forall v, done v -> v ∈ visited s).
```

**语义**：`tarjan_scc_keep_visited` 的全称量化版本——若调用前某个顶点集合 `done` 中的全部顶点都在 `visited` 中，递归 DFS 完成后它们仍在 `visited` 中。

#### `tarjan_scc_keep_dfn_low_order` 与 `tarjan_scc_keep_dfn_low_order'`

```coq
Theorem tarjan_scc_keep_dfn_low_order (u x y: V) (dfnx lowy: nat):
  Hoare (fun s =>
           u <> x /\ u <> y /\ x ∈ visited s /\ y ∈ visited s
           /\ dfn s x = dfnx /\ low s y = lowy /\ dfnx < lowy)
        (tarjan_scc g u)
        (fun _ s => dfn s x < low s y).

Theorem tarjan_scc_keep_dfn_low_order' (u x y: V) (dfnx lowy: nat):
  Hoare (fun s =>
           u <> x /\ u <> y /\ x ∈ visited s /\ y ∈ visited s
           /\ dfn s x = dfnx /\ low s y = lowy /\ ~ dfnx < lowy)
        (tarjan_scc g u)
        (fun _ s => ~ dfn s x < low s y).
```

**语义**：递归 DFS 保持两个已访问顶点之间的 dfn/low 大小关系——因为递归不改变已访问顶点的 dfn 和 low 值。分别处理 `dfnx < lowy` 和 `~ dfnx < lowy` 两种情况。

**证明方式**：对两个字段分别使用 `tarjan_scc_keep_dfn` 和 `tarjan_scc_keep_low`，通过 `Hoare_conj` 组合。

#### `tarjan_scc_keep_dfn_prod` 与 `tarjan_scc_keep_low_prod`

```coq
Theorem tarjan_scc_keep_dfn_prod (u: V) (p: V * nat):
  Hoare (fun s => u <> fst p /\ fst p ∈ visited s /\ dfn s (fst p) = snd p)
        (tarjan_scc g u)
        (fun _ s => fst p ∈ visited s /\ dfn s (fst p) = snd p).

Theorem tarjan_scc_keep_low_prod (u: V) (p: V * nat):
  Hoare (fun s => u <> fst p /\ fst p ∈ visited s /\ low s (fst p) = snd p)
        (tarjan_scc g u)
        (fun _ s => fst p ∈ visited s /\ low s (fst p) = snd p).
```

**语义**：`tarjan_scc_keep_dfn` 和 `tarjan_scc_keep_low` 的积类型包装版本——用 `V * nat` 对表示"顶点 + 值"的绑定。方便后续使用 `Hoare_forset` 对顶点值对做迭代时的调用。

---

## 11. Outer Loop Theorems — tarjan_scc_all

外层循环 `tarjan_scc_all` 遍历图中所有有效顶点，对未访问的顶点启动 `tarjan_scc`。

### `tarjan_scc_all_keep_visited`

```coq
Theorem tarjan_scc_all_keep_visited (v: V):
  Hoare (fun s => v ∈ visited s)
        (tarjan_scc_all g)
        (fun _ s => v ∈ visited s).
```

**语义**：`tarjan_scc_all` 不减少 `visited` 集合——已访问的顶点在整个外层循环中保持已访问。

**证明**：使用 `Hoare_forset` 处理 `tarjan_scc_all` 的 `forset` 结构：
- 对每个有效顶点 `a`：若 `a ∉ visited`，执行 `tarjan_scc a`（由 `tarjan_scc_keep_visited` 保持 visited）；若 `a` 已访问，skip。

### `tarjan_scc_all_visited_all`

```coq
Theorem tarjan_scc_all_visited_all:
  Hoare (fun s => True)
        (tarjan_scc_all g)
        (fun _ s => forall v, original_vvalid g v -> v ∈ visited s).
```

**语义**：`tarjan_scc_all` 完成后，图中**所有有效顶点**都在 `visited` 中——外层循环覆盖了整个图的所有有效顶点。

**证明**：使用 `Hoare_forset` 配合全称量化不变式：
1. 初始时 `done` 为 `∅`（平凡的 `∀v, ∅ v → v ∈ visited`）
2. 每步选取未处理的顶点 `a`：
   - 若 `a` 未访问：执行 `tarjan_scc a`，由 `tarjan_scc_self_visited` 得 `a ∈ visited`，由 `tarjan_scc_keep_visited_forall` 保持 `done` 全称条件
   - 若 `a` 已访问：skip，`a` 已在 visited 中
3. 最终将 `done` 扩展到 `original_vvalid g`（全有效顶点集），得最终后件

---

## 定义与定理清单

### 不变式定义 (8)

| 名称 | 类型 | 行号 | 摘要 |
|------|------|------|------|
| `visited_mono` | `SCCSt → SCCSt → Prop` | 42–43 | visited 单调递增 |
| `dfn_persist` | `SCCSt → SCCSt → Prop` | 45–46 | 已访问顶点的 dfn 持久 |
| `low_nonincreasing` | `SCCSt → SCCSt → Prop` | 48–49 | 已访问顶点的 low 非增 |
| `fa_persist` | `SCCSt → SCCSt → Prop` | 51–52 | 已访问顶点的 fa 持久 |
| `stack_in_visited` | `SCCSt → Prop` | 54–55 | 栈中顶点都在 visited 中 |
| `sccs_mono` | `SCCSt → SCCSt → Prop` | 57–58 | SCC 列表单调递增 |
| `timer_mono` | `SCCSt → SCCSt → Prop` | 60–61 | timer 单调递增 |
| `basics_invariant` | `SCCSt → SCCSt → Prop` | 63–70 | 总不变式（上述七项合取） |

### Ltac 战术 (3)

| 名称 | 行号 | 摘要 |
|------|------|------|
| `unfold_op` | 22–24 | 展开所有基本操作定义 |
| `my_destruct` | 26 | 展开 `A ∧ B ∧ C` |
| `hoare_bind''` | 28–29 | `Hoare_bind` 的简化语法糖 |

### 基本操作引理 (22)

| 名称 | 行号 | 摘要 |
|------|------|------|
| `visit_keep_visited` | 76–83 | visit 保持 visited |
| `set_dfn_keep_visited` | 85–92 | set_dfn 保持 visited |
| `set_dfn_new_dfn` | 94–103 | set_dfn 正确设置 dfn |
| `set_dfn_keep_other_dfn` | 105–116 | set_dfn 不改变其他顶点的 dfn |
| `set_low_keep_visited` | 118–125 | set_low 保持 visited |
| `set_low_new_low` | 127–136 | set_low 正确设置 low |
| `set_low_keep_other_low` | 138–149 | set_low 不改变其他顶点的 low |
| `set_fa_keep_visited` | 151–157 | set_fa 保持 visited |
| `set_fa_new_fa` | 159–169 | set_fa 正确设置 fa |
| `set_fa_keep_other_fa` | 171–182 | set_fa 不改变其他顶点的 fa |
| `incr_timer_keep_visited` | 184–190 | incr_timer 保持 visited |
| `push_stack_keep_visited` | 193–200 | push_stack 保持 visited |
| `push_stack_in_stack` | 202–209 | push_stack 正确压栈 |
| `update_low_keep_visited` | 211–219 | update_low 保持 visited |
| `update_low_nonincreasing` | 221–232 | update_low 使 low 非增 |
| `update_low_keep_dfn` | 234–242 | update_low 保持 dfn |
| `set_fa_keep_dfn` | 244–251 | set_fa 保持 dfn |
| `set_fa_keep_low` | 253–260 | set_fa 保持 low |
| `pop_scc_keep_visited` | 262–271 | pop_scc 保持 visited |
| `pop_scc_keep_dfn` | 273–282 | pop_scc 保持 dfn |
| `pop_scc_keep_low` | 284–293 | pop_scc 保持 low |
| `pop_scc_keep_fa` | 295–304 | pop_scc 保持 fa |

### preloop 引理 (8)

| 名称 | 行号 | 摘要 |
|------|------|------|
| `preloop_keep_visited` | 310–317 | preloop 保持 visited |
| `preloop_self_visited` | 319–326 | preloop 后 u ∈ visited |
| `preloop_in_stack` | 328–335 | preloop 后 u 在栈中 |
| `preloop_dfn_set` | 337–346 | preloop 设置 dfn[u] = timer |
| `preloop_low_set` | 348–357 | preloop 设置 low[u] = timer |
| `preloop_keep_dfn` | 359–372 | preloop 保持其他顶点的 dfn |
| `preloop_keep_low` | 374–387 | preloop 保持其他顶点的 low |
| `preloop_keep_fa` | 389–402 | preloop 保持其他顶点的 fa |

### process_edge 与辅助引理 (18)

| 名称 | 行号 | 摘要 |
|------|------|------|
| `get_low_update_low_keep_visited` | 408–418 | get low + update_low 保持 visited |
| `get_dfn_update_low_keep_visited` | 420–430 | get dfn + update_low 保持 visited |
| `process_edge_keep_visited` | 436–459 | process_edge 保持 visited |
| `set_fa_keep_not_visited` | 467–474 | set_fa 保持未访问性质 |
| `update_low_keep_fa` | 478–486 | update_low 保持 fa |
| `update_low_keep_visited_fa` | 490–502 | update_low 同时保持 visited 和 fa |
| `process_edge_keep_fa` | 508–563 | process_edge 保持 fa |
| `update_low_keep_other_low` | 571–580 | 不同顶点 low 不干扰 |
| `update_low_keep_other_dfn` | 585–593 | update_low 不修改其他顶点的 dfn |
| `set_fa_keep_nv_visited_dfn` | 598–607 | set_fa 合并保持 visited + dfn |
| `set_fa_keep_nv_visited_low` | 611–620 | set_fa 合并保持 visited + low |
| `set_fa_keep_visited_dfn` | 624–637 | Hoare_conj 版本：set_fa 保持 visited + dfn |
| `set_fa_keep_visited_low` | 639–652 | Hoare_conj 版本：set_fa 保持 visited + low |
| `update_low_keep_visited_dfn` | 654–667 | Hoare_conj 版本：update_low 保持 visited + dfn |
| `get_low_update_low_keep_visited_dfn` | 669–677 | get low + update_low 保持 visited + dfn |
| `get_dfn_update_low_keep_visited_dfn` | 679–687 | get dfn + update_low 保持 visited + dfn |
| `process_edge_keep_dfn` | 692–723 | process_edge 保持 dfn |
| `process_edge_keep_low` | 730–776 | process_edge 保持 low |

### forall 变体引理 (8)

| 名称 | 行号 | 摘要 |
|------|------|------|
| `set_fa_keep_visited_forall` | 787–794 | set_fa 保持 ∀ done → visited |
| `update_low_keep_visited_forall` | 796–804 | update_low 保持 ∀ done → visited |
| `get_low_update_low_keep_visited_forall` | 806–816 | get+update_low 保持 ∀ done → visited |
| `get_dfn_update_low_keep_visited_forall` | 818–828 | get+update_low 保持 ∀ done → visited |
| `preloop_keep_visited_forall` | 830–837 | preloop 保持 ∀ done → visited |
| `pop_scc_keep_visited_forall` | 839–848 | pop_scc 保持 ∀ done → visited |
| `process_edge_keep_visited_forall` | 850–875 | process_edge 保持 ∀ done → visited |
| `forset_process_edge_keep_visited_forall` | 877–892 | forset 保持 ∀ done → visited |

### forset 不动点引理 (4)

| 名称 | 行号 | 摘要 |
|------|------|------|
| `forset_process_edge_keep_visited` | 902–921 | forset 保持 visited |
| `forset_process_edge_keep_dfn` | 923–947 | forset 保持 dfn |
| `forset_process_edge_keep_low` | 949–973 | forset 保持 low |
| `forset_process_edge_keep_fa` | 975–998 | forset 保持 fa |

### 核心定理 (10)

| 名称 | 行号 | 摘要 |
|------|------|------|
| `tarjan_scc_keep_visited` | 1004–1021 | tarjan_scc 保持 visited |
| `tarjan_scc_keep_dfn` | 1023–1045 | tarjan_scc 保持 dfn（前提 u ≠ v） |
| `tarjan_scc_keep_low` | 1047–1069 | tarjan_scc 保持 low（前提 u ≠ v） |
| `tarjan_scc_keep_fa` | 1071–1094 | tarjan_scc 保持 fa（前提 u ≠ v） |
| `tarjan_scc_self_visited` | 1107–1126 | tarjan_scc u 后 u ∈ visited |
| `tarjan_scc_keep_visited_forall` | 1133–1151 | tarjan_scc 保持 ∀ done → visited |
| `tarjan_scc_keep_dfn_low_order` | 1163–1184 | tarjan_scc 保持 dfn[x] < low[y] |
| `tarjan_scc_keep_dfn_low_order'` | 1186–1207 | tarjan_scc 保持 ~(dfn[x] < low[y]) |
| `tarjan_scc_keep_dfn_prod` | 1211–1218 | 积类型包装的 dfn 保持 |
| `tarjan_scc_keep_low_prod` | 1220–1227 | 积类型包装的 low 保持 |

### 外层循环定理 (2)

| 名称 | 行号 | 摘要 |
|------|------|------|
| `tarjan_scc_all_keep_visited` | 1233–1254 | tarjan_scc_all 保持 visited |
| `tarjan_scc_all_visited_all` | 1256–1302 | tarjan_scc_all 完成后全部有效顶点在 visited 中 |

**总计**：8 个不变式定义 + 3 个 Ltac 战术 + 22 个基本操作引理 + 8 个 preloop 引理 + 18 个 process_edge/辅助引理 + 8 个 forall 变体引理 + 4 个 forset 不动点引理 + 10 个核心定理 + 2 个外层循环定理 = **83 项**

---

## 文件在 VCG 证明体系中的位置

该文件在 Tarjan SCC 验证体系中的层级关系如下：

```
Layer 3 (数学规格):  SCC_basic.v
    ├── dg_step / dg_reachable / mutually_reachable
    ├── is_SCC / scc_partition
    ├── condensation_edge / condensation_path
    └── condensation_is_acyclic

Layer 2 (程序定义):  Tarjan_scc.v
    ├── SCCSt 状态记录与基本操作
    ├── tarjan_scc_f / tarjan_scc (递归 DFS)
    ├── tarjan_scc_all (外层循环)
    └── tarjan_scc_f_mono_cont / tarjan_scc_unfold (不动点性质)

Layer 2.5 (不变式层):  Tarjan_scc_basics.v  ← 本文件
    ├── basics_invariant (不变式框架)
    ├── 基本操作的 Hoare 保持引理
    ├── tarjan_scc 核心保持定理
    └── tarjan_scc_all 外层循环保持定理

Layer 1 (正确性证明):  Tarjan_scc 的完整功能正确性证明（含 monadic specification）
    ├── 使用本文件的不变式保持定理
    ├── 结合 SCC_basic.v 的数学规格
    └── 证明 tarjan_scc 的输出 SCC 划分与数学规格一致
```

本文件的所有定理为后续的**正确性证明**提供了必要的 Hoare 逻辑基础设施——它们确保 Tarjan 算法的递归 DFS 不会破坏已完成部分的不变性质，使得下一层可以对算法行为做归纳论证。
