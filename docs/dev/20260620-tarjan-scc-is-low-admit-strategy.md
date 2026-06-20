# Tarjan_scc_is_low.v Admit 消除策略
**Author**: Claude
**Date**: 2026-06-20

## 概述

`Tarjan_scc_is_low.v` 中共有 **9 处 admit/Admitted**，分布如下：

| 行号 | 类型 | 位置 |
|------|------|------|
| 1166 | `Admitted.` | `popped_vertex_low_eq_dfn` 引理 |
| 1352 | `all: admit.` | `process_edge_keep_low_forset_inv` 的 tree edge 分支 |
| 1429 | `admit.` | `process_edge_keep_low_forset_inv` 的 skip 分支 (fa=u) |
| 1651 | `admit.` | `process_edge_keep_low_forset_inv` 的 cross edge 分支 (proper child) |
| 1705 | `Admitted.` | `process_edge_keep_low_forset_inv` 全引理 |
| 1866 | `Admitted.` | `tarjan_scc_keep_fa_children_in_universe` 引理 |
| 2075 | `admit.` | `forset_keep_low_forset_inv` 的 base case |
| 2076 | `Admitted.` | `forset_keep_low_forset_inv` 全引理 |
| 2139 | `Admitted.` | `tarjan_scc_all_scc_low_valid` 定理 |

依赖关系如下：
```
tarjan_scc_all_scc_low_valid (2139)
  └─ tarjan_scc_keep_low_valid (2078, 已证)
       └─ forset_keep_low_forset_inv (2076)
            ├─ process_edge_keep_low_forset_inv (1705)
            │    ├─ admits at 1352, 1429, 1651
            │    └─ tree_child_low_le (1168, 已证但依赖↓)
            │         └─ popped_vertex_low_eq_dfn (1166)
            └─ tarjan_scc_keep_fa_children_in_universe (1866)
```

错误修复必须**自底向上**：先解决 1166 → 再解决 1352/1429/1651 → 1705 → 1866 → 2075 → 2076 → 2139。

---

## Layer 1: `popped_vertex_low_eq_dfn` (line 1166)

### 当前状态
```coq
Lemma popped_vertex_low_eq_dfn (s: @SCCSt V) (v: V):
    dfn_inv s -> v ∈ visited s -> ~ In v (stack s) ->
    low s v = dfn s v.
Proof.
Admitted.
```

### 问题分析
该引理断言：已被 visited 但不在 stack 上的顶点，其 `low = dfn`。这是因为在 Tarjan SCC 算法中：
- 顶点通过 `push_stack`（在 `set_dfn`/`preloop` 中调用）首次进入 stack
- 顶点仅通过 `pop_scc` 离开 stack，`pop_scc` 以 `low s u = dfn s u` 为前提
- `pop_scc` 之后 low/dfn 不再被修改

### 策略：新增状态不变量

在 `Tarjan_scc_is_low.v` 中新增一个不变量定义：

```coq
Definition visited_not_on_stack_low_eq_dfn (s: @SCCSt V): Prop :=
  forall v, v ∈ visited s -> ~ In v (stack s) -> low s v = dfn s v.
```

#### 所需子引理

**引理 1.1** `preloop_establishes_visited_not_on_stack_low_eq_dfn`：
```coq
Lemma preloop_establishes_visited_not_on_stack_low_eq_dfn (u: V):
  Hoare (fun s: @SCCSt V => low_pre u s)
        (preloop u)
        (fun _ s => visited_not_on_stack_low_eq_dfn s).
```
证明思路：`preloop` 调用 `visit u;; set_dfn u;; push_stack u;; set_fa u u`。
- preloop 之后 u 在 stack 中（被 push_stack 推入），`~ In v (stack s)` 前提为空
- 其他顶点未被 visited（由 `dfn_inv` 保证：`dfn s v = 0 <-> ~v ∈ visited s`），所以 `v ∈ visited s` 前提也为空
- 因此不变量空洞成立

**引理 1.2** `set_fa_keep_visited_not_on_stack_low_eq_dfn`：
```coq
Lemma set_fa_keep_visited_not_on_stack_low_eq_dfn (v p: V):
  Hoare (fun s: @SCCSt V => visited_not_on_stack_low_eq_dfn s)
        (set_fa v p)
        (fun _ s => visited_not_on_stack_low_eq_dfn s).
```
证明思路：`set_fa` 不改变 `visited`、`stack`、`low`、`dfn`。

**引理 1.3** `update_low_keep_visited_not_on_stack_low_eq_dfn`：
```coq
Lemma update_low_keep_visited_not_on_stack_low_eq_dfn (u: V) (n: nat):
  Hoare (fun s: @SCCSt V => visited_not_on_stack_low_eq_dfn s)
        (update_low u n)
        (fun _ s => visited_not_on_stack_low_eq_dfn s).
```
证明思路：`update_low u n` 修改 `low s u`，但 u 在执行 `update_low` 时一定在 stack 中（作为当前 center）。其他 vertex 的 low 不变。对任意 `v` 满足 `~ In v (stack s)`，`v ≠ u`（因为 u 在 stack 中），所以 `low s v` 未被修改。

**引理 1.4** `pop_scc_keep_visited_not_on_stack_low_eq_dfn`：
```coq
Lemma pop_scc_keep_visited_not_on_stack_low_eq_dfn (u: V):
  Hoare (fun s: @SCCSt V => visited_not_on_stack_low_eq_dfn s /\ low s u = dfn s u)
        (pop_scc u)
        (fun _ s => visited_not_on_stack_low_eq_dfn s).
```
证明思路：`pop_scc` 将 u 及其上方的 scc 从 stack 中移除，但不修改 low/dfn。pop 之前 `low s u = dfn s u` 成立（前置条件）。pop 后：
- 被 pop 的顶点 w：`low s w = dfn s w` 已经在 pop 前通过不变量保证（因为 pop_scc 的前提包括 `low s u = dfn s u`，且对于栈中 u 以上的 scc，它们已被之前的 `pop_scc` 处理或不变量继承）
- 未被 pop 的顶点：low/dfn 不变，visited 不变，stack 状态可能变化（但仅移除顶点）

实际上，`pop_scc` 只 pop `stack_split_at` 返回的 `popped` 部分，这些顶点原本在 stack 中。pop 之后它们不在 stack 中，需要证明对这些顶点 `low = dfn`。但 `pop_scc` 的前置条件需要 `low s u = dfn s u`，并不直接要求 popped 部分中其他顶点的 low = dfn。这是一个更深的算法性质……

**简化方案**：不使用独立的不变量，而是直接利用 `low_forset_inv` 的结构进行归纳证明。

#### 简化证明方案

`popped_vertex_low_eq_dfn` 可以在 `low_forset_inv` 的框架内证明。关键观察：

1. 顶点 v 从 stack 中被移除只有两种方式：
   - **方式 A**：v 作为 SCC 的一部分被 `pop_scc v` 弹出（v 是 SCC 的根，此时 `low s v = dfn s v`）
   - **方式 B**：v 作为 SCC 的非根部分被 `pop_scc w` 弹出（w 是较低 dfn 的 SCC 根）

2. 在 `low_forset_inv` 中，`low_forset_inv_implies_low_le_dfn` 给出 `low s u ≤ dfn s u`。

3. 通过 `pop_scc_keep_scc_low_valid_v` 可知，被 pop 的 SCC 根 u 满足 `low s u = dfn s u`。

但严格证明需要 pop_scc 对 popped 部分所有顶点都保证 `low = dfn`。我们可以通过**反证 / contradiction**来避免完整的 pop_scc 行为分析：

**替代策略——直接使用 `low_forset_inv` 中的 min 结构**：

实际上 `tree_child_low_le` 只需要知道：**当 v 作为 u 的 proper tree child、且 v 不在 stack 中时，`low s v = dfn s v`**。

在这种受限场景下：
- `fa s v = u`、`fa s v ≠ v`（proper child）
- `v ∈ visited s`、`~ In v (stack s)`
- 这意味着 v 的 SCC 已被完全处理（v 被 pop 了）
- 在 `tarjan_scc` 的 fixpoint 归纳中，对 v 的递归调用 W v 返回了 `scc_low_valid_v v` 和 `dfn_valid`
- `pop_scc v` 在 `tarjan_scc v` 末尾被调用，要求 `low s v = dfn s v`

替代证明路径：**在 `low_forset_inv` 框架外，通过 `low_post v` 和后续的 pop_scc 推理**。

由于 `tree_child_low_le` 在 `process_edge` 上下文中被调用，此时递归调用 `W v`（即 `tarjan_scc g v`）已经返回。从 `W v` 的后置条件 `low_post v s`（即 `scc_low_valid_v s v /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s`）我们可以知道 `low s v = dfn s v` 吗？不直接——`scc_low_valid_v` 只给出 `low s v` 是某个 min 的值，不直接等于 `dfn s v`。

实际路径：`tarjan_scc v` 末尾调用 `pop_scc v`。`pop_scc v` 的前置条件之一是 `low s v = dfn s v`（来自 `pop_scc_keep_scc_low_valid_v` 的前置条件）。所以 `low s v = dfn s v` 在 `tarjan_scc v` 末尾成立。

**结论**：`popped_vertex_low_eq_dfn` 可通过以下方式证明：

```coq
Lemma popped_vertex_low_eq_dfn (s: @SCCSt V) (v: V):
    dfn_inv s -> v ∈ visited s -> ~ In v (stack s) ->
    low s v = dfn s v.
Proof.
  intros Hinv Hvis Hnstack.
  (* 利用 dfn_inv 给出 0 < dfn s v < timer s *)
  destruct Hinv as [Hlt [Hiff Hpos]].
  assert (Hdfn_pos: dfn s v > 0). {
    apply Hiff in Hvis. lia. }
  (* 使用 stack_in_visited 性质：
     所有 visited 顶点在某时刻被 push_stack，且只在 pop_scc 时离开 stack。
     可以用 well-founded induction 或使用 low_forset_inv 的 min 结构。
     此处需要一条专门的辅助引理 *)
Abort.
```

**实际推荐方案**：将 `visited_not_on_stack_low_eq_dfn` 融入 `low_forset_inv`：

```coq
Definition low_forset_inv (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    stack_in_visited s /\
    dfn_inv s /\
    dfn_valid g s root /\
    fa_visited s /\
    u ∈ visited s /\
    visited_not_on_stack_low_eq_dfn s /\    (* NEW *)
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
       min_value_of_subset Nat.le
         (fun w => back_edges_done s u done w \/ w = u) (dfn s))
      (fun x => x) (low s u).
```

然后修改已使用 `low_forset_inv` 的所有引理以适配新增的不变量组件。这是一个高工作量但最可靠的方案。

---

## Layer 2: Tree edge 分支 admits (lines 1352)

### 问题分析
在 `process_edge_keep_low_forset_inv` 的 tree edge 分支（`~ v ∈ visited s`），经过：
```
set_fa v u;; W v;; get' low v;; update_low u (low v)
```
后，需证明 `low_forset_inv u (done ∪ [v]) s'`。

### 策略
`update_low_tree_edge`（line 652-772，已证）直接提供了所需的 min 条件转换：从 `low_forset_inv u done s` + `fa s v = u` + `fa s v ≠ v` 到修改 `low` 后的 `low_forset_inv u (done ∪ [v]) s'`。

在 `hoare_auto_s` 之后，各个子目标应分别解决：
- `stack_in_visited`：由 `W v` 的后置条件保持
- `dfn_inv`：由 `update_low_keep_dfn_inv` 保持
- `dfn_valid`：由 `W` 的后置条件保持（`low_post v s` 包含 `dfn_valid`）
- `fa_visited`：`set_fa v u` 不破坏 `fa_visited`（因为 u ∈ visited s），递归 `W v` 保持它
- `u ∈ visited s`：不被修改
- `min` 条件：由 `update_low_tree_edge` 给出

若新增了 `visited_not_on_stack_low_eq_dfn` 组件，还需要证明 `W v` 和 `update_low u (low v)` 保持它。

---

## Layer 3: Skip 分支 admit (line 1429) — fa s0 v = u，v 在 stack 中

### 问题分析
在非 tree edge 分支的 skip 子分支（`~ dfn s0 v < low s0 u`），当 `fa s0 v = u` 时，需要证明：
`low_forset_inv u (done ∪ [v]) s0` 保持（状态未改变）。

关键困难：需要 `low s0 u ≤ low s0 v` 来证明 `children_done` 扩展 `[v]` 后 nested min 不变。但 `tree_child_low_le` 要求 `v` 不在 stack 中，这里 v **在** stack 中。

### 策略
使用 `low_forset_inv_children_done_low_le`（line 1125-1148，**已证**），该引理无 `~ In v (stack s)` 前提：

```coq
Lemma low_forset_inv_children_done_low_le (u v: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s ->
    children_done s u done v ->
    low s u <= low s v.
```

证明步骤：
1. 证明 `children_done s0 u done v`：即 `v ∈ done /\ fa s0 v = u /\ fa s0 v ≠ v`
   - `fa s0 v = u` 和 `fa s0 v ≠ v` 由分支条件给出
   - `v ∈ done` 需要论证：v 之前作为 tree child 被处理过，因此被添加到 `done` 中
   - 这可以从 `process_edge` 的算法逻辑推出
2. 应用 `low_forset_inv_children_done_low_le` 得到 `low s0 u ≤ low s0 v`
3. 使用 `min_value_of_subset_nested_update_left_nat`（来自 `Tarjan_scc_basics.v` line 1377）和 `children_done_add`（line 548）+ `back_edges_done_no_add`（line 594）处理 nested min 的集合扩展

这里 `v ∈ done` 是最微妙的前提。其论证思路：

在 `process_edge` 的非 tree edge 分支中，`v ∈ visited s`。此时 `fa s0 v = u` 说明 v 是通过 tree edge (u, v) 被首次发现的。这首次发现一定发生在这条边的 tree edge 处理中（因为非 tree edge 分支不修改 fa）。而 tree edge 处理将 v 加入 `done`（通过 `update_low_tree_edge`）。因此在该非 tree edge 被处理时，v 已经在 `done` 中。

更严格地，可以在 `process_edge` 的 Hoare triple 前置条件中携带：
```coq
(forall w, dg_step g u w -> w ∈ done \/ w = v)
```
即"所有邻边除了当前正在处理的 v，都已在 done 中"。但这样修改接口影响较大。

简化方案：在 `process_edge_keep_low_forset_inv` 的 Hoare 中利用 `forset` 提供的归纳假设：`Hdone_sub`（`done ⊆ dg_step g u` 即所有 done 中的顶点都是 u 的出边邻居）、`Huniv`（`a ∈ dg_step g u` 即当前处理的 a 是 u 的出边邻居）。在 skip 分支的 fa=u 情况下，v 已经在 done 中：因为 forset 依次处理每个出边，v 作为 tree child 在之前的某次迭代中已被处理。

所以这里可以新增一条辅助引理：

```coq
Lemma fa_eq_u_impl_in_done_or_current (u v: V) (done: V -> Prop) (s: @SCCSt V):
  done ⊆ dg_step g u ->
  fa s v = u -> fa s v <> v ->
  v ∈ done \/ v ∉ dg_step g u.
```

---

## Layer 4: Cross edge 分支 admit (line 1651) — proper child，v 不在 stack 中

### 问题分析
在非 tree edge 分支的 cross edge 子分支（`~ In v (stack s)`），当 `fa s0 v = u` 且 `fa s0 v ≠ v`（proper child）时，需要证明 nested min 在 `children_done` 扩展 `[v]` 后保持不变。

`tree_child_low_le` 已给出 `low s0 u ≤ low s0 v`（前提 `~ In v (stack s)` 满足）。

### 策略
1. 使用 `tree_child_low_le` 得到 `Hlow_le: low s0 u <= low s0 v`
2. 使用 `children_done_add s0 u v done`（`Hfa_eq` + `Hfa_not_self`）扩展 children_done 集合
3. 使用 `back_edges_done_no_add s0 u v done (or_introl Hnstack)` 保持 back_edges_done 不变
4. 在 `min_value_of_subset_nested_update_left_nat` 框架下证明 expanded set 的 min 仍为 `low s0 u`

具体证明结构：
```coq
eapply min_eq_forward.
- typeclasses eauto. (* TotalOrder Nat.le *)
- (* source min = Hmin from low_forset_inv *)
  exact Hmin.
- (* forward direction: each a1 in source set has a1 ≤ a2 in target *)
  intros a1 Ha1. exists a1. split.
  { (* a1 ∈ target set *)
    destruct Ha1 as [Ha1_L | Ha1_R].
    - left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
      exists w. split.
      + unfold min_object_of_subset. split.
        * apply Hchild_eq. exact Hw_in.
        * intros x Hx. apply Hchild_eq in Hx.
          simpl. destruct (equiv_dec w u) as [Heq_w|Hneq_w];
            [exfalso; (* children_done in w ≠ u *) .. |].
          destruct (equiv_dec x u) as [Heq_x|Hneq_x];
            [exfalso; (* children_done in x ≠ u *) .. |].
          apply Hw_min. exact Hx.
      + simpl. destruct (equiv_dec w u); [exfalso .. | exact Heq_a1].
    - right. ... (* back_edges side unchanged *) }
  { apply Nat.le_refl. }
- (* backward direction: symmetric *)
  intros a2 Ha2. exists a2. split.
  { ... } { apply Nat.le_refl. }
```

注意这里的 `low` 已是 `low s0`（未修改），不需要 `equiv_decb` 检查——此分支是 skip，low 不变。

---

## Layer 5: `tarjan_scc_keep_fa_children_in_universe` (line 1866)

### 问题分析
该引理断言 `tarjan_scc` 保持 `fa_children_in_universe` 性质：
```coq
forall v, fa s v = u /\ fa s v <> v -> dg_step g u v
```
即"如果 v 是 u 的 proper child（fa v = u, fa v ≠ v），则存在 graph edge u→v"。

### 策略
通过 fixpoint induction（与 `tarjan_scc_keep_visited` 模式一致）：

```coq
Lemma tarjan_scc_keep_fa_children_in_universe (parent a: V):
    Hoare (fun s: @SCCSt V => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g a)
          (fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
Proof.
  unfold tarjan_scc.
  apply (Hoare_fix_logicv_conj (tarjan_scc_f g) ...).
  (* 需要定义对应的 visited_tag  constructor *)
  ...
```

这需要：
1. 在 `visited_tag` 中新增一个 constructor：`VKeepFaChildrenUniverse (parent: V)`
2. 对应的 pre/post 定义
3. 在 `tarjan_scc_keep_low_valid` 的归纳调用中传递这个 property

但这里有一个架构问题：`tarjan_scc_keep_low_valid` 已经使用了 `Hoare_fix_logicv_conj` 来处理多种 `visited_tag`。需要检查 `visited_tag` 能否扩展。

**替代方案（更简单）**：不通过 fixpoint induction，而是作为一个独立的引理，通过组合已有的 `tarjan_scc_keep_*` 引理 + `process_edge` 级别的引理来证明：

```coq
Lemma process_edge_keep_fa_children_in_universe (u v parent: V) (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (fun s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v) (W x)
                     (fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)) ->
    Hoare (fun s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)
          (process_edge u W v)
          (fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
```

然后在 `forset` 级别利用 `Hoare_forset` 将此性质传播到所有递归调用。

此引理的证明：
- `set_fa v u`：如果 `parent ≠ v` 且 `fa s v = parent`，则 `set_fa v u` 后 `fa` 对 v 变为 `u`。如果 `parent = u`，则新创建的 fa 关系仍然满足（`dg_step g u v` 是当前处理的边）。如果 `parent ≠ u` 且 `parent ≠ v`，则 fa 不变。
- 其他操作（`W x`、`update_low` 等）不修改 fa，所以 property 不变。

---

## Layer 6: `forset_keep_low_forset_inv` base case admit (line 2075)

### 问题分析
在 `forset_keep_low_forset_inv` 的 forset 归纳基始情况中：
```coq
intro_state. split; [exact H | split].
+ unfold done_visited. intros v Hv_empty. exfalso. exact Hv_empty.
+ intros v [Hfa_eq Hfa_neq]. exfalso.
  (* Initially fa s v = v (identity, preloop doesn't set fa).
     From Hfa_eq: v = u, then Hfa_neq contradicts u ≠ u. *)
  admit.
```

`H` 是 `low_forset_inv u ∅ s`。需要证明：`(forall v, fa s v = u /\ fa s v <> v -> dg_step g u v)` 在前置状态下空洞成立（因为没有 proper child of u）。

### 策略

**方案 A（推荐）**：新增引理证明 preloop 之后 fa 保持 identity：

```coq
Lemma preloop_keeps_fa_init (u: V):
  Hoare (fun s => forall v, fa s v = v)
        (preloop u)
        (fun _ s => forall v, fa s v = v).
```

证明：`preloop` 只调用 `set_fa u u`，对 identity fa 这是 no-op。

然后在 `tarjan_scc_keep_low_valid` 中（调用 `forset_keep_low_forset_inv` 的地方），联合 `preloop_establishes_low_forset_inv` 和 `preloop_keeps_fa_init`：

```coq
eapply Hoare_bind.
{ apply Hoare_conj.
  - apply Hoare_conseq_pre with (P2 := fun s => low_pre x s).
    { intros s HP. exact HP. }
    apply preloop_establishes_low_forset_inv.
  - apply Hoare_conseq_pre with (P2 := fun s => True).
    { intros s _. apply initSt_fa_init. }  (* 需要一条 initSt 引理 *)
    apply preloop_keeps_fa_init. }
```

然后在 `forset_keep_low_forset_inv` 中增加一个前置条件或修改 P：

```coq
set (P := fun (done: V -> Prop) (s: SCCSt) =>
    low_forset_inv u done s /\ done_visited done s /\
    (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) /\
    (forall v, fa s v = v \/ exists w, w ∈ done /\ fa s v = w /\ fa s v <> v)).
```

**方案 B（更简单但不完美）**：直接证明 `forall v, fa s v = v` 来自 `low_forset_inv` 中已有的 `dfn_inv` + `fa_visited` + `initSt` 属性。这需要新增引理：

```coq
Lemma low_pre_fa_identity (s: @SCCSt V) (u: V):
  low_pre u s -> forall v, fa s v = v.
```

从 `low_pre` 的定义：`~ u ∈ visited s` + `dfn_inv s` + ...。`dfn_inv` 说 `dfn s v = 0 ↔ ~ v ∈ visited s`。初始状态 `initSt` 有 `fa v = v` 且只有 `preloop` 可能修改它（`set_fa u u` 不改变 u 的 fa，因为 fa u 已经是 u）。

这条引理需要 `initSt` 上 `fa` identity 在 `low_pre` 状态中保持不变——但 `low_pre` 是 `preloop` 的前置条件，`preloop` 之前的状态已经经过了未知数量的 `tarjan_scc` 调用（在 `tarjan_scc_all` 中）。

**更精细的分析**：在 `tarjan_scc_keep_low_valid` 被调用时，其前置条件是 `low_pre u s`。该状态可能来自 `tarjan_scc_all` 中的某次迭代，此时某些其他顶点的 fa 可能已被修改（作为 tree child of 之前的 root）。所以 `fa s v = v` 不一定全局成立。

但在 base case of `forset`，我们只关心 `fa s v = u` 的情况。`fa s v = u` 且 v ≠ u 时，需要 edge u→v。此时状态在 `preloop u` 之后、首次进入 forset 之前。fa 尚未被 `process_edge` 修改（因为 process_edge 修改的 fa 都以当前 forset center 为目标）。因此对 u 来说，目前没有任何 proper child。

**最终推荐方案 C**（针对 base case 的局部修复）：

```coq
(* 引理：low_pre 状态中 u 未 visited，所以没有 v 满足 fa s v = u 且 fa s v ≠ v *)
Lemma low_pre_no_fa_child_of_u (u: V) (s: @SCCSt V):
  low_pre u s -> forall v, ~ (fa s v = u /\ fa s v <> v).
```

证明：由 `low_pre` 我们有 `~ u ∈ visited s` 和 `fa_visited s`（`forall v, v ∈ visited s -> fa s v ∈ visited s`）。对任意 v：
- 若 `v ∈ visited s`：则 `fa s v ∈ visited s`。但 `fa s v = u` 且 `~ u ∈ visited s`，矛盾。
- 若 `~ v ∈ visited s`：则需要论证 `fa s v = v`（未 visited 顶点的 fa 保持 identity）— 这来自初始状态性质。

```coq
Lemma unvisited_fa_identity (s: @SCCSt V) (v: V):
  dfn_inv s -> ~ v ∈ visited s -> fa s v = v.
```

**注意**：这条引理需要 `dfn_inv` 配合算法的其他不变量才能证明。或者可以通过 `initSt` → `fa = identity` 以及所有修改 fa 的操作（`set_fa`）都要求 target 已被 visited 来论证。这个性质应该在 `Tarjan_scc_basics.v` 或 `Tarjan_scc_is_dfn.v` 中已经隐含。

综上，base case 的最简证明：

```coq
intros v [Hfa_eq Hfa_neq].
destruct H as [Hsiv [Hinv [Hvalid [Hfa_vis [Huvis Hmin]]]]].
destruct Hinv as [Hlt [Hiff Hpos]].
(* 若 v ∈ visited s：fa_visited 给出 fa s v ∈ visited s，
   即 u ∈ visited s，但 Hiff 和 ~ u ∈ visited s 矛盾。
   若 v ∉ visited s：需要 fa s v = v。
   若 fa s v = v 且 fa s v = u，则 v = u，与 fa s v ≠ v 矛盾。 *)
destruct (classic (v ∈ visited s)) as [Hvis_v | Hnot_vis_v].
- apply Hfa_vis in Hvis_v. rewrite Hfa_eq in Hvis_v.
  exfalso. apply (proj2 (Hiff u)). split; [| exact Huvis]. auto.
- (* v ∉ visited s → fa s v = v *)
  assert (Hfa_id: fa s v = v). {
    (* 需要 unvisited_fa_identity 引理 *)
    apply (unvisited_fa_identity s v Hinv Hnot_vis_v).
  }
  rewrite Hfa_id in Hfa_eq. subst v.
  apply Hfa_neq. reflexivity.
```

---

## Layer 7: `forset_keep_low_forset_inv` (line 2076, Admitted)

### 策略
修复所有内部 admit 后，此引理完成。主要包括：
1. layer 6 的 base case admit
2. `process_edge_keep_low_forset_inv` 的集成（layer 2-4）
3. `tarjan_scc_keep_fa_children_in_universe` 的集成（layer 5）

---

## Layer 8: `tarjan_scc_all_scc_low_valid` (line 2139)

### 问题分析
```coq
Theorem tarjan_scc_all_scc_low_valid:
    Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
          (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
          (fun _ s => scc_low_valid s).
```

### 策略
参考 `Tarjan_scc_is_dfn.v` 中已证的 `tarjan_scc_all_dfn_valid`：

```coq
Theorem tarjan_scc_all_dfn_valid:
  Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
        (tarjan_scc_all g)
        (fun _ s => dfn_valid g s root).
```

证明结构：
1. `tarjan_scc_all` 对 `original_listV g` 中每个顶点 `v` 调用 `tarjan_scc g v`（仅当 `v ∉ visited s`）
2. 对每个 `v ∈ original_listV g`，`tarjan_scc_keep_low_valid v` 给出 `scc_low_valid_v s v`（前提：`low_pre v s`）
3. 通过归纳组合：`scc_low_valid s`（对所有 visited 顶点的 `scc_low_valid_v`）

核心证明：
```coq
Proof.
  unfold tarjan_scc_all.
  (* 使用 Hoare_for 对 original_listV g 中的每个顶点迭代 *)
  eapply Hoare_for with
    (P := fun (_: V) (s: SCCSt) => scc_low_valid s /\ dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
    (body := fun v => if_ (fun s => negb (equiv_decb v v ∈ visited s)) 
                        (tarjan_scc (V:=V) (E:=E) g v) skip).
  ...
```

具体证明可完全参照 `Tarjan_scc_is_dfn.v` 中 `tarjan_scc_all_dfn_valid` 和 `tarjan_scc_all_scc_dfn_valid` 的证明模式。

`tarjan_scc_all_scc_is_low`（line 2141-2165）已通过 `scc_low_valid_implies_is_low`（line 219-243，**已证**）完成，只依赖 `tarjan_scc_all_scc_low_valid`。

---

## 实施顺序

### Phase 1：基础设施

1. **新增 `unvisited_fa_identity` 引理**（位置：`Tarjan_scc_is_low.v` 或 `Tarjan_scc_basics.v`）
   - `dfn_inv s -> ~ v ∈ visited s -> fa s v = v`

2. **新增 `preloop_keeps_fa_init` 引理**（位置：`Tarjan_scc_basics.v`）
   - `Hoare (fun s => forall v, fa s v = v) (preloop u) (fun _ s => forall v, fa s v = v)`

3. **新增 `low_pre_no_fa_child_of_u` 引理**（位置：`Tarjan_scc_is_low.v`）
   - `low_pre u s -> forall v, ~ (fa s v = u /\ fa s v <> v)`

### Phase 2：修复 `popped_vertex_low_eq_dfn`（line 1166）

4. 使用 `low_forset_inv` 结构或新增 `visited_not_on_stack_low_eq_dfn` 不变量证明此引理。

### Phase 3：修复 `process_edge_keep_low_forset_inv` 内部 admits

5. **Line 1352** (`all: admit.` tree edge 分支):
   - 将 `all: admit` 替换为具体子目标证明，主要使用 `update_low_tree_edge`

6. **Line 1429** (`admit.` skip 分支 fa=u):
   - 使用 `low_forset_inv_children_done_low_le` 证明 `low s0 u ≤ low s0 v`
   - 使用 `min_value_of_subset_nested_update_left_nat` 处理集合扩展

7. **Line 1651** (`admit.` proper child, v not on stack):
   - 使用 `tree_child_low_le`（修复后）证明 `low s0 u ≤ low s0 v`
   - 使用 `min_value_of_subset_nested_update_left_nat` 处理集合扩展

8. 完成 `process_edge_keep_low_forset_inv`（line 1705）

### Phase 4：修复 `tarjan_scc_keep_fa_children_in_universe`（line 1866）

9. 通过 fixpoint induction 或组合已有引理证明

### Phase 5：修复 `forset_keep_low_forset_inv`（line 2075-2076）

10. 使用 Phase 1 的引理修复 base case admit
11. 集成所有子组件

### Phase 6：修复 `tarjan_scc_all_scc_low_valid`（line 2139）

12. 参照 `tarjan_scc_all_dfn_valid` 的证明模式完成

---

## 风险与注意事项

1. **`popped_vertex_low_eq_dfn` 是最困难的 admit**。它的完整证明需要对算法的栈行为做归纳推理。如果 Phase 2 受阻，可以考虑：
   - 在 `tree_child_low_le` 中绕过此引理，改用 `low_forset_inv_children_done_low_le`（不需要 `~ In v (stack s)` 前提）
   - 修改 `tree_child_low_le` 的前提条件，使其从 `low_forset_inv` 而非 `popped_vertex_low_eq_dfn` 推导结论

2. **`visited_tag` 扩展的兼容性**：如果选择通过 fixpoint induction 证明 `tarjan_scc_keep_fa_children_in_universe`，需要扩展 `visited_tag` inductive type。这与已有的 `tarjan_scc_keep_low_valid` 中的 `visited_tag` 使用兼容。

3. **`low_forset_inv` 修改的影响面**：如果将 `visited_not_on_stack_low_eq_dfn` 融入 `low_forset_inv`，需要同步修改所有使用此不变量的引理（`preloop_establishes_low_forset_inv`、`update_low_tree_edge`、`update_low_back_edge`、`update_low_back_edge_fa_neq`、`process_edge_keep_low_forset_inv`、`forset_keep_low_forset_inv`）。修改量较大但结构清晰。

4. **`SCCSt` 结构的 fa 域**：`initSt` 的 fa 是 identity (`fun v => v`)。只有 `set_fa` 操作修改 fa。`set_fa v p` 将 `fa s v` 设为 `p`。在 `process_edge` 中，tree edge 分支调用 `set_fa v u`（将 v 设为 u 的 child）；其他分支不修改 fa。这保证了 fa 只从 identity 变为某个已 visited 顶点的值。
