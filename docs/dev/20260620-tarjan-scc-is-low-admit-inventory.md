# Tarjan_scc_is_low.v 当前 Admit 盘点与阻塞分析
**Author**: Kimi Code
**Date**: 2026-06-20
**Last reviewed**: 2026-06-20（已根据当前 HEAD 修正依赖关系与若干事实错误）

## 背景

`SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v` 正在证明 Tarjan SCC 算法中 `low` 值的正确性：对任意已访问顶点 `u`，`low u` 等于从 `u` 出发通过树边和至多一条回边可达的顶点的最小 `dfn`。该文件是 `Tarjan_scc` 单调正确性证明链的最后一环，当前仍有 **12 处 admit/Admitted** 未闭合。

本文档基于文件当前 HEAD 状态，逐条列出未闭合位置、引理语句、阻塞关系与修复优先级，供后续 proving/annotation 轮次作为 issue 跟踪使用。

---

## 当前 Admit 清单（12 处）

| # | 行号 | 类型 | 所在引理/定理 | 说明 |
|---|------|------|---------------|------|
| 1 | 1365 | `Admitted.` | `popped_vertex_low_eq_dfn` | 核心不变量：已弹出栈顶点满足 `low = dfn` |
| 2 | 1555 | `admit.` | `pop_scc_preserves_ancestor_inv` 内部 | `back_edges_done` 在 `stack_split_at` 前后集合等价 |
| 3 | 1558 | `Admitted.` | `pop_scc_preserves_ancestor_inv` | 依赖 #2 |
| 4 | 1766 | `Admitted.` | `process_edge_preserves_ancestor_inv` | `process_edge` 保持祖先 `low_forset_inv` 与 `fa` 关系 |
| 5 | 1781 | `Admitted.` | `W_preserves_ancestor_inv` | `W v`（即 `tarjan_scc g v`）保持祖先不变量 |
| 6 | 2014 | `admit.` | `process_edge_keep_low_forset_inv` skip 分支 | `fa s0 v = u` 时需 `low s0 u ≤ low s0 v` |
| 7 | 2236 | `admit.` | `process_edge_keep_low_forset_inv` cross edge 分支 | 集合扩展后 nested min 不变 |
| 8 | 2290 | `Admitted.` | `process_edge_keep_low_forset_inv` | 依赖 #6、#7（以及 tree edge 子目标） |
| 9 | 2451 | `Admitted.` | `tarjan_scc_keep_fa_children_in_universe` | `tarjan_scc` 保持 `fa` 子节点在图边宇宙中 |
| 10 | 2628 | `admit.` | `forset_keep_low_forset_inv` step case | `fa_children_are_done` 在 `process_edge` 后保持 |
| 11 | 2682 | `Admitted.` | `forset_keep_low_forset_inv` | 依赖 #8、#9、#10 |
| 12 | 2756 | `Admitted.` | `tarjan_scc_all_scc_low_valid` | 顶层定理，依赖 #11 |

---

## 依赖关系图

```
#12 tarjan_scc_all_scc_low_valid (2756)
  └─ tarjan_scc_keep_low_valid (2684–2745, 已 Qed 但依赖 #9、#11)
       ├─ #11 forset_keep_low_forset_inv (2682)
       │    ├─ #8 process_edge_keep_low_forset_inv (2290)
       │    │    ├─ 树边分支 → set_fa_W_preserves_low_forset_inv (1799, 已 Qed)
       │    │    │              └─ #5 W_preserves_ancestor_inv (1781)
       │    │    │                   ├─ #4 process_edge_preserves_ancestor_inv (1766)
       │    │    │                   └─ #3 pop_scc_preserves_ancestor_inv (1558)
       │    │    │                        └─ #2 stack_split_at min equivalence (1555)
       │    │    ├─ #6 skip fa=u (2014)：需要新的时序/集合引理
       │    │    └─ #7 cross edge proper child (2236)
       │    │         └─ #1 popped_vertex_low_eq_dfn (1365)
       │    ├─ #10 fa_children_are_done step case (2628)
       │    └─ #9 tarjan_scc_keep_fa_children_in_universe (2451) 的 IH
       └─ #9 tarjan_scc_keep_fa_children_in_universe (2451) 的 fixpoint conjunct
```

**关键路径**：
- #1 → #7 → #8（cross edge 分支）
- #2 → #3 → #5 → `set_fa_W_preserves_low_forset_inv` → #8（树边分支）
- #6 → #8（back-edge skip 分支，独立路径）
- #9、#10 → #11 → #12

**注意**：旧版依赖图把 #6 错误地标成依赖 #5；实际上 #6 处于 back-edge skip 分支，不调用 `W`，因此不依赖 `W_preserves_ancestor_inv`。真正依赖 #5 的是 #8 的**树边分支**（通过已 Qed 的 `set_fa_W_preserves_low_forset_inv` 传递）。

---

## 逐条分析

### #1 `popped_vertex_low_eq_dfn`（line 1365）

```coq
Lemma popped_vertex_low_eq_dfn (s: @SCCSt V) (v: V):
  dfn_inv s -> v ∈ visited s -> ~ In v (stack s) ->
  low s v = dfn s v.
```

**语义**：已被 visited 但不在当前栈上的顶点，其 `low` 值等于自身 `dfn`。该命题在通用形式下**并不显然成立**（非 SCC 根顶点被弹出时 `low` 通常等于 SCC 根的 `dfn`），但在本文件的使用场景（`tree_child_low_le`，其中 `v` 是 `u` 的 proper tree child 且已不在栈上）中，意味着 `v` 所在 SCC 已独立完成，`v` 是 SCC 根。

**阻塞**：#7（cross edge 分支需 `low s u ≤ low s v`，而 `low s v = dfn s v`）。

**修复方向**：
1. 弱化引理前提，改为 `tree_child_popped_low_eq_dfn`，要求 `fa s v = u`、`fa s v ≠ v` 与 `low_forset_inv u done s`；或
2. 新增全局不变量 `visited_not_on_stack_low_eq_dfn`，在 `preloop`/`set_fa`/`update_low`/`pop_scc` 上证明保持性。

---

### #2 `#3 `pop_scc_preserves_ancestor_inv`（lines 1555, 1558）

```coq
Lemma pop_scc_preserves_ancestor_inv (u v: V) (done: V -> Prop):
  Hoare (fun s => low_forset_inv u done s /\ fa s v = u)
        (pop_scc v)
        (fun _ s => low_forset_inv u done s /\ fa s v = u).
```

**内部 admit（#2）**：`cbv` 展开 `back_edges_done` 后，目标中的栈为 `rest`（`stack_split_at` 返回的后半段），而假设 `Hmin` 中的栈为 `stack s0`。需要证明对 `done` 中顶点，`In w rest ↔ In w (stack s0)`。

**所需辅助引理**：
```coq
Lemma stack_split_at_popped_fresh {V: Type} (stk: list V) (v: V):
  forall (popped rest: list V),
    stack_split_at stk v = (popped, rest) ->
    forall w, In w stk -> ~ In w popped -> In w rest.
```

修复 #2 后，#3 可改为 `Qed`。

---

### #4 `#5 `process_edge_preserves_ancestor_inv` / `W_preserves_ancestor_inv`（1766, 1781）

```coq
Lemma process_edge_preserves_ancestor_inv (u v x: V) (done: V -> Prop) (W: ...)
  (HW: forall x, Hoare (fun s => low_pre x s /\ v ∈ visited s) (W x)
                      (fun _ s => low_post x s /\ v ∈ visited s)):
  u <> v -> ~ done v -> dg_step g v x ->
  Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ v ∈ visited s)
        (process_edge v W x)
        (fun _ s => low_forset_inv u done s /\ fa s v = u).

Lemma W_preserves_ancestor_inv (u v: V) (done: V -> Prop) (W: ...):
  Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v)
        (W v)
        (fun _ s => low_forset_inv u done s /\ fa s v = u).
```

**语义**：祖先 `u` 的 `low_forset_inv` 与 `fa s v = u` 关系，在递归调用 `W v`（即 `tarjan_scc v`）前后保持不变。

**阻塞**：#8 的**树边分支**（`process_edge_keep_low_forset_inv` line 1907 调用 `set_fa_W_preserves_low_forset_inv`，后者在 line 1878 调用 `W_preserves_ancestor_inv`）。#6（skip fa=u）**不**依赖本组引理。

**修复方向**：
- `process_edge_preserves_ancestor_inv` 需按 tree/back/cross edge 分支分析，验证 `set_fa`/`W`/`update_low` 不修改 `u` 的 `low`、不破坏 `fa s v = u`。
- `W_preserves_ancestor_inv` 依赖 #3（`pop_scc` 保持）与 `process_edge_preserves_ancestor_inv`。
- 也可考虑直接把 `set_fa_W_preserves_low_forset_inv` 拆开，在 `process_edge_keep_low_forset_inv` 的树边分支里内联证明，从而绕开这组祖先保持引理。

---

### #6 `#7 `#8 `process_edge_keep_low_forset_inv`（2014, 2236, 2290）

```coq
Lemma process_edge_keep_low_forset_inv (u v: V) (done: V -> Prop) (W: ...):
  ~ done v -> dg_step g u v ->
  Hoare (fun s => low_forset_inv u done s)
        (process_edge u W v)
        (fun _ s => low_forset_inv u (done ∪ [v]) s).
```

**内部 admit（#6，line 2014）**：non-tree edge 的 skip 子分支中，`fa s0 v = u` 时需要 `low s0 u ≤ low s0 v`。当前 `tree_child_low_le` 要求 `~ In v (stack s)`，但此处 `v` 在栈中，故 `tree_child_low_le` **不适用**。

**修复**：
- 方案 A（推荐）：证明当 `fa s0 v = u` 且 `v` 已 visited 时，`v` 必已在 `done` 中（同一条边的 tree-edge 出现先于 back-edge 出现被处理），然后使用 `low_forset_inv_children_done_low_le`。
- 方案 B：通过时序论证，tree-edge 处理时已经执行过 `update_low u (low v)`，后续 `update_low` 只降不升，因此 `low u ≤ low v` 保持。

**注意**：#6 **不**依赖 #5 `W_preserves_ancestor_inv`；不要把 #6 放到祖先保持引理的修复链里。

**内部 admit（#7，line 2236）**：cross edge 分支（`~ In v (stack s)` 且 `fa s0 v = u`）需证明 `children_done` 扩展 `[v]` 后 nested min 仍为 `low s0 u`。依赖 #1 给出 `low s0 v = dfn s0 v`，以及 `min_value_of_subset_nested_update_left_nat` 处理集合扩展。

**树边分支的隐藏依赖**：`process_edge_keep_low_forset_inv` 的树边分支（line 1907）调用 `set_fa_W_preserves_low_forset_inv`（已 Qed），但后者在 line 1878 调用 `W_preserves_ancestor_inv`（#5，Admitted）。因此 #8 闭合前必须同时解决 #5、#6、#7。

---

### #9 `tarjan_scc_keep_fa_children_in_universe`（line 2451）

```coq
Lemma tarjan_scc_keep_fa_children_in_universe (parent a: V):
  Hoare (fun s: @SCCSt V => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)
        (tarjan_scc g a)
        (fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
```

**语义**：`tarjan_scc` 保持“proper child 的 `fa` 关系必须对应真实图边”。

**修复方向**：
- `visited_tag` 已包含 `VKeepFaChildren parent`，且 `tarjan_scc_keep_low_valid` 的 `Hoare_fix_logicv_conj` 调用（line 2694–2700）已经以 `VKeepFaChildren u` 作为第四个 conjunct。因此只需证明对应的 fixpoint 子目标，即本引理。
- 证明思路：对 `tarjan_scc` 做 fixpoint 归纳。`preloop` 不改 `fa`；`forset` 体内 `process_edge` 只在 tree-edge 分支调用 `set_fa a u`，而 `dg_step g u a` 正是本不变量要求；`pop_scc` 不改 `fa`。可能需要一个 `process_edge_keep_fa_children_in_universe` 辅助引理。

---

### #10 `#11 `forset_keep_low_forset_inv`（2628, 2682）

```coq
Lemma forset_keep_low_forset_inv (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                   (fun _ s => low_post x s /\ u ∈ visited s)) ->
  (forall a, Hoare (fun s => True) (W a) (fun _ s => a ∈ visited s)) ->
  (forall a done', Hoare (fun s => forall w, done' w -> w ∈ visited s) (W a)
                         (fun _ s => forall w, done' w -> w ∈ visited s)) ->
  (forall a, Hoare (fun s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) (W a)
                   (fun _ s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v)) ->
  Hoare (fun s => low_forset_inv u ∅ s /\ (forall v, fa s v = u -> v = u))
        (forset (fun v => dg_step g u v) (process_edge u W))
        (fun _ s => scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s).
```

**内部 admit（#10，line 2628）**：`process_edge` 的 tree edge 分支调用 `set_fa a u`，新增 `fa a = u` 关系，需要证明 `a ∈ done ∪ [a]` 满足 `children_done`。

**修复**：新增 `process_edge_keep_fa_children_are_done` 引理，分析 `process_edge` 中哪些操作会新增 `fa s v = u` 关系。

---

### #12 `tarjan_scc_all_scc_low_valid`（line 2756）

```coq
Theorem tarjan_scc_all_scc_low_valid:
  Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
        (tarjan_scc_all g)
        (fun _ s => scc_low_valid s).
```

**语义**：对图中所有顶点调用 `tarjan_scc` 后，每个已访问顶点都满足 `scc_low_valid_v`。

**修复方向**：参照 `Tarjan_scc_is_dfn.v` 中 `tarjan_scc_all_dfn_valid` 的证明结构，使用 `Hoare_for` 对 `original_listV g` 迭代，并在每次调用中应用 #11。

---

## 建议修复顺序

```
Step 1: 基础设施（零依赖，可并行）
  - 添加/证明 `stack_split_at_popped_fresh`（#2 所需）
  - 添加/证明 `fa_eq_u_implies_in_done` / `low_forset_inv_children_done_low_le`（#6 所需）
  - 选择并证明 #1 的修复路径（弱化引理 或 新增全局不变量）

Step 2: 自底向上闭合 admit
  #2 -> #3 -> #5（祖先保持链，供 #8 树边分支使用）
  #1 -> #7（#8 cross edge 分支）
  #6（#8 back-edge skip 分支，独立路径）
  #9、#10 并行

Step 3: 闭合 #8 与 #11
  (#5 + #6 + #7) -> #8
  (#8 + #9 + #10) -> #11

Step 4: 顶层闭合
  #11 -> #12
```

**重要**：在 #8 闭合前，必须同时确认树边分支通过 `set_fa_W_preserves_low_forset_inv` 隐式依赖的 #5 已被证明（或已用内联证明替换）。

---

## 风险与注意事项

1. **#1 的通用形式可能不成立**：若保持当前通用语句，需引入强全局不变量；推荐改为带 `fa s v = u` 与 `low_forset_inv` 前提的弱化版本。
2. **`low_forset_inv` 扩展成本**：若将 `visited_not_on_stack_low_eq_dfn` 融入 `low_forset_inv`，需同步修改 `preloop_establishes_low_forset_inv`、`update_low_tree_edge`、`update_low_back_edge` 等已闭合引理。
3. **`visited_tag` 已在使用**：`VKeepFaChildren` 已存在，且 `tarjan_scc_keep_low_valid` 的 fixpoint 调用已经以 `VKeepFaChildren u` 作为第四个 conjunct。#9 的修复只需完成该 conjunct 的证明，不必再调整 tag 架构。
4. **`set_fa_W_preserves_low_forset_inv` 是隐藏桥接点**：该引理已 `Qed`，但证明中调用 `W_preserves_ancestor_inv`（#5，Admitted）。 downstream agent 必须确认 #5 被证明，或选择内联替换 `set_fa_W_preserves_low_forset_inv`。
5. **禁止引入新 Axiom/Admitted**：所有修复最终必须改为 `Qed`，不能在 `common_case_formal_lib` 或 manual proof 文件中遗留额外公理。

---

## 相关文档

- `docs/dev/20260619-tarjan-scc-is-low-remaining-issues.md`：上一轮剩余 admit 修复方案（注意：该文档基于较早的 8-admit 状态，未包含当前新增的祖先保持引理 #3/#4/#5）
- `docs/dev/20260619-tarjan-scc-is-low-admit-fix-checklist.md`：逐层修复策略详细分析（同样基于较早状态，行号与当前 HEAD 不一致）
- `docs/dev/20260618-tarjan-scc-is-low-open-issues.md`：更早期的 open issue 汇总
