# Tarjan_scc_is_low.v 剩余 Admit 修复方案
**Author**: Claude
**Date**: 2026-06-20

## 概述

经过 Phase 1-3 的修复，`Tarjan_scc_is_low.v` 中的 admit 数量已大幅减少。本文档列出所有剩余 admit，按依赖顺序给出修复方案。

## 当前 admit 清单（共 11 处）

| # | 行号 | 位置 | 类型 |
|---|------|------|------|
| 1 | ~1462 | `pop_scc_preserves_ancestor_inv` min condition | admit |
| 2 | ~1647 | `W_preserves_ancestor_inv` | Admitted（依赖 #1） |
| 3 | ~1272 | `popped_vertex_low_eq_dfn` | Admitted |
| 4 | ~1777 | `process_edge_keep_low_forset_inv` tree edge `all:` | admit（依赖 #2） |
| 5 | ~1854 | `process_edge_keep_low_forset_inv` skip fa=u | admit |
| 6 | ~2076 | `process_edge_keep_low_forset_inv` proper child | admit（依赖 #3） |
| 7 | ~2130 | `process_edge_keep_low_forset_inv` | Admitted（依赖 #4-6） |
| 8 | ~2291 | `tarjan_scc_keep_fa_children_in_universe` | Admitted |
| 9 | ~2468 | `forset_keep_low_forset_inv` fa_child step case | admit |
| 10 | ~2522 | `forset_keep_low_forset_inv` | Admitted（依赖 #7-9） |
| 11 | ~2596 | `tarjan_scc_all_scc_low_valid` | Admitted（依赖 #10） |

## 依赖关系图

```
#11 tarjan_scc_all_scc_low_valid
  └─ #10 forset_keep_low_forset_inv
       ├─ #7 process_edge_keep_low_forset_inv
       │    ├─ #4 tree edge all:
       │    │    └─ #2 W_preserves_ancestor_inv
       │    │         └─ #1 pop_scc min condition  ← 最优先修复
       │    ├─ #5 skip fa=u
       │    └─ #6 proper child
       │         └─ #3 popped_vertex_low_eq_dfn
       ├─ #8 tarjan_scc_keep_fa_children_in_universe
       └─ #9 fa_child step case
```

---

## Admit #1: pop_scc_preserves_ancestor_inv min condition

**优先级**: ⭐⭐⭐ 最高（阻塞 #2 → #4 → #7 → #10 → #11 整条链）

**当前代码**:
```coq
unfold children_done, back_edges_done. cbv. cbv in Hmin.
(* After cbv: goal uses 'rest', Hmin uses 'stack s0' *)
admit.
```

**问题**: `cbv` 展开 RecordUpdate 后，目标中的 `back_edges_done` 使用 `rest`（pop 后的栈），而 `Hmin` 使用 `stack s0`（原始栈）。需要证明两者等价。

**修复方案**: 在 `Tarjan_scc_basics.v` 中添加引理：

```coq
Lemma stack_split_at_popped_fresh {V: Type} (stk: list V) (v: V):
  forall (popped rest: list V),
    stack_split_at stk v = (popped, rest) ->
    forall w, In w stk -> ~ In w popped -> In w rest.
```

然后在 `pop_scc_preserves_ancestor_inv` 的证明中用 `min_eq_forward` + `Sets_equiv_Sets_included` 建立两个 `back_edges_done` 集合的等价性：

```coq
assert (Hback_eq: (fun w => done w /\ In w rest /\ fa s0 w <> u) ==
                  (fun w => done w /\ In w (stack s0) /\ fa s0 w <> u)).
{ apply Sets_equiv_Sets_included. split.
  - intros w [Hd [Hin Hfa]]. split; [exact Hd | split;
      [eapply stack_split_at_rest_incl; eauto | exact Hfa]].
  - intros w [Hd [Hin Hfa]]. split; [exact Hd | split;
      [eapply stack_split_at_popped_fresh; eauto. 
       (* done vertices are not in popped: they were processed before v *) | exact Hfa]]. }
eapply min_eq_forward; [typeclasses eauto | exact Hmin | | ].
(* forward/backward directions: use Hback_eq to map witnesses *)
```

**预计工作量**: 1 个新引理 + 修改 1 处 admit。

---

## Admit #2: W_preserves_ancestor_inv

**优先级**: ⭐⭐⭐ 自动修复

**当前代码**: `Admitted.`

**问题**: 该引理仅组合 `preloop_preserves_ancestor_inv`（✅ Qed）、`process_edge_preserves_ancestor_inv`（✅ Qed）、`pop_scc_preserves_ancestor_inv`（⚠️ #1）。一旦 #1 修复，只需将 `Admitted.` 改为 `Qed.`。

**预计工作量**: 0（自动修复）。

---

## Admit #3: popped_vertex_low_eq_dfn

**优先级**: ⭐⭐

**当前代码**:
```coq
Lemma popped_vertex_low_eq_dfn (s: @SCCSt V) (v: V):
    dfn_inv s -> v ∈ visited s -> ~ In v (stack s) -> low s v = dfn s v.
Proof. Admitted.
```

**问题**: 该引理声称所有 visited 但不在栈上的顶点满足 `low = dfn`。这在一般情况下不对（非 SCC 根的顶点 `low ≠ dfn`），但在其使用上下文（`tree_child_low_le`）中是正确的（v 是 u 的 tree child，不在栈上意味着 v 的 SCC 已独立完成，v 是 SCC root）。

**修复方案**: 将引理修改为带更强前提的形式：

```coq
Lemma tree_child_popped_low_eq_dfn (u v: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s ->
    fa s v = u -> fa s v <> v ->
    ~ In v (stack s) ->
    low s v = dfn s v.
```

证明思路：从 `low_forset_inv u done s` 可知 `stack_in_visited s`。从 `fa s v = u` 可知 v 是 u 的 tree child。结合 `~ In v (stack s)` 可知 v 的 SCC 已独立弹出（若 v 与 u 在同一 SCC，v 仍在栈上）。因此 `pop_scc v` 被调用，其前置条件 `low v = dfn v` 在 pop 时成立。pop 后 low/dfn 不变，故当前状态 `low s v = dfn s v`。

**预计工作量**: 1 个修改引理 + 更新 1 处使用点。

---

## Admit #4: process_edge tree edge `all:`

**优先级**: ⭐⭐⭐（被 #2 阻塞）

**当前代码**:
```coq
hoare_auto_s.
unfold update_low. hoare_auto_s.
all: admit.
```

**问题**: tree edge 分支调用 `set_fa v u;; W v;; get' low v;; update_low u (low v)` 后需要证明 `low_forset_inv u (done ∪ [v]) s'`。

**修复方案**: 一旦 #1+#2 完成（`set_fa_W_preserves_low_forset_inv` 已 Qed），tree edge 的两个 subgoal 可直接使用：
- **Subgoal 1** (`low v < low u` → `set_low`): 应用 `update_low_tree_edge`，前提 `low_forset_inv u done s1`、`fa s1 v = u`、`fa s1 v ≠ v` 由 `set_fa_W_preserves_low_forset_inv` 提供。
- **Subgoal 2** (`~low v < low u` → skip): 应用 `low_forset_inv_expand_child_done`（✅ 已证明），前提同上。

**预计工作量**: 替换 `all: admit` 为两个子目标的具体证明（约 10 行）。

---

## Admit #5: process_edge skip fa=u

**优先级**: ⭐⭐

**当前代码**:
```coq
- (* fa s0 v = u: needs low s0 u ≤ low s0 v *)
  admit.
```

**问题**: 在 non-tree edge 的 skip 分支中，`fa s0 v = u`（v 是 u 的 proper child），需证明 min condition 在 `done` 扩展 `[v]` 后保持不变。关键是需要 `low s0 u ≤ low s0 v`。

**修复方案**: 使用 `low_forset_inv_children_done_low_le`（✅ 已证明），但需要 `children_done s0 u done v`，即 `v ∈ done`。需要证明在此上下文中 v 已被添加到 done（因为 tree edge 已在之前处理过）。

添加引理：
```coq
Lemma fa_eq_u_implies_in_done (u v: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s ->
    fa s v = u -> fa s v <> v ->
    v ∈ done.
```

证明思路：`fa s v = u` 意味着 v 是通过 u 的 tree edge 发现的。在 forset 中，每个 tree edge 处理后会将 child 加入 done。当前 non-tree 分支处理的是同一条边的第二次出现（不同 label），此时 v 已在 done 中。

**预计工作量**: 1 个新引理 + 修改 1 处 admit。

---

## Admit #6: process_edge proper child

**优先级**: ⭐（被 #3 阻塞）

**当前代码**:
```coq
assert (Hlow_le: low s0 u <= low s0 v)
  by (apply (tree_child_low_le u v done s0); ...).
admit.
```

**问题**: `tree_child_low_le` 依赖 `popped_vertex_low_eq_dfn`（#3）。一旦 #3 修复，此处的 `admit` 可以使用 `min_value_of_subset_nested_update_left_nat` + `low_forset_inv_expand_child_done` 来解决。

**预计工作量**: 依赖 #3，修复后约 15 行证明。

---

## Admit #7: process_edge_keep_low_forset_inv

**优先级**: ⭐⭐（依赖 #4-6）

**当前代码**: `Admitted.`

**问题**: 整个引理因内部 admits 未完成。一旦 #4、#5、#6 修复，`Admitted.` 改为 `Qed.`。

**预计工作量**: 0（自动修复）。

---

## Admit #8: tarjan_scc_keep_fa_children_in_universe

**优先级**: ⭐⭐

**当前代码**: `Admitted.`

**问题**: 需证明 `tarjan_scc` 保持 `fa_children_in_universe` 性质。

**修复方案 A（推荐）**: 通过 fixpoint induction，添加新的 `visited_tag` 构造函数 `VKeepFaChildrenUniverse`，类似于已有的 `VKeepFaChildren`。

**修复方案 B**: 直接写一个 Hoare 引理：
```coq
Lemma tarjan_scc_keep_fa_children_in_universe_proof (parent a: V):
    Hoare (fun s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)
          (tarjan_scc g a)
          (fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
```

对 `tarjan_scc g a` 做结构分解：`preloop a` 不改 fa；`forset` 中 `process_edge a W x` 的 tree edge 分支调用 `set_fa x a`，此时 `dg_step g a x` 成立；递归调用 `W x` 不改对 parent 的 fa 关系；`pop_scc a` 不改 fa。

**预计工作量**: 方案 A（1 个新 visited_tag + 相关证明），方案 B（1 个新引理，约 30 行）。

---

## Admit #9: forset_keep_low_forset_inv fa_child step case

**优先级**: ⭐⭐

**当前代码**:
```coq
{ (* fa_children_are_done preserved *)
  admit. }
```

**问题**: 在 forset 的 step case 中，需要证明 `process_edge u W a` 保持 `fa_children_are_done u (done ∪ [a])`（即 `fa w = u → w = u ∨ children_done (done ∪ [a]) w`）。

**修复方案**: 添加引理：
```coq
Lemma process_edge_keep_fa_children_are_done (u a: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit):
    dg_step g u a ->
    Hoare (fun s => forall v, fa s v = u -> v = u \/ children_done s u done v)
          (process_edge u W a)
          (fun _ s => forall v, fa s v = u -> v = u \/ children_done s u (done ∪ [a]) v).
```

证明：`process_edge` 中仅 tree edge 分支调用 `set_fa a u`，此时 `fa a = u` 且 `a ∈ done ∪ [a]` 满足 `children_done`。递归 `W a` 不改 fa 为 u 的顶点（只设 fa 为 a 或后代）。back edge / cross edge 不改 fa。

**预计工作量**: 1 个新引理 + 替换 1 处 admit。

---

## Admit #10-11: 顶层引理

**优先级**: ⭐

- `forset_keep_low_forset_inv`（#10）: Admitted，依赖 #7-9。
- `tarjan_scc_all_scc_low_valid`（#11）: Admitted，依赖 #10。

均为自动修复（内部 admit 解决后改为 Qed）。

---

## 修复顺序建议

```
Step 1: #1 pop_scc min → 解锁 #2 W_preserves → 解锁 #4 tree edge
Step 2: #4 tree edge + #5 skip fa=u + #3 popped_vertex (→ #6 proper child)
         → 解锁 #7 process_edge
Step 3: #8 fa_children + #9 fa_child step
         → 解锁 #10 forset → 解锁 #11 tarjan_scc_all
```

### 工作量估算

| Step | 新增引理 | 修改 admit | 难度 |
|------|---------|-----------|------|
| 1 | 1 (`stack_split_at_popped_fresh`) | 2 处 | 低 |
| 2 | 2 (`fa_eq_u_implies_in_done`, `tree_child_popped_low_eq_dfn`) | 3 处 | 中 |
| 3 | 2 (`process_edge_keep_fa_children_are_done`, `tarjan_scc_keep_fa_children_in_universe`) | 2 处 | 中 |

**总计**: 5 个新引理 + 7 处 admit → 0 处 admit。

---

## 已完成的引理（供参考）

| 引理 | 状态 | 用途 |
|------|------|------|
| `low_pre_fa_eq_u_implies_eq_u` | ✅ Qed | Phase 1，forset base case |
| `low_pre_no_fa_child_of_u` | ✅ Qed | Phase 1 |
| `low_forset_inv_expand_child_done` | ✅ Qed | tree edge skip 分支（#4 subgoal 2） |
| `set_fa_W_preserves_low_forset_inv` | ✅ Qed | tree edge 分支（#4） |
| `process_edge_preserves_ancestor_inv` | ✅ Qed | `W_preserves_ancestor_inv` 的组件 |
| `preloop_preserves_ancestor_inv` | ✅ Qed | `W_preserves_ancestor_inv` 的组件 |
