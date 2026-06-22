# Tarjan-scc-is-low.v Admit 关闭计划（更新版）

**Author**: Vitalrubbish
**Date**: 2026-06-21

## 1. 背景与范围

本计划针对当前 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`（共 3105 行）中仍未关闭的 `admit` / `Admitted` 进行审查，判断定理表述是否成立，并按依赖顺序给出关闭步骤。

> 说明：`docs/dev/20260621-tarjan-scc-is-low-admit-closure-plan.md` 是基于文件旧版本的计划，其中部分行号、引理状态与当前文件不一致（例如 `update_low_preserves_low_forset_inv_for_other` 已加入 `u <> v` 前提并已 `Qed`，`low_forset_inv_to_scc_low_valid` 已补充 `done_visited` 前提）。本计划根据当前文件内容重新整理。

该文件的目标：证明 Tarjan SCC 算法中每个已访问顶点的 `low` 值满足 `scc_is_low_v`，即 `low s u` 等于沿 DFS 树边再跟一条回边（或自身）能够到达的最小 `dfn`。

## 2. 当前 Admit 分布

| 行号 | 所在定理 | 形式 | 说明 |
|------|----------|------|------|
| 2579 | `W_preserves_ancestor_inv` | `admit` | `u = a` 分支 |
| 2628 | `W_preserves_ancestor_inv` | `admit` | 证明 `v ∈ visited s1` 以排除 `cv = a1` |
| 2688 | `W_preserves_ancestor_inv` | `admit` | non-tree edge 分支 |
| 2693 | `W_preserves_ancestor_inv` | `admit` | `pop_scc a` 分支 |
| 2698 | `W_preserves_ancestor_inv` | `Admitted` | 顶层 |
| 3035 | `low_forset_inv_to_scc_low_valid` | `Admitted` | 顶层 |
| 3057 | `forset_keep_low_forset_inv` | `Admitted` | 顶层 |
| 3063 | `tarjan_scc_keep_low_valid` | `Admitted` | 顶层 |
| 3074 | `tarjan_scc_all_scc_low_valid` | `Admitted` | 顶层 |

## 3. 定理正确性审查

### 3.1 `W_preserves_ancestor_inv`（5 处 admit）— 表述正确，但 fixpoint 不变式需补强

**定理内容**：若 `u <> v`、`~ done v`，且初始状态满足
```coq
low_forset_inv u done s /
fa s v = u /\
~ v ∈ visited s /\
~ done v /\
done_visited done s
```
则执行 `tarjan_scc g v` 后保持
```coq
low_forset_inv u done s /\
fa s v = u /\
done_visited done s
```

**正确性判断**：正确。这是 Tarjan 算法“子树处理期间祖先 `u` 的局部 low 不变式保持”的标准性质。

**关键障碍与修复思路**：

当前证明使用 `Hoare_fix_logicv_conj`，不变式为
```coq
let (cv, pu) := cp in
  cv = v /\ pu = u /\
  low_forset_inv pu done s /\ fa s cv = pu /\
  ~ a ∈ visited s /\ ~ done a /\ done_visited done s
```
该不变式已经逻辑上蕴含 `pu <> a`（因为 `pu ∈ visited s` 而 `~ a ∈ visited s`），但**证明在 `preloop` 之后丢失了 `~ a ∈ visited s`**，导致后续分支无法直接得到 `pu <> a`，从而无法调用以 `u <> a` 为前提的辅助引理。

因此需要：
1. 将 `pu <> a`（或等价的 `u <> a`）显式加入 fixpoint 不变式的 `P` 与 `Q`；
2. 在 `pop_scc` 分支补充 `done` 中顶点不会被当前子树弹出的栈顺序事实；
3. 在 tree-edge 的 `fa s cv = pu` 子目标中，改用 `fa_visited` 推出 `cv ∈ visited s`，从而直接排除 `cv = a1`（因为 `a1` 未访问）。

### 3.2 `low_forset_inv_to_scc_low_valid` — 表述正确，缺纯集合推导

**定理内容**：若 `done_visited (dg_step g u) s`、`fa_children_in_g`、`stack_fa_neq_self` 且 `low_forset_inv u (dg_step g u) s`，则 `scc_low_valid_v s u`。

**正确性判断**：正确。`low_forset_inv` 中的 `children_done` 与 `back_edges_done` 在 `done = dg_step g u` 时分别对应 DFS 树孩子与 `scc_back_edge`，而已有引理 `children_done_full_eq` 与 `back_edges_done_full_eq` 已建立集合等价。只需用 `min_eq_forward` 桥接即可。

### 3.3 `forset_keep_low_forset_inv` — 表述正确，证明依赖 `W_preserves_ancestor_inv`

**定理内容**：在 4 个关于 `W` 的合理 Hoare 假设下，`forset (process_edge u W)` 把 `low_forset_inv u ∅` 推进到 `scc_low_valid_v s u`（并附带 `dfn_valid`、`dfn_inv`、`fa_visited`）。

**正确性判断**：正确。这是主循环不变式。tree-edge、back-edge、cross-edge 三种情况分别对应：
- `update_low_tree_edge`（已证）；
- `update_low_back_edge`（已证）；
- cross-edge 不改变 `children_done`/`back_edges_done`，只需集合等价。

### 3.4 `tarjan_scc_keep_low_valid` — 表述正确，依赖上游引理

由 `preloop_establishes_low_forset_inv` + `forset_keep_low_forset_inv` + `low_forset_inv_to_scc_low_valid` + `pop_scc_keep_scc_low_valid_v` 组合得到。

### 3.5 `tarjan_scc_all_scc_low_valid` — 表述正确，需跨 DFS 树保持性

`tarjan_scc_all` 对每个未访问根点调用 `tarjan_scc`。需要证明：
- 此前 DFS 树中已访问顶点的 `scc_low_valid_v` 不被新 DFS 树破坏；
- 新 DFS 树内顶点由 `tarjan_scc_keep_low_valid` 覆盖。

## 4. 关闭计划

### Phase 1 — 补强并关闭 `W_preserves_ancestor_inv`（当前最大阻塞项）

1. **修改 fixpoint 不变式**
   在 `Hoare_fix_logicv_conj` 的 `P` 与 `Q` 中显式加入 `pu <> a`（利用 `pu ∈ visited` 与 `~ a ∈ visited` 可得）。这使得：
   - `u = a` 分支（行 2579）直接由 `pu <> a` 与 `pu = u` 矛盾得证；
   - non-tree edge 分支（行 2688）可直接用 `update_low_preserves_low_forset_inv_for_other`；
   - `pop_scc` 分支（行 2693）满足 `u <> a` 的前提。

2. **关闭 `fa s cv = pu` 子目标（行 2628）**
   不依赖栈祖先，而是：
   - 由 `low_forset_inv` 得 `fa_visited s`；
   - 由 `fa s cv = pu`、`pu = u`、`u <> v`（即 `pu <> cv`）得 `fa s cv <> cv`；
   - 由 `fa_visited` 得 `cv ∈ visited s`；
   - 但 `a1` 未访问，故 `cv <> a1`，排除 `equiv_dec cv a1` 的 `left` 分支。

3. **补充 `done` 顶点不被弹出的栈顺序引理**
   新增辅助引理（例如 `done_vertices_not_popped_in_subtree`）：
   > 在 `W_preserves_ancestor_inv` 的假设下，`done` 中的顶点要么在进入 `tarjan_scc g v` 之前已被弹出，要么位于 `u` 下方的祖先栈段；`tarjan_scc g v` 的任何 `pop_scc` 都不会把它们弹出。
   
   证明可基于 `stack_split_at` 的性质、`dfn_inv`（栈中 dfn 递增）以及 `done` 顶点在 `v` 之前被处理的事实。

4. **关闭 `pop_scc` 分支（行 2693）**
   在加入 `pu <> a` 与 `done_vertices_not_popped_in_subtree` 后，直接应用 `pop_scc_keeps_low_forset_inv_other`；`fa s cv = pu` 由 `pop_scc` 不修改 `fa` 保持；`done_visited` 由 `pop_scc_preserves_done_visited` 保持。

5. **去掉 `W_preserves_ancestor_inv` 顶层 `Admitted`**

### Phase 2 — 证明 `forset_keep_low_forset_inv`

6. **用 `Hoare_forset` 组织循环不变式**
   取
   ```coq
   P(done) :=
     low_forset_inv u done s /\
     dfn_valid g s root /\ dfn_inv s /\ fa_visited s /\
     done_visited done s /\
     (forall v, fa s v = u /\ fa s v <> v -> v ∈ done)
   ```
   初始状态满足该不变式（由 `low_forset_inv u ∅` 与前提 `forall v, fa s v = u -> v = u`）。

7. **Tree-edge 分支**
   - `set_fa a0 u` 后调用 `W a0`，使用 `set_fa_W_preserves_low_forset_inv`（其内部依赖已关闭的 `W_preserves_ancestor_inv`），得到 `low_forset_inv u done` 保持且 `fa s a0 = u`；
   - 由 `u` 已访问、`a0` 未访问得 `u <> a0`，从而 `fa s a0 <> a0`；
   - 用 `update_low_tree_edge` 完成 `done -> done ∪ [a0]` 的转移。

8. **Back-edge 分支**
   - `a0` 在栈中且 `fa s a0 <> u`；
   - 由 `done_visited done s` 得 `done ⊆ visited s`；
   - 用 `update_low_back_edge` 完成转移。

9. **Cross-edge 分支**
   - `a0` 已访问但不在栈中，且非 `u` 的树孩子；
   - 因此 `a0` 不属于 `children_done` 也不属于 `back_edges_done`；
   - 加入 `done` 不改变这两个集合，用 `min_eq_forward` 或集合等价直接得证。

10. **检查 `stack_fa_neq_self` 缺口**
    `low_forset_inv_to_scc_low_valid` 需要 `forall v, In v (stack s) -> fa s v <> v`。若现有不变式不足以推出，则需在 `P(done)` 中加入该条件并验证 preloop/forset/pop_scc 均保持。

11. **去掉 `forset_keep_low_forset_inv` 顶层 `Admitted`**

### Phase 3 — 收尾主要定理

12. **证明 `low_forset_inv_to_scc_low_valid`**
    - 用 `children_done_full_eq` 与 `back_edges_done_full_eq` 建立集合等价；
    - 用 `min_eq_forward` 把 `low_forset_inv` 的嵌套最小值转换为 `scc_low_valid_v` 的嵌套最小值。

13. **证明 `tarjan_scc_keep_low_valid`**
    - `preloop u` 建立 `low_forset_inv u ∅`（`preloop_establishes_low_forset_inv`）；
    - `forset` 推进到 `scc_low_valid_v s u`（`forset_keep_low_forset_inv`）；
    - 若 `low s u = dfn s u` 则 `pop_scc u` 保持 `scc_low_valid_v`（`pop_scc_keep_scc_low_valid_v`）；否则 skip 不改变状态。

14. **证明 `tarjan_scc_all_scc_low_valid`**
    - 对 `tarjan_scc_all` 的迭代/递归做归纳；
    - 单棵 DFS 树内部使用 `tarjan_scc_keep_low_valid`；
    - 新增跨树保持引理：若 `w` 已在某棵 DFS 树中，对新根调用 `tarjan_scc g r` 后 `scc_low_valid_v s w` 保持（因为后续操作只访问新顶点、只修改新顶点的 `fa`/`low`，不影响已结束树中顶点的 `dfn` 与 `low`）。

15. **全文件 `coqc` 编译检查**
    - 确保没有残留 `admit` / `Admitted`；
    - 检查辅助引理的依赖闭环。

## 5. 风险与依赖

| 风险点 | 说明 | 缓解措施 |
|--------|------|----------|
| `W_preserves_ancestor_inv` 的 `done_vertices_not_popped_in_subtree` 证明复杂 | 需要精确刻画 `done` 顶点与当前处理子树之间的栈位置关系 | 优先尝试从 `dfn_inv`、`stack_split_at` 系列引理直接证明；若不足再补新的全局不变式 |
| `stack_fa_neq_self` 可能无法从现有不变式推出 | 该条件是 `low_forset_inv_to_scc_low_valid` 的前提 | 在 `forset_keep_low_forset_inv` 的循环不变式中加入并验证保持性 |
| 参数统一问题 | 上下文存在 `fa s cv = pu` 时，Coq unifier 可能把以 `u` 为参数的辅助引理实例化为 `fa s cv` | 在深层分支调用前使用 `change (fa s cv) with pu in *` 或 `rewrite <- Hfa in *` 消除目标中的 `fa s cv` |
| `tarjan_scc_all_scc_low_valid` 跨树保持 | 需要说明不同 DFS 树之间的状态隔离 | 利用 `tarjan_scc` 不修改已访问顶点的 `dfn`/`low` 以及 `fa_visited` 等性质 |

## 6. 建议执行顺序

1. **先关闭 `W_preserves_ancestor_inv`**：它是 `set_fa_W_preserves_low_forset_inv` 的前提，也是 `forset_keep_low_forset_inv` 的阻塞项；
2. **再证明 `forset_keep_low_forset_inv` 与 `low_forset_inv_to_scc_low_valid`**；
3. **接着证明 `tarjan_scc_keep_low_valid`**；
4. **最后处理 `tarjan_scc_all_scc_low_valid`** 并完成全文件编译。
