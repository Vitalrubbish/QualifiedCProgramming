# Tarjan-scc-is-low.v Admit 关闭计划

**Author**: Vitalrubbish
**Date**: 2026-06-21

## 1. 背景

本计划针对 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v` 中尚未关闭的 `admit` / `Admitted` 进行审查，判断各定理表述是否成立，并给出按依赖顺序执行的关闭步骤。

该文件的目标：证明 Tarjan SCC 算法中 `low` 值的正确性，即算法执行后满足 `scc_is_low`（每个顶点的 `low` 等于沿 DFS 树边再跟一条回边能到达的最小 `dfn`）。

## 2. Admit 分布

| 行号 | 所在定理 | 当前状态 |
|------|----------|----------|
| 1860 | `update_low_preserves_low_forset_inv_for_other` | 局部 `admit` |
| 2524, 2546, 2548, 2554, 2557 | `W_preserves_ancestor_inv` | 5 处局部 `admit` |
| 2589 | `W_preserves_ancestor_inv` | 顶层 `Admitted` |
| 2876 | `low_forset_inv_to_scc_low_valid` | 顶层 `Admitted` |
| 2898 | `forset_keep_low_forset_inv` | 顶层 `Admitted` |
| 2904 | `tarjan_scc_keep_low_valid` | 顶层 `Admitted` |
| 2915 | `tarjan_scc_all_scc_low_valid` | 顶层 `Admitted` |

## 3. 定理正确性审查

### 3.1 `update_low_preserves_low_forset_inv_for_other` — 表述过强，需加前提

当前 statement 对任意 `u, v` 宣称：把 `low v` 改为 `min (low s v) n` 后，`low_forset_inv u done` 不变。

**反例**：取 `u = v`，`done = ∅`，`low s u = dfn s u`，再令 `n < dfn s u`。此时 `low_forset_inv` 原来成立，但更新后 `low s u` 被压到 `n`，而 `done = ∅` 时 nested min 集合只剩 `{dfn s u}`，`n` 不在其中，不变式被破坏。

**结论**：定理在 `u = v` 且 `n < low s v` 时不成立。但所有调用点（2283、2293 行）都位于 `forset_keeps_low_forset_inv`，该处已有 `Hneq : u <> a`（即 `u <> v`）。

**修复**：给该 lemma 增加前提 `u <> v`。

### 3.2 `W_preserves_ancestor_inv` — 定理正确，但 fixpoint 不变式需结构性增强

该定理说：对 `u` 的未访问孩子 `v`，在执行 `set_fa v u ;; tarjan_scc g v` 后，`low_forset_inv u done`、`fa s v = u`、`done_visited done` 都保持。

**新发现的关键障碍**：

1. **Fixpoint 变量隔离**：证明内部用 `hoare_fix` 引入的 `W` 是局部 fixpoint 变量（`W'`），而外部已证引理（如 `tarjan_scc_preserves_visited`）中的 `W` 是另一独立变量。二者类型相同但无法直接统一，已证的外部引理不能无额外条件地代入到 fixpoint IH 中。
2. **Forset 体不变式过弱**：在 `forset (process_edge u W)` 的循环体内，当前可用的不变量仅有 `done_visited done`（以及 `fa s v = u` 等零星事实），但 fixpoint IH 要求更强的前置条件（如 `low_forset_inv u done` 或 `a ∈ visited`）。这导致无法在当前证明结构内直接调用 IH 关闭 admit。
3. **需要的结构性修改**：要让 IH 可用，必须把循环体不变式增强到与 fixpoint 前置条件一致，即在 `hoare_fix` 的 fixpoint 不变式中显式包含：
   - `a ∈ visited s`
   - `done_visited done s`
   - `fa s v = u`
   - `low_forset_inv u done s`

   这意味着需要重构 `W_preserves_ancestor_inv` 的整体证明结构，而不仅仅是补充若干辅助引理。

**7 处 admit 的当前状态**：

| 位置 | 状态 / 所需修复 |
|------|----------------|
| `W_preserves_ancestor_inv` 中 `u = a` 分支 | 依赖 `forset_keep_low_forset_inv`（见 Phase 3） |
| `W_preserves_ancestor_inv` 中 `a ∈ visited` | **需增强 fixpoint 不变式** |
| `W_preserves_ancestor_inv` 中 `done_visited done`（forset 循环） | **需增强 fixpoint 不变式** |
| `W_preserves_ancestor_inv` 中 `pop_scc` 保持 `low_forset_inv` / `done_visited` | 依赖 `done_vertices_not_popped` 不变式 |
| `W_preserves_ancestor_inv` 中 `fa s v = u` | **需增强 fixpoint 不变式** |
| `low_forset_inv_to_scc_low_valid` | Phase 3 |
| `forset_keep_low_forset_inv` → `tarjan_scc_all_scc_low_valid` | Phase 3 |

**结论**：定理本身正确，但 5 处 `W_preserves_ancestor_inv` 内部 admit 中的 3 处（`a ∈ visited`、`done_visited`、`fa s v = u`）必须通过增强 fixpoint 不变式来关闭；剩余 2 处（`u = a` 分支、`pop_scc` 分支）分别依赖 `forset_keep_low_forset_inv` 和栈顺序不变式。

### 3.3 `low_forset_inv_to_scc_low_valid` — 缺 `done_visited` 前提

当前 statement 要求从 `low_forset_inv u (dg_step g u) s` 推出 `scc_low_valid_v s u`。bridging 需要：
- `children_done s u (dg_step g u) == dg_step (state_to_dfs_tree g s root) u`
- `back_edges_done s u (dg_step g u) == scc_back_edge s u`

但 `children_done` 只要求 `v ∈ done ∧ fa s v = u ∧ fa s v ≠ v`，不强制 `v ∈ visited s`。若存在未访问的 `v` 满足 `fa s v = u`，两边集合不等。

**结论**：当前表述不成立。应增加前提 `done_visited (fun v => dg_step g u v) s`。

### 3.4 `forset_keep_low_forset_inv` — 定理正确，证明结构复杂

这是把 `forset (process_edge u W)` 的循环不变式从 `done = ∅` 推到 `done = dg_step g u` 的核心引理。4 个关于 `W` 的 Hoare 假设均合理：
- `W x` 把 `low_pre x` 变为 `low_post x`；
- `W a` 使 `a` 被访问；
- `W a` 保持任意固定集合的 visited 性；
- `W a` 不产生新的 `fa = u` 的非自环子节点。

**结论**：定理正确，证明需按 `Hoare_forset` 组织。

### 3.5 `tarjan_scc_keep_low_valid` — 正确，依赖 3.1–3.4

由 `preloop_establishes_low_forset_inv` + `forset_keep_low_forset_inv` + `pop_scc_keep_scc_low_valid_v` 得到。

### 3.6 `tarjan_scc_all_scc_low_valid` — 大概率正确，需补跨 DFS 树保持性

`tarjan_scc_all` 会对每个未访问根点调用 `tarjan_scc`。需要证明：
- 已访问且属于此前 DFS 树的顶点，`scc_low_valid_v` 不被后续新 DFS 树破坏；
- 新 DFS 树内顶点由 `tarjan_scc_keep_low_valid` 覆盖。

需要新增跨树保持引理。

## 4. 关闭计划

### Phase 1 — 修正两条有缺陷的定理表述

1. **`update_low_preserves_low_forset_inv_for_other`**
   - 增加前提 `u <> v`；
   - 原证明中 `u ≠ v` 分支直接完成，`u = v` 分支被排除；
   - 两处调用点（2283、2293 行）传入现有 `Hneq : u <> a`。

2. **`low_forset_inv_to_scc_low_valid`**
   - 增加前提 `done_visited (fun v => dg_step g u v) s`；
   - 证明两个集合等价：
     - `children_done s u (dg_step g u) == dg_step (state_to_dfs_tree g s root) u`
     - `back_edges_done s u (dg_step g u) == scc_back_edge s u`
   - 使用 `state_to_dfs_tree_step_char` / `state_to_dfs_tree_step_char_backward`。

### Phase 2 — 重构 `W_preserves_ancestor_inv` 的 fixpoint 不变式并补充辅助引理

**首要任务：增强 fixpoint 不变式**

3. **重构 `W_preserves_ancestor_inv` 的证明结构**
   - 将 `hoare_fix` 引入的 fixpoint 不变式从当前较弱的形态增强为：
     ```
     P W a s s' :=
       a ∈ visited s
       ∧ low_forset_inv u done s
       ∧ done_visited done s
       ∧ fa s v = u
       ∧ (其他已具备的前提，如 dfn_valid、dfn_inv、fa_visited 等)
     ```
   - 目标：让 forset 循环体在调用 `W a` 之前已经拥有 `a ∈ visited` 和 `low_forset_inv u done` 等事实，从而 fixpoint IH 与外部已证引理（如 `tarjan_scc_preserves_visited`）可以在同一假设上下文中使用。
   - 如果直接统一 `W` 变量不可行，则通过把外部引理的结论重新表述为“对任意满足前提的 `W` 调用均成立”的形式，或将所需事实直接加入循环不变式来绕过变量隔离问题。

4. **`pop_scc_keeps_low_forset_inv_other`**
   - 当 `u <> a` 且 `done` 中顶点均不在被弹出集合时，`pop_scc a` 保持 `low_forset_inv u done`。
   - 参考已证的 `pop_scc_keep_scc_low_valid_v`，把论证翻译成 `children_done`/`back_edges_done` 语言。

5. **`pop_scc_preserves_done_visited`**
   - `pop_scc` 不改变 `visited`，只改 `stack` 和 `sccs`，因此保持 `done_visited`。

6. **`done_vertices_not_popped_in_subtree`**（关键不变式）
   - 在 `W_preserves_ancestor_inv` 假设下，`done` 中的顶点都不在 `v` 的子树/SCC 中，因此 `tarjan_scc g v` 的任何 `pop_scc` 都不会把它们弹出。
   - 证明思路：`done` 顶点是 `u` 的已处理邻居，处理完成后要么早已出栈，要么位于 `u` 下方的祖先栈中，不可能位于 `v` 的子树栈段。

7. **`forset_preserves_done_visited`** 与 **`process_edge_preserves_visited_of_fixed_set`**
   - 用 `Hoare_forset` 和已证的 `tarjan_scc_preserves_visited` 给出；
   - 注意：由于 fixpoint 变量隔离，可能需要把相关结论包装成只依赖于状态转移关系而非具体 `W` 变量的形式。

8. **`forset_keeps_fa_for_child`**
   - 组合 `process_edge_keeps_fa_simple` 与 `Hoare_forset`，证明在 `tarjan_scc g v` 执行期间 `fa s v = u` 保持；
   - 该事实也需要被纳入增强后的 fixpoint 不变式，否则 forset 体内无法调用 IH。

### Phase 3 — 完成主要引理

9. **补完 `W_preserves_ancestor_inv`**
   - 在 Phase 2 增强后的 fixpoint 不变式框架下，逐分支关闭 5 处 admit：
     - `u = a` 分支：由增强后的不变式直接导出矛盾，或依赖 `forset_keep_low_forset_inv`（Phase 3 第 10 步）提供所需上下文；
     - `a ∈ visited` 分支：由 fixpoint 不变式中的 `a ∈ visited` 直接可得；
     - `done_visited done` 分支：由 fixpoint 不变式中的 `done_visited done` 直接可得；
     - `pop_scc` 分支：用 `pop_scc_keeps_low_forset_inv_other` + `pop_scc_preserves_done_visited` + `done_vertices_not_popped_in_subtree` 组合证明；
     - `fa s v = u` 分支：由 fixpoint 不变式中的 `fa s v = u` 直接可得。
   - 最后去掉顶层 `Admitted`。

10. **证明 `forset_keep_low_forset_inv`**
    - 用 `Hoare_forset` 建立循环不变式：
      ```
      P(done) :=
        low_forset_inv u done s
        ∧ dfn_valid g s root ∧ dfn_inv s ∧ fa_visited s
        ∧ done_visited done s
        ∧ (∀ v, fa s v = u ∧ fa s v ≠ v → v ∈ done)
      ```
    - tree-edge 分支：用 `set_fa_W_preserves_low_forset_inv` + `low_forset_inv_expand_child_done`（已证）+ `update_low_tree_edge`（已证）；
    - back-edge 分支：用 `update_low_back_edge`（已证）；
    - cross-edge 分支：集合不变，low 不变，直接 `min_eq_forward`。

11. **证明 `low_forset_inv_to_scc_low_valid`**
    - 在增加 `done_visited` 前提后，用 Phase 1 的集合等价 + `min_eq_forward` 完成。

12. **证明 `tarjan_scc_keep_low_valid`**
    - 组合 `preloop_establishes_low_forset_inv`、`forset_keep_low_forset_inv`、`pop_scc_keep_scc_low_valid_v`。

13. **证明 `tarjan_scc_all_scc_low_valid`**
    - 新增跨 DFS 树保持引理：若 `w` 已在某棵 DFS 树中，对新根 `r` 调用 `tarjan_scc g r` 后 `scc_low_valid_v s w` 保持；
    - 然后对 `tarjan_scc_all` 的迭代做简单归纳。

## 5. 风险与依赖

- **最大风险（新增）**：`W_preserves_ancestor_inv` 的 fixpoint 不变式重构涉及改变证明骨架，可能发现当前 statement 的前提仍不足以支撑增强后的不变式，从而需要进一步调整定理前提。这是 Phase 2 的前置阻塞项，必须在其余 admit 之前完成。
- **次大风险**：`done_vertices_not_popped_in_subtree` 这类栈顺序不变式需要诉诸 Tarjan 实现的全局不变式（如 `stack_in_visited`、`dfn_inv`、`dfn_valid` 的相互作用）。如果实现中某些不变式尚未在 `Tarjan_scc_basics.v` / `Tarjan_scc_is_dfn.v` 中建立，可能需要先补那些引理。
- **表述修正影响面小**：Phase 1 的两处修改只影响本文件，且调用点都有现成假设可填。
- **`tarjan_scc_all_scc_low_valid` 工作量仍最大**：因为它把单棵树结论推广到森林，需要仔细处理不同 DFS 树之间的状态隔离。
- **建议执行顺序**：
  1. 先验证 Phase 1 的修改能编译通过，避免在错误 statement 上堆叠证明；
  2. 优先完成 Phase 2 的 fixpoint 不变式重构，确认 3 处"需增强 fixpoint 不变式"的 admit 可关闭；
  3. 再补充 `done_vertices_not_popped_in_subtree` 等栈顺序引理，关闭剩余 admit；
  4. 最后进入 Phase 3 收尾主要引理。
