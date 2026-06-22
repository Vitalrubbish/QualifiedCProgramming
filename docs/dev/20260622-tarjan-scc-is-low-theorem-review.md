# Tarjan_scc_is_low.v 定理审查

**Author**: Kimi Code CLI  
**Date**: 2026-06-22

## 审查维度

对每个定理从以下三个角度评分：

- **必要性 (Necessity)**：该定理在整体证明框架中是否不可或缺。
  - 高：核心结构定理，缺少则主定理无法连接。
  - 中：局部辅助，可被少量改写替代。
  - 低：可由更一般引理直接得到，或仅为证明技巧服务。
- **正确性 (Correctness)**：当前陈述在数学上是否成立。
  - 高：陈述显然或在已知假设下成立。
  - 中：成立，但可能需要补充前提或调整表述。
  - 低：怀疑存在反例或前提缺失。
- **可支持性 (Supportability)**：能否方便地由前序定义/引理导出。
  - 高：直接由定义或 1–2 个前序引理得到。
  - 中：需要组合多个引理，但思路清晰。
  - 低：需要额外引理或证明结构复杂。

---

## 1. SCC-low 定义与归纳引理

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 1 | `scc_low_witness` | 高 | 高 | 高 | `min_value_of_subset` 定义直接给出 witness；连接 `scc_is_low_v_val` 与 `scc_low_tree`。 |
| 2 | `scc_low_bound` | 高 | 高 | 高 | `min_value_of_subset` 的极小性；与 witness 配对使用。 |
| 3 | `dg_reachable_first_step` | 中 | 高 | 高 | 图论标准分解，用于 `scc_low_tree_decompose`。 |
| 4 | `scc_low_tree_decompose` | 高 | 高 | 中 | 关键结构引理，把 `scc_low_tree` 拆成 `{u} ∪ back_edge ∪ children_tree`；依赖 `dg_reachable_first_step`。 |
| 5 | `scc_low_valid_induction` | 高 | 高 | 中 | 归纳核心：子节点的 low 最小值等于其子树 dfn 最小值；依赖 witness/bound 与 min 性质。 |
| 6 | `scc_low_valid_induction_is_low` | 高 | 高 | 高 | 直接由 5 与定义得到，是归纳步骤。 |
| 7 | `scc_low_valid_implies_is_low` | 高 | 高 | 中 | 主连接引理之一，把局部 `scc_low_valid` 推广为全局 `scc_is_low`；依赖 DFS 树良基归纳。 |

## 2. `wf_scc_state` / `wf_scc_state_pre` 抽象

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 8 | `pop_scc_preserves_wf_scc_state` | 高 | 高 | 高 | `pop_scc` 保持完整 `wf_scc_state`。 |
| — | `preloop_preserves_wf_scc_state` | 高 | 高 | 高 | `preloop` 从 `wf_scc_state_pre u` 恢复到完整 `wf_scc_state`。 |
| — | `set_fa_preserves_wf_scc_state_pre` | 高 | 高 | 高 | `set_fa v u` 创建指向未访问顶点 `v` 的 pending 树边，因此只保持 `wf_scc_state_pre v`，不保持完整 `wf_scc_state`。 |
| — | `set_low_preserves_wf_scc_state` | 高 | 高 | 高 | `set_low` 只改 `low`，保持完整 `wf_scc_state`。 |
| — | `update_low_preserves_wf_scc_state` | 高 | 高 | 高 | `update_low` 保持完整 `wf_scc_state`。 |

`wf_scc_state` 与 `wf_scc_state_pre` 已发展为系统抽象；`low_forset_inv`、`low_pre`、`low_post` 均基于它们定义，从而消除大量重复的 `dfn_inv`/`dfn_valid`/`fa_visited` 合取支，并正确刻画 `set_fa` 的 pending 树边语义。

## 3. `low_pre` / Fa 约束辅助引理

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 9 | `low_pre_fa_eq_u_implies_eq_u` | 中 | 高 | 高 | 在 `low_pre u` 状态下，未访问的 `u` 不能是别人的父节点；由 `fa_visited` 直接得到。 |
| ~~10~~ | ~~`low_pre_no_fa_child_of_u`~~ | ~~低~~ | ~~高~~ | ~~高~~ | **已删除**：在整个框架（包括原证明草稿）中未被引用，可由 `low_pre_fa_eq_u_implies_eq_u` 在需要处内联得到。 |

## 4. 空集 / low=dfn 代数事实

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 11 | `preloop_low_eq_dfn` | 高 | 高 | 高 | `preloop` 定义直接给出。 |
| 12 | `children_done_empty` | 高 | 高 | 高 | 空集 trivial。 |
| 13 | `back_edges_done_empty_char` | 高 | 高 | 高 | 空集 trivial。 |
| 14 | `low_eq_dfn_to_min_empty` | 高 | 高 | 高 | 由 12、13 与 `low s u = dfn s u` 直接得到；用于 `preloop_establishes_low_forset_inv`。 |
| 15 | `preloop_establishes_low_forset_inv` | 高 | 高 | 高 | 由 11、14 与基本不变式组合。 |

## 5. `pop_scc` 与 `stack_split_at` 结构

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 16 | `stack_split_at_partition` | 中 | 高 | 高 | 已合并原 `stack_split_at_rest_incl`/`popped_fresh`/`covers` 三个引理；一次性刻画 `stack_split_at` 把栈划分为 `popped` 与 `rest` 的性质。 |
| 17 | `scc_low_valid_v_low_eq_dfn_implies_dfn_le_back_edge_dfn` | 中 | 高 | 高 | 当 `low u = dfn u` 时，回边目标 dfn 不会更小；直接由 `scc_low_valid_v` 定义得到。 |
| 18 | `pop_scc_keep_scc_low_valid_v` | 高 | 高 | 中 | `tarjan_scc_keep_low_valid` 的 pop 分支所需；依赖 `low u = dfn u` 保证弹栈不会破坏 min。 |

## 6. `children_done` / `back_edges_done` 集合更新

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 21 | `children_done_add` | 高 | 高 | 高 | forset 迭代中 `done` 扩张所需。 |
| 22 | `children_done_no_add` | 高 | 高 | 高 | 同上。 |
| 23 | `back_edges_done_add` | 高 | 高 | 高 | 同上。 |
| 24 | `back_edges_done_no_add` | 高 | 高 | 高 | 同上。 |

## 7. `set_fa` / `set_low` 辅助

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 25 | `set_fa_preserves_low_pre_rich` | 高 | 高 | 高 | `set_fa` 只改 `fa`，直接可得。 |
| 26 | `set_low_keep_low_forset_inv_components` | 高 | 高 | 高 | `set_low` 只改 `low`，直接可得。 |
| 27 | `set_low_preserves_low_forset_inv` | 高 | 高 | 高 | 由 26 与 `~done v`、`u<>v` 保证 `v` 不出现在 `children_done`/`back_edges_done` 中。 |

## 8. `update_low` 具体情形

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 28 | `update_low_tree_edge` | 高 | 高 | 中 | 树边更新 `low u := min(low u, low v)`；需要 `min_value_of_subset` 的嵌套更新引理。 |
| 29 | `low_forset_inv_implies_low_le_dfn` | 高 | 高 | 高 | `low_forset_inv` 的定义直接给出 `low u <= dfn u`。 |
| 30 | `update_low_back_edge` | 高 | 高 | 中 | 回边更新 `low u := min(low u, dfn v)`；覆盖 `fa v = u` 与 `fa v ≠ u` 两种情况。 |
| 31 | `low_forset_inv_children_done_low_le` | 中 | 高 | 高 | 直接由 `low_forset_inv` 定义得到，用于 28。 |
| 32 | `low_forset_inv_expand_child_done` | 高 | 高 | 中 | forset 迭代关键：扩张 `done` 为 `done∪{v}` 并保持不变式；依赖嵌套 min 更新。 |

## 9. `low_forset_inv` 对“其他”顶点的保持

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 33 | `update_low_preserves_low_forset_inv_for_other` | 高 | 高 | 高 | 更新 `low v` 不影响 `u` 的不变式；由 `~done v`、`u≠v` 保证。 |
| 34 | `set_fa_preserves_low_forset_inv_for_new_child` | 高 | 高 | 高 | 设置 `fa x:=v` 不影响 `u`，因为 `x` 未访问；`x` 不可能在 `children_done/back_edges_done u done` 中。 |
| 35 | `preloop_keeps_low_forset_inv_other` | 高 | 高 | 中 | `preloop a` 对 `u≠a` 保持 `low_forset_inv u done`；组合 33、34 与基本不变式。 |
| 36 | `pop_scc_keeps_low_forset_inv_other` | 高 | 高 | 中 | `pop_scc a` 对 `u` 保持不变式；依赖栈拆分条件。 |

## 10. `fa` 保持

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 38 | `preloop_keeps_fa` | 高 | 高 | 高 | `preloop` 不改 `fa`。 |
| 39 | `process_edge_keeps_fa_simple` | 高 | 高 | 高 | `process_edge` 不改已访问顶点的 `fa`。 |
| 40 | `forset_keeps_fa` | 高 | 高 | 中 | 由 39 与 forset 不动点规则得到。 |

## 11. Min / Visited / `done_visited` 保持

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 41 | `set_fa_preserves_min` | 高 | 高 | 高 | `set_fa v u` 在 `~done v` 时不改变 `low_forset_inv u done` 的 min 条件；关键引理。 |
| 42 | `pop_scc_preserves_done_visited` | 高 | 高 | 高 | `pop_scc` 不改 `visited`，直接可得。 |
| — | `tarjan_scc_preserves_visited` | — | — | — | **已删除**。等价结论由 `Tarjan_scc_basics` 中的 `tarjan_scc_keep_visited` 提供，直接复用即可。 |

## 12. 祖先不变式保持

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 43 | `pop_scc_preserves_ancestor_inv` | 高 | 高 | 中 | `pop_scc` 保持祖先不变式；依赖 37 与栈条件。 |
| 44 | `preloop_preserves_ancestor_inv` | 高 | 高 | 中 | `preloop` 保持祖先不变式；依赖 36、38。 |

## 13. 栈序与 dfn 序

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 45 | `stack_split_at_in_popped_before_a` | 中 | 高 | 高 | 纯列表结构。 |
| 46 | `in_list_one_above_other` | 中 | 高 | 高 | 纯列表结构。 |
| 47 | `preloop_above_existing` | 高 | 高 | 高 | `preloop` 把新顶点压到栈顶。 |
| 48 | `done_dfn_lt_not_done` | 高 | 高 | 中 | 已补充 `done_visited done s` 前提；在 done 顶点均为已访问的前提下，done 栈顶点的 dfn 严格小于当前顶点 `a`。 |
| 49 | `current_above_done_vertex` | 高 | 高 | 中 | 已补充 `done_visited done s` 前提；由 48 与栈序得到 done 顶点在 `a` 下方。 |
| 50 | `done_vertex_dfn_lt` | 中 | 高 | 中 | 已补充 `done_visited done s` 前提；49 的直接推论。 |
| 51 | `done_not_popped_by_subtree_pop_scc` | 高 | 高 | 中 | 由 50、45 与 dfn 严格不等式得到；是 `W_preserves_ancestor_inv` 的关键输入。 |

## 14. `W` 保持祖先不变式

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 52 | `W_preserves_ancestor_inv` | 高 | 高 | 中 | 核心不动点引理；依赖 43、44、51 等。陈述中的 `stack_dfn_order` 与 `dfn_injective` 合取可提取为单独前提以提升可读性。 |
| 53 | `set_fa_W_preserves_low_forset_inv` | 高 | 高 | 中 | 树边分支核心：先 `set_fa v u` 再递归 `tarjan_scc g v`；依赖 41、52。 |

## 15. Properness

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 54 | `low_forset_inv_proper` | 高 | 高 | 中 | forset 不动点规则必需；由集合等价与 min 性质得到。 |
| ~~55~~ | ~~`children_done_visited_proper`~~ | ~~低~~ | ~~高~~ | ~~高~~ | **已删除**：`children_done_visited` 及其 `Proper` 实例在整个框架中未被引用；`done_visited` 已足够约束 `done ⊆ visited`。 |
| 56 | `done_visited_proper` | 中 | 高 | 高 | 直接。 |

## 16. `fa_children` 与 `full_eq`

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 57 | `process_edge_keep_fa_children` | 高 | 高 | 中 | 保持“fa-子节点都是图边”的性质；树边分支使用 `dg_step g u v`。 |
| 58 | `tarjan_scc_keep_fa_children_in_universe` | 高 | 高 | 中 | 由 57 与不动点规则得到。 |
| 59 | `children_done_full_eq` | 高 | 高 | 中 | `done = dg_step g u` 时 `children_done` 等于 DFS 树子节点；依赖 `state_to_dfs_tree` 特征化。 |
| 60 | `back_edges_done_full_eq` | 高 | 高 | 中 | `done = dg_step g u` 时 `back_edges_done` 等于 `scc_back_edge`；依赖 `state_to_dfs_tree_step_char`。 |
| 61 | `low_forset_inv_to_scc_low_valid` | 高 | 高 | 高 | 由 59、60 与 min 等价得到；关闭 forset 循环。 |

## 17. forset 保持与主定理

| # | 定理 | 必要性 | 正确性 | 可支持性 | 备注 |
|---|------|--------|--------|----------|------|
| 62 | `forset_keeps_low_forset_inv` | 高 | 高 | 中 | forset 保持 `low_forset_inv u done`；树边分支的 `update_low a (low x)` 步骤应使用 `update_low_preserves_low_forset_inv_for_other`（因为 `u <> a` 且 `a ∉ done`）。 |
| 63 | `forset_keep_low_forset_inv` | 高 | 高 | 中 | forset 遍历所有子节点后得到 `scc_low_valid_v`；依赖 62、61。 |
| 64 | `tarjan_scc_keep_low_valid` | 高 | 高 | 中 | 单顶点主定理；`HW_done_vis` 假设应由 `Tarjan_scc_basics.tarjan_scc_keep_visited_forall` 提供，而非仅由单点 visited IH 提升。组合 15、63、18。 |
| 65 | `tarjan_scc_establishes_and_preserves_scc_low_valid` | 高 | 高 | 低 | 跨子树保持/建立 `scc_low_valid`；依赖 52/64。这是当前框架中最大的未证义务，需证明一次顶层 `tarjan_scc` 不会破坏已有顶点的 `scc_low_valid_v`。 |
| 66 | `tarjan_scc_all_scc_low_valid` | 高 | 高 | 高 | 全局 `scc_low_valid`；改用常值不变式 `scc_low_valid s /\ wf_scc_state s`（不依赖 `done`），避免原 `done`-索引不变式对已访问但非 `done` 顶点的失配。由 65 与 `Hoare_forset` 得到。 |
| 67 | `tarjan_scc_all_scc_is_low` | 高 | 高 | 高 | 最终目标；由 66 与 7。 |

---

## 已应用的修改

本次审查后，已对 `Tarjan_scc_is_low.v` 做如下调整（文件可编译）：

1. **`done_dfn_lt_not_done` 系列补前提**：为 `done_dfn_lt_not_done`、`current_above_done_vertex`、`done_vertex_dfn_lt` 显式加入 `done_visited done s` 前提，消除潜在反例。
2. **删除冗余/平凡定理**：
   - `pop_scc_keeps_fa`（`True -> True`）
   - `update_low_back_edge_fa_neq`（`update_low_back_edge` 的特例）
   - `tarjan_scc_preserves_visited`（`Tarjan_scc_basics` 中已有等价 `tarjan_scc_keep_visited`）
   - `set_low_keep_low_forset_inv_components`（被新的 `set_low_preserves_wf_scc_state` 覆盖）
   - `visited_tag` 及其 pre/post 定义（死代码）
3. **合并 `stack_split_at_*` 引理**：原三个列表划分引理合并为 `stack_split_at_partition`。
4. **系统化 `wf_scc_state` 抽象**：
   - 新增 `preloop_preserves_wf_scc_state`、`set_fa_preserves_wf_scc_state`、
     `set_low_preserves_wf_scc_state`、`update_low_preserves_wf_scc_state`。
   - 用 `wf_scc_state` 重新定义 `low_forset_inv`、`low_pre`、`low_post`。
5. **拆分 `low_forset_inv`**：新增 `low_forset_inv_core`，仅保留与 `done` 相关的 min 条件；`low_forset_inv` 变为 `wf_scc_state /\ u ∈ visited /\ low_forset_inv_core`。
6. **补充跨子树两阶段引理**：新增 `forset_end_implies_scc_low_valid_v`，显式刻画 forset 结束时从 `low_forset_inv` 到 `scc_low_valid_v` 的转换。
7. **更新高层主定理证明思路**：`tarjan_scc_keep_low_valid`、`tarjan_scc_establishes_and_preserves_scc_low_valid`、`tarjan_scc_all_scc_low_valid`、`tarjan_scc_all_scc_is_low` 均改为基于 `wf_scc_state` 的表述。

## 第二轮审查后的额外调整

在对整个框架进行第二轮“用不到的定理 / 缺失引理”审查后，又做了以下细化：

1. **删除真正未被引用的定义/引理**：
   - `low_pre_no_fa_child_of_u`：原叙述中从未被后续证明引用，可由 `low_pre_fa_eq_u_implies_eq_u` 在需要处内联。
   - `children_done_visited` 及其 `Proper` 实例 `children_done_visited_proper`：框架中从未使用；`done_visited` 已足以保证 `done ⊆ visited`。
2. **修正证明思路中的前序引用**：
   - `forset_keeps_low_forset_inv` 的树边 `update_low a (low x)` 步骤，应使用 `update_low_preserves_low_forset_inv_for_other`（前提 `u <> a` 且 `a ∉ done`），而不是 `update_low_tree_edge`。
   - `tarjan_scc_keep_low_valid` 的 `HW_done_vis` 假设应由外部 `Tarjan_scc_basics.tarjan_scc_keep_visited_forall` 直接提供。
3. **重新设计全局循环不变式**：
   - `tarjan_scc_all_scc_low_valid` 改用常值不变式 `scc_low_valid s /\ wf_scc_state s`（不依赖 `done`）。原 `done`-索引不变式 `forall w, done w -> scc_low_valid_v s w` 对“已访问但尚未加入 done”的顶点失配；而常值 `visited`-索引不变式在顶层迭代中成立，因为每个顶层 `tarjan_scc g a` 都会以弹出 `a` 的 SCC 结束，所有新访问顶点最终都满足 `scc_low_valid_v`。
   - 这使得 `tarjan_scc_all_scc_low_valid` 仅依赖 `tarjan_scc_establishes_and_preserves_scc_low_valid` 作为唯一未证义务。
4. **引入 `wf_scc_state_pre` 修正 `set_fa` / `preloop` 抽象**：
   - 新增 `wf_scc_state_pre u s := wf_scc_state s /\ ~ u ∈ visited s` 刻画 pending 树边状态。
   - `preloop_preserves_wf_scc_state` 的 precondition 改为 `wf_scc_state_pre u`，postcondition 为完整 `wf_scc_state`。
   - 删除错误的 `set_fa_preserves_wf_scc_state`，新增 `set_fa_preserves_wf_scc_state_pre`：
     `set_fa v u` 在 `u ∈ visited /\ ~ v ∈ visited` 时保持 `wf_scc_state_pre v`（不保持完整 `wf_scc_state`，因为新边 `u -> v` 的 dfn 顺序要在 `preloop v` 后才满足）。
   - `low_pre u` 现在直接定义为 `wf_scc_state_pre u s`。
   - 删除冗余的 `set_fa_preserves_low_pre_rich`（其功能已由 `set_fa_preserves_wf_scc_state_pre` 覆盖）。
5. **解决 `set_fa_preserves_wf_scc_state_pre` 的 `dfn_pre` 拆分困难**：
   - 困难：`dfn_pre v s root` 已是 4 个分量的合取，再拆成 4 个独立 Hoare_conj 分支机械冗长。
   - 方案：把 `dfn_pre v s root /\ u ∈ visited s` 当作**一个整体**与 `stack_in_visited s` 做 Hoare_conj；
     - Q1 用 `set_fa_preserves_dfn_pre_child_rich`（来自 `Tarjan_scc_is_dfn.v`）直接保持；
     - Q2 用 `set_fa` 不改变 `stack`/`visited` 直接保持；
     - 合并后 `dfn_pre v /\ stack_in_visited` 即 `wf_scc_state_pre v`。
   - 这样只需一次 Hoare_conj，避免把已捆绑的 `dfn_pre` 再拆开。

## 剩余建议

当前已无不处于“已应用”状态的高优先级建议。后续可选的进一步优化包括：
- 考虑用一个更精简的“标签”类型统一 `Hoare_fix_logicv_conj` 的辅助通道，以替代当前 `w ∈ visited s` + 外部 fa-children 引理的组合；
- 在形式化证明时，利用 `wf_scc_state` 保持引理批量处理全局不变式，减少重复论证。

---

## 总体评估

- **必要性**：整体定理网络紧凑，删除/合并后冗余进一步减少，剩余定理在框架中都有明确位置。
- **正确性**：在补全 `done_visited` 前提后，主要可疑点已消除；其余定理陈述正确。
- **可支持性**：低层引理（集合更新、基本 Hoare）多可直接由定义得到；中层（`update_low`、祖先保持、栈序）需要组合；高层主定理结构清晰，依赖关系合理。当前唯一较大的未证义务是 `tarjan_scc_establishes_and_preserves_scc_low_valid`（跨子树保持 `scc_low_valid`），其余高层定理的证明思路已完整。
