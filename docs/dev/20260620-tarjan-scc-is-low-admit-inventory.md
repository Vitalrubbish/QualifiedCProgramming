# Tarjan_scc_is_low.v 当前 Admit 盘点与阻塞分析
**Author**: Claude & Kimi Code
**Date**: 2026-06-20
**Last reviewed**: 2026-06-20（已根据当前 HEAD 修正依赖关系；新增 2 处 admit）

## 背景

`SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v` 正在证明 Tarjan SCC 算法中 `low` 值的正确性。当前文件已编译通过，但有 **9 处 admit/Admitted** 未闭合（原始盘点 12 处，已关闭 #2 `stack_split_at` 内部 admit 与 #3 `pop_scc_preserves_ancestor_inv`，新增 `set_fa_W_preserves_low_forset_inv` 与 `tarjan_scc_keep_low_valid` 两处因依赖上游 admit 及自身内部类型错误而重新 admit）。

---

## 当前 Admit 清单（9 处）

| # | 行号 | 类型 | 所在引理/定理 | 说明 |
|---|------|------|---------------|------|
| 1 | 1414 | `Admitted.` | `popped_vertex_low_eq_dfn` | 核心不变量：已弹出栈顶点满足 `low = dfn`（通用形式过强） |
| 2 | 1886 | `Proof. Admitted.` | `process_edge_preserves_ancestor_inv` | `process_edge` 保持祖先 `low_forset_inv` 与 `fa` 关系 |
| 3 | 1901 | `Proof. Admitted.` | `W_preserves_ancestor_inv` | `W v`（即 `tarjan_scc g v`）保持祖先不变量，依赖 #2 |
| 4 | 1930 | `Proof. Admitted.` | `set_fa_W_preserves_low_forset_inv` | **新增 admit**：树边分支关键桥接引理，依赖 #3（原为 Qed 但调用 #3 而 #3 未证明，且 min 条件 proof 有类型错误） |
| 5 | 1943 | `Proof. Admitted.` | `process_edge_keep_low_forset_inv` | 内部含 `skip fa=u` 与 `cross edge proper child` 两处 admit（原 #6、#7），依赖 #4 与 #1 |
| 6 | 2104 | `Admitted.` | `tarjan_scc_keep_fa_children_in_universe` | `tarjan_scc` 保持 `fa` 子节点在图边宇宙中（fixpoint 归纳） |
| 7 | 2117 | `Proof. Admitted.` | `forset_keep_low_forset_inv` | 内部含 `fa_children_are_done` step case admit（原 #10），依赖 #5、#6 |
| 8 | 2123 | `Proof. Admitted.` | `tarjan_scc_keep_low_valid` | **新增 admit**：top-level fixpoint 定理，依赖 #7（原为 Qed 但含内部类型错误） |
| 9 | 2134 | `Admitted.` | `tarjan_scc_all_scc_low_valid` | 顶层定理，依赖 #7（通过 #8） |

### 与原始盘点的变更说明

- **#2 (原 1555) `stack_split_at` internal admit** → 已关闭（新增 `stack_split_at_popped_fresh` 辅助引理）
- **#3 (原 1558) `pop_scc_preserves_ancestor_inv`** → 已关闭（Qed，line 1678）
- **新增 #4 `set_fa_W_preserves_low_forset_inv`**：原为 Qed（line 2009），但证明调用 `W_preserves_ancestor_inv`（#3）且 min 条件子目标 `destruct s0; ... exact Hmin_s0` 有类型错误（fa 更新后 children_done/back_edges_done 集合类型不匹配）。因 #3 仍为 Admitted 且内部类型错误需重写 proof，故重新 admit 以待统一修复。
- **新增 #8 `tarjan_scc_keep_low_valid`**：原为 Qed（line 2876），但其内部 fixpoint induction 中 `VKeepFaChildren` conjunct 的子证明有类型错误（`intros v Hfa_eq` 处 "No product even after head-reduction"）。因依赖 #7 且自身 proof 需修复，故重新 admit。

---

## 依赖关系图

```
#9 tarjan_scc_all_scc_low_valid (2134)
  └─ #8 tarjan_scc_keep_low_valid (2123)
       ├─ IH via Hoare_fix_logicv_conj (VKeepFaChildren u)
       └─ #7 forset_keep_low_forset_inv (2117)
            ├─ #6 tarjan_scc_keep_fa_children_in_universe (2104) — fixpoint 第四个 conjunct
            ├─ #5 process_edge_keep_low_forset_inv (1943)
            │    ├─ #4 set_fa_W_preserves_low_forset_inv (1930) — 树边分支
            │    │    └─ #3 W_preserves_ancestor_inv (1901)
            │    │         └─ #2 process_edge_preserves_ancestor_inv (1886)
            │    ├─ skip fa=u 分支（原 #6#6）→ 需要 low s u ≤ low s v
            │    └─ cross edge proper child（原 #7）→ 依赖 #1 popped_vertex_low_eq_dfn
            └─ fa_children_are_done step case（原 #10）
```

**关键路径**：
- #2 → #3 → #4 → #5（树边分支）→ #7 → #8 → #9
- #1 → #5（cross edge 分支）→ #7 → #8 → #9
- #6 → #7 → #8 → #9

---

## 建议修复顺序

```
Step 1: 基础设施（零依赖，可并行）
  - ✅ stack_split_at_popped_fresh（已添加）
  - ✅ low_forset_inv_children_done_low_le（已证明，line 1298）
  - 选择 #1 popped_vertex_low_eq_dfn 修复路径：
      A. 弱化为 tree_child_popped_low_eq_dfn（推荐）
      B. 新增全局不变量 visited_not_on_stack_low_eq_dfn

Step 2: 自底向上闭合 admit
  #6（tarjan_scc_keep_fa_children_in_universe）—— fixpoint 归纳，独立
  #2（process_edge_preserves_ancestor_inv）→ #3（W_preserves_ancestor_inv）→ #4（set_fa_W_preserves_low_forset_inv）
  #1 → #5 的 cross edge 分支

Step 3: 闭合 #5（process_edge_keep_low_forset_inv）与 #7（forset_keep_low_forset_inv）
  (#2 + #3 + #4 + #1) → #5
  (#5 + #6 + fa_children_are_done) → #7

Step 4: 顶层闭合
  #7 → #8（tarjan_scc_keep_low_valid）
  #8 → #9（tarjan_scc_all_scc_low_valid）
```

---

## 逐条分析（新增 admit）

### #4 `set_fa_W_preserves_low_forset_inv`（line 1930）

```coq
Lemma set_fa_W_preserves_low_forset_inv (u v: V) (done: V -> Prop) (W: ...):
  dg_step g u v ->
  Hoare (fun s => low_forset_inv u done s /\ ~ v ∈ visited s /\ ~ done v)
        (set_fa v u;; W v)
        (fun _ s => low_forset_inv u done s /\ fa s v = u).
```

**语义**：树边分支：先 `set_fa v u` 再递归 `W v`，保持 `low_forset_inv u done` 与 `fa s v = u`。

**阻塞**：#5 树边分支需要此引理。

**修复方向**：
1. 子目标 1（`set_fa v u` 保持 `low_forset_inv`）：已证明除 min 条件外的所有组件。min 条件需要新增 helper lemma `set_fa_preserves_low_forset_inv_min`，因为 `destruct s0; simpl; exact Hmin_s0` 在 fa 更新后类型不匹配。该 helper 使用 `min_eq_forward` + 集合等价性 `Hchild_eq`/`Hback_eq`（`children_done`/`back_edges_done` 在 fa 更新 v 时不改变，因为 `v ∉ done`）。
2. 子目标 2（`W v` 保持不变量）：需要 #3 `W_preserves_ancestor_inv`。

### #8 `tarjan_scc_keep_low_valid`（line 2123）

```coq
Theorem tarjan_scc_keep_low_valid (u: V):
  Hoare (fun s: @SCCSt V => low_pre u s)
        (tarjan_scc g u)
        (fun _ s => low_post u s).
```

**语义**：`tarjan_scc g u` 满足 `low_pre u` → `low_post u`（即从 `low_pre` 状态出发，递归完成后得到 `scc_low_valid_v s u`）。

**阻塞**：#9 顶层定理依赖此引理。

**原证明结构**：使用 `Hoare_fix_logicv_conj` 结合四个 `visited_tag` conjunct：
1. `VSelf`：自身 visited — `tarjan_scc_self_visited`
2. `VKeep w`：保持 visited — `tarjan_scc_keep_visited`
3. `VKeepAll done`：保持 done visited — `tarjan_scc_keep_visited_forall`
4. `VKeepFaChildren u`：保持 fa 子节点在图边宇宙 — **需要 #6**

**错误位置**：在 `VKeepFaChildren` 子目标的 `preloop` 保持性证明中（原 line 2830 附近），`intros v Hfa_eq` 的目标不是 forall 类型。需要在证明中提供 `process_edge` 级别的 fa 保持引理。

**修复方向**：
1. 完成 #6 `tarjan_scc_keep_fa_children_in_universe` 的证明（fixpoint 归纳）
2. 修复 `tarjan_scc_keep_low_valid` 内部 `VKeepFaChildren` 子目标的保持性证明
3. 确保 #7 `forset_keep_low_forset_inv` 已闭合（提供 `scc_low_valid_v s u` 后件）

---

## 风险与注意事项

1. **#1 的通用形式可能不成立**：若保持当前通用语句，需引入强全局不变量；推荐改为带 `fa s v = u` 与 `low_forset_inv` 前提的弱化版本。
2. **`low_forset_inv` 扩展成本**：若将 `visited_not_on_stack_low_eq_dfn` 融入 `low_forset_inv`，需同步修改 `preloop_establishes_low_forset_inv`、`update_low_tree_edge`、`update_low_back_edge` 等已闭合引理。
3. **`visited_tag` 已在使用**：`VKeepFaChildren` 已存在，`tarjan_scc_keep_low_valid` 的 fixpoint 调用已经以 `VKeepFaChildren u` 作为第四个 conjunct。#6 的修复只需完成该 conjunct 的证明，不必再调整 tag 架构。
4. **`set_fa_W_preserves_low_forset_inv` 是隐藏桥接点**：该引理原为 Qed 但调用未证明的 `W_preserves_ancestor_inv`，且 min 条件子目标有类型错误。修复 #3 后还需修复该引理内部的 min 条件证明。
5. **`tarjan_scc_keep_low_valid` 内部类型错误**：原 Qed 证明中 `VKeepFaChildren` 子目标有 type error。修复时需重写该部分的 `Hoare_fix_logicv_conj` 归纳步骤。
6. **禁止引入新 Axiom/Admitted**：所有修复最终必须改为 `Qed`，不能在 `common_case_formal_lib` 或 manual proof 文件中遗留额外公理。
7. **文件当前可编译**：所有 9 处 admit 均以单行 `Admitted.` 形式存在，无语法错误。可以从任意 admit 开始修复，修复完成后将对应 `Admitted.` 改为 `Qed.`。

---

## 相关文档

- `docs/dev/20260619-tarjan-scc-is-low-remaining-issues.md`：上一轮剩余 admit 修复方案（注意：该文档基于较早的 8-admit 状态，未包含当前新增的祖先保持引理 #3/#4/#5）
- `docs/dev/20260619-tarjan-scc-is-low-admit-fix-checklist.md`：逐层修复策略详细分析（同样基于较早状态，行号与当前 HEAD 不一致）
- `docs/dev/20260618-tarjan-scc-is-low-open-issues.md`：更早期的 open issue 汇总
