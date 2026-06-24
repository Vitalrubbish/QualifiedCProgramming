# W_preserves_ancestor_inv 剩余 admit 修复计划

**Author**: Kimi Code CLI  
**Date**: 2026-06-24

## 1. 当前状态

`SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v` 中的 `W_preserves_ancestor_inv`（line 2635–3141）目前仍有 **5 处局部 `admit.` 与 1 处顶层 `Admitted.`**：

| 位置（行号） | 类型 | 所处分支 | 目标命题 |
|---|---|---|---|
| 2969 | `admit.` | Tree edge → `W v ;; get' low v ;; update_low` | `In par (stack s)`（`W v` 后 `par` 仍在栈中） |
| 2971 | `admit.` | Tree edge → `W v ;; get' low v ;; update_low` | `dfn s anc < dfn s par`（`W v` 后 dfn 不等式保持） |
| 3012 | `admit.` | Tree edge → `update_low a lv` 后件 | `forall w, d w -> In w (stack s) -> dfn s w < dfn s a` |
| 3020 | `admit.` | Tree edge → `update_low a lv` 后件 | `forall w, d w -> In w (stack s) -> dfn s w < dfn s a` |
| 3131 | `admit.` | `If (low a = dfn a)` → `pop_scc a` 分支 | 调用 `pop_scc_preserves_ancestor_inv` 后剩余合取式 |
| 3141 | `Admitted.` | 定理顶层 | 关闭全部子目标后改为 `Qed.` |

这些 admit 可归约为两类核心问题：

1. **栈/祖先不变式在递归调用 `W v` 与 `pop_scc a` 后的保持**：需要证明 `par`/`anc` 不会被 `W v` 内部的 `pop_scc` 弹出。
2. **`update_low` / `pop_scc` 对 dfn 序不变式的保持**：`dfn` 与 `stack` 不被这些操作修改（或修改可预测），因此原有 dfn 序事实可直接传递。

## 2. 核心不变式回顾

当前证明已把 `P_forset` 强化为包含：

```coq
low_forset_inv anc d s /\ fa s a = par /\ done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ dfn s anc < dfn s a /\ fa s tv = tp /\ tv ∈ visited s /\ ~ d a /\ In a (stack s) /\ anc <> a /\ par <> a /\ dg_step g par a /\ (forall w, d w -> In w (stack s) -> dfn s w < dfn s a) /\ In par (stack s) /\ dfn s anc < dfn s par
```

其中 `In par (stack s)` 与 `dfn s anc < dfn s par` 已经在进入 forset body 时成立。问题出在这两个事实经过 `W v` 与 `pop_scc a` 后没有被显式传递。

关键观察：

- `W v` 可能执行 `pop_scc v`，但只弹出 `v` 的子树/SCC；`par` 与 `anc` 是 `v` 的祖先（`dg_step g par a` 且 `dg_step g a v`），`dfn s par < dfn s a < dfn s v`，因此不会被弹出。
- `pop_scc a` 只修改 `stack` 与 `sccs`，不修改 `fa`、`visited`、`dfn`、`low`；且只弹出 `a` 及其上方顶点，`par`/`anc` 因 `dfn` 更小而位于 `a` 下方。
- `update_low` 只修改 `low`，不修改 `stack`/`dfn`，因此 dfn 序合取式直接保持。

## 3. 修复方案

### 3.1 新增辅助引理：栈中低位顶点在 `pop_scc` 后保留

在 `W_preserves_ancestor_inv` 之前新增：

```coq
Lemma pop_scc_preserves_stack_below (a x: V) (s: @SCCSt V):
  In a (stack s) ->
  In x (stack s) ->
  dfn s x < dfn s a ->
  stack_dfn_order s ->
  forall s', exec (pop_scc a) s s' -> In x (stack s').
```

**证明思路**：

1. `pop_scc a` 展开为 `stack_split_at (stack s) a` 后只保留 `rest` 段。
2. 由 `stack_split_at_partition` 可知：若 `In x (stack s)` 且 `~ In x popped`，则 `In x rest`。
3. 反设 `In x popped`，由 `stack_split_at_in_popped_before_a` 得存在 `l1, l2` 使 `stack s = l1 ++ x :: l2` 且 `In a l2`。
4. 由 `stack_dfn_order` 得 `dfn s a <= dfn s x`，与 `dfn s x < dfn s a` 矛盾。

> 该引理可同时覆盖 `W v` 内部 `pop_scc v` 后 `par`/`anc` 的保留，以及 `pop_scc a` 后 `par`/`anc` 的保留。

### 3.2 修复 Tree edge 分支（line 2969、2971）

当前结构在 `W v` 上使用了两次 `IH` 的 `Hoare_conj`：

- 第一次 `IH v (anc, a, d, tv, tp)` 得到祖先不变式。
- 第二次 `IH v (anc, a, d, a, par)` 得到 `fa s a = par`。

**问题**：两次 IH 的后件都没有显式包含 `In par (stack s)` 与 `dfn s anc < dfn s par`。

**修复步骤**：

1. **把 `In par (stack s)` 与 `dfn s anc < dfn s par` 作为 frame 加入 `W v` 的前件/后件**。
   由于 `W v` 只可能弹出 `v` 的子树，而 `par` 在栈中位于 `v` 下方（`dfn s par < dfn s a < dfn s v`），这两个性质被 `pop_scc_preserves_stack_below` 保持。

2. **重写 `Hoare_conj` 后的 `Hoare_bind` 前件**（line 2950 开始）：
   将
   ```coq
   low_forset_inv anc d s /\ fa s a = par /\ ... /\ In par (stack s) /\ dfn s anc < dfn s par
   ```
   加入 `get' low v ;; update_low a lv` 的前件，并确保 `W v` 的后件包含它。

3. **关闭 line 2969**：
   直接由 `W v` 后件中的 `In par (stack s)` 得到。

4. **关闭 line 2971**：
   `dfn` 在 `W v` 中不被修改，因此 `dfn s anc < dfn s par` 保持；若 `W v` 后件未显式携带，可用 `Hoare_conseq_post` 把它加回。

### 3.3 修复 `update_low` 后 `dfn_d_lt`（line 3012、3020）

`update_low a lv` 只修改 `low a`，不修改 `stack` 或 `dfn`。因此

```coq
forall w, d w -> In w (stack s) -> dfn s w < dfn s a
```

在 `update_low` 前后完全相同。

**修复步骤**：

1. 在 `update_low` 的 pre/post 中显式加入 `dfn_d_lt`。
2. 在 `unfold set_low; intro_state; hoare_auto_s` 后，直接复用前件的 `Hdfn_d_lt_a`。
3. 两处 `admit.` 改为 `exact Hdfn_d_lt_a`（或对应上下文中的名称）。

### 3.4 修复 `pop_scc a` 分支（line 3131）

当前在 line 3128 调用 `pop_scc_preserves_ancestor_inv` 后得到：

```coq
low_forset_inv anc d s /\ fa s a = par /\ In anc (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ done_visited d s
```

需要补充到 `Q` 的剩余合取式：

```coq
(forall w, d w -> In w (stack s) -> dfn s w < dfn s a) /\ dfn s anc < dfn s a /\ fa s tv = tp /\ tv ∈ visited s /\ ~ d a /\ In par (stack s) /\ dfn s anc < dfn s par /\ anc <> a /\ par <> a /\ dg_step g par a
```

**修复步骤**：

1. `fa s tv = tp`、`tv ∈ visited s`、`~ d a`、`dg_step g par a`、`anc <> a`、`par <> a`：
   `pop_scc a` 不修改 `fa`、`visited`、`d` 关系，直接保持。

2. `In par (stack s)`、`In anc (stack s)`：
   由 `pop_scc_preserves_stack_below` 得到（前提 `dfn s par < dfn s a` 与 `dfn s anc < dfn s a` 已在 `P_forset` 中）。

3. `dfn s anc < dfn s a`、`dfn s anc < dfn s par`、`forall w, d w -> In w (stack s) -> dfn s w < dfn s a`：
   `pop_scc a` 不修改 `dfn`，因此直接保持。

4. 可 inline 一个小 proof script：
   ```coq
   intros _ s Hpost.
   destruct Hpost as [Hlow_inv' [Hfa_a' [Hina'' [Horder'' [Hinj'' Hdv'']]]]].
   assert (Hin_par': In par (stack s)) by (eapply pop_scc_preserves_stack_below; eauto; try lia).
   assert (Hdfn_anc_a': dfn s anc < dfn s a) by (simpl; auto).
   assert (Hdfn_anc_par': dfn s anc < dfn s par) by (simpl; auto).
   ... (* 其余合取式由 pop_scc 只改 stack/sccs 直接得到 *)
   ```

### 3.5 顶层 `Admitted.` → `Qed.`

关闭上述 5 处 admit 后，将 line 3141 的 `Admitted.` 改为 `Qed.`。

## 4. 推荐实施顺序

1. **新增 `pop_scc_preserves_stack_below`** 并交互式验证（`rocq_start` + `rocq_check`）。
2. **修复 Tree edge 分支**：
   - 在 `W v` 的 Hoare triple 中显式携带 `In par (stack s)` 与 `dfn s anc < dfn s par`。
   - 关闭 line 2969、2971。
3. **修复 `update_low` 后件**：关闭 line 3012、3020。
4. **修复 `pop_scc a` 分支**：关闭 line 3131。
5. **把 `Admitted.` 改为 `Qed.`**，并用 `rocq_compile_file` 整文件验证。

## 5. 依赖的已有引理

- `stack_split_at_partition`
- `stack_split_at_in_popped_before_a`
- `stack_dfn_order`
- `pop_scc_preserves_ancestor_inv`
- `update_low_preserves_low_forset_inv_for_other`
- `done_not_popped_by_subtree_pop_scc`

## 6. 风险与注意事项

- `W v` 内部的 `pop_scc` 可能发生在 `v` 的任意递归深度；只要 `par`/`anc` 的 dfn 严格小于 `v` 的 dfn，且栈序成立，`pop_scc_preserves_stack_below` 就适用。
- 需要确认 `par <> v` 与 `anc <> v`：由 `dg_step g par a`、`dg_step g a v` 与无自环假设可推出（图边无自环，且 `dg_step` 反映原图边）。
- `update_low` 分支中的 `Hdfn_d_lt_a` 名称在不同子目标中可能不同，需按 `destruct` 后的实际绑定名引用。
- 完成本定理后，下游 `set_fa_W_preserves_low_forset_inv`（line 3176 起）仍可能因调用 `W_preserves_ancestor_inv` 而出现类型/前提不匹配，需要单独回归检查。
