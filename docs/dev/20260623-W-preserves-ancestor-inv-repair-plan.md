# W_preserves_ancestor_inv 修复计划

**Author**: Kimi Code CLI  
**Date**: 2026-06-23

## 1. 问题定位

`W_preserves_ancestor_inv` 当前的证明尝试用自定义 `F_inv` 调用 `Hoare_forset`，但仍有两处核心缺口：

1. **架构层面：`F_inv` 缺少 dfn 序不变式**

   引理最终后件要求：
   ```coq
   forall w, done w -> In w (stack s) -> dfn s w < dfn s v
   ```
   但当前 `P`/`Q`/`F_inv` 都没有携带它，导致最后的 `If` 分支（`pop_scc` / skip）无法推出最终后件。

2. **实现层面：Tree edge 分支的 `Hoare_bind` 结构错误**

   在 `set_fa a0 a` 之后，代码把 `apply Hoare_conseq_pre ... apply (IH_full a0)` 的第二子目标误当成 `W a0` 之后的 continuation（`get' low a0 ;; update_low a ...`）。因此 `refine (fun u_val => _)` 引入的是状态变量而不是 `W a0` 返回的 `unit`，导致 `u_val : SCCSt` 的类型错误。

## 2. 解决方案

### 2.1 新增辅助引理：`preloop` 建立 dfn 序不变式

在 `W_preserves_ancestor_inv` 之前加入：

```coq
Lemma preloop_preserves_done_dfn_lt_v (u v a: V) (done: V -> Prop):
  Hoare (fun s =>
           (((a = v) /\ done_visited done s /\ ~ v ∈ visited s /\ dfn_inv s) \/
            ((a <> v) /\ (forall w, done w -> In w (stack s) -> dfn s w < dfn s v)))
           /\ ~ done a)
        (preloop a)
        (fun _ s => forall w, done w -> In w (stack s) -> dfn s w < dfn s v).
```

证明分两种情况：

- **`a = v`**：任意 `w ∈ done` 都满足 `w ∈ visited` 且 `v` 未访问、`dfn_inv` 成立，用 `preloop_after_visited_dfn_lt` 直接得到 `dfn s w < dfn s v`。
- **`a <> v`**：`preloop a` 只把 `a` 压栈并设置 `dfn a`，不修改其它顶点的 `dfn`。对栈中任意 `w ≠ a`，`dfn s w` 与 `dfn s v` 保持不变，原不等式继续成立；`w = a` 不可能，因为 `~ done a`。

### 2.2 强化 `P`、`Q`、`F_inv`

在 `W_preserves_ancestor_inv` 内部定义：

```coq
set (dfn_lt_v := fun (s: SCCSt) =>
  forall w, done w -> In w (stack s) -> dfn s w < dfn s v).
```

然后：

- `P a s` 末尾增加 `(a = v \/ dfn_lt_v s)`。
  初始时 `a = v`，该析取左支成立，不强加初始状态没有的 dfn 序。
- `Q a _ s` 加入 `dfn_lt_v s`。
- `F_inv todo s` 加入 `dfn_lt_v s`。

这样 `forset` 循环就能把 dfn 序不变式从空集保持到全集。

### 2.3 `preloop` 子证明

把 `a = v \/ dfn_lt_v s` 加入 `preloop` 的后件，与已有的低链/visited/fa/栈序等性质通过 `Hoare_conj` 合并。使用 2.1 的辅助引理提供该后件。

### 2.4 `forset` body（`H_body`）

#### Tree edge 分支

`set_fa a0 a` 之后使用正确的 `Hoare_bind`：

```coq
eapply Hoare_bind with
  (Q := fun _ s => P a0 tt s /\ a ∈ visited s /\ v ∈ visited s)
  (R := fun _ s => F_inv (todo ∪ [a0]) s).
```

- 第一子目标（`W a0`）：用 `apply (IH_full a0)` 或 `Hoare_conseq_pre` 把 `set_fa` 后的状态整理成 `P a0 /\ a ∈ visited /\ v ∈ visited`。其中 `low_forset_inv` 用 `set_fa_preserves_low_forset_inv_for_new_child`，`fa s v = u` 由 `a0 ≠ v`（`v` 已访问而 `a0` 未访问）保证。
- 第二子目标（`lv <- get' (low a0);; update_low a lv`）：`intros _.`，再用一次 `Hoare_bind` 拆分 `get'` 与 `update_low`。`update_low` 用 `update_low_preserves_low_forset_inv_for_other` 保持 `low_forset_inv`，其余 `visited`/`fa`/`done_visited`/`stack_dfn_order`/`dfn_injective`/`dfn_lt_v` 均因 `update_low` 只改 `low` 而保持。

#### Non-tree edge 分支

- Back edge（`a0` 在栈中）：`update_low a (dfn a0)`，用 `update_low_preserves_low_forset_inv_for_other`；`dfn_lt_v` 因 `dfn` 与栈不变而保持。
- Cross edge（`a0` 不在栈中）：直接跳过，状态不变，所有 `F_inv`  conjuncts 保持。

### 2.5 最终 `If` 分支

`forset` 结束后得到 `F_inv (fun w => dg_step g a w) s`，其中已包含 `dfn_lt_v s`。

- **`pop_scc a` 分支**：
  - `low_forset_inv u done`：用 `pop_scc_keeps_low_forset_inv_other`，其前提要求 `done` 顶点不在被弹出的 `popped` 段。该前提由 `done_not_popped_by_subtree_pop_scc` 提供，而该引理的前提正是 `F_inv` 中的 `dfn_lt_v`、`stack_dfn_order`、`In a (stack s)` 与 `~ done a`。
  - `fa s v = u`、`done_visited`、`stack_dfn_order`、`dfn_injective`、`dfn_lt_v`：`pop_scc` 只修改 `stack` 与 `sccs`，不修改 `fa`/`visited`/`dfn`/`low`，故均保持。

- **Skip 分支**：直接由 `F_inv` 得到目标后件（它已包含 `dfn_lt_v`）。

### 2.6 收尾

`Hfix` 证明后，用 `Hoare_conseq_pre` 把原引理前件映到 `P v`：原前件有 `~ v ∈ visited`，所以 `a = v` 析取成立；再用 `Hoare_conseq_post` 把 `Q v` 映回原后件。

## 3. 实施步骤

1. 在 `W_preserves_ancestor_inv` 前插入 `preloop_preserves_done_dfn_lt_v` 并证明。
2. 在 `W_preserves_ancestor_inv` 证明内：
   - 定义 `dfn_lt_v`；
   - 修改 `P`、`Q`、`F_inv`；
   - 修改 `preloop` 后件并加入 dfn 序；
   - 重写 Tree edge 分支的 `Hoare_bind` 结构；
   - 在 Non-tree edge 分支保留 `dfn_lt_v`；
   - 补全 `If` 分支的 `pop_scc` 与 skip 证明。
3. 用 `rocq-mcp`（`rocq_compile_file` / `rocq_start`）逐段验证。
4. 如有必要，顺带修正文件后面 `forset_keeps_low_forset_inv` 的重复 `Proof.` 与 `s_tree_pre` 笔误，以便整文件通过编译检查。

## 4. 关键引理清单

- `preloop_after_visited_dfn_lt`（来自 `Tarjan_scc_is_dfn.v`）
- `set_fa_preserves_low_forset_inv_for_new_child`
- `update_low_preserves_low_forset_inv_for_other`
- `pop_scc_keeps_low_forset_inv_other`
- `done_not_popped_by_subtree_pop_scc`
- `preloop_preserves_stack_dfn_order`
- `preloop_preserves_dfn_injective`
- `preloop_self_visited` / `preloop_keep_visited`

## 5. 当前状态

本计划尚未落地为实际证明代码；下一步是按上述步骤改写 `W_preserves_ancestor_inv` 的 `Proof` 体并交互式验证。
