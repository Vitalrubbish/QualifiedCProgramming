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

1. **`hoare_fix_nolv_auto` 的参数替换问题**：
   - 当前证明使用 `hoare_fix_nolv_auto` 自动生成 fixpoint 的 `P`/`Q`。
   - 该策略会把原目标中的具体顶点 `v` 替换成 fixpoint 参数 `a`，于是目标中关于特定子节点 `v` 的属性 `fa s v = u` 被错误地参数化为 `fa s a = u`。
   - 结果是：fixpoint 不变式中的 `a` 同时承担“顶层调用的子节点 `v`”和“递归调用时的任意参数”两种角色，导致不变式无法同时适用于顶层调用与递归调用。

2. **Fixpoint 变量隔离**：
   - 证明内部用 `hoare_fix` 引入的 `W` 是局部 fixpoint 变量（`W'`），而外部已证引理（如 `tarjan_scc_preserves_visited`）中的 `W` 是另一独立变量。
   - 二者类型相同但无法直接统一，已证的外部引理不能无额外条件地代入到 fixpoint IH 中。

3. **Forset 体不变式过弱**：
   - 在 `forset (process_edge u W)` 的循环体内，当前可用的不变量仅有 `done_visited done`（以及 `fa s v = u` 等零星事实），但 fixpoint IH 要求更强的前置条件（如 `low_forset_inv u done` 或 `a ∈ visited`）。
   - 这导致无法在当前证明结构内直接调用 IH 关闭 admit。

4. **需要的结构性修改**：
   - 必须弃用 `hoare_fix_nolv_auto`，改用显式的 `Hoare_fix`（或等价地手工指定 `P`/`Q`），将 `fa s v = u` 以自由变量形式捕获在不变式中，而不是把它当成 fixpoint 参数的一部分。
   - 增强后的 fixpoint 不变式应显式包含：
     - `a ∈ visited s`
     - `low_forset_inv u done s`
     - `done_visited done s`
     - `fa s v = u`（`v` 为顶层调用时固定的子节点，不作为 fixpoint 参数）
   - 预计需要重写约 90 行的 `W_preserves_ancestor_inv` 证明骨架。

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

#### 3.2.1 `W_preserves_ancestor_inv` 的解决思路

**核心方案：使用 `Hoare_fix_logicv` 手工指定 `P`/`Q`，将 `v` 作为独立逻辑变量捕获。**

`hoare_fix_nolv_auto` 只能生成 `P: A -> Σ -> Prop`，它会把目标中所有出现的具体顶点都试图参数化，从而把固定的 `v` 混进 fixpoint 参数 `a`。改用 `Hoare_fix_logicv` 可以把 `v` 提升到逻辑变量 `C` 中，让 `a` 单纯作为递归参数：

```coq
eapply Hoare_fix_logicv with (C := V) (c := v)
  (P := fun a v s =>
     low_forset_inv u done s
     /\ fa s v = u
     /\ ~ done a
     /\ done_visited done s
     /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s)
  (Q := fun a v _ s =>
     low_forset_inv u done s
     /\ fa s v = u
     /\ v ∈ visited s
     /\ done_visited done s).
```

**为什么这能解决三个 admit：**

- **`fa s v = u` 不再被参数化**：`v` 作为逻辑变量自由出现，在 fixpoint 调用的整个过程中保持固定，`P` 和 `Q` 都直接断言 `fa s v = u`。
- **`a ∈ visited` 进入局部循环不变式**：fixpoint 体内部先走 `preloop a`，该步骤会建立 `a ∈ visited s`。随后对 `forset (process_edge a W)` 使用包含 `a ∈ visited` 的局部循环不变式（例如用 `Hoare_forset` 直接推理，或调整 `forset_keeps_low_forset_inv` 的 IH 形式），从而在该上下文中直接调用 `IH x`。
- **`done_visited done` 成为 `P`/`Q` 的固定组成部分**：由于 `P` 显式包含 `done_visited done s`，fixpoint IH 的后置条件 `Q` 也包含它，forset 循环体和 pop_scc 分支都不需要额外证明。

**实现要点：**

1. **弃用 `hoare_fix_nolv_auto`**，改为显式 `eapply Hoare_fix_logicv with (...)`，手工填写 `P`、`Q`、逻辑变量 `v`。
2. **用 `Hoare_bind` 把 `preloop` 与 `forset+pop_scc` 分开**：
   - `preloop a` 的任务：从 `P a v s` 推出 `P a v s /\ a ∈ visited s /\ v ∈ visited s`；
   - `forset+pop_scc` 的任务：在上述增强状态下保持 `Q` 的三部分。
3. **在 forset 循环体中直接调用 `IH x`**：由于当前状态满足 `P x v s` 且 `a ∈ visited s` 已在局部循环不变式中，可以直接用 `apply (IH x)` 或 `eapply Hoare_conseq_pre` 适配。
4. **如果 `forset_keeps_low_forset_inv` 的 IH 形式仍要求 `a ∈ visited` 出现在 `W x` 前置条件中**，有两种处理方式：
   - **(A) 调整 `forset_keeps_low_forset_inv` 的假设**：把 `a ∈ visited` 从 `IH` 前提中移到 forset 循环不变式中，使 `IH` 只要求 `low_forset_inv u done /\ ~ x ∈ visited /\ ~ done x /\ done_visited done`。
   - **(B) 在 `W_preserves_ancestor_inv` 中内联 forset 循环证明**：不调用 `forset_keeps_low_forset_inv`，而是直接对 `forset` 使用 `Hoare_forset`，在循环不变式中显式写入 `a ∈ visited`、`low_forset_inv u done`、`fa s v = u`、`done_visited done`。
5. **`pop_scc` 分支**：在 `u <> a` 前提下，用 `pop_scc_keeps_low_forset_inv_other` 保持 `low_forset_inv`，用 `pop_scc_preserves_done_visited` 保持 `done_visited`，用 `done_vertices_not_popped_in_subtree` 保证 `done` 中顶点不被弹出。`fa s v = u` 由 `pop_scc` 不修改 `fa` 直接保持。

**预期改动范围**：`W_preserves_ancestor_inv` 证明骨架约 90 行，主要集中在 fixpoint 引入、`preloop` 后状态拆分、以及 forset 循环体的 `IH` 调用方式。

#### 3.2.2 处理 `u` 被统一为 `fa s c` 的参数统一问题

**新发现**：在 `Hoare_fix_logicv` 框架下，`P`/`Q` 和循环不变式中都包含 `fa s c = u`。当进入 forset 循环体、tree-edge、non-tree edge 或 `pop_scc` 等深层分支并尝试 `apply`/`refine`/`eapply` 某个以 `u` 为参数的辅助 lemma（如 `set_fa_preserves_low_forset_inv_for_new_child`、`update_low_preserves_low_forset_inv_for_other`、`pop_scc_keeps_low_forset_inv_other`）时，Coq 8.20.1 的 unification 会把 lemma 参数 `u` 错误实例化为 `fa s0 c`，导致后续分支中 `u` 变量消失，无法继续引用 `u`。

**根本原因**：当前上下文存在等式 `fa s0 c = u`。当 lemma 的结论或前提中出现与 `fa s0 c` 匹配的位置时，unifier 倾向于把参数 `u` 直接折叠为 `fa s0 c`，而不是保持 `u` 为独立变量。

**解决方案（按推荐顺序）**：

1. **在 apply 前把目标与相关假设中的 `fa s c` 统一替换为 `u`**（最推荐）：
   在进入需要引用 `u` 的深层分支后、调用辅助 lemma 之前，先执行：
   ```coq
   change (fa s c) with u in *.
   ```
   或等价的 rewrite：
   ```coq
   rewrite <- Hfa in *.
   ```
   这样上下文和目标中不再出现 `fa s c`，只剩下 `u`。随后 `apply`/`refine` 辅助 lemma 时，Coq 没有理由把 `u` 反向替换为 `fa s c`，`u` 将保持为独立参数。

2. **如果 `change`/`rewrite` 范围过大**，可以只针对包含 `fa s c` 的关键假设和当前目标进行替换：
   ```coq
   change (fa s c) with u in Hinv, Hfa, |-.
   ```
   注意：替换后 `Hfa` 可能变成 `u = u`，此时可以直接 `clear Hfa` 或保留不影响后续证明。

3. **备选：改变等式方向**：
   在进入深层分支前将 `Hfa: fa s c = u` 对称化为 `u = fa s c`：
   ```coq
   symmetry in Hfa.
   ```
   在某些情况下，等式方向会影响 unifier 的选择，使其更倾向于保持 `u` 不变。若该方案单独有效，改动最小。

4. **备选：使用 `remember` 隔离 `u`**：
   ```coq
   remember u as u0 eqn:Hu0.
   ```
   这样当前上下文中 `u` 的所有出现都变为新变量 `u0`，而 `Hu0: u0 = u` 作为等式存在。调用辅助 lemma 时传入 `u0`：
   ```coq
   apply (update_low_preserves_low_forset_inv_for_other u0 ...).
   ```
   如果 unifier 仍然尝试替换，可以在 apply 前再执行 `change (fa s c) with u0 in *`。

5. **备选：在 apply 时使用 `@` 全显式语法并显式锁定 `u`**：
   ```coq
   refine (@update_low_preserves_low_forset_inv_for_other V E equiv0 H0 g u _ _ _ _ _ _ _).
   ```
   若 `u` 仍被替换，说明问题不在参数推断而在目标形态，应回到方案 1 先做 `change`/`rewrite`。

**被阻塞分支的具体处理建议**：

| 行号 | 内容 | 处理建议 |
|------|------|----------|
| 2558 | `u = a` 分支 | 依赖 `forset_keep_low_forset_inv`（Phase 3 第 10 步），暂保留 admit |
| 2587–2588 | Tree-edge `set_fa+W` | 在 `set_fa` 后、调用 `set_fa_preserves_low_forset_inv_for_new_child` 或 `IH` 前，执行 `change (fa s c) with u in *`，保持 `u` 为参数 |
| 2590 | Non-tree edge | 在调用 `update_low_preserves_low_forset_inv_for_other` 前执行 `change (fa s c) with u in *`，确保 `u` 不被折叠 |
| 2592 | `pop_scc` | 在调用 `pop_scc_keeps_low_forset_inv_other` 前执行 `change (fa s c) with u in *`；`fa s c = u` 的保持由 `pop_scc` 不修改 `fa` 直接得出 |

**结论**：`Hoare_fix_logicv` 方案本身正确，`preloop` 和 `IH` 类型也已验证。当前阻塞 purely 是 Coq unification 在等式 `fa s c = u` 存在时的方向选择问题。通过在深层分支中主动把 `fa s c` 替换为 `u`（方案 1），可以关闭 tree-edge、non-tree edge、`pop_scc` 三处 admit；`u = a` 分支仍依赖 `forset_keep_low_forset_inv`（Phase 3）。

**结论**：定理本身正确，但 5 处 `W_preserves_ancestor_inv` 内部 admit 中的 3 处（`a ∈ visited`、`done_visited`、`fa s v = u`）必须通过上述显式 `Hoare_fix_logicv` 方案来关闭；`fa s c = u` 导致的参数统一问题需用 `change`/`rewrite` 技巧处理；剩余 `u = a` 分支依赖 `forset_keep_low_forset_inv`，`pop_scc` 分支在解决统一问题后用栈顺序引理即可关闭。

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
   - 弃用 `hoare_fix_nolv_auto`，改用显式 `Hoare_fix_logicv` 手工指定 fixpoint 不变式 `P`、后置条件 `Q`，并把顶层子节点 `v` 作为独立逻辑变量 `C` 捕获：
     ```coq
     eapply Hoare_fix_logicv with (C := V) (c := v)
       (P := fun a v s =>
          low_forset_inv u done s /\ fa s v = u /\ ~ done a /\ done_visited done s
          /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s)
       (Q := fun a v _ s =>
          low_forset_inv u done s /\ fa s v = u /\ v ∈ visited s /\ done_visited done s).
     ```
   - 用 `Hoare_bind` 把 `preloop a` 与 `forset+pop_scc` 分开：`preloop` 负责建立 `a ∈ visited` 和 `v ∈ visited`；`forset+pop_scc` 在包含这些事实的局部不变式下保持 `Q`。
   - 在 forset 循环体中直接调用 `IH x`，因为 `P x v s` 已经包含 `low_forset_inv u done`、`fa s v = u`、`done_visited done` 等所需前提；局部循环不变式额外提供 `a ∈ visited`。
   - **处理 `u` 被统一为 `fa s c` 的问题**：在 tree-edge、non-tree edge、`pop_scc` 等深层分支中，调用以 `u` 为参数的辅助 lemma 前，先执行 `change (fa s c) with u in *`（或 `rewrite <- Hfa in *`），强制把上下文和目标中的 `fa s c` 替换为 `u`，避免 Coq unifier 把 lemma 参数 `u` 折叠为 `fa s c`。
   - 工作量估算：预计需重写约 90 行的证明骨架，主要是 fixpoint 引入、`preloop` 后状态拆分、以及 forset 循环体的 `IH` 调用方式。

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
   - 在 Phase 2 显式 `Hoare_fix_logicv` 框架下，逐分支关闭 5 处 admit：
     - `u = a` 分支：依赖 `forset_keep_low_forset_inv`（Phase 3 第 10 步）提供所需上下文，暂保留 admit；
     - `a ∈ visited` 分支：由 `preloop a` 建立后进入 forset 局部循环不变式，循环体调用 `IH x` 时直接拥有该事实；
     - `done_visited done` 分支：由 `P`/`Q` 显式包含 `done_visited done`，forset 与 pop_scc 直接保持；
     - `pop_scc` 分支：在调用 `pop_scc_keeps_low_forset_inv_other` 前先用 `change (fa s c) with u in *` 解决参数统一问题，再用 `pop_scc_keeps_low_forset_inv_other` + `pop_scc_preserves_done_visited` + `done_vertices_not_popped_in_subtree` 组合证明；`fa s v = u` 由 `pop_scc` 不修改 `fa` 直接保持；
     - `fa s v = u` 分支：由 `P`/`Q` 显式包含 `fa s v = u`（`v` 作为自由逻辑变量）直接可得；
     - **tree-edge / non-tree edge 分支**：在调用 `set_fa_preserves_low_forset_inv_for_new_child`、`update_low_preserves_low_forset_inv_for_other` 等辅助 lemma 前，先用 `change (fa s c) with u in *`（或 `rewrite <- Hfa in *`）消除目标中的 `fa s c`，防止 lemma 参数 `u` 被折叠为 `fa s c`。
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

- **最大风险（更新）**：`W_preserves_ancestor_inv` 的 fixpoint 不变式重构已从“增强不变式”具体化为“手工重写显式 `Hoare_fix_logicv` 证明骨架”。核心风险在于：
  - 显式 `Hoare_fix_logicv` 的 `P`/`Q` 形式必须严格匹配命令语义，否则 `eapply` 会失败；
  - `fa s v = u` 以自由逻辑变量捕获后，需要确保在递归调用和 forset 循环体中都能保持；
  - `P` 不能包含 `a ∈ visited` 或 `v ∈ visited`（初始调用不满足），但 `Q` 需要包含 `v ∈ visited`，这对 `preloop` 与 `forset` 之间的状态拆分提出了精确要求；
  - 重写约 90 行证明骨架期间，可能暴露当前 theorem statement 缺少的必要前提（例如 `v` 与 `a` 的关系、或 `done` 的额外约束）。
  **当前进展**：`Hoare_fix_logicv` 调用本身成功，`IH` 类型正确，`preloop` 证明已编译通过；`fa s c = u` 导致的参数统一问题已有明确解决方案（`change`/`rewrite` 技巧），不再是结构性阻塞。
  这是 Phase 2 的前置阻塞项，必须在其余 admit 之前完成。
- **次大风险**：`done_vertices_not_popped_in_subtree` 这类栈顺序不变式需要诉诸 Tarjan 实现的全局不变式（如 `stack_in_visited`、`dfn_inv`、`dfn_valid` 的相互作用）。如果实现中某些不变式尚未在 `Tarjan_scc_basics.v` / `Tarjan_scc_is_dfn.v` 中建立，可能需要先补那些引理。
- **表述修正影响面小**：Phase 1 的两处修改只影响本文件，且调用点都有现成假设可填。
- **`tarjan_scc_all_scc_low_valid` 工作量仍最大**：因为它把单棵树结论推广到森林，需要仔细处理不同 DFS 树之间的状态隔离。
- **建议执行顺序**：
  1. 先验证 Phase 1 的修改能编译通过，避免在错误 statement 上堆叠证明；
  2. 优先完成 Phase 2 的 fixpoint 不变式重构，确认 3 处"需增强 fixpoint 不变式"的 admit 可关闭；
  3. 再补充 `done_vertices_not_popped_in_subtree` 等栈顺序引理，关闭剩余 admit；
  4. 最后进入 Phase 3 收尾主要引理。
