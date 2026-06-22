# Tarjan-scc-is-low.v Admit 关闭计划（v3 当前文件版）

**Author**: Vitalrubbish
**Date**: 2026-06-21

## 1. 背景

本计划基于当前 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`（3323 行）的最新状态，重新盘点所有未关闭的 `admit` / `Admitted`，判断对应定理是否成立，并给出按依赖顺序执行的关闭步骤。

> 说明：此前已有 `20260621-tarjan-scc-is-low-admit-closure-plan-v2.md`，但文件在当天继续演进（新增 `done_not_popped_by_subtree_pop_scc`、`tarjan_scc_establishes_and_preserves_scc_low_valid` 等引理，且 `W_preserves_ancestor_inv`、`forset_keep_low_forset_inv`、`tarjan_scc_keep_low_valid`、`tarjan_scc_all_scc_low_valid` 的证明骨架均有调整），因此重新整理 v3。

## 2. 当前 Admit 全量盘点

| 所在引理/定理 | 行号 | 形式 | 具体阻塞点 |
|---|---|---|---|
| `done_not_popped_by_subtree_pop_scc` | 2515 | `Admitted` | DFS 栈结构：done 顶点为何在 `a` 下方 |
| `W_preserves_ancestor_inv` | 2652 | `admit` | `cv = a1` 时证明 `cv ∈ visited` |
| `W_preserves_ancestor_inv` | 2713 | `admit` | non-tree edge：`intro_state` evar / pre-weakening |
| `W_preserves_ancestor_inv` | 2717 | `admit` | `pop_scc a`：需 `done_not_popped` + `In a stack` |
| `W_preserves_ancestor_inv` | 2724 | `Admitted` | 顶层 |
| `forset_keep_low_forset_inv` | 3148 | `admit` | tree-edge：`set_fa_W` + `update_low_tree_edge` 组合 |
| `forset_keep_low_forset_inv` | 3152 | `admit` | non-tree edge：back-edge / cross-edge 分支 |
| `forset_keep_low_forset_inv` | 3174 | `Admitted` | 顶层 |
| `tarjan_scc_keep_low_valid` | 3202 | `admit` | `preloop` 后建立 `low_forset_inv a ∅` + `fa-child→self` |
| `tarjan_scc_keep_low_valid` | 3214 | `admit` | forset 步骤：应用 `forset_keep_low_forset_inv` |
| `tarjan_scc_keep_low_valid` | 3218 | `admit` | `pop_scc a`（`low a = dfn a`）分支 |
| `tarjan_scc_keep_low_valid` | 3220 | `admit` | skip（`low a <> dfn a`）分支 |
| `tarjan_scc_keep_low_valid` | 3221 | `Admitted` | 顶层 |
| `tarjan_scc_establishes_and_preserves_scc_low_valid` | 3242 | `Admitted` | 跨 DFS 树保持性 |
| `tarjan_scc_all_scc_low_valid` | 3268 | `admit` | 后加强：`visited ⊆ original_vvalid` |
| `tarjan_scc_all_scc_low_valid` | 3284 | `admit` | `a` 未访问分支：调用跨树保持引理 |
| `tarjan_scc_all_scc_low_valid` | 3291 | `admit` | `a` 已访问分支：需 `scc_low_valid_v s a` |
| `tarjan_scc_all_scc_low_valid` | 3292 | `Admitted` | 顶层 |

共 **18 处** admit/Admitted（6 个顶层 + 12 个局部）。

## 3. 定理正确性审查

### 3.1 `done_not_popped_by_subtree_pop_scc` — 表述可能偏弱，性质正确

**当前 statement**：
```coq
low_forset_inv u done s -> done_visited done s -> ~ done a ->
forall w, done w -> forall popped' rest',
  stack_split_at (stack s) a = (popped', rest') -> ~ In w popped'.
```

**判断**：结论方向正确——`done` 中的顶点都是 `u` 的已处理邻居，处理时间早于当前子树顶点 `a`，因此它们在栈中位于 `a` 下方或已被弹出。

**潜在问题**：当前前提未要求 `In a (stack s)`，也未要求 `a` 的 dfn 大于 `done` 中顶点的 dfn。仅凭 `low_forset_inv` 与 `done_visited` 是否足够，需要验证。若不足，建议补强为：
```coq
low_forset_inv u done s -> done_visited done s -> ~ done a ->
In a (stack s) ->
(forall w, done w -> exists dfn_w, dfn s w < dfn s a) ->
...
```
实际使用时（`W_preserves_ancestor_inv` 的 `pop_scc` 分支）通常能拿到 `a ∈ visited` 以及 `a` 刚被 `preloop` 压栈，因此 `In a (stack s)` 和 dfn 顺序事实可获得。

### 3.2 `W_preserves_ancestor_inv` — 表述正确，4 处 admit 可关闭

**判断**：定理正确。子树 `tarjan_scc g v` 处理期间，父顶点 `u` 的 `low_forset_inv`、`fa s v = u`、`done_visited` 均保持。

当前证明已将 `pu <> a` 加入 `Hoare_fix_logicv_conj` 不变式，`u = a` 分支已解决。剩余 3 处 admit 的关闭思路：

- **2652 `cv = a1`**：不依赖把 `cv ∈ visited` 穿线进 forset 不变式，而是直接利用 `low_forset_inv` 中的 `fa_visited`：
  - `fa s1 cv = pu = u`，且 `u <> v = cv`（由 `Hneq` 与 `cv = v`），故 `fa s1 cv <> cv`；
  - `fa_visited` 推出 `cv ∈ visited s1`；
  - `a1` 未访问，故 `cv <> a1`，矛盾。

- **2713 non-tree edge**：`update_low a lv` 只改 `low a`。由于 `u <> a`（`Hneq_ua`），可用 `update_low_preserves_low_forset_inv_for_other`。当前阻塞是 `intro_state` 产生 evar，导致 pre-weakening 无法统一。建议把该分支改写成显式 `apply Hoare_bind` / `apply Hoare_choice`，避免 `intro_state`。

- **2717 `pop_scc a`**：
  - 先证 `In a (stack s)`（由 `preloop` 性质）；
  - 用 `done_not_popped_by_subtree_pop_scc` 得到 `done` 顶点不在被弹段；
  - 应用 `pop_scc_keeps_low_forset_inv_other` 保持 `low_forset_inv`；
  - `fa s cv = pu` 由 `pop_scc` 不修改 `fa` 保持；
  - `done_visited` 由 `pop_scc_preserves_done_visited` 保持。

### 3.3 `forset_keep_low_forset_inv` — 表述正确，2 处 admit 可关闭

**判断**：定理正确。循环不变式 `P(done)` 已完整：
```coq
low_forset_inv u done s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s /\
done_visited done s /\ (forall v, fa s v = u /\ fa s v <> v -> v ∈ done)
```

- **3148 tree-edge**：`set_fa a0 u ;; W a0` 后用 `set_fa_W_preserves_low_forset_inv` 保持 `low_forset_inv u done` 并得到 `fa a0 = u`；再用 `update_low_tree_edge` 转移到 `done ∪ [a0]`。`dfn_valid`/`dfn_inv`/`fa_visited` 由 W 假设保持；`done_visited (done ∪ [a0])` 由 `a0 ∈ visited` 得到；`fa-child→done` 由旧顶点 `fa` 不变 + 新顶点 `a0` 属于 `done ∪ [a0]` 得到。

- **3152 non-tree edge**：分 back-edge 与 cross-edge。
  - Back-edge：`a0 ∈ stack` 且 `fa s a0 <> u`，用 `update_low_back_edge`（需 `done ⊆ visited`，由 `done_visited` 给出）。
  - Cross-edge：`a0` 已访问但不在栈，且非 `u` 树孩子。`children_done` 与 `back_edges_done` 均不因加入 `a0` 而改变，`low u` 也不变，直接用集合等价保持 `low_forset_inv`。

### 3.4 `tarjan_scc_keep_low_valid` — 表述正确，但 fixpoint 后置需加强

**判断**：定理 `low_pre u -> tarjan_scc g u -> low_post u` 正确。

当前 4 处 admit：

- **3202 `preloop` 分支**：`preloop_establishes_low_forset_inv` 已给出 `low_forset_inv a ∅` 及 `dfn_valid`/`dfn_inv`/`fa_visited`。`forall v, fa s v = a -> v = a` 由 `low_pre_no_fa_child_of_u` 与 `fa` 不被 preloop 修改得到。这处 admit 主要是 `Hoare_conj` 嵌套整理问题。

- **3214 forset 步骤**：需把 fixpoint IH 的后置条件加强为 `low_post x s /\ x ∈ visited s`（见下述“必要表述调整”），从而满足 `forset_keep_low_forset_inv` 的 `HW_pre_post` 假设。

- **3218 `pop_scc a`**：forset 后已有 `scc_low_valid_v s a /\ low s a = dfn s a`，直接应用 `pop_scc_keep_scc_low_valid_v`。

- **3220 skip 分支**：状态不变，`scc_low_valid_v s a` 与 `dfn_valid`/`dfn_inv`/`fa_visited` 直接给出 `low_post a s`。

#### 必要表述调整：fixpoint 后置加强

`tarjan_scc_keep_low_valid` 当前使用 `Hoare_fix_logicv_conj`，`Q = low_post a s`。但 `forset_keep_low_forset_inv` 要求 `W x` 的后置包含 `x ∈ visited s`（即 `HW_pre_post` 中的 `low_post x s /\ u ∈ visited s`）。建议把 fixpoint 后置改为：
```coq
fun (a: V) (_: V) (_: unit) (s: SCCSt) => low_post a s /\ a ∈ visited s
```
这样 `IH_low` 直接给出 `a ∈ visited s`，`forset_keep_low_forset_inv` 的四个 W 假设都能由 IH 与 `tarjan_scc_preserves_visited` 组合得到。

### 3.5 `tarjan_scc_establishes_and_preserves_scc_low_valid` — 表述可能需微调

**当前 statement**：
```coq
Hoare (fun s => scc_low_valid s /\ dfn_inv s /\ fa_visited s /\ dfn_valid g s root /\ ~ a ∈ visited s)
      (tarjan_scc g a)
      (fun _ s => scc_low_valid s /\ dfn_inv s /\ fa_visited s /\ dfn_valid g s root).
```

**判断**：结论方向正确。执行 `tarjan_scc g a` 后，新访问的顶点（`a` 及其 SCC 树）满足 `scc_low_valid_v`，且旧已访问顶点保持。

**证明依赖**：
1. `tarjan_scc_keep_low_valid a` 给出 `scc_low_valid_v s a`；
2. 新增跨树保持引理：对任意已访问 `w`，`tarjan_scc g a` 保持 `scc_low_valid_v s w`。

跨树保持的核心：已访问 `w` 的 `dfn`/`low`/`fa` 不被 `tarjan_scc g a` 修改；`state_to_dfs_tree` 对 `w` 的子树结构也不变；`pop_scc` 可能弹出 `a` 的子树，但 `pop_scc_keep_scc_low_valid_v` 已保证被弹顶点保持，未被弹的祖先顶点也保持。

### 3.6 `tarjan_scc_all_scc_low_valid` — 表述需加强

**当前 statement**：
```coq
Hoare (fun s => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
      (tarjan_scc_all g)
      (fun _ s => scc_low_valid s).
```

**判断**：结论过强或前提过弱。若初始状态已包含非空 `visited` 且这些顶点不满足 `scc_low_valid_v`，则算法不会重新处理它们，结论不成立。

**修复建议**：有两种方案。

**方案 A（推荐）**：把前置加强为包含 `scc_low_valid s`：
```coq
Hoare (fun s => scc_low_valid s /\ dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
      (tarjan_scc_all g)
      (fun _ s => scc_low_valid s).
```
顶层 `tarjan_scc_all_scc_is_low` 的调用处（初始状态）需证明 `scc_low_valid s` 初始为空真（当 `visited s = ∅`）。

**方案 B**：保持当前前置，但把 `tarjan_scc_all` 的循环不变式 `P(done)` 从“`done` 中顶点满足 `scc_low_valid_v`”改为“所有已访问顶点满足 `scc_low_valid_v`”：
```coq
P(done) := (forall w, w ∈ visited s -> scc_low_valid_v s w) /\ ...
```
这样 `a` 已访问分支直接由不变式得到 `scc_low_valid_v s a`。该方案不需改定理前置，但需证明 `P` 在 forset 步骤保持（特别是 `tarjan_scc g a` 建立新顶点的 `scc_low_valid_v` 并保持旧顶点）。

两种方案都可行；方案 B 对后续调用者更友好。

## 4. 关闭计划

### Phase 1 — 关闭 `W_preserves_ancestor_inv` 及其前置引理

1. **证明 `done_not_popped_by_subtree_pop_scc`**
   - 若当前前提不足，加入 `In a (stack s)` 与 dfn 顺序假设；
   - 基于 `dfn_inv`（栈中 dfn 严格递增）与 `done_visited` 证明 `done` 顶点 dfn 小于 `a`，故位于 `a` 下方，不会被 `stack_split_at a` 弹出。

2. **关闭 `W_preserves_ancestor_inv` 内部 admit**
   - **2652**：用 `fa_visited` 直接推出 `cv ∈ visited s1`；
   - **2713**：改写 non-tree edge 分支为显式 `Hoare_bind`，用 `update_low_preserves_low_forset_inv_for_other`（需 `u <> a`）；
   - **2717**：证 `In a (stack s)`，用 `done_not_popped_by_subtree_pop_scc` + `pop_scc_keeps_low_forset_inv_other` + `pop_scc_preserves_done_visited`。

3. **去掉 `W_preserves_ancestor_inv` 顶层 `Admitted`**

### Phase 2 — 关闭 `forset_keep_low_forset_inv`

4. **Tree-edge 分支（3148）**
   - `set_fa a0 u ;; W a0` 用 `set_fa_W_preserves_low_forset_inv`；
   - `update_low u (low s a0)` 用 `update_low_tree_edge`；
   - 整理 `dfn_valid`/`dfn_inv`/`fa_visited` 与 `fa-child→done` 的保持。

5. **Non-tree edge 分支（3152）**
   - Back-edge：用 `update_low_back_edge`；
   - Cross-edge：证集合不变 + `low u` 不变。

6. **去掉 `forset_keep_low_forset_inv` 顶层 `Admitted`**

### Phase 3 — 关闭 `tarjan_scc_keep_low_valid`

7. **加强 fixpoint 后置条件**
   把 `Hoare_fix_logicv_conj` 的 `Q` 改为 `low_post a s /\ a ∈ visited s`，确保 `forset_keep_low_forset_inv` 的 `HW_pre_post` 可满足。

8. **关闭各 admit**
   - **3202**：用 `preloop_establishes_low_forset_inv` + `low_pre_no_fa_child_of_u`；
   - **3214**：调用 `forset_keep_low_forset_inv`，四个 W 假设分别由 `IH_low`（加强后）、`IH_vis_point`、lift 后的 `IH_vis_point`、`tarjan_scc_keep_fa_children_in_universe` 给出；
   - **3218**：`pop_scc_keep_scc_low_valid_v`；
   - **3220**：状态不变，直接组合假设。

9. **去掉 `tarjan_scc_keep_low_valid` 顶层 `Admitted`**

### Phase 4 — 关闭全局定理

10. **证明 `tarjan_scc_establishes_and_preserves_scc_low_valid`**
    - 新顶点 `a`：`tarjan_scc_keep_low_valid a`；
    - 旧已访问顶点：新增并证明跨树保持引理。

11. **修复 `tarjan_scc_all_scc_low_valid` 表述并关闭 admit**
    - 推荐采用方案 B：把循环不变式 `P(done)` 的前件改为 `forall w, w ∈ visited s -> scc_low_valid_v s w`；
    - **3268**：证明或假设 `visited s ⊆ original_vvalid g`；
    - **3284**：未访问分支调用 `tarjan_scc_establishes_and_preserves_scc_low_valid`；
    - **3291**：已访问分支直接由不变式得到 `scc_low_valid_v s a`。

12. **去掉 `tarjan_scc_all_scc_low_valid` 顶层 `Admitted`**

### Phase 5 — 编译与清理

13. 全文件 `coqc` 编译；
14. 搜索确认无残留 `admit` / `Admitted`；
15. 运行相关 regression test（如有）。

## 5. 风险与依赖

| 风险 | 说明 | 缓解 |
|---|---|---|
| `done_not_popped_by_subtree_pop_scc` 前提不足 | 当前 statement 未显式要求 `In a (stack s)` 或 dfn 顺序 | 在使用处补强前提，或修改引理 statement |
| `W_preserves_ancestor_inv` 的 evar 问题 | `intro_state` 在 non-tree edge 分支产生未实例化变量 | 改用显式 `Hoare_bind`/`Hoare_choice` 结构 |
| `low_post` 未含 `u ∈ visited s` | 导致 `forset_keep_low_forset_inv` 的 `HW_pre_post` 假设难以满足 | 把 fixpoint 后置加强为 `low_post a s /\ a ∈ visited s` |
| `tarjan_scc_all_scc_low_valid` 前提过弱 | 初始已访问顶点可能不满足 `scc_low_valid_v` | 把循环不变式扩展为“所有已访问顶点满足” |
| 跨树保持引理 | 需精确说明 `tarjan_scc g a` 不破坏旧顶点 `scc_low_valid_v` | 先关闭 `W_preserves_ancestor_inv` 与 `forset_keep_low_forset_inv` 后再处理 |

## 6. 建议执行顺序

1. 先完成 Phase 1（`W_preserves_ancestor_inv`），因为它是 `set_fa_W_preserves_low_forset_inv` 的前提；
2. 再完成 Phase 2（`forset_keep_low_forset_inv`）；
3. 同时做 Phase 3 中的 fixpoint 后置加强，再关闭 `tarjan_scc_keep_low_valid`；
4. 最后处理 Phase 4 的全局跨树保持与 `tarjan_scc_all_scc_low_valid`。
