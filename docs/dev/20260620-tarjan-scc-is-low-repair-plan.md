# Tarjan_scc_is_low.v Admit 修复计划
**Author**: Claude
**Date**: 2026-06-20
**Based on**: `20260620-tarjan-scc-is-low-admit-inventory.md` (已过时，见变更说明)

## 当前 Admit 状态（6 处，从 9 处减少）

| # | 行号 | 引理/定理 | 难度 | 说明 |
|---|------|-----------|------|------|
| 1 | 1414 | `popped_vertex_low_eq_dfn` | ★★☆ | 叶节点纯引理：弹出顶点 low=dfn |
| 2 | 1886 | `process_edge_preserves_ancestor_inv` | ★★★ | process_edge 三路分支，保持祖先不变式 |
| 3 | 1901 | `W_preserves_ancestor_inv` | ★★★ | tarjan_scc 不动点归纳，依赖 #2 |
| 4 | 2229 | `forset_keep_low_forset_inv` | ★★★ | 核心 forset 归纳引理，依赖 #2、#3 |
| 5 | 2235 | `tarjan_scc_keep_low_valid` | ★★☆ | 主定理：单顶点 low 正确性，依赖 #3、#4 |
| 6 | 2246 | `tarjan_scc_all_scc_low_valid` | ★☆☆ | 全局定理：所有顶点 low 正确性，依赖 #5 |

### 较 20260620 盘点文档的变更

已闭合 3 处 admit：
- **原 #4 `set_fa_W_preserves_low_forset_inv`** → 已 Qed（bullet nesting 冲突修复）
- **原 #5 `process_edge_keep_low_forset_inv`** → 已删除（该引理从未在文件中作为独立 Lemma 存在，其功能被整合进 `forset_keep_low_forset_inv`）
- **原 #6 `tarjan_scc_keep_fa_children_in_universe`** → 已 Qed（前序 commit `46261b2` 完成）

另外：
- **`W_preserves_ancestor_inv` 签名已修正**：`HW_post`（无 `u ∈ visited`）→ `HW_vis`（含 `u ∈ visited`），消除了原 false dependency chain

---

## 依赖关系图（更新后）

```
popped_vertex_low_eq_dfn (1)      process_edge_preserves_ancestor_inv (2)
        ↓                                    ↓
 tree_child_low_le ✓               W_preserves_ancestor_inv (3)
                                            ↓
                                 set_fa_W_preserves_low_forset_inv ✓
                                            ↓
                                 forset_keep_low_forset_inv (4)
                                            ↓
                                 tarjan_scc_keep_low_valid (5)
                                            ↓
                                 tarjan_scc_all_scc_low_valid (6)
                                            ↓
                                 tarjan_scc_all_scc_is_low ✓
```

**独立可修**：#1、#2

**串行依赖链**：#2 → #3 → (#4 已 Qed) → [forset 体] → #5 → #6

**交叉依赖**：#1 在 #2 的 cross edge 分支中被需要（通过 `tree_child_low_le` 模式），但不是 #2 的形式前提

---

## 逐条修复方案

### Step 1: `popped_vertex_low_eq_dfn`（line 1403-1414）

```coq
Lemma popped_vertex_low_eq_dfn (s: @SCCSt V) (v: V):
  dfn_inv s -> v ∈ visited s -> ~ In v (stack s) ->
  low s v = dfn s v.
```

**语义**：已被访问但不在栈上的顶点已被 `pop_scc` 弹出，当时要求 `low = dfn`，该等式在弹出后保持不变。

**阻塞**：当前被 `tree_child_low_le`（Qed）调用，但该调用点可替换为更直接的论证（见该引理的 proof sketch）。

**修复方向**（按 inventory 建议选 A）：
- **A（推荐）**：弱化为 `tree_child_popped_low_eq_dfn`，加前提 `fa s v = u` + `fa s v <> v` + `low_forset_inv u done s`，仅处理树边孩子的弹出情形。可复用已有引理 `low_forset_inv_children_done_low_le` 的模式。
- **B**：引入全局不变量 `visited_not_on_stack_low_eq_dfn` 并加入 `low_forset_inv` 定义（影响面大，不推荐）。

**预计**：~1-2h，选择方案 A。

---

### Step 2: `process_edge_preserves_ancestor_inv`（line 1878-1886）

```coq
Lemma process_edge_preserves_ancestor_inv (u v x: V) (done: V -> Prop)
  (W: V -> program (@SCCSt V) unit)
  (HW: forall x, Hoare (fun s => low_pre x s /\ v ∈ visited s) (W x)
                      (fun _ s => low_post x s /\ v ∈ visited s)):
  u <> v -> ~ done v -> dg_step g v x ->
  Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ v ∈ visited s)
        (process_edge v W x)
        (fun _ s => low_forset_inv u done s /\ fa s v = u /\ v ∈ visited s).
```

**语义**：当 `v` 是 `u` 的树孩子（`fa s v = u`），处理 `v` 的一条邻边 `x` 时，`u` 的 `low_forset_inv` 和 `fa v = u` 关系保持不变。

**难点**：`process_edge` 展开为 `if_else` + `Hoare_choice`，三路分支：
1. **树边**（`~ x ∈ visited`）：`set_fa x v ;; W x ;; update_low v (low s x)` — 需要证明 `set_fa` + 递归 + `update_low` 三个操作都不破坏 `u` 的 `low_forset_inv` 和 `fa v = u`
2. **回边**（`x ∈ visited /\ x ∈ stack`）：仅 `update_low v (dfn s x)` — `update_low` 只改 `v` 的 low（不在 `children_done u done` 中，因为 `v ∉ done`），且不改变 `fa`
3. **非树非回边**（`x ∈ visited /\ ~ x ∈ stack`）：skip — 完全不变

**关键 sub-lemma 需求**（树边分支）：
- `set_fa` 不改变 `u` 的 `children_done` / `back_edges_done`（因为 `x ≠ u` 且 `x ∉ done`）
- `W x` 递归保持 `u` 的 `low_forset_inv`（由待证的 #3 保证，但这里需要的是不同的 HW 参数 —— 带 `v ∈ visited` 而非 `u ∈ visited`）
- `update_low v _` 不改变 `u` 的 `low` 值和 `fa v = u`

**注意**：此引理的 HW 是 `v ∈ visited`（被处理顶点自身的递归），而 #3 的 HW_vis 是 `u ∈ visited`（祖先视角）。两者是不同的 Hoare 假设，因此 #2 不完全依赖 #3 —— 它需要独立的证明。

**预计**：~3-5h。最复杂的单 lemma。

---

### Step 3: `W_preserves_ancestor_inv`（line 1891-1901）

```coq
Lemma W_preserves_ancestor_inv (u v: V) (done: V -> Prop)
  (W: V -> program (@SCCSt V) unit)
  (HW_vis: forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                          (fun _ s => low_post x s /\ u ∈ visited s))
  (HW_keep_all: forall (a: V) (done': V -> Prop), ...):
  Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v)
        (W v)
        (fun _ s => low_forset_inv u done s /\ fa s v = u).
```

**语义**：`W v`（即 `tarjan_scc g v`）执行后，祖先 `u` 的 `low_forset_inv` 和树边关系 `fa v = u` 被保持。

**前提分析**：
- `HW_vis`：递归子调用 `W x` 保持 `u ∈ visited`（祖先在 visited 中）
- `HW_keep_all`：递归子调用保持 visited forall（标准的 forset 归纳前提）

**证明策略**：
1. `unfold tarjan_scc; hoare_fix_nolv_auto V` — 展开不动点
2. 展开 `tarjan_scc_f`：`preloop v` 检查 + `forset (process_edge v W)`
3. `preloop v` 处理：`~v ∈ visited` → 设置 dfn/low/stack/fa + 入栈。需要证明这些操作不破坏 `u` 的 `low_forset_inv`（`u ≠ v` 因为 `~ done v`，且 `u ∈ visited`）
4. `forset` 体：对每条邻边 `x`（`dg_step g v x`），调用 `process_edge v W x`
5. 对 forset 做归纳：初始时 `low_forset_inv` 成立（via `preloop_establishes_low_forset_inv` 风格），每条边处理后保持（via #2 的变体或直接证明）

**关键 sub-lemma**（来自 proof sketch 注释 line 1909-1918）：
- `set_fa_preserves_low_forset_inv`：已证明（`set_fa_W_preserves_low_forset_inv` 的子目标 1）
- `W_preserves_low_forset_inv_and_fa`：即本引理自身的不动点归纳部分

**与 #2 的关系**：#2 处理 `process_edge`（level 2），#3 处理 `W v`（level 1 fixpoint）。#3 的证明需要 #2 作为 `process_edge` 步骤的保持引理。但 #2 的 HW 是 `v ∈ visited`，而 #3 的 context 是 `u ∈ visited` —— 需要在 #3 中构造适配的 HW 实例。

**预计**：~3-5h（fixpoint 归纳结构参照 `Tarjan_scc_is_dfn.v`）。

---

### Step 4: `forset_keep_low_forset_inv`（line 2218-2229）

```coq
Lemma forset_keep_low_forset_inv (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                   (fun _ s => low_post x s /\ u ∈ visited s)) ->
  (forall a, Hoare (fun s => True) (W a) (fun _ s => a ∈ visited s)) ->
  (forall (a: V) (done': V -> Prop), Hoare (fun s => forall w, done' w -> w ∈ visited s) (W a)
                                       (fun _ s => forall w, done' w -> w ∈ visited s)) ->
  (forall a, Hoare (fun s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) (W a)
                    (fun _ s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v)) ->
  Hoare (fun s => low_forset_inv u ∅ s /\ (forall v, fa s v = u -> v = u))
        (forset (fun v => dg_step g u v) (process_edge u W))
        (fun _ s => scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s).
```

**语义**：从 `low_forset_inv u ∅`（空 done 集合）出发，对 `u` 的所有邻边执行 `process_edge u W`，最终得到 `scc_low_valid_v s u`。

**这是整个文件最核心的引理**。它建立了 DFS 树根 `u` 的 low 正确性。

**证明策略**：
1. 对 `forset` 做归纳：
   - **初始**：`done = ∅`，`low_forset_inv u ∅` 成立
   - **归纳步**：当前 `done` 集合处理完毕后，将新顶点 `v` 加入 `done`，需要证明 `low_forset_inv u (done ∪ [v])` 被保持
2. 对每个 `process_edge u W v` 调用：
   - 如果 `dg_step g u v`（树边）：调用 `set_fa_W_preserves_low_forset_inv`（已 Qed）风格的模式，但需要以 `done` 为参数
   - 如果非树边：`process_edge` 直接 skip 或 update_low

**关键 sub-goals**（参照 inventory 文档 line 47-49）：
- `fa_children_are_done` step case：证明 `fa` 子节点在 `done` 集合展开时正确归类
- `low_forset_inv_proper`（已 Qed）：`done` 集合等价下的 `low_forset_inv` 保持
- `low_forset_inv_expand_child_done`（已 Qed, line 1329）：将孩子的孩子节点加入 `children_done`

**预计**：~4-6h。文件中最核心也最复杂的引理。

---

### Step 5: `tarjan_scc_keep_low_valid`（line 2231-2235）

```coq
Theorem tarjan_scc_keep_low_valid (u: V):
  Hoare (fun s: @SCCSt V => low_pre u s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => low_post u s).
```

**语义**：`tarjan_scc g u` 从 `low_pre u`（未访问 + dfn_inv + dfn_valid + fa_visited）出发，完成后得到 `low_post u`（`scc_low_valid_v s u` + dfn_inv + dfn_valid + fa_visited）。

**证明策略**：
1. `unfold tarjan_scc; hoare_fix_nolv_auto V` — 展开不动点
2. 结合 `Hoare_fix_logicv_conj` 使用四个 `visited_tag` conjunct（参照 `Tarjan_scc_is_dfn.v` 的 `tarjan_scc_keep_dfn_valid` 证明模式）：
   - `VSelf`：自身 visited ← `tarjan_scc_self_visited`（已有）
   - `VKeep`：保持 visited ← `tarjan_scc_keep_visited`（已有）
   - `VKeepAll`：保持 done → visited ← `tarjan_scc_keep_visited_forall`（已有）
   - `VKeepFaChildren`：保持 fa 子节点关系 ← `tarjan_scc_keep_fa_children_in_universe`（已 Qed ✓）
3. 在 `tarjan_scc_f` 的 preloop 阶段建立 `low_forset_inv u ∅`
4. 在 forset 阶段调用 #4 `forset_keep_low_forset_inv`

**关键 preloop 子目标**：
- `preloop_establishes_low_forset_inv`（已 Qed, line 381）：从 `low_pre u` 建立 `low_forset_inv u ∅`
- `tarjan_scc_keep_fa_children_in_universe`（已 Qed, line 2182）：给 `VKeepFaChildren` tag

**预计**：~1-2h（组装型，依赖 #3 和 #4 的完成）。

---

### Step 6: `tarjan_scc_all_scc_low_valid`（line 2241-2246）

```coq
Theorem tarjan_scc_all_scc_low_valid:
  Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
        (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
        (fun _ s => scc_low_valid s).
```

**语义**：对整个图执行 `tarjan_scc_all`，所有顶点的 `scc_low_valid` 成立。

**证明策略**（参照 `tarjan_scc_all_scc_is_low` 的证明模式，line 2248-2272）：
- `tarjan_scc_all` 展开后对每个根顶点调用 `tarjan_scc`
- 需要 `tarjan_scc_keep_low_valid`（#5）作为每个根顶点的 Hoare 规约
- 结合 `tarjan_scc_all_dfn_valid`（从 `Tarjan_scc_is_dfn.v` require）和 `tarjan_scc_all_keep_dfn_inv`
- 使用 `Hoare_conj` 组装多个后件

**预计**：~30min（纯组合，参照已有 `tarjan_scc_all_scc_is_low` 证明）。

---

## 推荐执行顺序

```
Phase 1（可并行）
  Step 1: popped_vertex_low_eq_dfn         ★★☆  ~1-2h
  Step 2: process_edge_preserves_ancestor_inv ★★★  ~3-5h

Phase 2（串行）
  Step 3: W_preserves_ancestor_inv          ★★★  ~3-5h  (依赖 Step 2)

Phase 3（串行）
  Step 4: forset_keep_low_forset_inv        ★★★  ~4-6h  (依赖 Step 1+2 模式, Step 3)

Phase 4（串行组装）
  Step 5: tarjan_scc_keep_low_valid         ★★☆  ~1-2h  (依赖 Step 3 + Step 4)
  Step 6: tarjan_scc_all_scc_low_valid      ★☆☆  ~30min  (依赖 Step 5)
```

**总计预计**：~12-20 小时

**关键路径**：Step 2 → Step 3 → Step 4 → Step 5 → Step 6（~11-18h）

**最大风险点**：
1. Step 2 的树边分支可能需要新增多个 sub-lemma（`set_fa`/`W x`/`update_low` 对 `u` 的不变式保持）
2. Step 4 的 `fa_children_are_done` step case 可能需要新增关于 `children_done` 展开的不变式引理
3. Step 1 如果方案 A 不够（调用处需要更强的形式），可能需要退到方案 B

---

## 相关文档

- `docs/dev/20260620-tarjan-scc-is-low-admit-inventory.md`：前序盘点（9 admit 状态，已过时）
- `docs/dev/20260619-tarjan-scc-is-low-remaining-issues.md`：早期 8-admit 修复方案
- `docs/dev/20260619-tarjan-scc-is-low-admit-fix-checklist.md`：逐层修复策略
