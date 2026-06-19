# Tarjan_scc_is_low.v — Admit 消除修复清单

**Author**: Claude Code Agent
**Date**: 2026-06-19

---

## 0. 文件证明目的

`Tarjan_scc_is_low.v` 的目标是证明 Tarjan SCC 算法正确计算了每个顶点的 `low` 值。
核心命题是：

$$
\text{tarjan\_scc\_all} \vdash \text{scc\_is\_low}
$$

其中 `scc_is_low s` 意为：对于所有已访问顶点 `v`，`low s v` 等于从 `v` 出发、经由 DFS tree 边和后向边可达的顶点中 `dfn` 的最小值。

### 证明架构

文件采用分层架构，自底向上：

1. **Layer 0 — 数学模型**：定义 `scc_low_tree`、`scc_low_valid`、`scc_is_low` 等纯数学谓词
2. **Layer 1 — 等价性桥接**：证明 `scc_low_valid` → `scc_is_low`（well-founded induction on `timer - dfn`）
3. **Layer 2 — 不变式设计**：定义 `low_forset_inv`（forset 循环不变式），用嵌套 min 结构编码"当前已处理子节点与后向边的最小值等于 `low s u`"
4. **Layer 3 — 逐边保持**：`process_edge_keep_low_forset_inv` 证明处理单条边保持 `low_forset_inv`
5. **Layer 4 — 循环提升**：`forset_keep_low_forset_inv` 通过 `Hoare_forset` 将单步不变式提升到整个邻居循环
6. **Layer 5 — 单顶点主定理**：`tarjan_scc_keep_low_valid` 组合 preloop / forset / pop_scc
7. **Layer 6 — 全局定理**：`tarjan_scc_all_scc_low_valid` + `tarjan_scc_all_scc_is_low`

### 已证明的定理（Layer 0–2 全部完成，Layer 3 部分完成）

| 定理 | 位置 | 说明 |
|------|------|------|
| `scc_low_witness` | L69 | low 值的 witness 引理 |
| `scc_low_bound` | L78 | low 值下界引理 |
| `dg_reachable_first_step` | L92 | 可达性第一步分解 |
| `scc_low_tree_decompose` | L112 | low tree 分解为 self ∪ back_edges ∪ children |
| `scc_low_valid_induction` | L157 | 从子节点 is_low 推导 low 值 min 等价 |
| `scc_low_valid_induction_is_low` | L201 | 单节点 valid→is_low 桥接 |
| `scc_low_valid_implies_is_low` | L219 | **关键桥接定理**: valid → is_low (well-founded induction) |
| `preloop_low_eq_dfn` | L280 | preloop 后 low = dfn |
| `children_done_empty` | L291 | done=∅ 时 children_done 为空 |
| `back_edges_done_empty_char` | L300 | done=∅ 时 back_edges_done∪[u] = [u] |
| `low_eq_dfn_to_min_empty` | L311 | low=dfn 时 nested min 条件成立 (done=∅) |
| `preloop_establishes_low_forset_inv` | L343 | preloop 建立 low_forset_inv u ∅ |
| `stack_split_at_rest_incl` | L405 | stack_split_at 保持栈成员关系 |
| `scc_low_valid_v_low_eq_dfn_implies_dfn_le_back_edge_dfn` | L422 | 后向边 dfn 序关系 |
| `pop_scc_keep_scc_low_valid_v` | L449 | pop_scc 保持 scc_low_valid_v |
| `children_done_add` | L526 | done 扩展时 children_done 分解 |
| `children_done_no_add` | L542 | done 扩展时 children_done 不变条件 |
| `back_edges_done_add` | L556 | done 扩展时 back_edges_done 分解 |
| `back_edges_done_no_add` | L572 | done 扩展时 back_edges_done 不变条件 |
| `set_fa_preserves_low_pre_rich` | L592 | set_fa 保持 low_pre ∧ visited |
| `set_low_keep_low_forset_inv_components` | L603 | set_low 保持不变式组件 |
| `update_low_tree_edge` | L615 | 树边 update_low 保持 low_forset_inv |
| `low_forset_inv_implies_low_le_dfn` | L735 | low_forset_inv → low ≤ dfn |
| `update_low_back_edge` | L753 | 后向边 update_low 保持 low_forset_inv |
| `low_forset_inv_proper` | L1276 | low_forset_inv 对 done 集合等价是 Proper morphism |

---

## 1. 定理依赖关系图

```
tarjan_scc_all_scc_is_low                           [Admitted, L1432]
├── tarjan_scc_all_scc_low_valid                    [Admitted, L1425]
│   └── tarjan_scc_keep_low_valid                   [Admitted, L1414]
│       ├── preloop_establishes_low_forset_inv      [Proved, L343]
│       ├── forset_keep_low_forset_inv              [Admitted, L1403]
│       │   ├── low_forset_inv_proper               [Proved, L1276]
│       │   └── process_edge_keep_low_forset_inv    [Admitted, L1266]
│       │       ├── update_low_tree_edge            [Proved, L615]
│       │       ├── update_low_back_edge            [Proved, L753]
│       │       ├── tree_child_low_le               [Admitted, L1089]
│       │       ├── children_done_{add,no_add}      [Proved]
│       │       ├── back_edges_done_{add,no_add}    [Proved]
│       │       ├── set_fa_preserves_low_pre_rich   [Proved]
│       │       └── low_forset_inv_implies_low_le_dfn  [Proved]
│       └── pop_scc_keep_scc_low_valid_v            [Proved, L449]
└── scc_low_valid_implies_is_low                    [Proved, L219]
    ├── scc_low_valid_induction_is_low              [Proved]
    └── scc_low_tree_decompose                      [Proved]
```

**符号说明**: `[Proved]` = 无 Admitted, `[Admitted, Lxxx]` = 仍含 Admitted。

---

## 2. Admitted 逐条分析

### A. `tree_child_low_le` (L1083–1089) — **Leaf Lemma**

```coq
Lemma tree_child_low_le (u v: V) (done: V -> Prop) (s: @SCCSt V):
  fa s v = u -> fa s v <> v ->
  v ∈ visited s -> ~ In v (stack s) ->
  low_forset_inv u done s ->
  low s u <= low s v.
```

**用途**: 在 `process_edge_keep_low_forset_inv` 的 cross-edge proper-child 子情形（L1212）中使用。
当 `fa s0 v = u, fa s0 v ≠ v`（即 v 是 u 的 proper tree child），且 v 已被访问但不在栈中（其 SCC 已被弹出），
需要证明 `low s u ≤ low s v` 以便 `children_done_add` 后 min 值保持不变。

**证明思路**:
- 方法 A（推荐）: 由于 `fa s v = u` 且 `fa s v ≠ v`，v 已被访问且 SCC 已被弹出，说明树边 u→v 已被处理。
  v 应已在 `done` 中（在 forset 遍历邻居列表时，v 的第一条入射边触发 tree-edge 分支，v 被加入 done）。
  cross-edge 是第二条或后续的 u→v 边。当 v ∈ done 时，从 `low_forset_inv u done s` 可以直接推出 `low s u ≤ low s v`。
  需要辅助引理：
  ```coq
  Lemma low_forset_inv_children_done_low_le (u v: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s ->
    children_done s u done v ->
    low s u <= low s v.
  ```
  然后需要在 cross-edge 上下文中证明 `children_done s u done v`（即 `v ∈ done ∧ fa s v = u ∧ fa s v ≠ v`）。
- 方法 B: 使用更一般的 DFS tree ordering 论证（`dfn_valid` 保证 `dfn s u < dfn s v`），结合 `low_forset_inv_implies_low_le_dfn` 得到 `low s u ≤ dfn s u < dfn s v`，但还需要 `dfn s v` 与 `low s v` 的关系。

**依赖**: `low_forset_inv_implies_low_le_dfn` (已证明), `children_done` 定义

**难度**: ★★☆ (Medium)


### B. `process_edge_keep_low_forset_inv` (L1091–1266) — **核心 Lemma**

```coq
Lemma process_edge_keep_low_forset_inv (u v: V) (done: V -> Prop)
  (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                   (fun _ s => low_post x s /\ u ∈ visited s)) ->
  Hoare (fun s => low_forset_inv u done s)
        (process_edge u W v)
        (fun _ s => low_forset_inv u (done ∪ [v]) s).
```

#### B1. 树边分支 (L1126) — `admit`

触发条件: `~ v ∈ visited s`（v 未访问 → tree edge）。

程序: `set_fa v u;; W v;; lv <- get' low v;; update_low u lv`

需要证明: 该程序序列将 `low_forset_inv u done` 变为 `low_forset_inv u (done ∪ [v])`。

分解:
1. `set_fa v u` 后: `low_forset_inv u done` 保持（fa 只在 `children_done` 中被使用，而 v ∉ done）
2. `W v` (即 `tarjan_scc v`) 后: 需要 `low_forset_inv u done` **仍保持**
3. `update_low u (low s v)` 后: `update_low_tree_edge` 给出 `low_forset_inv u (done ∪ [v])`

**核心缺口**: 步骤2 — `low_forset_inv u done` 在递归调用 `tarjan_scc v` 下的保持性。
需要证明以下引理：

```coq
Lemma low_forset_inv_preserved_by_tarjan_scc_child (u v: V) (done: V -> Prop):
  ~ v ∈ done ->
  Hoare (fun s => low_forset_inv u done s /\ low_pre v s)
        (tarjan_scc v)
        (fun _ s => low_forset_inv u done s).
```

**论证要点**:
- `tarjan_scc v` 只修改 v 的子树中顶点的 low/dfn/fa/visited/stack 值
- `children_done s u done` 中的顶点不在 v 的子树中（它们在 done 中，早于 v 被处理）
- `back_edges_done s u done` 中顶点是 u 的祖先（在后向边情形），不会在 v 的子树中
- v 的子树中的后向边可能指向 u 并降低 `low s u`，但这只会使 min 值更小，保持 `≤` 关系
- `pop_scc v` 弹出 v 的 SCC，只移除 v 及其后代（不在 done 中），不影响 back_edges_done（它们指向 u 的祖先，不会被 pop）

**注意**: 当前 `tree_child_low_le` 也存在类似问题。实际上，`low_forset_inv u done` 的 min 条件需要"低值保持为最小值"的等式，而不仅仅是 ≤。如果 `low s u` 被降低到新值 m'，需要证明 m' 仍在嵌套 min 的集合中且仍为最小值。

**依赖**: `update_low_tree_edge` (✓), `set_fa_preserves_low_pre_rich` (✓), `low_pre`/`low_post` 定义

**难度**: ★★★ (Hard)


#### B2. 后向边分支 (L1131) — `admit`

触发条件: `v ∈ visited s ∧ In v (stack s)` → back edge。

程序: `dv <- get' dfn v;; update_low u dv`

需要证明: `update_low_back_edge` 的前提条件。

已有 `update_low_back_edge`，要求:
- `dg_step g u v` — 由 `process_edge` 的调用上下文提供
- `In v (stack s)` — 由分支条件提供
- `done ⊆ visited s` — **缺口**: 需要证明 forset 遍历中 done 的所有顶点均已被访问
- `v ∈ done ∨ fa s v ≠ u` — **缺口**: 后向边的目标 v 是 u 的祖先，故 `fa s v ≠ u`（除非自环，但可单独处理）
- `low_forset_inv u done s` — 由 precondition 提供

**需要的辅助引理**:
```coq
Lemma forset_done_subset_visited (u v: V) (done: V -> Prop) (s: @SCCSt V):
  low_forset_inv u done s -> done ⊆ visited s.
```
或更直接地，证明 `children_done` 和 `back_edges_done` 中的顶点都在 visited 中（从定义可推出）。

```coq
Lemma back_edge_fa_neq (u v: V) (s: @SCCSt V):
  dfn_inv s -> dfn_valid g s root -> fa_visited s ->
  u ∈ visited s -> v ∈ visited s -> In v (stack s) ->
  dg_step g u v ->
  fa s v <> u.
```
论证: 如果 `fa s v = u`，则 v 是 u 的 tree child，但 v 已在栈中意味着 v 是 u 的祖先（DFS 栈性质），矛盾（除非 u=v 自环）。

**依赖**: `update_low_back_edge` (✓), `dfn_inv`, `dfn_valid`, `fa_visited`

**难度**: ★★☆ (Medium)


#### B3. Cross-edge proper child 子情形 (L1212) — `admit`

触发条件: `v ∈ visited s ∧ ~ In v (stack s) ∧ fa s v = u ∧ fa s v ≠ v`。

状态不变（无 update_low），只需证明 `children_done` 扩展后 min 不变。

需要: `low s u ≤ low s v`。

这正是 `tree_child_low_le` (Admitted A) 提供的。此 admit 在 `tree_child_low_le` 证明后自动消除。

或者，可以在此直接使用 `low_forset_inv_children_done_low_le` 加上 `children_done s u done v` 的证明。

**依赖**: `tree_child_low_le` (Admitted A) 或等效引理

**难度**: ★★☆ (Medium, 取决于 A 的解法)


### C. `forset_keep_low_forset_inv` (L1378–1403) — **循环提升 Lemma**

```coq
Lemma forset_keep_low_forset_inv (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                   (fun _ s => low_post x s /\ u ∈ visited s)) ->
  Hoare (fun s => low_forset_inv u ∅ s)
        (forset (fun v => dg_step g u v) (process_edge u W))
        (fun _ s => scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s).
```

#### C1. Postcondition 转换 (L1395) — `admit`

需要: `low_forset_inv u (all_neighbors) s → scc_low_valid_v s u`。

其中 `all_neighbors = fun v => dg_step g u v`（即 u 的所有邻居）。

**证明思路**:
展开定义:
```coq
scc_low_valid_v s u :=
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le (dg_step (state_to_dfs_tree g s root) u) (low s) ∪
     min_value_of_subset Nat.le (scc_back_edge s u ∪ [u]) (dfn s))
    (fun x => x) (low s u)

low_forset_inv u (all_neighbors) s :=
  dfn_inv s /\ dfn_valid g s root /\ fa_visited s /\ u ∈ visited s /\
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le (children_done s u (all_neighbors)) (low s) ∪
     min_value_of_subset Nat.le (fun w => back_edges_done s u (all_neighbors) w \/ w = u) (dfn s))
    (fun x => x) (low s u)
```

关键等价:
1. `children_done s u (all_neighbors)` vs `dg_step (state_to_dfs_tree g s root) u`:
   当 done = 所有邻居时，`children_done` 恰好是那些 `fa s v = u ∧ fa s v ≠ v` 的邻居，
   即 u 的 tree children。而 `dg_step (state_to_dfs_tree ...) u` 给出的也是 DFS tree 中 u 的 tree children。
   需要证明这两个集合在 `dfn_valid` 下等价。

2. `(back_edges_done s u (all_neighbors) ∪ [u])` vs `(scc_back_edge s u ∪ [u])`:
   当 done = 所有邻居时，`back_edges_done` 恰好是那些 `fa s v ≠ u` 的邻居中仍在栈中的，
   即 scc_back_edge（后向边）。需要证明等价性。

**需要的辅助引理**:
```coq
Lemma children_done_all_neighbors_eq_tree_edges (u: V) (s: @SCCSt V):
  dfn_valid g s root -> dfn_inv s -> fa_visited s ->
  children_done s u (fun v => dg_step g u v) ==
  dg_step (state_to_dfs_tree g s root) u.
```

```coq
Lemma back_edges_done_all_neighbors_eq_scc_back_edge (u: V) (s: @SCCSt V):
  dfn_valid g s root -> dfn_inv s -> fa_visited s ->
  (fun w => back_edges_done s u (fun v => dg_step g u v) w \/ w = u) ==
  (scc_back_edge s u ∪ [u]).
```

**依赖**: `dfn_valid`, `dfn_inv`, `fa_visited`, `state_to_dfs_tree_step_char`(来自 `Tarjan_scc_basics.v`)

**难度**: ★★★ (Hard, 需要两个集合等价引理)


### D. `tarjan_scc_keep_low_valid` (L1409–1414) — **单顶点主定理**

```coq
Theorem tarjan_scc_keep_low_valid (u: V):
  Hoare (fun s: @SCCSt V => low_pre u s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => low_post u s).
```

程序结构 (`tarjan_scc` = `Lfix tarjan_scc_f u`):
```
preloop u;;
forset (dg_step g u) (process_edge u W);;
If (fun s => low s u = dfn s u) (pop_scc u)
```

**证明结构** (使用 `Lfix` well-founded fixpoint):

1. 使用 `Lfix` 获得归纳假设:
   ```coq
   HW: forall x, Hoare (low_pre x) (tarjan_scc x) (low_post x)
   ```
   需要强化为:
   ```coq
   HW_rich: forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s)
                              (tarjan_scc x)
                              (fun _ s => low_post x s /\ u ∈ visited s)
   ```
   强化需要 `tarjan_scc` 保持 `u ∈ visited`（使用 `tarjan_scc_keep_visited` 或类似引理，应从 `Tarjan_scc_is_dfn.v` 已有）。

2. **preloop**:
   `preloop_establishes_low_forset_inv` → `low_forset_inv u ∅ s`

3. **forset**:
   `forset_keep_low_forset_inv` 使用 `HW_rich` →
   `scc_low_valid_v s u ∧ dfn_valid g s root ∧ dfn_inv s ∧ fa_visited s`

4. **If-then-else (pop_scc)**:
   - 若 `low s u = dfn s u`: `pop_scc_keep_scc_low_valid_v` → `low_post u s`
   - 若 `low s u ≠ dfn s u`: 状态不变，后条件已由 forset 给出为 `low_post u s`

**依赖**: `preloop_establishes_low_forset_inv` (✓), `forset_keep_low_forset_inv` (Admitted C), `pop_scc_keep_scc_low_valid_v` (✓)

**注意事项**:
- `pop_scc_keep_scc_low_valid_v` 的 precondition 需要 `low s u = dfn s u`，这恰由 `If` 分支条件提供
- 需要确认 `scc_low_valid_v s u ∧ dfn_valid ∧ dfn_inv ∧ fa_visited` 在没有 pop 时已经等于 `low_post u s`（从定义可直接得到）

**难度**: ★★☆ (Medium, 组装已就绪的零件)


### E. `tarjan_scc_all_scc_low_valid` (L1420–1425) — **全局 valid 定理**

```coq
Theorem tarjan_scc_all_scc_low_valid:
  Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
        (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
        (fun _ s => scc_low_valid s).
```

`tarjan_scc_all` = `forset (original_vvalid g) (fun v => If (~v ∈ visited) (tarjan_scc v))`

**证明思路**: 类比 `Tarjan_scc_is_dfn.v` 中的 `tarjan_scc_all_scc_is_dfn`。
使用 `Hoare_forset` 或直接归纳，证明每个顶点的 `tarjan_scc` 调用建立其 `scc_low_valid_v`，
然后对所有已访问顶点取 `forall`。

**依赖**: `tarjan_scc_keep_low_valid` (Admitted D), `Hoare_forset`, `Tarjan_scc_is_dfn.v` 中的参考模式

**难度**: ★★☆ (Medium, 有参考模板)


### F. `tarjan_scc_all_scc_is_low` (L1427–1432) — **最终定理**

```coq
Theorem tarjan_scc_all_scc_is_low:
  Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
        (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
        (fun _ s => scc_is_low s).
```

**证明思路**: 直接组合:
- `tarjan_scc_all_scc_low_valid` → 后条件中 `scc_low_valid s`
- `scc_low_valid_implies_is_low` → `scc_low_valid s → scc_is_low s`
- 使用 `Hoare_conseq_post` 组合

**依赖**: `tarjan_scc_all_scc_low_valid` (Admitted E), `scc_low_valid_implies_is_low` (✓)

**难度**: ★☆☆ (Easy, 一行组合)


---

## 3. 自底向上修复顺序

```
Step 0  (基础引理, 0 admit)
  └─ low_forset_inv_children_done_low_le         [NEW]
  └─ forset_done_subset_visited                   [NEW]
  └─ back_edge_fa_neq                             [NEW]
     注: 这三个引理在 Tarjan_scc_is_dfn.v 或 Tarjan_scc_basics.v 中可能有
          对应版本，优先复用。

Step 1  (Leaf lemma, 1 admit)
  └─ tree_child_low_le                            [Admitted A, L1089]
     注: 可使用 Step 0 的 low_forset_inv_children_done_low_le

Step 2  (核心 preservation, 1 admit total after sub-fixes)
  ├─ B1: 树边分支递归保持                           [internal admit, L1126]
  │     └─ low_forset_inv_preserved_by_tarjan_scc_child  [NEW, hardest]
  ├─ B2: 后向边分支前提条件                         [internal admit, L1131]
  │     └─ 使用 Step 0 的 forset_done_subset_visited + back_edge_fa_neq
  ├─ B3: cross-edge proper child 子情形            [internal admit, L1212]
  │     └─ 使用 Step 1 的 tree_child_low_le
  └─ process_edge_keep_low_forset_inv              [Admitted B, L1266]

Step 3  (循环提升, 1 admit)
  ├─ C1: low_forset_inv → scc_low_valid_v 转换     [internal admit, L1395]
  │     └─ children_done_all_neighbors_eq_tree_edges  [NEW]
  │     └─ back_edges_done_all_neighbors_eq_scc_back_edge  [NEW]
  └─ forset_keep_low_forset_inv                    [Admitted C, L1403]

Step 4  (单顶点主定理, 1 admit)
  └─ tarjan_scc_keep_low_valid                     [Admitted D, L1414]

Step 5  (全局 valid, 1 admit)
  └─ tarjan_scc_all_scc_low_valid                  [Admitted E, L1425]

Step 6  (最终定理, 1 admit)
  └─ tarjan_scc_all_scc_is_low                     [Admitted F, L1432]

总计: 6 个顶层 Admitted + 4 个内部 admit + 6 个 NEW 辅助引理
```

**预计工作量**:
- Step 0: 3 个中等引理，每个约 20-60 行证明
- Step 1: 1 个引理，约 15-30 行
- Step 2 (B1): **最困难部分**，可能需要 200+ 行证明和额外的子引理
- Step 2 (B2): 约 30-50 行
- Step 2 (B3): 约 10 行 (使用 Step 1)
- Step 3: 2 个集合等价引理 + 转换证明，约 100-150 行
- Step 4: 组装，约 30-50 行
- Step 5: 参考 Tarjan_scc_is_dfn.v，约 50-80 行
- Step 6: 一行组合，约 5 行


---

## 4. 关键风险与阻塞点

### 风险 1: `low_forset_inv` 在递归调用下的保持性 (Step 2, B1)

这是最大的不确定性。核心问题是: `low s u` 可能在 `tarjan_scc v` 执行期间被 v 子树中的 cross/back edges 降低。
`low_forset_inv` 的 min 条件是**等式**而非不等式，因此 `low s u` 变化后需要证明新值仍在 min 集合中且保持最小值。

**缓解策略**:
- 深入分析 v 的子树能否真的改变 `low s u`。如果 `update_low` 只在 tree/back edge 时更新，且 back edge 只指向祖先，
  那么从 v 的子树出发的后向边只能指向 v 的祖先（包括 u）。如果这样的边存在，`update_low u (dfn w)` 会被调用，
  降低 `low s u`。此情形需要专门的论证。
- 备选方案: 将 `low_forset_inv` 的 min 条件从等式弱化为 `≤` 不等式，但这会破坏 downstream 证明。

### 风险 2: `scc_low_valid_v` ↔ `low_forset_inv all_neighbors` 等价 (Step 3, C1)

两个集合等价引理 (`children_done_all_neighbors_eq_tree_edges` 和 `back_edges_done_all_neighbors_eq_scc_back_edge`)
需要仔细的 DFS 树性质推理。`state_to_dfs_tree_step_char` 和 `state_to_dfs_tree_step_char_backward`
(来自 `Tarjan_scc_basics.v`) 提供了 tree edges 的正逆向特征，是证明的关键。

### 风险 3: 回调参数强化

`forset_keep_low_forset_inv` 的回调假设已是强化形式 `low_pre x /\ u ∈ visited → low_post x /\ u ∈ visited`。
在 `tarjan_scc_keep_low_valid` 中使用 `Lfix` 时，需将归纳假设 `low_pre → low_post` 强化为此形式。
这需要 `tarjan_scc` 保持 `u ∈ visited` 的引理，可从 `Tarjan_scc_is_dfn.v` 或 `Tarjan_scc_basics.v` 中复用。


---

## 5. 参考文件

| 文件 | 作用 |
|------|------|
| `Tarjan_scc_is_dfn.v` | dfn 正确性证明的完整参考模板，包括 `Hoare_forset` 用法、递归回调强化、全局定理组合 |
| `Tarjan_scc_basics.v` | `state_to_dfs_tree_step_char`/`_backward`、`min_value_of_subset_nested_update_*`、`children_done_add`/`no_add` 等基础引理 |
| `Tarjan_scc.v` | `tarjan_scc`、`tarjan_scc_all`、`process_edge`、`update_low` 程序定义 |
| `MaxMinLib/MaxMin.v` | `min_eq_forward`/`min_eq_forward'`、`min_union_iff` 等 min 操作引理 |
| `StateRelHoare.v` | `Hoare_forset` 定理及其 Proper morphism 条件 |
| `SCC_basic.v` | `SCCSt` 状态定义、`state_to_dfs_tree`、`scc_back_edge` 等基础定义 |
| `docs/dev/20260618-tarjan-scc-is-low-open-issues.md` | 上一版问题清单（部分 Issue 已解决: Issue #2 callback shape 已修复, Issue #4 doc mismatch 可选处理） |
| `docs/dev/20260617-tarjan-scc-is-low-design.md` | 原始设计文档 |
| `docs/dev/20260618-tarjan-scc-is-low-min-lemma-issue.md` | 嵌套 min 引理设计讨论 |

---

## 6. 验证命令

```bash
# 查看当前所有 admit
cd /mnt/d/Rocq/QualifiedCProgramming
grep -n "Admitted" SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v

# 编译检查
eval $(opam env)
coqc -Q SeparationLogic QualifiedCProgramming \
  SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v
```
