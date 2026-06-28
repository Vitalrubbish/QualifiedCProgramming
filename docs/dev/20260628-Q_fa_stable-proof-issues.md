# Q_fa_stable 证明过程发现的问题
**Author**: Claude
**Date**: 2026-06-28

## 背景

在对 `Tarjan_scc_is_low.v` 中 `Q_fa_stable` 相关引理进行实际证明时，共证明了 11 个引理，剩余 4 个 `Admitted`。本文档记录证明过程中发现的设计与阻塞问题。

---

## 问题 1：`process_edge_keep_fa_forall` 的泛型 `P` 签名存在语义缺陷

### 现象

以下签名**无法在泛型 `P` 下证明**：

```coq
Lemma process_edge_keep_fa_forall
      (u v: V) (W: V -> program (@SCCSt V) unit)
      (P: @SCCSt V -> V -> Prop) (s0: @SCCSt V):
  (forall x snap,
     Hoare (fun s => s = snap /\ forall w, P snap w -> fa s w = fa snap w) (W x)
           (fun _ s => forall w, P snap w -> fa s w = fa snap w)) ->
  Hoare (fun s => s = s0 /\ (forall w, P s0 w -> fa s w = fa s0 w) /\ (P s0 v -> v ∈ visited s0))
        (process_edge u W v)
        (fun _ s => forall w, P s0 w -> fa s w = fa s0 w).
```

### 根因

在树边分支中，证明需要以下链条：

1. `set_fa v u` 将状态从 `s0` 变为 `s_mid`，其中 `fa s_mid v = u`
2. 递归调用 `W v` 使用 IH，IH 后条件为 `forall w, P snap w -> fa s_post w = fa snap w`，其中 `snap` 必须是调用前状态（即 `s_mid`）
3. 目标需要 `forall w, P s0 w -> fa s_post w = fa s0 w`

衔接需要：对任意满足 `P s0 w` 的 `w`：

- 从 `set_fa_keep_fa_forall`：`fa s_mid w = fa s0 w`（因为 `~ P s0 v`）
- 从 IH：若 `P s_mid w` 则 `fa s_post w = fa s_mid w`
- 因此需要 **`P s0 w -> P s_mid w`** 来完成链条

**`P s0 w -> P s_mid w` 对泛型 `P` 不成立。** `set_fa v u` 改变 `fa v`，泛型 `P` 可以依赖 `fa v` 的值。例如：

```coq
P s w := fa s v = some_old_value
```

在 `set_fa v u` 后将 `fa s_mid v` 改为 `u`，对于任意 `w ≠ v`：
- `P s0 w` 为真（`fa s0 v = some_old_value`）
- `P s_mid w` 为假（`fa s_mid v = u ≠ some_old_value`）

导致链条断裂。

### 在实际使用中不触发

当 `P snap w := w ∈ visited snap`（本文件的预期实例化）时，`visited` 不受 `set_fa` 影响，`P s0` 与 `P s_mid` 等价，问题不触发。

### 修复方案

**方案 A**：将 `P` 从 `SCCSt -> V -> Prop` 改为简单谓词 `Q: V -> Prop`，IH 后条件始终相对于固定快照 `s0` 表达：

```coq
Lemma process_edge_keep_fa_forall_fixed
      (u v: V) (W: V -> program (@SCCSt V) unit)
      (Q: V -> Prop) (s0: @SCCSt V):
  (forall x,
     Hoare (fun s => forall w, Q w -> fa s w = fa s0 w) (W x)
           (fun _ s => forall w, Q w -> fa s w = fa s0 w)) ->
  Hoare (fun s => s = s0 /\ (forall w, Q w -> fa s w = fa s0 w) /\ (Q v -> v ∈ visited s0))
        (process_edge u W v)
        (fun _ s => forall w, Q w -> fa s w = fa s0 w).
```

此时 IH 的 `fa s0` 是常量，不存在快照切换问题。`forset_process_edge_keep_fa_forall` 和 `Hoare_fix_logicv_conj` 中的 `P1` 属性也需同步修改。

**方案 B**：保持泛型签名，但增加 `P` 的 `set_fa`-稳定性前提：

```coq
(P_stable : forall s1 s2,
   (forall w, P s1 w -> fa s1 w = fa s2 w) ->
   forall w, P s1 w -> P s2 w)
```

此前提表达：如果 `s1` 与 `s2` 的 `fa` 在 `P s1`-顶点上一致，则 `P` 保持。由于 `set_fa v u` 只改变 `fa v` 而 `~ P s0 v`，该前提在树边分支满足。

---

## 问题 2：`tarjan_scc_keep_fa_stable_unvisited` 的 forset 步骤阻塞

### 现象

主定理 `tarjan_scc_keep_fa_stable_unvisited` 使用 `Hoare_fix_logicv_conj` 进行 Lfix 归纳。归纳步骤中 `tarjan_scc_f g W a` 分解为三段：

1. `preloop a` — 已可直接使用 `preloop_keep_fa_forall` + `preloop_keep_visited_forall` 证明
2. `forset (dg_step g a) (process_edge a W)` — **阻塞点**
3. `If (low s a = dfn s a) (pop_scc a)` — 已可分别用 `pop_scc_keep_fa_forall` 和 skip 处理

`forset` 步骤需要证明：对所有邻居 `v`，`process_edge a W v` 保持 `Q_fa_stable a c`（相对于快照 `c`）。这需要一个 `forset_process_edge` 组合引理。问题 1 阻塞了该引理的泛型版本；即使具体化 `P`，`forset` 本身的迭代归纳也有相当规模（参考 `Tarjan_scc_is_dfn.v` 中 `forset_process_edge_keep_combined` 约 200 行）。

### 依赖关系

```
tarjan_scc_keep_fa_stable_unvisited
  └── forset_process_edge_keep_fa_forall (concrete P)
        └── process_edge_keep_fa_forall (concrete P)
              ├── set_fa_keep_fa_forall ✓
              ├── IH (from Hoare_fix_logicv_conj)
              └── get_low_update_low_keep_fa_forall ✓
```

### 当前状态

`Hoare_fix_logicv_conj` 的框架已搭建（使用 `C := SCCSt`，辅助属性为 `tarjan_scc_keep_visited`），归纳假设形状正确。阻塞项仅为 forset 组合引理。

---

## 已证明引理清单（11 个）

| 引理 | 行数 | 要点 |
|------|------|------|
| `Q_fa_stable_old_visited` | 1 | 第一个 conjunct 投影 |
| `Q_fa_stable_old_fa` | 1 | 第二个 conjunct 投影 |
| `Q_fa_stable_done_fa` | 3 | 通过 `done_visited` 桥接 |
| `Q_fa_stable_preserves_old_parent` | 2 | 传递性 |
| `preloop_keep_fa_no_restriction` | 3 | preloop 不修改 fa |
| `preloop_keep_fa_forall` | 5 | forall 泛化 |
| `set_fa_keep_fa_forall` | 6 | `~ P v` 排除被修改顶点 |
| `pop_scc_keep_fa_forall` | 7 | pop_scc 不修改 fa |
| `update_low_keep_fa_forall` | 7 | set_low 分支 + skip |
| `get_low_update_low_keep_fa_forall` | 7 | 组合引理 |
| `get_dfn_update_low_keep_fa_forall` | 7 | 同 low 版本 |

---

## 待完成工作

1. **修复 `process_edge_keep_fa_forall` 签名**：采用方案 A（具体化 `Q: V -> Prop`）或方案 B（增加 `P` 稳定性前提）
2. **证明 forset 组合引理**：基于修复后的 `process_edge` 引理
3. **完成 `tarjan_scc_keep_fa_stable_unvisited` 的 Lfix 归纳**：将 forset 引理嵌入归纳步骤
4. **`tarjan_scc_keep_fa` 降级为推论**：从 unvisited 版本直接 `destruct` 得出
