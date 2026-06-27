# Tarjan SCC is_low 证明设计分析

**Author**: Vitalrubbish
**Date**: 2026-06-27

## 1. 顶层规约

### 1.1 主定理

```
{low_pre u ∧ original_vvalid g u ∧ stack_dfn_order ∧ dfn_injective}
    tarjan_scc g u
{low_post u}
```

其中：

```
low_pre u s   := wf_scc_state s ∧ ~ u ∈ visited s
low_post u s  := wf_scc_state s ∧ scc_is_low_v s u
```

`scc_is_low_v s u` 断言 `low s u` **恰好等于** 从 u 出发沿 DFS 树走任意步、最后可选地跳一条回边，所能到达的所有顶点的 dfn 的最小值。

### 1.2 程序展开：`tarjan_scc_f g u`

`tarjan_scc g u` 展开为 `Lfix (tarjan_scc_f g) u`，其中 `tarjan_scc_f` 的体为：

```
{low_pre u}
    preloop u;
    forset (fun v => dg_step g u v) (process_edge u W v);
    if low u == dfn u then pop_scc u else skip
{low_post u}
```

边分类 `process_edge u W v`：

```
if ~ v ∈ visited then           (* 树边 *)
    set_fa v u ;; W v ;; lv ← get' (low v) ;; update_low u lv
else if In v (stack ...) then   (* 回边 *)
    update_low u (dfn v)
else                            (* 交叉边 *)
    skip
```

## 2. 全局良构不变量：`wf_scc_state`

四项始终被保持的全局不变量（line 329）：

```
wf_scc_state s :=
    stack_in_visited s ∧      (* 栈中顶点都已 visited *)
    dfn_inv s ∧               (* dfn 时间戳性质 *)
    dfn_valid g s root ∧      (* DFS 树边 dfn 排序 *)
    fa_visited s               (* fa v ≠ v → fa v ∈ visited *)
```

所有基本操作（preloop、set_fa、set_low、update_low、pop_scc）都保持它：

```
{wf_scc_state_pre u}              {wf_scc_state ∧ u ∈ visited ∧ ~v ∈ visited}
    preloop u                         set_fa v u
{wf_scc_state}                    {wf_scc_state_pre v ∧ u ∈ visited}

{wf_scc_state}                    {wf_scc_state ∧ u ∈ visited}
    set_low u n                       update_low u n
{wf_scc_state}                    {wf_scc_state}

{wf_scc_state}
    pop_scc u
{wf_scc_state}
```

## 3. 程序各阶段的 {Pre} → {Post} 分解

### 3.1 阶段 1：preloop

```
{low_pre a ∧ stack_dfn_order ∧ dfn_injective}
    preloop a
{ forset_inv a ∅
∧ In a (stack)
∧ stack_dfn_order ∧ dfn_injective
∧ low a = dfn a
∧ fa_child_of_u a
∧ fa_not_done_implies_eq_u a ∅ }
```

即在 preloop 之后，我们拥有启动 forset 所需的全部 7 个前提。

### 3.2 阶段 2：forset（迭代不变量）

forset 使用增强不变量 `I`（line 2242）：

```
I(u, done, s) :=
    forset_inv u done s
  ∧ done_visited done s
  ∧ In u (stack s)
  ∧ stack_dfn_order s
  ∧ dfn_injective s
  ∧ low_src u done s
  ∧ (∀ v, done v → dg_step g u v → fa s v = u → fa s v ≠ v → scc_is_low_v s v)
  ∧ fa_child_of_u u s
  ∧ fa_not_done_implies_eq_u u done s
```

forset 的 Hoare 规约：

```
{I(u, ∅)}
    forset (fun v => dg_step g u v) (process_edge u W v)
{I(u, dg_step g u)}
```

结合初始建立（阶段 1 的输出蕴含 `I(u, ∅)`）与完成后桥接（`I(u, dg_step g u)` 中取 `forset_inv` 部分再配合其他前提推出 `scc_is_low_v s u`），得到 `low_post u`。

### 3.3 阶段 3：if / pop_scc

```
{low_post u ∧ In u (stack)}
    if low u == dfn u then pop_scc u else skip
{low_post u}
```

## 4. 不动点不变量：`forset_inv`

```
forset_inv u done s :=
    wf_scc_state s
  ∧ u ∈ visited s
  ∧ In u (stack s)
  ∧ low s u <= dfn s u                                — (A)
  ∧ (∀ v, done v → dg_step g u v →                     — (B)
        (fa s v = u → low s u <= low s v)
      ∧ (In v (stack s) → low s u <= dfn s v))
```

**纯不等式形式是核心设计决策**：

- (A) `low u ≤ dfn u`：low 的上界
- (B) 对每个已处理邻居 v：
  - 若是 u 的树孩子（`fa v = u`）：`low u ≤ low v`
  - 若在栈中（回边目标或其可达后代）：`low u ≤ dfn v`

`update_low` 只能**降低** `low u`，不等式在下降时单调——旧不等式在新值下自动成立。若用等式则每次更新都需重新证明。

## 5. 来源追踪：`low_src`

```
low_src u done s :=
    low s u = dfn s u                                                   — (Src1)
  ∨ (∃ v, done v ∧ dg_step g u v ∧ fa s v = u ∧ fa s v ≠ v            — (Src2)
          ∧ low s u = low s v)
  ∨ (∃ w, done w ∧ dg_step g u w ∧ In w (stack s) ∧ fa s w ≠ u        — (Src3)
          ∧ low s u = dfn s w)
```

三项选言追踪 `low u` 当前值的**来源**：
- (Src1) 仍是初始值 `dfn u`
- (Src2) 来自某个已处理树孩子 v 的 `low v`
- (Src3) 来自某个已处理回边目标 w 的 `dfn w`

**来源追踪在 forset 体中的演化**：

```
{low_src u done}                    {low_src u done}
    (处理树孩子 a, lv < low u)          (处理回边目标 a, dfn a < low u)
{low_src u (done ∪ [a])}            {low_src u (done ∪ [a])}
  — 来源从 (Src1) 或旧 (Src2)         — 来源从 (Src1) 或旧 (Src3)
    变为新 (Src2): a 的 low v          变为新 (Src3): a 的 dfn a

{low_src u done}                    {low_src u done}
    (处理树孩子 a, lv >= low u)         (处理回边目标 a, dfn a >= low u)
{low_src u (done ∪ [a])}            {low_src u (done ∪ [a])}
  — 来源不变                           — 来源不变
```

## 6. forset 体对各类边的处理

forset 体逐边处理时的 Hoare 三元组（均在 `I(u, done, s0)` 前提下）：

### 6.1 树边

```
{I(u, done, s0) ∧ ~ a ∈ visited ∧ a ∉ done ∧ dg_step g u a ∧ dfn s0 u < timer s0}
    set_fa a u ;; W a ;; lv ← get' (low a) ;; update_low u lv
{I(u, done ∪ [a], s')}
```

内部调用 `W a`（即递归调用 `tarjan_scc_f g a`），W 的 frame 假设保证：

```
{forset_inv u done ∧ ... (anc=u 的 9 个前提)}
    W a
{ forset_inv u done                      — u 的 forset_inv 保持
∧ In u (stack)                            — u 仍在栈中
∧ ... (stack_dfn_order, dfn_injective 等)
∧ low_post a                              — 孩子 a 的 low 正确
∧ a ∈ visited
∧ (fa a = u → fa' a = u) }                — 父子关系保持
```

### 6.2 回边（a ≠ u）

```
{I(u, done, s0) ∧ a ∈ visited ∧ In a (stack s0) ∧ dg_step g u a ∧ fa s0 a ≠ u}
    update_low u (dfn a)
{I(u, done ∪ [a], s')}
```

内部 case split：
- `dfn a < low u` → `set_low_back_preserves_I`：`low u` 下降为新值 `dfn a`，来源变为 (Src3)
- `dfn a >= low u` → skip，不变

### 6.3 回边自环（a = u）

```
{I(u, done, s0) ∧ In u (stack s0) ∧ dg_step g u u}
    update_low u (dfn u)
{I(u, done ∪ [u], s')}
```

`dfn u < low u ≤ dfn u` 矛盾，故恒走 skip 分支。

### 6.4 交叉边

```
{I(u, done, s0) ∧ a ∈ visited ∧ ~ In a (stack s0) ∧ dg_step g u a}
    skip
{I(u, done ∪ [a], s0)}
```

不修改任何字段，仅扩展 done。

## 7. 桥接：`forset_inv` → `scc_is_low_v`

当 forset 完成（`done = dg_step g u`）：

```
{forset_inv u (dg_step g u) s
 ∧ done_visited (dg_step g u) s
 ∧ fa_child_of_u u s
 ∧ (∀ v, dg_step (state_to_dfs_tree g s root) u v → scc_is_low_v s v)
 ∧ low_src u (dg_step g u) s}
    —— (纯逻辑推理，不需要程序执行) ——
{scc_is_low_v s u}
```

证明框架：
1. `scc_low_tree s u` 至少含 `u` → `min_nonempty_exists` 取出最小 dfn 值 m 及取得者 w
2. `low_u_le_dfn_scc_low_tree`：`low u ≤ dfn w = m`（用不等式不变量 + 孩子 IH）
3. `low_src` 三项选言各自证明 `m ≤ low u`：
   - (Src1) `low u = dfn u`：`u` 在树中，`m ≤ dfn u = low u`
   - (Src2) `low u = low v`（v 是树孩子）：孩子 low 正确 + 可达性传递
   - (Src3) `low u = dfn w`（w 是回边目标）：`w` 在树中，`m ≤ dfn w = low u`
4. `Nat.le_antisymm` → `low u = m` → `scc_is_low_v s u`

## 8. 递归归纳假设（Lfix）

### 8.1 `Q_low`——全范式后条件（主归纳）

```
Q_low u s0 tt s :=
    {~ u ∈ visited s0 ∧ wf_scc_state s0 ∧ stack_dfn_order s0 ∧ dfn_injective s0}
        Lfix (tarjan_scc_f g) u
    { low_post u                                           — SELF
    ∧ u ∈ visited s
    ∧ stack_dfn_order s ∧ dfn_injective s
    ∧ (∀ anc d,                                            — FRAME (11 项)
          forset_inv anc d s0 → In anc (stack s0) →
          dfn_injective s0 → low_src anc d s0 →
          (∀ w, d w → dg_step g anc w → fa s0 w = anc → fa s0 w ≠ w →
           scc_is_low_v s0 w) →
          fa_child_of_u anc s0 → fa_not_done_implies_eq_u anc (d ∪ [u]) s0 →
          done_visited d s0 → dfn s0 anc < timer s0 →
          forset_inv anc d s
        ∧ In anc (stack s) ∧ stack_dfn_order s ∧ dfn_injective s
        ∧ low_src anc d s
        ∧ (∀ w, d w → dg_step g anc w → fa s w = anc → fa s w ≠ w →
             scc_is_low_v s w)
        ∧ fa_child_of_u anc s ∧ fa_not_done_implies_eq_u anc (d ∪ [u]) s
        ∧ done_visited d s
        ∧ (fa s0 u = anc → fa s u = anc))
    ∧ (∀ w, w ∈ visited s0 → fa s w = fa s0 w) }           — FA
```

**三层结构**：
| 层 | 内容 | 作用 |
|----|------|------|
| **SELF** | `low_post u` + visited 等 | u 自身 low 正确 |
| **FRAME** | 任意祖先 anc 的 `forset_inv` 在调用后仍成立 | 允许在 forset 体中的树边上调用 `W v` |
| **FA** | 已 visited 顶点的 fa 不变 | fa 稳定性 |

### 8.2 `Q_fa_rich`——fa+visited 保持（独立归纳）

```
Q_fa_rich u s0 tt s :=
    {~ u ∈ visited s0}
        Lfix (tarjan_scc_f g) u
    { (∀ w, w ∈ visited s0 → w ∈ visited s)          — visited 保持
    ∧ (∀ w, w ∈ visited s0 → fa s w = fa s0 w) }     — fa 保持
```

### 8.3 为什么 fa 保持要独立归纳

`Q_low` 的 FRAME 太重（11 个合取支），用它证 fa 保持会循环：
- 证 `Q_low` 的 forset 部分需要 fa 保持
- 证 fa 保持又需要 forset 体的 Hoare 推理

**解法**：先做轻量 Lfix 归纳证 `Q_fa_rich`，再在 `Q_low` 证明中自由引用。

## 9. HW_frame 桥：从 `Q_low` 到 forset 可用形式

`Q_low_to_HW_frame`（line 2513）将全称量化的 `Q_low` 转换为 `forset_keep_forset_inv` 所需的具象 Hoare 三元组：

```
给定 IH: ∀ s0 a, {s = s0} W a {Q_low a s0}

则对满足 10 个前提的 anc, d, v, s0:
  {s = s0}
      W v
  { forset_inv anc d        — anc 的 forset_inv 保持
  ∧ In anc (stack)
  ∧ stack_dfn_order ∧ dfn_injective ∧ low_src anc d
  ∧ (孩子 IH 保持)
  ∧ fa_child_of_u anc ∧ fa_not_done_implies_eq_u anc (d ∪ [v])
  ∧ done_visited d
  ∧ low_post v              — v 自身 low 正确
  ∧ v ∈ visited
  ∧ (fa s0 v = anc → fa s' v = anc) }
```

## 10. 主定理证明的管道图

将阶段 1-3 串联（阶段 4 的 Frame 保持同理但针对 anc）：

```
{low_pre a ∧ stack_dfn_order ∧ dfn_injective}    — 初始状态 s0'
        │
        │  preloop_establishes_forset_precond
        ▼
{ forset_inv a ∅                                   — s_pre
∧ In a (stack)
∧ stack_dfn_order ∧ dfn_injective
∧ low a = dfn a
∧ fa_child_of_u a ∧ fa_not_done_implies_eq_u a ∅ }
        │
        │  forset_keep_forset_inv (用 HW_frame 桥接 Lfix IH)
        ▼
{ low_post a                                        — s_forset
∧ In a (stack)
∧ stack_dfn_order ∧ dfn_injective }
        │
        │  if low a == dfn a then pop_scc_a else skip
        ▼
{ low_post a                                        — s2 (最终状态)
∧ a ∈ visited
∧ stack_dfn_order ∧ dfn_injective }
```

**Frame 保持管道**（对任意祖先 anc，与上述主流程同时进行）：

```
{forset_inv anc d ∧ In anc (stack) ∧ ... (10 个前提)}   — s0'
        │
        │  preloop_preserves_frame
        ▼
{forset_inv anc d ∧ In anc (stack) ∧ ... (8 项)}         — s_pre
        │
        │  forset_keeps_anc_frame（Admitted）
        ▼
{forset_inv anc d ∧ In anc (stack) ∧ ... (9 项)}         — s_forset
        │
        │  pop_scc / skip 保持 frame
        ▼
{forset_inv anc d ∧ In anc (stack) ∧ ... (9 项)          — s2
 ∧ (fa s0' a = anc → fa s2 a = anc)}
```

## 11. 设计总结

```
顶层规约
  {low_pre u}
      tarjan_scc g u
  {low_post u}

展开为 Lfix 递归 + 三阶段管道
  {low_pre u}
      preloop u                     — 建立 forset_inv u ∅ + 6 个前置条件
  {forset 入口条件}
      forset (process_edge u W v)   — 不变量 I(u, done)：不等式 + 来源追踪 + 孩子 IH
  {I(u, 所有邻居) → low_post u}     — 桥接引理：不等式 + 来源 → 精确等式
      if low u == dfn u then pop    — 保持 low_post u
  {low_post u}

其中 Lfix 递归假设 Q_low 提供三层保障
  SELF:  low_post u                 — u 自身正确
  FRAME: 祖先的 forset_inv 保持      — 允许在树边上递归调用 W
  FA:    fa 对已 visited 顶点不变    — fa 稳定性

并有一个独立的轻量 Lfix 归纳 Q_fa_rich
  — 避免 Q_low 的 FRAME 重证明与 fa 保持之间的循环依赖
```

### 关键设计决策

| # | 决策 | 理由 |
|---|------|------|
| 1 | `forset_inv` 用纯不等式 | 对 `low u` 下降单调，避免每次 `update_low` 后重新证明等式 |
| 2 | `low_src` 三项选言 | 追踪 `low u` 来源，是 forset 完成时将不等式反转为等式的关键信息 |
| 3 | fa 保持（`Q_fa_rich`）与 low 正确性（`Q_low`）分离为两个 Lfix 归纳 | 避免 FRAME 重证明 ↔ fa 保持的循环依赖 |
| 4 | `Q_low` 内含全称量化的祖先 FRAME | 让递归调用能保持*调用者*的 `forset_inv`，使得 `Hoare_forset` 体能在树边上安全调用 `W` |
| 5 | `HW_frame` 桥（`Q_low_to_HW_frame`） | 将全称量化范式转为 `forset_keep_forset_inv` 期望的具象 Hoare 三元组 |
| 6 | 三重抽象层次（`forset_inv` ⊆ `I` ⊆ `Q_low`） | 逐层添加信息：不等式 → 加入来源追踪和孩子 IH → 加入递归 frame 保证 |

## 12. 当前证明状态

主定理 `tarjan_scc_keep_low_valid` 为 `Admitted`（line 3714）。剩余未关闭子目标：

| 行号 | 引理 | 阻塞原因 |
|------|------|----------|
| 3117 | `preloop_keep_scc_is_low_v_for_d` | `scc_low_tree` 在 preloop 前后的保持性 |
| 3140 | `forset_keep_fa_a` | `Q_low` 假设穿入 `process_edge_keep_fa` 保持 `fa[a]` |
| 3207 | `forset_keeps_anc_frame` | forset 体保持祖先 frame；`set_fa_state` 的 RecordUpdate simpl |
| 3302 | `forset_keep_fa_of_visited` | 3 TODO：`wf_scc_state` 经 `set_fa`、`visited` 经 `W v`、`update_low` 命名 |
| 3480 | `Hchild_anc_pre` | frame 部分：`scc_low_tree` 在 preloop 后保持 |
| 3549 | `Hdfn_fs_lt` | dfn 排序在 forset 中保持 |
| 3635 | `low_src` 在 pop_scc 后 | 栈依赖的 `low_src`（`In w (stack)` 依赖余栈 rest） |
| 3638 | `scc_is_low_v` 在 pop_scc 后 | 栈依赖的孩子归纳假设 |
