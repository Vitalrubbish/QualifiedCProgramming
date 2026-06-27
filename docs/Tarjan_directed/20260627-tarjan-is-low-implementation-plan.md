# Tarjan_scc_is_low.v：FRAME 压平 + Level 2 引理实施计划

**Author**: Vitalrubbish
**Date**: 2026-06-27

## Context

`Tarjan_scc_is_low.v`（3716 行）主定理 `tarjan_scc_keep_low_valid` 为 `Admitted`，有 ~10 个未关闭子目标。根因不是语义不可证，而是两层障碍叠加：

- **障碍 A — 簿记爆炸**：`Q_low` 的 FRAME 部分采用 `∀ anc d, 9前提→10结论` 的参数化形式。每次使用，调用方必须实例化 anc/d、逐条建立 9 个前提、从 10 个结论解构目标。20 个合取支的簿记量超过单次推理承载能力。
- **障碍 B — 缺少中间引理**：dfn 保持、visited 保持、scc_low_tree 保持等性质每次都要从零现场推导。

改进采用双轨策略：**FRAME 压平**（将 `9前提→10结论` 压缩为 `I anc d s0 → fa_not_done → I anc d s ∧ fa_not_done`）+ **35 个 Level 2 引理**（按操作分组，每个有独立可验证的语句）。

## Current State

**文件**：`SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`（3716 行）

**已证明部分**：`wf_scc_state`、`forset_inv`、`low_src`、`preloop_establishes_forset_precond`、`forset_keep_forset_inv`、`Q_low_to_HW_frame`、`tarjan_scc_keep_fa`（`Q_fa_rich` 归纳）等基础设施均已证明。

## Design Summary

### Track A: FRAME 压平（纯重构）—— ✅ Round 1 已完成

将局部 `I`（9 合取支，不含 `fa_not_done_implies_eq_u` 因为它需要在 `Q_low` FRAME 中使用 `(d ∪ [u])` 修饰符）提升为顶层定义，`Q_low` FRAME 简化为 `I anc d s0 → fa_not_done... → I anc d s ∧ fa_not_done...`（2前提→2结论，原为 9前提→10结论）。

```coq
Definition I (u: V) (done: V -> Prop) (s: SCCSt): Prop :=
  forset_inv u done s /\
  done_visited done s /\
  In u (stack s) /\
  stack_dfn_order s /\
  dfn_injective s /\
  low_src u done s /\
  (forall v, done v -> dg_step g u v -> fa s v = u -> fa s v <> v -> scc_is_low_v s v) /\
  fa_child_of_u u s /\
  dfn s u < timer s.

Definition Q_low (u: V) (s0: SCCSt) (_: unit) (s: SCCSt): Prop :=
  (~ u ∈ visited s0 /\ wf_scc_state s0 /\ stack_dfn_order s0 /\ dfn_injective s0) ->
  (low_post u s /\ u ∈ visited s /\ stack_dfn_order s /\ dfn_injective s /\
   (forall anc d,
      I anc d s0 -> fa_not_done_implies_eq_u anc (d ∪ [u]) s0 ->
      I anc d s /\ fa_not_done_implies_eq_u anc (d ∪ [u]) s) /\
   (forall anc d, I anc d s0 -> fa s0 u = anc -> fa s u = anc) /\
   (forall w, w ∈ visited s0 -> fa s w = fa s0 w)).
```

### Track B: Level 2 引理（35 个，8 组）

| 组 | 操作 | 引理 | 数量 | 复杂度 |
|----|------|------|------|--------|
| A | `set_fa_state` 字段投影 | L1–L11 | 11 | 纯机械 |
| B | `preloop` 语义 | L12–L13 | 2 | 语义中等 |
| C | `get'/update_low` 保持 | L14–L20 | 7 | 纯机械 |
| D | `process_edge` 保持 J | L21–L23 | 3 | 机械组合 |
| E | `forset` 级保持 | L24–L26 | 3 | Hoare_forset 组合 |
| F | `I_anc` FRAME 保持 | L27–L30 | 4 | Hoare_forset + 边分类 |
| G | `pop_scc` 语义 | L31–L33 | 3 | 语义（栈分裂） |
| H | W 调用提取 | L34–L35 | 2 | 从 Q_low 实例化 |

## Implementation Rounds

### Round 1: FRAME 压平（Track A）✅ 已完成

**产出**：
- 顶层 `Definition I`（9 合取支）和 `Lemma I_proper`
- `Q_low` 定义简化为 `I` carrier
- `Q_low_to_HW_frame` 适配新 `Q_low` 形状
- `forset_keep_fa_of_visited` 和主定理的 destruct 模式更新
- 主定理中添加转换 wrapper（2 个临时 admit，将在 Round 7-9 关闭）
- 文件编译通过

### Round 2: 组 A — set_fa_state 字段投影（L1–L11）

**文件**：`Tarjan_scc_is_low.v`（在 SCCSt record 相关区域之后）

**引理**：

```coq
(* 字段投影 — simpl 直接展开 *)
L1:  Lemma set_fa_state_visited s v p: visited (set_fa_state s v p) = visited s.
L2:  Lemma set_fa_state_timer s v p: timer (set_fa_state s v p) = timer s.
L3:  Lemma set_fa_state_dfn s v p: dfn (set_fa_state s v p) = dfn s.
L4:  Lemma set_fa_state_low s v p: low (set_fa_state s v p) = low s.
L5:  Lemma set_fa_state_stack s v p: stack (set_fa_state s v p) = stack s.
L6:  Lemma set_fa_state_sccs s v p: sccs (set_fa_state s v p) = sccs s.
L7:  Lemma set_fa_state_fa_self s v p: fa (set_fa_state s v p) v = p.
L8:  Lemma set_fa_state_fa_other s v p w: w ≠ v -> fa (set_fa_state s v p) w = fa s w.

(* 复合性质 — 使用 L1-L8 展开 *)
L9:  Lemma set_fa_state_wf_scc_state s v a:
       wf_scc_state s -> a ∈ visited s -> wf_scc_state (set_fa_state s v a).
L10: Lemma set_fa_state_stack_dfn_order s v p:
       stack_dfn_order s -> stack_dfn_order (set_fa_state s v p).
L11: Lemma set_fa_state_dfn_injective s v p:
       dfn_injective s -> dfn_injective (set_fa_state s v p).
```

**证明方式**：`unfold set_fa_state; simpl;` 然后逐合取支展开。

### Round 3: 组 C — get'/update_low 保持（L14–L20）

**文件**：`Tarjan_scc_is_low.v`

**引理**：

```coq
L14: Lemma get_low_preserves_fa (v w: V) (p: V):
       Hoare (fun s => fa s w = p) (get' (fun s' => low s' v)) (fun _ s => fa s w = p).
L15: Lemma get_low_preserves_visited (v w: V):
       Hoare (fun s => w ∈ visited s) (get' (fun s' => low s' v)) (fun _ s => w ∈ visited s).
L16: Lemma get_low_preserves_wf_scc_state (v: V):
       Hoare (fun s => wf_scc_state s) (get' (fun s' => low s' v)) (fun _ s => wf_scc_state s).
L17: Lemma update_low_preserves_stack_dfn_order (a: V) (lv: nat):
       Hoare (fun s => stack_dfn_order s) (update_low a lv) (fun _ s => stack_dfn_order s).
L18: Lemma update_low_preserves_dfn_injective (a: V) (lv: nat):
       Hoare (fun s => dfn_injective s) (update_low a lv) (fun _ s => dfn_injective s).
L19: Lemma update_low_preserves_visited (a w: V) (lv: nat):
       Hoare (fun s => w ∈ visited s) (update_low a lv) (fun _ s => w ∈ visited s).
L20: Lemma update_low_preserves_wf_scc_state (a: V) (lv: nat):
       Hoare (fun s => wf_scc_state s) (update_low a lv) (fun _ s => wf_scc_state s).
```

**证明方式**：`get'` 不修改状态（`unfold get'; hoare_auto_s`）；`update_low` 只修改 `low` 字段（`unfold update_low, update'; hoare_auto_s`，然后 simpl）。

### Round 4: 组 D — process_edge 保持 J（L21–L23）

**文件**：`Tarjan_scc_is_low.v`

**定义 J**：

```coq
Definition J (w: V) (s_pre: SCCSt) (done: V -> Prop) (s: SCCSt): Prop :=
  wf_scc_state s /\ stack_dfn_order s /\ dfn_injective s /\
  w ∈ visited s /\ fa s w = fa s_pre w.
```

**引理**：

```coq
L21: Lemma back_edge_preserves_J (a v w: V) (done: V -> Prop) (s_pre s0: SCCSt):
       Hoare (fun s => s = s0 /\ J w s_pre done s /\ v ∈ visited s
                    /\ In v (stack s) /\ dg_step g a v)
             (update_low a (dfn s0 v))
             (fun _ s => J w s_pre (done ∪ [v]) s).

L22: Lemma cross_edge_preserves_J (a v w: V) (done: V -> Prop) (s_pre: SCCSt):
       Hoare (fun s => J w s_pre done s /\ v ∈ visited s /\ ~ In v (stack s))
             skip
             (fun _ s => J w s_pre (done ∪ [v]) s).

L23: Lemma tree_edge_preserves_J (a v w: V) (done: V -> Prop) (s_pre: SCCSt)
       (W: V -> program SCCSt unit)
       (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
       Hoare (fun s => s = s0 /\ J w s_pre done s /\ ~ v ∈ visited s /\ dg_step g a v)
             (set_fa v a ;; W v ;; lv <- get' (fun s' => low s' v) ;; update_low a lv)
             (fun _ s => J w s_pre (done ∪ [v]) s).
```

### Round 5: 组 B — preloop 语义（L12–L13）

**文件**：`Tarjan_scc_is_low.v`

**引理**：

```coq
L12: Lemma preloop_preserves_scc_low_tree (a w: V) (s0 s_pre: SCCSt):
       w ≠ a -> (s0, tt, s_pre) ∈ preloop a ->
       scc_low_tree s0 w == scc_low_tree s_pre w.

L13: Lemma preloop_preserves_scc_is_low_v (a w: V) (s0 s_pre: SCCSt):
       w ≠ a -> (s0, tt, s_pre) ∈ preloop a ->
       scc_is_low_v s0 w -> scc_is_low_v s_pre w.
```

**关键论证**：preloop 修改 visited[a]=true, dfn[a]=timer, low[a]=timer, stack=a::stack。对 w ≠ a，`state_to_dfs_tree` 的新边仅涉及 a，不影响 w 的 `scc_low_tree`。

### Round 6: 组 G — pop_scc 语义（L31–L33）

**文件**：`Tarjan_scc_is_low.v`

**引理**：

```coq
L31: Lemma pop_scc_preserves_I_for_rest (a anc: V) (d: V -> Prop) (s: SCCSt):
       I anc d s -> In anc (stack s) -> low s a = dfn s a ->
       let s_pop := pop_scc_state s a in
       let '(popped, rest) := stack_split_at (stack s) a in
       anc ∈ rest -> I anc d s_pop.

L32: Lemma pop_scc_preserves_low_src (a anc: V) (d: V -> Prop) (s: SCCSt):
       low_src anc d s -> In anc (stack s) -> low s a = dfn s a ->
       let s_pop := pop_scc_state s a in
       let '(popped, rest) := stack_split_at (stack s) a in
       anc ∈ rest -> low_src anc d s_pop.

L33: Lemma pop_scc_preserves_scc_is_low_v_for_rest (a w: V) (s: SCCSt):
       scc_is_low_v s w ->
       (fa s w = a -> False) ->
       scc_is_low_v (pop_scc_state s a) w.
```

### Round 7: 组 H — W 调用提取（L34–L35）

**文件**：`Tarjan_scc_is_low.v`

**引理**：

```coq
L34: Lemma W_preserves_I (W: V -> program SCCSt unit)
       (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
       forall v anc d s0,
         I anc d s0 -> dfn s0 anc < timer s0 -> ~ v ∈ visited s0 ->
         Hoare (fun s' => s' = s0) (W v) (fun _ s' => I anc d s').

L35: Lemma W_preserves_fa (W: V -> program SCCSt unit)
       (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
       forall v w s0,
         w ∈ visited s0 -> ~ v ∈ visited s0 ->
         Hoare (fun s' => s' = s0) (W v) (fun _ s' => fa s' w = fa s0 w).
```

### Round 8: 组 E — forset 级保持（L24–L26）

**文件**：`Tarjan_scc_is_low.v`

**引理**：

```coq
L24: Lemma forset_preserves_visited (a w: V) (W: V -> program SCCSt unit)
       (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
       forall s_pre,
         w ∈ visited s_pre -> wf_scc_state s_pre ->
         Hoare (fun s => s = s_pre)
               (forset (fun v => dg_step g a v) (process_edge a W))
               (fun _ s => w ∈ visited s).

L25: Lemma forset_preserves_dfn (a w: V) (n: nat) (W: V -> program SCCSt unit)
       (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
       forall s_pre,
         Hoare (fun s => s = s_pre /\ dfn s w = n)
               (forset (fun v => dg_step g a v) (process_edge a W))
               (fun _ s => dfn s w = n).

L26: Lemma forset_preserves_fa (a w: V) (p: V) (W: V -> program SCCSt unit)
       (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
       forall s_pre,
         Hoare (fun s => s = s_pre /\ w ∈ visited s /\ fa s w = p)
               (forset (fun v => dg_step g a v) (process_edge a W))
               (fun _ s => fa s w = p).
```

### Round 9: 组 F — I_anc FRAME 保持（L27–L30）

**文件**：`Tarjan_scc_is_low.v`

**引理**：

```coq
Definition HW_frame_I (W: V -> program SCCSt unit) :=
  forall v anc d s0,
    I anc d s0 -> dfn s0 anc < timer s0 -> ~ v ∈ visited s0 ->
    Hoare (fun s' => s' = s0) (W v)
          (fun _ s' => I anc d s' /\ low_post v s' /\ v ∈ visited s').

L27: Lemma tree_edge_preserves_I_anc (a anc v: V) (d: V -> Prop) (s0: SCCSt)
       (W: V -> program SCCSt unit) (HW: HW_frame_I W):
       I anc d s0 -> ~ v ∈ visited s0 -> dg_step g a v -> dfn s0 anc < timer s0 ->
       Hoare (fun s' => s' = s0)
             (set_fa v a ;; W v ;; lv <- get' (fun s' => low s' v) ;; update_low a lv)
             (fun _ s' => I anc d s').

L28: Lemma back_edge_preserves_I_anc (a anc v: V) (d: V -> Prop) (s0: SCCSt):
       I anc d s0 -> v ∈ visited s0 -> In v (stack s0) -> dg_step g a v ->
       Hoare (fun s' => s' = s0) (update_low a (dfn s0 v)) (fun _ s' => I anc d s').

L29: Lemma cross_edge_preserves_I_anc (a anc v: V) (d: V -> Prop) (s0: SCCSt):
       I anc d s0 -> v ∈ visited s0 -> ~ In v (stack s0) -> dg_step g a v ->
       I anc d s0.

L30: Lemma forset_keeps_anc_frame_proved (a anc: V) (d: V -> Prop) (s_pre: SCCSt)
       (W: V -> program SCCSt unit) (HW: HW_frame_I W):
       I anc d s_pre ->
       Hoare (fun s => s = s_pre)
             (forset (fun v => dg_step g a v) (process_edge a W))
             (fun _ s => I anc d s).
```

### Round 10: 关闭所有 Admit + 最终验证

用所有 L1–L35 关闭 8 个 admit，运行 `rocq_compile_file` 最终验证。

## Admit → 引理映射

| Admit（行号） | 所用引理 | 关闭轮次 |
|---------------|---------|---------|
| `preloop_keep_scc_is_low_v_for_d` | L12, L13 | Round 10 |
| `forset_keep_fa_a` | L35 | Round 10 |
| `forset_keeps_anc_frame` | L27–L30（组合为 L30） | Round 10 |
| `forset_keep_fa_of_visited` TODO #1 | L9, L10, L11 | Round 10 |
| `forset_keep_fa_of_visited` TODO #2 | L24 | Round 10 |
| `forset_keep_fa_of_visited` TODO #3 | L14–L20 | Round 10 |
| `forset_keep_fa_of_visited` 非树边分支 | L21, L22 | Round 10 |
| `Hchild_anc_pre` | L12, L13 | Round 10 |
| `Hdfn_fs_lt` | L25 | Round 10 |
| `low_src` after pop_scc | L31, L32 | Round 10 |
| `scc_is_low_v` after pop_scc | L33 | Round 10 |
| `Hdfn_s2_lt` (Round 1 新增) | L25 | Round 10 |
| `Hfa_trans` (Round 1 新增) | L35 | Round 10 |

## 每轮验证协议

每轮完成后：
1. `make -f _tarjan_low.mk` 编译 `Tarjan_scc_is_low.v`
2. 如果编译失败，在本轮内修复（不进入下一轮）
3. 最终轮次：确认文件中无遗留 `Admitted` 和 `admit.`

## 风险与缓解

| 风险 | 缓解 |
|------|------|
| FRAME 压平改变 `I` 形状导致已证引理 destruct 模式破裂 | Round 1 已完成，编译通过 |
| `I` 第 9 合取支 `dfn s u < timer s` 导致额外证明负担 | 检查所有 `I` 构造点是否已有该信息 |
| 组 B preloop 语义证明涉及 `state_to_dfs_tree` 深层性质 | 允许 L12 使用更弱的结论（`⊆` 而非 `==`） |
| 组 G pop_scc 语义的栈依赖处理比预期复杂 | L31–L33 的假设条件已为最典型调用场景设计 |
