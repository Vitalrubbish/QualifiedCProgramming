# Tarjan_scc_is_low.v：FRAME 压平 + Level 2 引理重构计划

**Author**: Vitalrubbish
**Date**: 2026-06-27

## 1. 问题诊断

### 1.1 根因

当前 `Tarjan_scc_is_low.v` 有 ~10 个 admit。根因不是语义不可证，而是两层障碍叠加：

**障碍 A — 簿记爆炸**：`Q_low` 的 FRAME 部分采用 `∀ anc d, 9前提 → 11结论` 的参数化形式。
每次使用，调用方必须实例化 anc/d、逐条建立 9 个前提、从 11 个结论解构目标。
9+11=20 个合取支的簿记量超过 agent 单次推理承载能力——agent 在建立前提的途中就因
变量 shadowing、上下文过深而迷路，**根本走不到语义推理**。

**障碍 B — 缺少中间引理**：在 `Q_low` 的巨大参数化接口之下，缺少针对具体性质的
独立可引用引理。dfn 保持、visited 保持、scc_low_tree 保持等性质每次都要从零开始
现场推导。

### 1.2 对比 Kosaraju

| | Kosaraju | Tarjan |
|---|---|---|
| FRAME 形式 | 平铺合取支，直接 destruct | ∀ anc d, 9前提→11结论，需实例化+建立前提 |
| 使用成本 | 1 行 destruct | ~17 行前提建立 |
| 为什么不同 | 无"调用者不变量被子调用保持"问题 | forset 需要递归调用不破坏调用者状态 |

Kosaraju 不需要参数化 FRAME，因为它的递归没有 forset 内的嵌套 W 调用。

### 1.3 改进双轨策略

- **A. FRAME 压平**：把 `I`（line 2242）从内部不变提升为 `Q_low` FRAME 的打包载体，
  替换 `9前提→11结论` 为 `I anc d s0 → I anc d s`。纯重构，零风险。
- **B. Level 2 引理**：35 个中间引理，按操作分组，每个有独立可验证的语句。

## 2. FRAME 压平（改进 A）

### 2.1 现有 `I` 定义（line 2242）

```coq
I(u, done, s) :=
    forset_inv u done s
  ∧ done_visited done s
  ∧ In u (stack s)
  ∧ stack_dfn_order s
  ∧ dfn_injective s
  ∧ low_src u done s
  ∧ (∀ v, done v → dg_step g u v → fa s v = u → fa s v ≠ v
       → scc_is_low_v s v)
  ∧ fa_child_of_u u s
  ∧ fa_not_done_implies_eq_u u done s
```

需补第 10 合取支 `dfn s u < timer s`。

### 2.2 `Q_low` FRAME 部分：改前 vs 改后

**改前**：

```coq
Q_low u s0 _ s :=
  (~ u ∈ visited s0 ∧ wf_scc_state s0 ∧ ...) →
  ( low_post u s ∧ ... ∧
    (∀ anc d,
       forset_inv anc d s0 → In anc (stack s0) →
       dfn_injective s0 → low_src anc d s0 →
       (∀ w, d w → dg_step g anc w → fa s0 w = anc → fa s0 w ≠ w
        → scc_is_low_v s0 w) →
       fa_child_of_u anc s0 →
       fa_not_done_implies_eq_u anc (d ∪ [u]) s0 →
       done_visited d s0 → dfn s0 anc < timer s0 →
       forset_inv anc d s ∧ In anc (stack s) ∧ ... [11 结论]) ∧
    (∀ w, w ∈ visited s0 → fa s w = fa s0 w)
  )
```

**改后**：

```coq
Q_low u s0 _ s :=
  (~ u ∈ visited s0 ∧ wf_scc_state s0 ∧ ...) →
  ( low_post u s ∧ u ∈ visited s ∧ stack_dfn_order s ∧ dfn_injective s ∧
    (∀ anc d, I anc d s0 → I anc d s) ∧                  (* FRAME，1前提→1结论 *)
    (∀ anc d, I anc d s0 → fa s0 u = anc → fa s u = anc) ∧  (* fa 传递 *)
    (∀ w, w ∈ visited s0 → fa s w = fa s0 w)                (* FA 层 *)
  )
```

### 2.3 `Q_low_to_HW_frame` 简化

**改前**：~35 行，逐个建立 9 个前提，再解构 11 个结论。

**改后**：

```coq
Lemma Q_low_to_HW_frame ...:
  ...
  specialize (IH s0 v).
  refine (Hoare_conseq_post _ _ _ _ _ IH).
  intros b s' HQ. unfold Q_low in HQ.
  assert (Hant: ~ v ∈ visited s0 ∧ ...) by ...
  destruct (HQ Hant) as [Hlow_post [Hvis [Horder_s [Hinj_s [Hframe Hfa_all]]]]].
  specialize (Hframe anc d Hinv_s0).   (* 一行！不再需要 9 个前提 *)
  destruct Hframe as [HI_s HI_fa].
  destruct HI_s as [Hfinv_s [Hdone_vis_s [Hinstk_s ...]]].  (* 解构 I *)
  ...
```

### 2.4 风险评估

纯重构——不改变语义内容。所有已证明引理的证明模式不变（仍然从 `I` 解构字段），
只是调用方不需要自己建立前提。

## 3. Level 2 引理清单（改进 B）

### 3.1 分组总览

| 组 | 涉及操作 | 引理数 | 复杂度 |
|----|---------|--------|--------|
| A | `set_fa_state` | L1–L11 | 纯机械 |
| B | `preloop` | L12–L13 | 语义中等 |
| C | `get'/update_low` | L14–L20 | 纯机械 |
| D | `process_edge` | L21–L23 | 机械 |
| E | `forset` | L24–L26 | Hoare_forset 组合 |
| F | `I_anc` FRAME | L27–L30 | Hoare_forset + 边分类 |
| G | `pop_scc` | L31–L33 | 语义（栈分裂） |
| H | W 调用提取 | L34–L35 | 从 Q_low 实例化 |

### 3.2 组 A：set_fa_state 字段投影（L1–L11）

解决 `forset_keep_fa_of_visited` TODO #1。

```coq
(* 字段投影 *)
Lemma set_fa_state_visited s v p:
  visited (set_fa_state s v p) = visited s.
Lemma set_fa_state_timer s v p:
  timer (set_fa_state s v p) = timer s.
Lemma set_fa_state_dfn s v p:
  dfn (set_fa_state s v p) = dfn s.
Lemma set_fa_state_low s v p:
  low (set_fa_state s v p) = low s.
Lemma set_fa_state_stack s v p:
  stack (set_fa_state s v p) = stack s.
Lemma set_fa_state_sccs s v p:
  sccs (set_fa_state s v p) = sccs s.
Lemma set_fa_state_fa_self s v p:
  fa (set_fa_state s v p) v = p.
Lemma set_fa_state_fa_other s v p w:
  w ≠ v → fa (set_fa_state s v p) w = fa s w.

(* 复合性质 *)
Lemma set_fa_state_wf_scc_state s v a:
  wf_scc_state s → a ∈ visited s → wf_scc_state (set_fa_state s v a).
Lemma set_fa_state_stack_dfn_order s v p:
  stack_dfn_order s → stack_dfn_order (set_fa_state s v p).
Lemma set_fa_state_dfn_injective s v p:
  dfn_injective s → dfn_injective (set_fa_state s v p).
```

**证明方式**：`unfold set_fa_state; simpl;` 然后逐合取支展开。

### 3.3 组 B：preloop 语义（L12–L13）

关 `preloop_keep_scc_is_low_v_for_d`（line 3117）和 `Hchild_anc_pre`（line 3480）。

```coq
Lemma preloop_preserves_scc_low_tree (a w: V) (s0 s_pre: SCCSt):
  w ≠ a → (s0, tt, s_pre) ∈ preloop a →
  scc_low_tree s0 w == scc_low_tree s_pre w.

Lemma preloop_preserves_scc_is_low_v (a w: V) (s0 s_pre: SCCSt):
  w ≠ a → (s0, tt, s_pre) ∈ preloop a →
  scc_is_low_v s0 w → scc_is_low_v s_pre w.
```

**关键论证**：preloop 改 visited[a]=true, dfn[a]=timer, low[a]=timer, stack=a::stack。
对 w ≠ a，`state_to_dfs_tree` 的新边仅涉及 a（新 visited 节点），不影响 w 的
`scc_low_tree`。

### 3.4 组 C：基本操作保持（L14–L20）

关 `forset_keep_fa_of_visited` TODO #3（line 3299）。

```coq
Lemma get_low_preserves_fa (v w: V) (p: V):
  Hoare (fun s => fa s w = p) (get' (fun s' => low s' v)) (fun _ s => fa s w = p).

Lemma get_low_preserves_visited (v w: V):
  Hoare (fun s => w ∈ visited s) (get' (fun s' => low s' v)) (fun _ s => w ∈ visited s).

Lemma update_low_preserves_stack_dfn_order (a: V) (lv: nat):
  Hoare (fun s => stack_dfn_order s) (update_low a lv) (fun _ s => stack_dfn_order s).

Lemma update_low_preserves_dfn_injective (a: V) (lv: nat):
  Hoare (fun s => dfn_injective s) (update_low a lv) (fun _ s => dfn_injective s).

Lemma update_low_preserves_visited (a w: V) (lv: nat):
  Hoare (fun s => w ∈ visited s) (update_low a lv) (fun _ s => w ∈ visited s).
```

### 3.5 组 D：process_edge 保持 J（L21–L23）

关 `forset_keep_fa_of_visited` 非树边分支（line 3301）。

`J` = `wf_scc_state ∧ stack_dfn_order ∧ dfn_injective ∧ w ∈ visited ∧ fa w = fa s_pre w`。

```coq
Lemma back_edge_preserves_J (a v w: V) (done: V -> Prop) (s_pre: SCCSt):
  Hoare (fun s => s = s0 ∧ J done s ∧ v ∈ visited s ∧ In v (stack s) ∧ dg_step g a v)
        (update_low a (dfn s0 v))
        (fun _ s => J (done ∪ [v]) s).

Lemma cross_edge_preserves_J (a v w: V) (done: V -> Prop):
  Hoare (fun s => J done s ∧ v ∈ visited s ∧ ~ In v (stack s))
        skip
        (fun _ s => J (done ∪ [v]) s).

Lemma tree_edge_preserves_J (a v w: V) (done: V -> Prop) (s_pre: SCCSt)
      (W: V -> program SCCSt unit)
      (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
  Hoare (fun s => s = s0 ∧ J done s ∧ ~ v ∈ visited s ∧ dg_step g a v)
        (set_fa v a ;; W v ;; lv <- get' (fun s' => low s' v) ;; update_low a lv)
        (fun _ s => J (done ∪ [v]) s).
```

### 3.6 组 E：forset 级保持（L24–L26）

关 `forset_keep_fa_of_visited` TODO #2 和 `Hdfn_fs_lt`（line 3549）。

```coq
Lemma forset_preserves_visited (a w: V) (W: V -> program SCCSt unit)
      (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
  forall s_pre,
    w ∈ visited s_pre → wf_scc_state s_pre →
    Hoare (fun s => s = s_pre)
          (forset (fun v => dg_step g a v) (process_edge a W))
          (fun _ s => w ∈ visited s).

Lemma forset_preserves_dfn (a w: V) (n: nat) (W: V -> program SCCSt unit)
      (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
  forall s_pre,
    Hoare (fun s => s = s_pre ∧ dfn s w = n)
          (forset (fun v => dg_step g a v) (process_edge a W))
          (fun _ s => dfn s w = n).

Lemma forset_preserves_fa (a w: V) (p: V) (W: V -> program SCCSt unit)
      (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
  forall s_pre,
    Hoare (fun s => s = s_pre ∧ w ∈ visited s ∧ fa s w = p)
          (forset (fun v => dg_step g a v) (process_edge a W))
          (fun _ s => fa s w = p).
```

### 3.7 组 F：I_anc FRAME 保持（L27–L30）

关 `forset_keeps_anc_frame`（line 3207）。

```coq
(* 需要 W 保持 I_anc 的假设 *)
Definition HW_frame_I :=
  forall v anc d s0,
    I anc d s0 → dfn s0 anc < timer s0 → ~ v ∈ visited s0 →
    Hoare (fun s' => s' = s0) (W v) (fun _ s' => I anc d s' ∧ low_post v s' ∧ v ∈ visited s').

Lemma tree_edge_preserves_I_anc (a anc v: V) (d: V -> Prop) (s0: SCCSt)
      (W: V -> program SCCSt unit) (HW: HW_frame_I W):
  I anc d s0 → ~ v ∈ visited s0 → dg_step g a v → dfn s0 anc < timer s0 →
  Hoare (fun s' => s' = s0)
        (set_fa v a ;; W v ;; lv <- get' (fun s' => low s' v) ;; update_low a lv)
        (fun _ s' => I anc d s').

Lemma back_edge_preserves_I_anc (a anc v: V) (d: V -> Prop):
  I anc d s0 → v ∈ visited s0 → In v (stack s0) → dg_step g a v →
  Hoare (fun s' => s' = s0) (update_low a (dfn s0 v)) (fun _ s' => I anc d s').

Lemma cross_edge_preserves_I_anc (a anc v: V) (d: V -> Prop):
  I anc d s0 → v ∈ visited s0 → ~ In v (stack s0) → dg_step g a v →
  I anc d s0.  (* skip — 不需要 Hoare，直接逻辑蕴含 *)

Lemma forset_keeps_anc_frame_proved (a anc: V) (d: V -> Prop) (s_pre: SCCSt)
      (W: V -> program SCCSt unit) (HW: HW_frame_I W):
  I anc d s_pre →
  Hoare (fun s => s = s_pre)
        (forset (fun v => dg_step g a v) (process_edge a W))
        (fun _ s => I anc d s).
```

### 3.8 组 G：pop_scc 保持（L31–L33）

关 `low_src` admit（line 3635）和 `scc_is_low_v` admit（line 3638）。

```coq
Lemma pop_scc_preserves_I_for_rest (a anc: V) (d: V -> Prop) (s: SCCSt):
  I anc d s → In anc (stack s) → low s a = dfn s a →
  let s_pop := pop_scc_state s a in
  let '(popped, rest) := stack_split_at (stack s) a in
  anc ∈ rest → I anc d s_pop.

Lemma pop_scc_preserves_low_src (a anc: V) (d: V -> Prop) (s: SCCSt):
  low_src anc d s → In anc (stack s) → low s a = dfn s a →
  let s_pop := pop_scc_state s a in
  let '(popped, rest) := stack_split_at (stack s) a in
  anc ∈ rest → low_src anc d s_pop.

Lemma pop_scc_preserves_scc_is_low_v_for_rest (a w: V) (s: SCCSt):
  scc_is_low_v s w →
  (fa s w = a → False) →   (* w 不是 a 的孩子 *)
  scc_is_low_v (pop_scc_state s a) w.
```

### 3.9 组 H：W 调用提取（L34–L35）

```coq
Lemma W_preserves_I (W: V -> program SCCSt unit)
      (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
  forall v anc d s0,
    I anc d s0 → dfn s0 anc < timer s0 → ~ v ∈ visited s0 →
    Hoare (fun s' => s' = s0) (W v) (fun _ s' => I anc d s').

Lemma W_preserves_fa (W: V -> program SCCSt unit)
      (IH: forall s0 x, Hoare (fun s => s = s0) (W x) (Q_low x s0)):
  forall v w s0,
    w ∈ visited s0 → ~ v ∈ visited s0 →
    Hoare (fun s' => s' = s0) (W v) (fun _ s' => fa s' w = fa s0 w).
```

## 4. 引理 → Admit 映射表

| Admit（行号） | 所用引理 |
|---------------|---------|
| `preloop_keep_scc_is_low_v_for_d` (3117) | L12, L13 |
| `forset_keep_fa_a` (3139) | L35 |
| `forset_keeps_anc_frame` (3207) | L27–L30（组合为 L30） |
| TODO #1: `wf_scc_state` through `set_fa` (3272) | L9, L10, L11 |
| TODO #2: `w ∈ visited` through `W v` (3281) | L24（或从 J 中删除该合取支） |
| TODO #3: `get' ;; update_low` (3299) | L14–L20 |
| 非树边分支 (3301) | L21, L22 |
| `Hchild_anc_pre` (3480) | L12, L13 |
| `Hdfn_fs_lt` (3549) | L25 |
| `low_src` after pop_scc (3635) | L31, L32 |
| `scc_is_low_v` after pop_scc (3638) | L33 |

## 5. 实施顺序

| 轮次 | 内容 | 工作量估计 |
|------|------|-----------|
| 1 | FRAME 压平（改 `I`、`Q_low`、`Q_low_to_HW_frame`） | 纯重构，~1h |
| 2 | 组 A (L1–L11)：set_fa_state 字段投影 | 纯机械，~30min |
| 3 | 组 C (L14–L20)：get'/update_low 保持 | 纯机械，~30min |
| 4 | 组 D (L21–L23)：process_edge 保持 J | 用 L1–L11 + L14–L20 组合 |
| 5 | 组 B (L12–L13)：preloop 语义 | 有语义内容，~1–2h |
| 6 | 组 G (L31–L33)：pop_scc 语义 | 有语义内容，~1–2h |
| 7 | 组 H (L34–L35)：W 调用提取 | 依赖步骤 1（FRAME 压平） |
| 8 | 组 E (L24–L26)：forset 组合 | 用 Hoare_forset + 组 D |
| 9 | 组 F (L27–L30)：I_anc FRAME | 用 Hoare_forset + 组 H |
| 10 | 关 admit | 每个 1–3 行引理调用 |

## 6. 验证

每轮完成后 `rocq_compile_file` 编译整个文件，确保已证明部分不退化。
全部 admit 关闭后，`rocq_compile_file` 应返回编译成功。
