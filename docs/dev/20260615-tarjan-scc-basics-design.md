# Tarjan_scc_basics.v 设计文档

**Author**: Vitalrubbish
**Date**: 2026-06-15

## 概述

本文档给出 `Tarjan_scc_basics.v` 的完整设计。该文件位于
`SeparationLogic/algorithms/Tarjan_directed/` 下，是 Tarjan 有向图 SCC 验证的
**Layer 2b 第一个证明文件**。它建立 Tarjan SCC monadic 程序的基本不变量
和 Hoare 三元组，是后续 `Tarjan_scc_is_dfn.v`、`Tarjan_scc_is_low.v`、
`Tarjan_scc_stack.v`、`SCC_correctness.v` 的**共同基础**。

本文档应与以下文档协同阅读：

- `docs/dev/20260614-tarjan-scc-monadic-correctness-design.md` — Layer 2 总体设计
- `docs/dev/20260612-scc-basic-design.md` — SCC_basic.v 设计文档（Layer 3）
- `docs/Tarjan_directed/Tarjan_scc.md` — Tarjan_scc.v 定义/定理参考
- `docs/plan-tarjan-scc-2sat-verification.md` — 六阶段总计划

**参考实现**：`SeparationLogic/algorithms/Tarjan/Tarjan_basics.v`（1577 行）—
桥判定版本的基本不变量证明。本文档中标记 `[BRIDGE]` 的段落描述了与桥判定版本的差异。

---

## 1. 文件定位

### 1.1 在三层架构中的位置

```
Layer 3 (数学规格层):  SCC_basic.v                           ✅ 已完成
        ↑ 数学依赖 (is_SCC, scc_partition, dg_step, …)
Layer 2b (正确性证明):  Tarjan_scc_basics.v                   🆕 本文档
                      → Tarjan_scc_is_dfn.v                  🆕 后续
                      → Tarjan_scc_is_low.v                  🆕 后续
                      → Tarjan_scc_stack.v                   🆕 后续
                      → SCC_correctness.v                    🆕 后续
        ↑ 程序定义依赖 (SCCSt, tarjan_scc, …)
Layer 2a (Monad 程序):  Tarjan_scc.v                          ✅ 已完成
```

### 1.2 在证明文件依赖链中的位置

```
Tarjan_scc_basics.v ─────────────────────────────┐
    │  visited/dfn/low/fa/stack 保持性             │
    │  preloop/process_edge/update_low Hoare 三元组 │
    │  tarjan_scc Hoare fixpoint 骨架               │
    v                                              v
Tarjan_scc_is_dfn.v                          Tarjan_scc_is_low.v
    │  dfn_inv 保持性                              │  low_valid 归纳版
    │  dfn_valid 实例证明                           │  is_low 全局性质
    │  dfn_tree_increasing                         │  low_valid_implies_is_low
    v                                              v
Tarjan_scc_stack.v ───────────────────────────────┘
    │  stack_split_at 规约
    │  stack_dfn_ordered, stack_tree_reachable
    │  low_eq_dfn_marks_scc_root
    v
SCC_correctness.v
    │  tarjan_scc_correctness
    │  tarjan_scc_all_correctness
    v
Tarjan_scc_tarjan.v (聚合)
```

`Tarjan_scc_basics.v` 是依赖图的**根节点**——所有后续证明文件都直接或间接依赖它。

---

## 2. Context 与依赖

### 2.1 Require Import

```coq
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
(* ↑ 提供 OriginalGraphType / OriginalGraph_gvalid / original_vvalid 等图基础设施；
   虽然文件名含 "tarjan"，但它是整个 GraphLib 的基础 Record 定义所在模块 *)
From Algorithms.Tarjan_directed Require Import Tarjan_scc.
(* ↑ 提供 SCCSt / tarjan_scc / tarjan_scc_f / preloop / process_edge 等程序定义 *)

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
```

### 2.2 Section Context

```coq
Section BASICS.

Context {V E: Type}
        `{EqDec V eq}
        (g: OriginalGraphType V E)
        `{OriginalGraph_gvalid g}.
```

**`[BRIDGE]`**：桥判定版本有 `root: V` 和 `g_vvalid_root: vvalid g root` 参数，
因为其正确性定理以 root 为起点。SCC 版本的 `tarjan_scc u` 对任意 `u` 执行，
且最终 `tarjan_scc_all` 遍历全图——因此 **Context 不需要固定 root**。

### 2.3 可用基础设施

| 来源 | 设施 | 用途 |
|------|------|------|
| `StateRelBasic.v` | `program Σ A`, `get`, `get'`, `update`, `update'`, `If`, `if_else`, `forset`, `Lfix`, `bind`, `ret`, `choice`, `skip`, `assume`, `assume!!` | Monadic 程序组合子 |
| `StateRelHoare.v` | `Hoare P c Q`, `Hoare_bind`, `Hoare_get`, `Hoare_update'`, `Hoare_choice`, `Hoare_forset`, `Hoare_fix` | Hoare 三元组推理规则 |
| `FixpointLib.v` | `mono_cont`, `Lfix_fixpoint'`, `mono_cont_intro`, `mono_cont_auto`, `mono_cont_choice`, `mono_cont_bind`, `mono_cont_const` | 最小不动点单调性/连续性 |
| `Tarjan_scc.v` | `SCCSt`, `initSt`, `visit`, `set_dfn`, `set_low`, `set_fa`, `incr_timer`, `push_stack`, `update_low`, `pop_scc`, `preloop`, `process_edge`, `tarjan_scc_f`, `tarjan_scc`, `tarjan_scc_all`, `unfold_op` | 程序定义 + State Record |

### 2.4 可用 Tactic

桥判定版本的 `Tarjan_tactics.v` 定义了以下可在本文件中**借鉴或复制**的 tactic：

| Tactic | 用途 |
|--------|------|
| `unfold_op` | 展开 `visit`, `set_dfn`, `set_low`, `set_fa`, `incr_timer`, `push_stack`, `update_low`, `pop_scc` 定义 |
| `hoare_auto_s` | 自动 Hoare 推理：bind 展开、`get`/`update`/`assume`/`choice` 的对应规则 |
| `intro_state` | `intro s;` 后提取 Hoare 前提 |
| `my_destruct H` | 等价于 `destruct H as [? [? ?]]` |
| `hoare_fix_nolv_auto` | 配合 `Lfix` 的 Hoare 不动点规则 + 自动归纳 |
| `hoare_bind` | 应用 `Hoare_bind` 规则 |
| `hoare_bind'` | 带状态简化的 bind |
| `hoare_cons_pre` | 弱化 Hoare 前置条件 |
| `hoare_cons_post` | 强化 Hoare 后置条件 |
| `equiv_dec_simpl` | 利用 `EqDec` 简化 `equiv_decb x v` 条件分支 |

**设计决策**：tactic 的获取方式按来源区分：

1. **直接可用**（来自 `StateRelHoare.v`，已通过 `Require Import` 引入）：
   - `hoare_fix_nolv_auto`（`StateRelHoare.v` 第 882 行）—— 对 `Lfix` 应用 `Hoare_fix`
   - `intro_state`（`StateRelHoare.v` 第 461 行）—— `intro s` + 提取 Hoare 前提
   - `hoare_bind`、`hoare_bind'`、`hoare_cons_pre`、`hoare_cons_post`
   - 这些**无需在本文件中重新定义**。

2. **需要在本文件内联定义**：
   - `unfold_op`：展开 SCC 版本的 8 个原语操作（与桥判定版本操作不同）
   - `hoare_auto_s`：自动 Hoare 推理（桥判定版本的 `Tarjan_tactics.v` 定义，
     但引用 `Tarjan.St` 类型，不兼容 SCCSt；需要适配后在本文件内联）
   - `hoare_bind''`：`Tactic Notation "hoare_bind''" uconstr(H) := eapply Hoare_bind; [ | intros; eapply H]; intros.`
     （桥判定版本从 `tracelib/CommonTactics.v` 获取；SCC 版本因不走 TraceLib 路径，
     需在本文件内联此简单定义）
   - `equiv_dec_simpl` / `my_destruct`：小型便利 tactic，直接在本文件定义

3. **不需要** `Require Import Tarjan_tactics`，原因：
   - 桥判定的 `Tarjan_tactics.v` 引用 `Tarjan.St`（含 `tedge`/`bridges` 字段），
     类型与 `SCCSt` 不兼容
   - `hoare_auto_s` 的类型匹配是战术层面的，无法通过类型类自动切换
   - 保持 `Tarjan_scc_basics.v` 自包含，避免跨子项目的硬依赖

---

## 3. 不变量定义

### 3.1 visited 单调增

```coq
(* 程序不删除已访问的顶点 *)
Definition visited_mono (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> v ∈ visited s2.
```

**`[BRIDGE]`**：桥判定版本以 Hoare rule 形式表达（前置含 `v ∈ visited` → 后置含 `v ∈ visited`）。
SCC 版本保留两种形式：Hoare rule 用于操作规约，`visited_mono` 用于不变式组合。

### 3.2 dfn 持久性

```coq
(* 已 visited 顶点的 dfn 值不会被修改 *)
Definition dfn_persist (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> dfn s1 v = dfn s2 v.
```

**关键推论**：`set_dfn v n` 只在 `~ v ∈ visited s1` 时有效（由 `preloop` 保证）。

### 3.3 low 持久性

```coq
(* 已 visited 顶点的 low 值只可能减小（不可能增大）。
   注意：与 dfn_persist 不同——update_low 会修改已 visited 顶点的 low 值。
   但 low 只可能减小，因此 low_persist 这里表述为"不会增大" *)
Definition low_nonincreasing (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> low s2 v <= low s1 v.
```

**`[BRIDGE]`**：桥判定版本的 low 持久性是严格的 `=`（low 只赋值一次）。
SCC 版本中 `update_low u n` 可能更新已 visited 顶点 `u` 的 low 值
（处理回边时，`u` 已经 visited 但其 low 值被更新）。
因此 low 持久性表述为**不增**而非严格不变。这会影响后续 `is_low` 归纳证明。

**等价替代**：若归纳证明中严格不变性更易使用，可以定义更强的不变量：

```coq
(* 已分配最终 low 值的顶点（即不在栈中的 visited 顶点）low 值持久 *)
Definition low_persist_final (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> ~ In v (stack s2) -> low s1 v = low s2 v.
```

**条件 `~ In v (stack s2)` 的合理性**：在 Tarjan 算法的操作语义下，
一个 visited 顶点只要仍在栈中，就存在被尚未处理的后代回边（back edge）
降低其 low 值的可能；一旦被 `pop_scc` 弹出栈，其 SCC 已闭合，
后续操作不再修改其 low 值。因此"不在栈中"等价于"low 值已最终确定"。
这是一个操作层面的不变量——严格的数学表述将在 `Tarjan_scc_stack.v` 中
通过 `low_eq_dfn_marks_scc_root` 给出。

实际实现中，两者都可能需要，视证明需求选择。

### 3.4 fa 持久性

```coq
(* 已 visited 顶点的 fa 值不会被修改 *)
Definition fa_persist (s1 s2: SCCSt): Prop :=
  forall v, v ∈ visited s1 -> fa s1 v = fa s2 v.
```

**关键推论**：`set_fa v u` 只在 `~ v ∈ visited s1` 时触发（树边情况，`process_edge` 中
`v` 未 visited 后才 `set_fa v u`）。

### 3.5 stack ⊆ visited

```coq
(* 栈中顶点均已 visited *)
Definition stack_in_visited (s: SCCSt): Prop :=
  forall v, In v (stack s) -> v ∈ visited s.
```

### 3.6 sccs 单调增

```coq
(* 已收集的 SCC 不丢失 *)
Definition sccs_mono (s1 s2: SCCSt): Prop :=
  forall scc, In scc (sccs s1) -> In scc (sccs s2).
```

### 3.7 timer 单调增

```coq
(* timer 只增不减 *)
Definition timer_mono (s1 s2: SCCSt): Prop :=
  timer s1 <= timer s2.
```

### 3.8 汇总不变量

```coq
(* 程序中所有原语操作保持的完整不变量 *)
Definition basics_invariant (s1 s2: SCCSt): Prop :=
  visited_mono s1 s2 /\
  dfn_persist s1 s2 /\
  low_nonincreasing s1 s2 /\
  fa_persist s1 s2 /\
  timer_mono s1 s2 /\
  stack_in_visited s2 /\
  sccs_mono s1 s2.
```

---

## 4. 原语操作的 Hoare 三元组

每个原语操作（`visit`, `set_dfn`, `set_low`, `set_fa`, `incr_timer`,
`push_stack`, `update_low`, `pop_scc`）需要证明两个方向的引理：

### 4.1 正向保持性（"执行操作后，不变量成立"）

以 `visit` 为例：

```coq
Lemma visit_keep_visited_mono: forall v s1,
  Hoare (fun s => s = s1)
        (visit v)
        (fun _ s2 => visited_mono s1 s2).
```

### 4.2 反向保持性（"若操作前某性质成立，则操作后仍成立"）

以 `visit` 和 visited 为例：

```coq
Lemma visit_keep_visited (v w: V):
  Hoare (fun s => w ∈ visited s)
        (visit v)
        (fun _ s => w ∈ visited s).
```

**`[BRIDGE]`**：桥判定版本采用反向保持性风格（`Tarjan_preloop_keep_visited` 等）。
SCC 版本两者都需要——正向版本用于组装完整不变量的保持性，
反向版本用于在 `Hoare_fix` 归纳中传递特定顶点的性质。

### 4.3 各操作需要证明的引理

| 操作 | 保持 visited | 保持 dfn | 保持 low | 保持 fa | 保持 stack_in_visited | 保持 sccs_mono |
|------|-------------|----------|----------|---------|----------------------|----------------|
| `visit v` | ✅ | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (不变) |
| `set_dfn v n` | ✅ (不变) | ✅ (新赋值) | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (不变) |
| `set_low v n` | ✅ (不变) | ✅ (不变) | ✅ (新赋值) | ✅ (不变) | ✅ (不变) | ✅ (不变) |
| `set_fa v p` | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (新赋值) | ✅ (不变) | ✅ (不变) |
| `incr_timer` | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (不变) |
| `push_stack v` | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (新增 v) | ✅ (不变) |
| `update_low u n` | ✅ (不变) | ✅ (不变) | ✅ (可能减小) | ✅ (不变) | ✅ (不变) | ✅ (不变) |
| `pop_scc u` | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (不变) | ✅ (移除 popped) | ✅ (新增 SCC) |

### 4.4 原语操作 Hoare 三元组模板

```coq
(* ---------- visit ---------- *)
Lemma visit_keep_visited (v w: V):
  Hoare (fun s => w ∈ visited s)
        (visit v)
        (fun _ s => w ∈ visited s).
Proof.
  unfold visit. intro_state. hoare_auto_s. sets_unfold. tauto.
Qed.

(* ---------- set_dfn ---------- *)
Lemma set_dfn_keep_visited (v w: V) (n: nat):
  Hoare (fun s => w ∈ visited s)
        (set_dfn v n)
        (fun _ s => w ∈ visited s).
Proof.
  unfold set_dfn. intro_state. hoare_auto_s. sets_unfold. tauto.
Qed.

Lemma set_dfn_new_dfn (v: V) (n: nat):
  Hoare (fun s => ~ v ∈ visited s)
        (set_dfn v n)
        (fun _ s => dfn s v = n).
Proof.
  unfold set_dfn. intro_state. hoare_auto_s.
  equiv_dec_simpl v v. auto.
Qed.

Lemma set_dfn_keep_other_dfn (v w: V) (n: nat) (dfnw: nat):
  Hoare (fun s => v <> w /\ dfn s w = dfnw)
        (set_dfn v n)
        (fun _ s => dfn s w = dfnw).
Proof.
  unfold set_dfn. intro_state. hoare_auto_s.
  my_destruct H. equiv_dec_simpl v w.
Qed.

(* ---------- set_low ---------- *)
Lemma set_low_keep_visited (v w: V) (n: nat):
  Hoare (fun s => w ∈ visited s)
        (set_low v n)
        (fun _ s => w ∈ visited s).
Proof.
  unfold set_low. intro_state. hoare_auto_s. sets_unfold. tauto.
Qed.

Lemma set_low_new_low (v: V) (n: nat):
  Hoare (fun s => True)
        (set_low v n)
        (fun _ s => low s v = n).
Proof.
  unfold set_low. intro_state. hoare_auto_s.
  equiv_dec_simpl v v. auto.
Qed.

Lemma set_low_keep_other_low (v w: V) (n: nat) (loww: nat):
  Hoare (fun s => v <> w /\ low s w = loww)
        (set_low v n)
        (fun _ s => low s w = loww).
Proof.
  unfold set_low. intro_state. hoare_auto_s.
  my_destruct H. equiv_dec_simpl v w.
Qed.

(* ---------- set_fa ---------- *)
Lemma set_fa_keep_visited (v w: V) (p: V):
  Hoare (fun s => w ∈ visited s)
        (set_fa v p)
        (fun _ s => w ∈ visited s).
Proof.
  unfold set_fa. intro_state. hoare_auto_s. sets_unfold. tauto.
Qed.

Lemma set_fa_new_fa (v: V) (p: V):
  Hoare (fun s => True)
        (set_fa v p)
        (fun _ s => fa s v = p).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  equiv_dec_simpl v v. auto.
Qed.

Lemma set_fa_keep_other_fa (v w: V) (p: V) (faw: V):
  Hoare (fun s => v <> w /\ fa s w = faw)
        (set_fa v p)
        (fun _ s => fa s w = faw).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  my_destruct H. equiv_dec_simpl v w.
Qed.

(* ---------- incr_timer ---------- *)
Lemma incr_timer_keep_visited (w: V):
  Hoare (fun s => w ∈ visited s)
        incr_timer
        (fun _ s => w ∈ visited s).
Proof.
  unfold incr_timer. intro_state. hoare_auto_s. sets_unfold. tauto.
Qed.

(* ---------- push_stack ---------- *)
Lemma push_stack_keep_visited (v w: V):
  Hoare (fun s => w ∈ visited s)
        (push_stack v)
        (fun _ s => w ∈ visited s).
Proof.
  unfold push_stack. intro_state. hoare_auto_s. sets_unfold. tauto.
Qed.

Lemma push_stack_in_stack (v: V):
  Hoare (fun s => True)
        (push_stack v)
        (fun _ s => In v (stack s)).
Proof.
  unfold push_stack. intro_state. hoare_auto_s.
  simpl. left; reflexivity.
Qed.

(* ---------- update_low ---------- *)
Lemma update_low_keep_visited (u w: V) (n: nat):
  Hoare (fun s => w ∈ visited s)
        (update_low u n)
        (fun _ s => w ∈ visited s).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  - sets_unfold. tauto.
  - sets_unfold. tauto.
Qed.

Lemma update_low_nonincreasing (u: V) (n: nat) (old_low: nat):
  Hoare (fun s => low s u = old_low)
        (update_low u n)
        (fun _ s => low s u <= old_low).
Proof.
  unfold update_low.
  hoare_bind (Hoare_get' (fun s => low s u)). simpl.
  intro_state. hoare_auto_s.
  - (* n < old_low 分支：执行 set_low u n，low s u = n <= old_low *)
    sets_unfold; lia.
  - (* ~ n < old_low 分支：skip，low s u = old_low *)
    sets_unfold; lia.
Qed.
(* 注：在实际使用中，通常先 get' 获取当前 low 值，再传入此引理 *)
```

(* ---------- pop_scc ---------- *)
(* pop_scc 是单步 update' (fun s => pop_scc_state s u)，无 bind 链 *)
Lemma pop_scc_keep_visited (u w: V):
  Hoare (fun s => w ∈ visited s)
        (pop_scc u)
        (fun _ s => w ∈ visited s).
Proof.
  unfold pop_scc.
  apply Hoare_update'. intro s. simpl. reflexivity.
Qed.

Lemma pop_scc_keep_dfn (u w: V) (dfnw: nat):
  Hoare (fun s => dfn s w = dfnw)
        (pop_scc u)
        (fun _ s => dfn s w = dfnw).
Proof.
  unfold pop_scc.
  apply Hoare_update'. intro s. simpl. reflexivity.
Qed.

(* 更多 pop_scc 保持性引理类推（low/fa/timer/stack_in_visited 同理） *)

### 4.5 `set_dfn` 将 dfn 从 0 改为正数

```coq
Lemma set_dfn_zero_to_n (v: V) (n: nat):
  Hoare (fun s => dfn s v = 0)
        (set_dfn v n)
        (fun _ s => dfn s v = n).
Proof.
  unfold set_dfn. intro_state. hoare_auto_s.
  equiv_dec_simpl v v. auto.
Qed.
```

**重要性**：dfn 初始值为 0（`initSt`），`dfn s v = 0` ↔ `~ v ∈ visited s`。
此引理是 `dfn_inv` 证明的基础。

---

## 5. 复合操作的 Hoare 三元组

### 5.1 `preloop u`

```coq
Lemma preloop_keep_visited (u w: V):
  Hoare (fun s => w ∈ visited s)
        (preloop u)
        (fun _ s => w ∈ visited s).
Proof.
  unfold preloop.
  hoare_bind incr_timer_keep_visited. simpl. clear a.
  hoare_bind (push_stack_keep_visited u w). simpl. clear a.
  hoare_bind (visit_keep_visited u w).
  (* 注意: preloop 内部顺序与 Tarjan_scc.v 定义一致:
     get timer → set_dfn → set_low → incr_timer → push_stack → visit *)
  ...
Qed.

Lemma preloop_self_visited (u: V):
  Hoare (fun s => True)
        (preloop u)
        (fun _ s => u ∈ visited s).
Proof. ... Qed.

Lemma preloop_in_stack (u: V):
  Hoare (fun s => True)
        (preloop u)
        (fun _ s => In u (stack s)).
Proof. ... Qed.

Lemma preloop_dfn_set (u: V) (t: nat):
  Hoare (fun s => timer s = t)
        (preloop u)
        (fun _ s => dfn s u = t).
Proof. ... Qed.

Lemma preloop_low_set (u: V) (t: nat):
  Hoare (fun s => timer s = t)
        (preloop u)
        (fun _ s => low s u = t).
Proof. ... Qed.

Lemma preloop_keep_dfn (u v: V) (dfnv: nat):
  Hoare (fun s => u <> v /\ v ∈ visited s /\ dfn s v = dfnv)
        (preloop u)
        (fun _ s => v ∈ visited s /\ dfn s v = dfnv).
Proof. ... Qed.

Lemma preloop_keep_low (u v: V) (lowv: nat):
  Hoare (fun s => u <> v /\ v ∈ visited s /\ low s v = lowv)
        (preloop u)
        (fun _ s => v ∈ visited s /\ low s v = lowv).
Proof. ... Qed.
```

### 5.2 `process_edge u W v`

```coq
Lemma process_edge_keep_visited (u v w: V) (W: V -> program SCCSt unit):
  (forall x, Hoare (fun s => w ∈ visited s) (W x) (fun _ s => w ∈ visited s)) ->
  Hoare (fun s => w ∈ visited s)
        (process_edge u W v)
        (fun _ s => w ∈ visited s).
Proof.
  intros H_W_keep_visited.
  unfold process_edge, if_else. unfold_op.
  hoare_auto_s.
  - (* 树边分支: set_fa → W v → get low v → update_low *)
    hoare_bind (set_fa_keep_visited v u w). simpl. clear a.
    apply H_W_keep_visited. simpl. clear a.
    (* get' (fun s => low s v) 不改变 state *)
    hoare_bind (update_low_keep_visited u w (low_after_W v)). ...
  - (* 非树边分支: If in_stack → get dfn v → update_low *)
    hoare_auto_s.
    hoare_bind (update_low_keep_visited u w dfn_v). ...
Qed.

Lemma process_edge_keep_dfn (u v w: V) (W: V -> program SCCSt unit) (dfnw: nat):
  (forall x, Hoare (fun s => u <> w /\ w ∈ visited s /\ dfn s w = dfnw)
                  (W x)
                  (fun _ s => w ∈ visited s /\ dfn s w = dfnw)) ->
  Hoare (fun s => u <> w /\ w ∈ visited s /\ dfn s w = dfnw)
        (process_edge u W v)
        (fun _ s => w ∈ visited s /\ dfn s w = dfnw).
Proof. ... Qed.

Lemma process_edge_keep_low (u v w: V) (W: V -> program SCCSt unit) (loww: nat):
  (forall x, Hoare (fun s => u <> w /\ w ∈ visited s /\ low s w = loww)
                  (W x)
                  (fun _ s => w ∈ visited s /\ low s w = loww)) ->
  Hoare (fun s => u <> w /\ w ∈ visited s /\ low s w = loww)
        (process_edge u W v)
        (fun _ s => w ∈ visited s /\ low s w = loww).
Proof. ... Qed.
```

**`[BRIDGE]` 关键差异**：桥判定版本的 `process_edge` 包含了 `set_tree u v e`（同时设置
`visited`, `fa`, `tedge`），而 SCC 版本仅设置 `fa`（树边）或不设置（非树边）。
SCC 版本无 `tedge` 字段，也无 `post_rec` 步骤（桥判定中`post_rec` 用于更新 low）。

### 5.3 `pop_scc u`

`pop_scc` 定义为 `update' (fun s => pop_scc_state s u)`，是单步 `update'`。
其 Hoare 推理使用 `Hoare_update'`，核心规约由纯函数引理 `pop_scc_state_spec` 提供。

```coq
(* 纯函数引理：描述 pop_scc_state 对 stack 和 sccs 的修改 *)
Lemma pop_scc_state_spec (s: SCCSt) (u: V):
  In u (stack s) ->
  exists popped rest,
    stack_split_at (stack s) u = (popped, rest) /\
    stack (pop_scc_state s u) = rest /\
    sccs (pop_scc_state s u) = (fun v => In v popped) :: sccs s /\
    visited (pop_scc_state s u) = visited s /\
    dfn (pop_scc_state s u) = dfn s /\
    low (pop_scc_state s u) = low s /\
    fa (pop_scc_state s u) = fa s /\
    timer (pop_scc_state s u) = timer s.
Proof.
  unfold pop_scc_state.
  destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
  intros Hinu. exists popped, rest.
  split; [exact Hsplit |].
  (* 其余字段由 Record 构造直接得出 *)
  simpl; repeat split.
Qed.

(* Hoare 保持性引理 *)
Lemma pop_scc_keep_visited (u w: V):
  Hoare (fun s => w ∈ visited s)
        (pop_scc u)
        (fun _ s => w ∈ visited s).
Proof.
  unfold pop_scc.
  (* 使用 Hoare_update'：需证 visited (pop_scc_state s u) = visited s *)
  apply Hoare_update'.
  intro s. simpl. reflexivity.
Qed.

(* 新 SCC 生成规约 *)
Lemma pop_scc_new_scc (u: V):
  Hoare (fun s => In u (stack s))
        (pop_scc u)
        (fun _ s =>
          exists popped rest,
            stack_split_at (stack s ++ popped) u = (popped, rest) /\
            sccs s = (fun v => In v popped) :: sccs s).
Proof.
  unfold pop_scc.
  apply Hoare_update'.
  intros s Hinu.
  apply pop_scc_state_spec; auto.
Qed.
```

**注意**：`pop_scc` 是单步 `update'`，无需 `hoare_auto_s` 分解 bind 链。
其证明模式与其他原语操作（`get`/`update`/`if_else` 组合）不同。

---

## 6. 核心 Hoare Fixpoint 证明

### 6.1 `forset` 边遍历的 Hoare 保持性

`tarjan_scc_f` 使用 `forset (fun v => dg_step g u v) (process_edge u W)`
遍历 `u` 的所有出边。需要证明 `forset` 保持了不变量。

`forset` 定义为 `Lfix (forset_f body) universe`（`StateRelBasic.v` 第 220 行），
因此可以直接使用 `hoare_fix_nolv_auto (V -> Prop)` 对其应用 `Hoare_fix` 归纳，
与桥判定版本的模式一致（见 §9.2）。

**参考**：`Hoare_forset`（`StateRelHoare.v` 第 1240 行）为 `forset` 提供了封装好的 Hoare 规则：

```coq
Theorem Hoare_forset {Σ A}
  (P: (A -> Prop) -> Σ -> Prop)
  (universe: A -> Prop)
  (body: A -> program Σ unit)
  (ProperP: Proper (Sets.equiv ==> eq ==> iff) P):
  (forall done a,
    done ⊆ universe ->
    a ∈ universe ->
    ~a ∈ done ->
    Hoare (fun s => P done s) (body a) (fun _ s => P (done ∪ [a]) s)) ->
  Hoare (fun s => P ∅ s) (forset universe body) (fun _ s => P universe s).
```

其前提采用逐元素归纳：`body a` 将 `P done` 变为 `P (done ∪ [a])`；额外要求
`ProperP`（`P` 关于集合等价的 Proper 性）。考虑到 `ProperP` 的证明开销以及
与桥判定版本保持一致性，**本文件采用手动 `hoare_fix_nolv_auto` 方法**
（见 §6.2 和 §9.2），直接展开 `forset` 为 `Lfix (forset_f body)` 并应用两层不动点归纳。
若后续文件需要更简洁的 `forset` 推理，可在需要时引入 `Hoare_forset`。

**两层 Lfix 结构**：
```
tarjan_scc u
= Lfix tarjan_scc_f u               ← 外層 Lfix（顶点递归，参数类型 V）
= tarjan_scc_f (Lfix tarjan_scc_f) u
= preloop u ;; forset ... ;; pop_scc
  where forset = Lfix (forset_f ...) ← 内層 Lfix（边迭代，参数类型 V -> Prop）
```
外層归纳参数类型为 `V`，内層为 `V -> Prop`（当前待处理出边集合）。

### 6.2 `tarjan_scc` 的 Hoare 不动点证明

这是本文件的**核心证明**。模式参考桥判定 `Tarjan_keep_visited_inv`（第 72-99 行）。

```coq
Theorem tarjan_scc_keep_visited (u v: V):
  Hoare (fun s => v ∈ visited s)
        (tarjan_scc u)
        (fun _ s => v ∈ visited s).
Proof.
  unfold tarjan_scc.
  hoare_fix_nolv_auto V.
  intros W IH u.
  unfold tarjan_scc_f.
  (* preloop *)
  hoare_bind preloop_keep_visited. simpl. clear a.
  (* forset *)
  unfold forset.
  hoare_fix_nolv_auto (V -> Prop).
  intros W0 IH0 todo.
  unfold forset_f.
  hoare_auto_s.
  intro_state.
  hoare_auto_s.
  - (* choice 非空分支: 选一个 a ∈ todo, process_edge u W a, 递归 W0 *)
    hoare_bind'' IH0.
    eapply Hoare_bind.
    { hoare_cons_pre (process_edge_keep_visited u a v W).
      - intros x. apply IH. }
    simpl. intros _.
    hoare_cons_pre IH0. ...
  - (* choice 空分支: assume!! (todo == ∅);; skip *)
    hoare_auto_s.
  - (* pop_scc (若 low u = dfn u) *)
    hoare_bind pop_scc_keep_visited.
Qed.
```

**`[BRIDGE]` 核心差异**：

| 维度 | 桥判定 | SCC |
|------|--------|-----|
| 递归结构 | `fixpoint`（使用 `hoare_fix_nolv_auto`） | `Lfix`（使用 `hoare_fix_nolv_auto`） |
| 不动点参数类型 | `V`（顶点遍历） + `E -> Prop`（边遍历） | `V`（单次 DFS） + `V -> Prop`（出边遍历） |
| 边遍历 | `forset (dg_step g u v) body` | 同左（`forset` 内部展开为 `Lfix (forset_f body)`） |
| 归纳假设 | `IH: forall x, Hoare P (W x) Q` | `IH: forall x, Hoare P (W x) Q`（同） |
| `post_rec` | 有（递归后更新 low） | 无 — low 更新直接在 `process_edge` 的 `update_low` 中完成 |

**两层 Lfix**：`tarjan_scc` 的证明需要两层 `hoare_fix_nolv_auto`：
1. 外层：`Lfix tarjan_scc_f` → `tarjan_scc u` 的递归
2. 内层：`Lfix (forset_f ...)` → `forset` 的迭代

### 6.3 完整保持性定理列表

```coq
Theorem tarjan_scc_keep_visited (u v: V):
  Hoare (fun s => v ∈ visited s) (tarjan_scc u) (fun _ s => v ∈ visited s).

Theorem tarjan_scc_keep_dfn (u v: V) (dfnv: nat):
  Hoare (fun s => u <> v /\ v ∈ visited s /\ dfn s v = dfnv)
        (tarjan_scc u)
        (fun _ s => v ∈ visited s /\ dfn s v = dfnv).

Theorem tarjan_scc_keep_low (u v: V) (lowv: nat):
  Hoare (fun s => u <> v /\ v ∈ visited s /\ low s v = lowv)
        (tarjan_scc u)
        (fun _ s => v ∈ visited s /\ low s v = lowv).

Theorem tarjan_scc_keep_fa (u v: V) (fav: V):
  Hoare (fun s => u <> v /\ v ∈ visited s /\ fa s v = fav)
        (tarjan_scc u)
        (fun _ s => v ∈ visited s /\ fa s v = fav).

Theorem tarjan_scc_keep_dfn_low_order (u x y: V):
  Hoare (fun s => u <> x /\ u <> y /\ x ∈ visited s /\ y ∈ visited s /\ dfn s x < low s y)
        (tarjan_scc u)
        (fun _ s => dfn s x < low s y).

Theorem tarjan_scc_keep_dfn_low_order' (u x y: V):
  Hoare (fun s => u <> x /\ u <> y /\ x ∈ visited s /\ y ∈ visited s /\ ~ dfn s x < low s y)
        (tarjan_scc u)
        (fun _ s => ~ dfn s x < low s y).

(* 方便后续使用的 prod 版本 *)
Theorem tarjan_scc_keep_dfn_prod (u: V) (p: V * nat):
  Hoare (fun s => u <> fst p /\ fst p ∈ visited s /\ dfn s (fst p) = snd p)
        (tarjan_scc u)
        (fun _ s => fst p ∈ visited s /\ dfn s (fst p) = snd p).

Theorem tarjan_scc_keep_low_prod (u: V) (p: V * nat):
  Hoare (fun s => u <> fst p /\ fst p ∈ visited s /\ low s (fst p) = snd p)
        (tarjan_scc u)
        (fun _ s => fst p ∈ visited s /\ low s (fst p) = snd p).
```

**`[BRIDGE]`**：桥判定额外有 `Tarjan_keep_eset_in_visited_inv`（边集合已处理不变量），
用于组合 `forset` 边遍历的假设。SCC 版本因 `process_edge` 结构不同
（无 `post_rec`/`set_tree` 步骤），可能需要简化版的 `eset_in_visited` 或直接使用
`forall v, dg_step g u v -> v ∈ visited s` 作为 `forset` 的后置条件。

---

## 7. `tarjan_scc_all` 外层循环

### 7.1 外层循环的 Hoare 保持性

```coq
Theorem tarjan_scc_all_keep_visited (v: V):
  Hoare (fun s => v ∈ visited s)
        tarjan_scc_all
        (fun _ s => v ∈ visited s).
Proof.
  unfold tarjan_scc_all.
  (* forset (original_vvalid g) body *)
  apply Hoare_forset with
    (P := fun todo s => v ∈ visited s).
  ...
Qed.
```

**注意**：`tarjan_scc_all` 的 `forset` 遍历全集 `original_vvalid g`，
body 是 `fun u => If (fun s => ~ u ∈ visited s) (tarjan_scc u)`。
这与单次 `tarjan_scc` 的 `forset` 遍历 `dg_step g u` 的模式一致，
因此证明结构可复用。

---

## 8. 完整引理清单

### 8.1 基本定义 (7)

| 名称 | 类型 | 摘要 |
|------|------|------|
| `visited_mono` | `SCCSt -> SCCSt -> Prop` | visited 只增不删 |
| `dfn_persist` | `SCCSt -> SCCSt -> Prop` | 已 visited 顶点的 dfn 不变 |
| `low_nonincreasing` | `SCCSt -> SCCSt -> Prop` | 已 visited 顶点的 low 不增 |
| `fa_persist` | `SCCSt -> SCCSt -> Prop` | 已 visited 顶点的 fa 不变 |
| `stack_in_visited` | `SCCSt -> Prop` | 栈中顶点均已 visited |
| `sccs_mono` | `SCCSt -> SCCSt -> Prop` | 已收集 SCC 不丢失 |
| `timer_mono` | `SCCSt -> SCCSt -> Prop` | timer 只增不减 |

### 8.2 原语操作引理 (~32)

| 操作 | 引理数 | 典型引理 |
|------|--------|---------|
| `visit` | 1 | `visit_keep_visited` |
| `set_dfn` | 3 | `set_dfn_keep_visited`, `set_dfn_new_dfn`, `set_dfn_keep_other_dfn` |
| `set_low` | 3 | `set_low_keep_visited`, `set_low_new_low`, `set_low_keep_other_low` |
| `set_fa` | 3 | `set_fa_keep_visited`, `set_fa_new_fa`, `set_fa_keep_other_fa` |
| `incr_timer` | 1 | `incr_timer_keep_visited` |
| `push_stack` | 2 | `push_stack_keep_visited`, `push_stack_in_stack` |
| `update_low` | 4 | `update_low_keep_visited`, `update_low_keep_dfn`, `update_low_nonincreasing`, `update_low_keep_other_low` |
| `pop_scc` | 2 | `pop_scc_keep_visited`, `pop_scc_new_scc` |

### 8.3 复合操作引理 (~12)

| 操作 | 引理 |
|------|------|
| `preloop` | `preloop_keep_visited`, `preloop_keep_dfn`, `preloop_keep_low`, `preloop_self_visited`, `preloop_in_stack`, `preloop_dfn_set`, `preloop_low_set` |
| `process_edge` | `process_edge_keep_visited`, `process_edge_keep_dfn`, `process_edge_keep_low` |
| `pop_scc_state` | `pop_scc_state_stack_in_visited`（纯函数引理，非 Hoare） |

### 8.4 核心 Hoare Fixpoint 定理 (~8)

| 名称 | 摘要 |
|------|------|
| `tarjan_scc_keep_visited` | 递归 DFS 保持 visited 包含性 |
| `tarjan_scc_keep_dfn` | 递归 DFS 保持其他顶点的 dfn 值 |
| `tarjan_scc_keep_low` | 递归 DFS 保持其他顶点的 low 值 |
| `tarjan_scc_keep_fa` | 递归 DFS 保持其他顶点的 fa 值 |
| `tarjan_scc_keep_dfn_low_order` | 递归 DFS 保持 dfn < low 序关系 |
| `tarjan_scc_keep_dfn_low_order'` | 递归 DFS 保持 ~ dfn < low 序关系 |
| `tarjan_scc_keep_dfn_prod` | prod 包装版 |
| `tarjan_scc_keep_low_prod` | prod 包装版 |

### 8.5 外层循环定理 (~2)

| 名称 | 摘要 |
|------|------|
| `tarjan_scc_all_keep_visited` | 全图遍历保持 visited 包含性 |
| `tarjan_scc_all_visited_all` | 终止时所有有效顶点均已 visited |

### 8.6 Tactic 定义（本文件内联，~3）

| 名称 | 摘要 |
|------|------|
| `unfold_op` | 展开所有原语操作定义（SCC 版本操作集） |
| `hoare_auto_s` | 自动 Hoare 推理（改编自桥判定版本，适配 SCCSt） |
| `hoare_bind''` | `eapply Hoare_bind; [ \| intros; eapply H]; intros.`（便利包装） |

**注**：`hoare_fix_nolv_auto` / `intro_state` / `hoare_bind` 等来自 `StateRelHoare.v`，
通过 `Require Import` 直接可用，不在此列。

**预估总引理数**：~65（含原语 ~25 + 复合 ~14 + 核心 fixpoint ~8 + 外层 ~2 + 辅助/中间 ~16）
**预估总行数**：880–1440 行（中位 ~1100 行，详见 §14）

---

## 9. 证明策略

### 9.1 原语操作证明

所有原语操作的证明采用统一策略：

```coq
Lemma xxx_keep_yyy ... :
  Hoare ...
Proof.
  unfold <operation>.        (* 展开操作定义 *)
  intro_state.               (* intro s + 提取 Hoare 前提 *)
  hoare_auto_s.              (* 自动分解 bind/update/get/assume *)
  (* 剩余目标: 纯逻辑命题 *)
  sets_unfold; tauto.        (* 或: my_destruct H; equiv_dec_simpl x y; auto *)
Qed.
```

### 9.2 不动点（Lfix）证明

```coq
Theorem tarjan_scc_keep_xxx ... :
  Hoare ... (tarjan_scc u) ...
Proof.
  unfold tarjan_scc.         (* 展开为 Lfix tarjan_scc_f u *)
  hoare_fix_nolv_auto V.     (* 外層不动点归纳 *)
  intros W IH u.
  unfold tarjan_scc_f.
  hoare_bind <preloop_lemma>. (* preloop 阶段 *)
  simpl. clear a.
  unfold forset.             (* 展开为 Lfix (forset_f ...) *)
  hoare_fix_nolv_auto (V -> Prop).  (* 内層不动点归纳 *)
  intros W0 IH0 todo.
  unfold forset_f.
  hoare_auto_s.              (* 处理 choice 结构 *)
  intro_state.
  hoare_auto_s.
  - (* 非空分支: 选 a ∈ todo, process_edge, 递归 *)
    hoare_bind'' IH0.        (* 使用内层归纳假设 *)
    eapply Hoare_bind.       (* process_edge 保持性 *)
    { hoare_cons_pre (process_edge_keep_xxx ... IH). }
    ...
  - (* 空分支: skip *)
    hoare_auto_s.
  - (* pop_scc: If low u = dfn u *)
    hoare_auto_s.
    + hoare_bind pop_scc_keep_xxx.
    + ...
Qed.
```

### 9.3 `hoare_fix_nolv_auto` 的工作方式

`hoare_fix_nolv_auto` 定义于 `StateRelHoare.v` 第 882 行（非 `Tarjan_tactics.v`）：

```coq
Ltac hoare_fix_nolv_auto A :=
   match goal with
  | |- @Hoare ?Σ ?R ?P1 (Lfix ?F ?a) ?P2 =>
    let P := fresh "P" in evar (P: A -> Σ -> Prop);
    let Q := fresh "Q" in evar (Q: A -> R -> Σ -> Prop);
    let h := fresh "h" in assert (P = P) as h;[
      let P' := eval pattern (a) in P1 in
      match P' with
      | ?P'' _ => exact (Logic.eq_refl P'') end |];
    clear h;
    let h := fresh "h" in assert (Q = Q) as h;[
      let Q' := eval pattern (a) in P2 in
      match Q' with
      | ?Q'' _ => exact (Logic.eq_refl Q'') end |];
    clear h;
    eapply Hoare_fix with (P:= P) (Q := Q);
    subst P Q
  end.
```

该 tactic 从目标的 `Lfix F a` 中提取参数 `a`，利用 `eval pattern` 自动构造
参数化的 `P` 和 `Q`，然后应用 `Hoare_fix`。

**关键依赖**：`Hoare_fix`（`StateRelHoare.v` 第 581 行）的签名如下：

```coq
Theorem Hoare_fix {Σ A B: Type}:
forall (P: A -> Σ -> Prop) (Q: A -> B -> Σ -> Prop)
       (F: (A -> program Σ B)-> (A -> program Σ B)) (a: A),
  (forall W, (forall a, Hoare (P a) (W a) (Q a)) ->
             (forall a, Hoare (P a) (F W a) (Q a))) ->
  Hoare (P a) (Lfix F a) (Q a).
```

**注意**：`Hoare_fix` 没有 `mono_cont` 前提——其证明直接对 `Lfix` 定义中的 `Nat.iter n F ∅`
做自然数归纳。`Tarjan_scc.v` 中已证明的 `tarjan_scc_f_mono_cont` 与
`forset_f_mono_cont_body` 不是 `Hoare_fix` 所必需的，但它们在需要展开
`Lfix`（如 `tarjan_scc_unfold`）时仍然有用：`Lfix_fixpoint'` 需要 `mono_cont` 前提。

---

## 10. 与桥判定版本的关键差异总结

| 维度 | 桥判定 (`Tarjan_basics.v`) | SCC (`Tarjan_scc_basics.v`) |
|------|---------------------------|----------------------------|
| **State Record** | `St`（7 字段：`visited`, `timer`, `fa`, `tedge`, `dfn`, `low`, `bridges`） | `SCCSt`（7 字段：`visited`, `timer`, `fa`, `dfn`, `low`, `stack`, `sccs`） |
| **图关系** | `step`（无向，对称） | `dg_step`（有向） |
| **程序结构** | `Lfix` + `forset` + `for_branch1`/`for_branch2` | `Lfix` + `forset` + `process_edge` |
| **边处理** | `for_branch1`（树边/回边/交叉边） + `for_branch2` | `process_edge`（统一处理，内部 `if_else` 分树边/回边） |
| **子程序** | `set_tree`, `post_rec`, `update_low` | `set_fa`, `update_low`（无 `set_tree` 和 `post_rec`） |
| **root 参数** | Context 中有固定的 `root` | 无固定 root（`tarjan_scc u` 任意 `u`） |
| **TraceLib** | 有（ghost code） | 无 |
| **low 持久性** | 严格 `=`（已 visited 顶点的 low 不变） | 不增 `<=`（已 visited 顶点的 low 可被 `update_low` 减小） |
| **`no_cross_edge`** | 需要 | 有向图中天然区分方向，不需要 |
| **栈语义** | 无栈 | 有栈 `stack`（Tarjan SCC 核心） |

---

## 11. 后续文件接口

`Tarjan_scc_basics.v` 为以下文件提供基础引理：

### 11.1 Tarjan_scc_is_dfn.v

需要引用的引理：
- `set_dfn_new_dfn`, `set_dfn_keep_other_dfn` → `dfn_inv` 保持性
- `preloop_dfn_set` → `preloop` 后 dfn 有效
- `tarjan_scc_keep_dfn`, `tarjan_scc_keep_dfn_prod` → `tarjan_scc` 后 dfn 保持

### 11.2 Tarjan_scc_is_low.v

需要引用的引理：
- `set_low_new_low`, `set_low_keep_other_low` → `low_valid` 归纳
- `update_low_nonincreasing` → `update_low` 保持 `low_valid`
- `tarjan_scc_keep_low`, `tarjan_scc_keep_low_prod` → `tarjan_scc` 后 low 保持
- `tarjan_scc_keep_dfn_low_order` → dfn/low 序关系保持

### 11.3 Tarjan_scc_stack.v

需要引用的引理：
- `push_stack_in_stack` → 栈入栈引理
- `stack_in_visited` → 栈元素是 visited
- `pop_scc_new_scc` → 弹出操作规约

### 11.4 SCC_correctness.v

需要引用的引理：
- 所有 `tarjan_scc_keep_xxx` 定理 → 组装完整不变量
- `basics_invariant` → 完整不变量的保持性

---

## 12. 文件结构

```coq
Require Import ... (依赖列表见 §2.1)

(* ================================================================ *)
(* Tactic Definitions                                                *)
(* ================================================================ *)
Ltac unfold_op := ...
Ltac hoare_auto_s := ...
(* hoare_fix_nolv_auto / intro_state 来自 StateRelHoare.v，无需在此定义 *)

Section BASICS.
  Context {V E: Type} `{EqDec V eq} (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}.

(* ================================================================ *)
(* Invariant Definitions                                             *)
(* ================================================================ *)
Definition visited_mono ...
Definition dfn_persist ...
Definition low_nonincreasing ...
Definition fa_persist ...
Definition stack_in_visited ...
Definition sccs_mono ...
Definition timer_mono ...
Definition basics_invariant ...

(* ================================================================ *)
(* Primitive Operation Lemmas                                        *)
(* ================================================================ *)
(* visit, set_dfn, set_low, set_fa, incr_timer, push_stack,
   update_low, pop_scc — 每个操作约 2-4 个引理 *)

(* ================================================================ *)
(* Composite Operation Lemmas                                        *)
(* ================================================================ *)
(* preloop, process_edge, pop_scc_state *)

(* ================================================================ *)
(* forset Body Lemmas (edge iteration)                               *)
(* ================================================================ *)
(* forset_f 保持性，用于 Lfix (forset_f ...) 的 Hoare_fix *)

(* ================================================================ *)
(* Core Hoare Fixpoint Theorems                                      *)
(* ================================================================ *)
(* tarjan_scc_keep_visited, tarjan_scc_keep_dfn, tarjan_scc_keep_low,
   tarjan_scc_keep_fa, tarjan_scc_keep_dfn_low_order, ... *)

(* ================================================================ *)
(* Outer Loop Theorems                                               *)
(* ================================================================ *)
(* tarjan_scc_all_keep_visited, tarjan_scc_all_visited_all *)

End BASICS.
```

---

## 13. 开发注意事项

1. **`mono_cont` 的前提角色**：`Tarjan_scc.v` 中已证明 `tarjan_scc_f_mono_cont`
   和 `forset_f_mono_cont_body`。`Hoare_fix` 本身不需要 `mono_cont` 前提（其证明
   直接对 `Nat.iter n F ∅` 做自然数归纳），但 `mono_cont` 在需要展开 `Lfix`
   时仍然必要（`Lfix_fixpoint'` 需要 `mono_cont`，用于 `tarjan_scc_unfold` 等）。

2. **`hoare_fix_nolv_auto` 直接可用**：`hoare_fix_nolv_auto` 定义于
   `StateRelHoare.v` 第 882 行，直接匹配 `Lfix` 目标——桥判定版本和 SCC 版本
   都使用 `Lfix`，不需要适配。`hoare_fix_nolv_auto` 通过 `eval pattern` 自动
   从目标提取参数 `a` 并构造参数化的 `P` / `Q`，然后应用 `Hoare_fix`。
   本文件无需重新定义此 tactic。

3. **`equiv_dec_simpl`**：由于 Context 使用 `EqDec V eq`（typeclass），
   需要确认 `equiv_decb` 的可判定性在证明中可被 `destruct (equiv_decb x v)` 展开。

4. **`sets_unfold`**：集合操作（`∪`, `[v]`, `∈`）在 Hoare 证明中频繁出现。
   需要 `SetsClass.SetsClass` 的 `sets_unfold` tactic 展开集合记法。

5. **`low_nonincreasing` vs `low_persist`**：如 §3.3 所述，
   由于 `update_low` 可能在 `process_edge` 中修改已 visited 顶点的 low 值，
   `low_nonincreasing`（不增）是正确的持久性表述；严格 `=` 版本仅对不在栈中的已 visited 顶点成立。

6. **栈不变量与后续文件的接口**：本文件只建立基本的栈不变量（`stack_in_visited`）。
   更精细的栈不变量（`stack_dfn_ordered`, `stack_is_unassigned`,
   `stack_tree_reachable`）留给 `Tarjan_scc_stack.v`——它们需要 `dfn_inv` 和
   `is_low` 作为前提。

7. **`forset` 与 `Lfix` 的两层结构**：
   ```
   tarjan_scc u
   = Lfix tarjan_scc_f u               ← 外層 Lfix（顶点递归）
   = tarjan_scc_f (Lfix tarjan_scc_f) u
   = preloop u ;; forset ... ;; pop_scc
     where forset = Lfix (forset_f ...) ← 内層 Lfix（边迭代）
   ```
   证明时外層 `hoare_fix_nolv_auto V`，内層 `hoare_fix_nolv_auto (V -> Prop)`。

---

## 14. 行数估算

**参考**：桥判定版本 `Tarjan_basics.v` 为 1577 行（含 tree/offspring/bridge/edge
等复杂不变量）。SCC 版本去除了 tree/bridge 不变量，但增加了栈相关不变量，
且两层 Lfix 证明结构与桥判定版本一致。综合评估：

| 部分 | 预估行数 |
|------|---------|
| Require Import + Tactic 定义 | 50–80 |
| 不变量定义（7 个 + basics_invariant） | 50–80 |
| 原语操作引理（~25 条，含 pop_scc） | 150–250 |
| 复合操作引理（~14 条） | 150–250 |
| forset 边遍历引理（两层 Lfix 准备） | 80–120 |
| 核心 Hoare Fixpoint 定理（~8 条） | 300–500 |
| 外层循环引理（~2 条） | 60–100 |
| 空行/注释/Section 声明 | 40–60 |
| **总计** | **880–1440 行** |

中位预估：**~1100 行**（约为桥判定版本 1577 行的 70%，反映 SCC 版本不变量
更少但栈相关逻辑新增的净效果）。

---

*设计文档版本：1.0*
*最后更新：2026-06-15*
