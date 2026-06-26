# Tarjan SCC: 迁移至 Hoare_normal_LFix 的完整计划

**Author**: Vitalrubbish
**Date**: 2026-06-26

## 1. 动机

### 1.1 当前状态

`Tarjan_scc_basics.v` 已通过移除 `tarjan_scc_f` 的冗余 `if_else` 守卫恢复了编译。当前使用 `hoare_fix_nolv_auto`（底层为 `Hoare_fix`）：

```coq
IH: forall a, Hoare P (W a) Q
```

其中 `P` 和 `Q` 是固定的语义前置/后置。这要求 IH 的调用点状态必须满足 `P`，在 `forset` 内部需要反复通过 `intro_state` 建立 `s = s0` 上下文来匹配。这种模式下容易出现变量 shadowing，也是之前证明维护困难的原因之一。

### 1.2 目标：Kosaraju 风格

```coq
IH: forall s0 a, Hoare (fun s => s = s0) (W a) (Q a s0)
```

核心改进：
- **IH 前置统一为 `s = s0`**：不依赖具体语义，可在任意中间状态调用，只需 `apply (IH s_current v)`
- **后置参数化初始状态**：`Q a s0` 将初始状态 `s0` 作为参数传入，可以表达"dfn 从调用初态起不变"这样的性质
- **guard 处理标准化**：`Hoare_normal_assume_bind` 将 `assume P` 提升为假设 `P s0`，无需展开 `if_else`

## 2. 现有基础设施

### 2.1 已就绪

`Tarjan_scc_is_dfn.v` 已定义（从 Kosaraju 复制）：

```coq
Theorem Hoare_normal_LFix {Σ A B: Type}:      (* 行 19 *)
  forall (Q: A -> Σ -> B -> Σ -> Prop)
         (f: (A -> M Σ B) -> (A -> M Σ B)),
    (forall W,
       (forall s0 a, Hoare (fun s => s = s0) (W a) (Q a s0)) ->
       (forall s0 a, Hoare (fun s => s = s0) (f W a) (Q a s0))) ->
    (forall s0 a, Hoare (fun s => s = s0) (Lfix f a) (Q a s0)).

Theorem Hoare_normal_LFix_closed {Σ A B: Type}:  (* 行 43 *)
  (* 带不变式 R 的版本，用于 is_dfn.v 的复杂证明 *)
```

`Tarjan_scc_basics.v` 中已有的 primitive 引理提供正常前置形式（如 `Hoare (v ∈ visited) (visit w) (v ∈ visited)`），这些在 normal form 下可直接配合 `Hoare_conseq_pre` 使用。

### 2.2 缺失（仅在 Kosaraju.v 中）

```coq
Theorem Hoare_normalize {Σ A: Type}:           (* Kosaraju.v:243 *)
  forall P f Q,
    (forall s0, P s0 -> Hoare (fun s => s = s0) f Q) ->
    Hoare P f Q.

Theorem Hoare_normal_assume_bind {Σ A: Type}:  (* Kosaraju.v:255 *)
  forall P f Q s0,
    (P s0 -> Hoare (fun s => s = s0) f Q) ->
    Hoare (fun s => s = s0) (assume P;; f) Q.
```

这两个 lemma 是 normal form 证明流的关键桥梁：
- `Hoare_normalize`：将 normal form 的逐点证明提升回任意前置
- `Hoare_normal_assume_bind`：消除 `assume` 守卫，将守卫条件变为假设

## 3. 后置条件的参数化

迁移的核心变化是后置条件的签名。对比：

| 定理 | 当前后置 | Normal form 后置 |
|------|---------|-----------------|
| `keep_visited` | `fun _ s => v ∈ visited s` | `fun u s0 _ s => v ∈ visited s`（不变） |
| `keep_dfn` | `fun _ s => v ∈ visited s /\ dfn s v = dfnv` | `fun u s0 _ s => v ∈ visited s /\ dfn s v = dfn s0 v` |
| `keep_low` | `fun _ s => v ∈ visited s /\ low s v = lowv` | `fun u s0 _ s => v ∈ visited s /\ low s v <= low s0 v` |
| `keep_fa` | `fun _ s => v ∈ visited s /\ fa s v = fav` | `fun u s0 _ s => v ∈ visited s /\ fa s v = fa s0 v` |

关键变化：`dfnv`/`lowv`/`fav` 参数**消失**，改为引用初始状态 `s0` 的值。这使得后置条件是"自包含"的——不需要外部提供具体数值。

`keep_visited` 不需要 `u` 参数（后置不引用 `s0`），可以简化为 `fun (_: V) (_: SCCSt) (_: unit) (s: SCCSt) => v ∈ visited s`。

## 4. 迁移步骤

### Step 1: 添加 `Hoare_normalize` 和 `Hoare_normal_assume_bind`

**文件**: `Tarjan_scc_basics.v`（在 tactic 定义区域后，`Section BASICS` 前）

从 Kosaraju.v 复制两个定理（含证明，共约 15 行）。它们仅依赖 `Hoare_assume_bind`（已在 `StateRelHoare.v` 中）和 `Hoare_normalize`（递归使用 `intro_state` 的思想）。

### Step 2: 迁移 primitive 引理至 normal form（可选优化）

当前 primitive 引理（如 `set_dfn_keep_visited`、`pop_scc_keep_visited`）使用普通前置 `P`。在 normal form 证明中，通过 `Hoare_normalize` + `Hoare_conseq_pre` 即可适配，**无需修改**。

需要新增的 normal form 专用版本（可选，用于简化证明）：

```coq
(* 示例：normal form 的 pop_scc_keep_visited *)
Lemma pop_scc_keep_visited_nf (u w: V) (s0: SCCSt):
  Hoare (fun s => s = s0) (pop_scc u)
    (fun _ s => w ∈ visited s0 -> w ∈ visited s).
```

但这不是必需的——可以直接用 `Hoare_normalize` 包装原引理。

### Step 3: 迁移 `tarjan_scc_keep_visited`

**目标后置**: `Q u s0 _ s := v ∈ visited s`（不引用 s0）

```coq
Theorem tarjan_scc_keep_visited (u v: V):
  Hoare (fun s => v ∈ visited s) (tarjan_scc g u) (fun _ s => v ∈ visited s).
Proof.
  apply Hoare_normalize. intros s0 Hvis.
  apply (Hoare_normal_LFix (fun u' s0' _ s => v ∈ visited s) tarjan_scc_f).
  intros W IH s0' u'.
  (* IH: forall s0 a, Hoare (s = s0) (W a) (fun _ s => v ∈ visited s) *)
  unfold tarjan_scc_f.
  (* preloop u' at state s0' *)
  eapply Hoare_bind.
  { apply Hoare_normalize. intros s1 Heq. subst s1.
    apply preloop_keep_visited. }
  simpl. intros _.
  (* forset + If *)
  eapply Hoare_bind with (R := fun _ s => v ∈ visited s).
  { (* forset: use normal-form forset lemma *)
    apply (forset_process_edge_keep_visited_nf u' W v). intros x.
    (* IH works at any state — apply at current *)
    apply IH. }
  simpl. intros _.
  (* If (low = dfn) (pop_scc) *)
  apply Hoare_normalize. intros s1 Hvis1.
  unfold If. apply Hoare_choice.
  - (* pop_scc branch *)
    apply Hoare_normal_assume_bind. intros Hlow_eq.
    apply Hoare_normalize. intros s2 Heq. subst s2.
    apply pop_scc_keep_visited.
  - (* skip branch *)
    apply Hoare_normal_assume_bind. intros Hlow_neq.
    apply Hoare_ret'. auto.
Qed.
```

关键模式：
- `Hoare_normalize` 将任意前置转为 `s = s0` 形式
- `Hoare_normal_assume_bind` 消除 `assume` 守卫，条件变为假设
- IH 直接用 `apply IH`（因为 IH 的 `s0` 参数可匹配当前状态）
- `intro_state` 完全消失，所有状态变量由证明者显式命名（`s0, s1, s2, ...`）

### Step 4: 迁移 `tarjan_scc_keep_dfn`

**目标后置**: `Q u s0 _ s := v ∈ visited s /\ dfn s v = dfn s0 v`

关键差异：后置引用 `s0` 的 dfn 值，因此 IH 需要在线程中携带：

```coq
IH: forall s0 a,
  Hoare (fun s => s = s0) (W a)
    (fun _ s => v ∈ visited s /\ dfn s v = dfn s0 v)
```

在 `process_edge` 内部递归调用时的用法：
```coq
apply (IH s_current v').  (* s_current 是 forset 内部的当前状态 *)
```

前置条件从 `u <> v` 变为 trivial（`s = s0` 自然满足），而"u <> v" 条件由 `process_edge` 的 `if_else (~v ∈ visited)` 保证（未访问则 u ≠ v 自动成立）。

**需要注意**：`preloop_keep_dfn` 的后置是 `u <> v`。在 normal form 下，这个条件变成：
```coq
Hoare (s = s0) (preloop u) (fun _ s => u <> v /\ dfn s v = dfn s0 v)
```
因为 preloop 前 v 已被 visit（dfn s0 v 已定义），且 u 和 v 不同（u 是当前顶点，v 是递归目标）。需要新增/适配这个引理。

### Step 5: 迁移 `tarjan_scc_keep_low`、`tarjan_scc_keep_fa`、`tarjan_scc_self_visited`、`tarjan_scc_keep_visited_forall`

这三个遵循与 Step 3-4 相同的模式。

### Step 6: 迁移 `Tarjan_scc_is_dfn.v`

此文件**已定义** `Hoare_normal_LFix` 和 `Hoare_normal_LFix_closed`，但当前的证明使用的是 `hoare_fix_nolv_auto` 和 `Hoare_fix_logicv_conj`（旧风格）。

| 当前证明 | 使用模式 | 迁移目标 |
|---------|---------|---------|
| `tarjan_scc_keep_dfn_inv` | `hoare_fix_nolv_auto` | `Hoare_normal_LFix` |
| `tarjan_scc_keep_fa_visited_rich` | `Hoare_fix_logicv_conj` | `Hoare_normal_LFix_closed` + `Hoare_fix_logicv_conj` |
| `tarjan_scc_keep_fa_visited` | `Hoare_fix_logicv_conj` | 同上 |
| `tarjan_scc_keep_combined` | `hoare_fix_nolv_auto` | `Hoare_normal_LFix` |

最大的挑战是 `Hoare_fix_logicv_conj` 的迁移。它在 normal form 下有对应的 `Hoare_fix_logicv_conj'`（`StateRelHoare.v:686`）。需要证明其 normal form 版本与 `Hoare_normal_LFix_closed` 的等价性，或直接使用 `Hoare_normal_LFix_closed` 重写。

**`dfn_injective` 定理**（`is_dfn.v` 约行 1809）：当前使用 `hoare_fix_nolv_auto` + 手动 `eapply Hoare_bind`。迁移到 `Hoare_normal_LFix` 后，前置变为 `s = s0`，后置变为 `Q u s0 _ s := dfn_injective s /\ dfn_inv s`。IH 不依赖具体前置，在 `process_edge` 内部也能直接调用。

### Step 7: 迁移 `Tarjan_scc_is_low.v`

这是最大的文件（~2643 行），但迁移模式与 Step 6 相同。主要涉及：
- `scc_is_low` 相关定理：使用 `Hoare_normal_LFix`
- 带辅助不变量的定理：使用 `Hoare_normal_LFix_closed`

### Step 8: 清理

- 删除冗余的 `intro_state` 调用
- 统一状态变量命名约定（`s0` 始终是函数入口状态，`s1, s2, ...` 是中间状态）
- 删除不再需要的 `dfnv`/`lowv`/`fav` 显式参数传递

## 5. 工作量估算

| 步骤 | 内容 | 预估工作量 | 风险 |
|------|------|-----------|------|
| 1 | 添加 `Hoare_normalize` + `Hoare_normal_assume_bind` | 0.5h | 低 |
| 2 | 适配/新增 normal form primitive 引理 | 1h | 低 |
| 3-5 | 迁移 `Tarjan_scc_basics.v` 6 个定理 | 3h | 中 |
| 6 | 迁移 `Tarjan_scc_is_dfn.v` | 4h | 高（`Hoare_fix_logicv_conj` 适配） |
| 7 | 迁移 `Tarjan_scc_is_low.v` | 6h | 高（文件大，依赖多） |
| 8 | 清理 | 1h | 低 |

总计约 **15-20 小时**。

## 6. 关键设计决策

### 6.1 `Hoare_normal_assume_bind` vs 显式展开 `if_else`

Kosaraju 使用 `Hoare_normal_assume_bind` 处理 `assume` 守卫。对比：

```coq
(* 方案 A: Hoare_normal_assume_bind *)
apply Hoare_normal_assume_bind. intros Hguard.
(* Hguard: P s0，继续证明 body *)

(* 方案 B: 显式展开 if_else *)
unfold If. apply Hoare_choice.
- apply Hoare_assume_bind. ...
- apply Hoare_assume_bind. ...
```

方案 A 更简洁（单行消除），方案 B 在需要分支特殊处理时更灵活。推荐**默认使用方案 A**，仅在 `If` 的两个分支需要完全不同的证明时使用方案 B。

### 6.2 后置条件中的 `<=` vs `=`

当前 `tarjan_scc_keep_low` 的后置是 `low s v = lowv`（精确相等）。在 normal form 下，更自然的表达是 `low s v <= low s0 v`（不增加）。但当前下游证明可能依赖 `=` 形式，需要检查并适配。

### 6.3 `intro_state` 的残余用途

即使在 normal form 下，`intro_state`（即 `Hoare_state_intro`）在某些局部证明中仍有价值——当需要从 `Hoare P c Q` 获取 `P` 在特定状态的信息时。但在 normal form 下，可以直接 `apply Hoare_normalize` 代替 `intro_state`，语义更清晰。

## 7. Kosaraju 参考模式

Kosaraju 的 `DFS_finish_visited_incr`（`Kosaraju.v:381`）是迁移的最佳模板：

```
unfold function_body
→ Hoare_bind (handle first operation)
→ Hoare_repeat_break / Hoare_normalize (enter forset)
→ Hoare_choice (handle forset body branches)
→ Hoare_normal_assume_bind (eliminate each assume guard)
→ IH applied at current state
→ Hoare_ret' for base cases
```

Tarjan 的 `tarjan_scc_f` 更简单（没有 `repeat_break`），模式为：

```
unfold tarjan_scc_f
→ Hoare_bind (preloop)
→ Hoare_bind / Hoare_normalize (forset, using IH)
→ Hoare_normalize (If low=dfn)
→ Hoare_choice or Hoare_normal_assume_bind (pop_scc or skip)
```
