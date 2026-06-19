# tarjan_scc_keep_fa_visited_rich 的 forset 层级修复

**Author**: Kimi Code CLI
**Date**: 2026-06-16

---

## 1. 问题现象

在 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_dfn.v` 中，`Lemma tarjan_scc_keep_fa_visited_rich` 的证明在第 478 行无法通过编译：

```coq
eapply Hoare_bind.
apply (forset_process_edge_keep_fa_visited_rich x W). intros a. apply IH.
```

Coq 报错：

```text
Unable to unify "(fun s : SCCSt => x ∈ visited s /\ fa_visited s) s1"
with "(fun s : SCCSt => s = s0) s1".
```

## 2. 障碍分析

### 2.1 两个「当前顶点」的错位

`tarjan_scc_keep_fa_visited_rich` 要证明的是：从调用顶点 `u` 出发执行 `tarjan_scc u`，保持

```coq
u ∈ visited s  ∧  fa_visited s
```

但 `tarjan_scc_f` 的函数体内部遍历的是 **当前处理顶点 `x` 的出边邻居**：

```coq
Definition tarjan_scc_f W u :=
  preloop u;;
  forset (fun v => dg_step g u v) (process_edge u W);;
  If (fun s => low s u = dfn s u) (pop_scc u).
```

用 `Hoare_fix` 打开不动点后，归纳假设 `IH` 给出的是递归体保持 **外层调用者 `u`** 的状态：

```coq
∀ a, Hoare (u ∈ visited ∧ fa_visited) (W a) (u ∈ visited ∧ fa_visited)
```

而 `forset_process_edge_keep_fa_visited_rich x W` 在参数为 `x` 时，要求递归体保持的是 **forset 中心 `x`** 的状态：

```coq
∀ a, Hoare (x ∈ visited ∧ fa_visited) (W a) (x ∈ visited ∧ fa_visited)
```

`x` 是不动点证明中的任意参数，**不一定等于 `u`**，因此 `IH` 不能直接提供 `W a` 保持 `x ∈ visited` 的前提。

### 2.2 为什么已有引理不够

`Tarjan_scc_basics.v` 中的 `forset_process_edge_keep_fa` 只保护单个顶点 `v` 的 `fa s v = fav`，无法直接承载全称量词：

```coq
fa_visited s := ∀ v, fa s v ≠ v → fa s v ∈ visited s
```

因此需要一条能在 `forset` 层级承载 `fa_visited` 的引理；但仅有这条引理仍不够，因为不动点归纳假设缺少对当前 forset 中心 `x` 的 visited 保持性。

## 3. 解决方案

### 3.1 核心思路：用 `Hoare_fix_logicv_conj` 引入已证性质

`Tarjan_scc_basics.v` 中已经证明：

```coq
Theorem tarjan_scc_keep_visited (u v: V):
  Hoare (v ∈ visited s) (tarjan_scc g u) (fun _ s => v ∈ visited s).
```

它说明 `tarjan_scc` 的递归调用不会取消任何已访问顶点。利用 `StateRelHoare.v` 中的 `Hoare_fix_logicv_conj`，可以把这条已知性质作为辅助不变式折叠进 `fa_visited` 的不动点归纳：

```coq
Theorem Hoare_fix_logicv_conj {Σ A B C}:
  ∀ F P1 Q1 a c {D} P2 Q2,
    (∀ a d, Hoare (P2 a d) (Lfix F a) (Q2 a d)) ->
    (∀ W,
      (∀ a d, Hoare (P2 a d) (W a) (Q2 a d)) ->
      (∀ a c, Hoare (P1 a c) (W a) (Q1 a c)) ->
      (∀ a c, Hoare (P1 a c) (F W a) (Q1 a c))) ->
    Hoare (P1 a c) (Lfix F a) (Q1 a c).
```

取：

- `P2 x d s := d ∈ visited s`（已知对 `Lfix F` 成立）
- `P1 x c s := u ∈ visited s ∧ fa_visited s`
- `Q1 x c _ s := u ∈ visited s ∧ fa_visited s`

于是归纳假设额外得到：

```coq
IHvis : ∀ a d, Hoare (d ∈ visited) (W a) (d ∈ visited)
```

这正好补上 forset 层缺失的 `x ∈ visited` 保持性。

### 3.2 forset 层级的不变式组合

在 `tarjan_scc_f x` 的函数体内，对 `forset (dg_step g x) (process_edge x W)` 做如下处理：

1. **前置状态**：`preloop x` 后已有 `(u ∈ visited ∧ fa_visited) ∧ x ∈ visited`。
2. **组合保持三个事实**：
   - 用 `forset_process_edge_keep_fa_visited_rich x W` 保持 `x ∈ visited ∧ fa_visited`。
     需要 `W a` 保持 `x ∈ visited`（来自 `IHvis a x`）和 `fa_visited`（来自不动点 `IH`）。
   - 用 `forset_process_edge_keep_visited x u W` 保持 `u ∈ visited`。
     需要 `W a` 保持 `u ∈ visited`（来自 `IHvis a u`）。
3. **forset 结束后**：得到 `u ∈ visited ∧ x ∈ visited ∧ fa_visited`。
4. **`pop_scc x`** 保持 `u ∈ visited` 和 `fa_visited`。

最终得到目标后件 `u ∈ visited ∧ fa_visited`。

## 4. 修复后的证明骨架

```coq
Lemma tarjan_scc_keep_fa_visited_rich (u: V):
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s)
        (tarjan_scc g u)
        (fun _ s => u ∈ visited s /\ fa_visited s).
Proof.
  unfold tarjan_scc.
  eapply Hoare_fix_logicv_conj with
    (P2 := fun (x: V) (d: V) (s: SCCSt) => d ∈ visited s)
    (Q2 := fun (x: V) (d: V) (_: unit) (s: SCCSt) => d ∈ visited s)
    (P1 := fun (x: V) (_: unit) (s: SCCSt) => u ∈ visited s /\ fa_visited s)
    (Q1 := fun (x: V) (_: unit) (_: unit) (s: SCCSt) => u ∈ visited s /\ fa_visited s)
    (a := u) (c := tt).
  - (* 已证：tarjan_scc 保持任意顶点的 visited 状态 *)
    intros x d. apply tarjan_scc_keep_visited.
  - intros W IHvis IHfa x.
    unfold tarjan_scc_f.
    (* preloop：保持 u∈visited∧fa_visited，并建立 x∈visited *)
    eapply Hoare_bind.
    { apply Hoare_conj with
        (Q1 := fun _ s => u ∈ visited s /\ fa_visited s)
        (Q2 := fun _ s => x ∈ visited s).
      - apply Hoare_conj;
          [ eapply Hoare_conseq_pre; [| apply preloop_keep_visited]; tauto
          | eapply Hoare_conseq_pre; [| apply preloop_keep_fa_visited]; tauto ].
      - apply preloop_self_visited. }
    intros _. intro_state. destruct H as [[Huvis Hfa] Hxvis].
    (* forset：组合保持 u∈visited 与 x∈visited∧fa_visited *)
    eapply Hoare_bind.
    { apply Hoare_conj.
      - apply Hoare_conseq_pre with (P2 := fun s => x ∈ visited s /\ fa_visited s).
        { intros s1 Hs1. subst s1. split; auto. }
        apply (forset_process_edge_keep_fa_visited_rich x W).
        intros a. apply Hoare_conj.
        + eapply Hoare_conseq_pre; [| apply (IHvis a x)]; auto.
        + eapply Hoare_conseq_pre; [| apply (IHfa a tt)]; tauto.
      - apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
        { intros s1 Hs1. subst s1. auto. }
        apply (forset_process_edge_keep_visited x u W).
        intros a. apply (IHvis a u). }
    intros _. intro_state. destruct H as [[Hxvis' Hfa'] Huvis'].
    (* pop_scc / skip *)
    intro_state. hoare_auto_s.
    + apply Hoare_conj.
      * eapply Hoare_conseq_pre; [| apply (pop_scc_keep_visited x u)]; auto.
      * eapply Hoare_conseq_pre; [| apply pop_scc_keep_fa_visited]; tauto.
    + destruct H1. subst s. split; auto.
Qed.
```

## 5. 设计取舍

- **不修改 `Tarjan_scc_basics.v`**：已有的 `forset_process_edge_keep_fa_visited_rich` 和 `forset_process_edge_keep_visited` 已经足够，只需要在 proof 结构层面正确组合。
- **不引入新的顶层定义或公理**：修复仅使用已有 Hoare 组合子和已有引理。
- **不改动 spec 定义**：`fa_visited` 的定义和语义保持不变。

## 6. 验证标准

修复后应满足：

1. `coqc` 成功编译 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_dfn.v`。
2. 文件内无遗留 `Admitted` 或额外 `Axiom`。
3. `tarjan_scc_keep_fa_visited` 仍可由 `tarjan_scc_keep_fa_visited_rich` 通过 `Hoare_conj` 与 `tarjan_scc_keep_visited` 组合得到。
