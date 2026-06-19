# Tarjan-SCC-is-low-min-lemma-issue
**Author**: Vitalrubbish
**Date**: 2026-06-18

## 问题概述

在证明 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v` 中的 `process_edge_keep_low_forset_inv` 时，遇到三个 `admit`（tree edge、back edge、cross edge 的 min 条件分支），其核心原因是 `low_forset_inv` 使用了**嵌套**的 `min_value_of_subset`：

```coq
min_value_of_subset Nat.le
  (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
   min_value_of_subset Nat.le
     (fun w => back_edges_done s u done w \/ w = u) (dfn s))
  (fun x => x) (low s u).
```

内层 `min_value_of_subset` 会把候选集合塌缩成 singleton，导致我们无法直接对 `children_done` / `back_edges_done` 做集合等价重写或构造 witness。当前 `process_edge_keep_low_forset_inv` 的 tree edge、back edge、cross edge 分支均因此无法关闭。

## 相关文件

- `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`
- `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_basics.v`
- `SeparationLogic/MaxMinLib/MaxMin.v`
- `SeparationLogic/MaxMinLib/Interface.v`

## 当前状态

- `Tarjan_scc_is_low.v` 仍有 5 个 `Admitted`。
- 其中 `process_edge_keep_low_forset_inv` 占 3 个，全部卡在 min 条件更新。
- 其余 2 个 `Admitted` 位于 `low` 的保持性证明（递归调用 `W v` 后 `low u` 不变）。

## 阻塞点分析

`min_value_of_subset` 是关系型定义，非函数：

- 当候选集非空时，它返回该集合在 `le` 下的最小值所组成的 singleton；
- 当候选集为空时，它返回空集。

因此嵌套结构：

```
min( min(children_done, low) ∪ min(back_edges_done, dfn) ) == low u
```

中，内层 `min(children_done, low)` 已经不再是 `children_done` 本身，而是一个被 `low` 映射并取最小后的集合。当我们把新顶点 `v` 加入 `children_done` 时，需要证明：

```
min( min(children_done ∪ {v}, low) ∪ min(back_edges_done, dfn) )
== min( min(children_done, low) ∪ min(back_edges_done, dfn) ∪ {low v} )
```

这不是一个简单的集合等价重写能解决的问题，因为它涉及内层 min 的“塌缩”行为。

## 期望解决方案

**目标**：在只修改 `Tarjan_directed/` 目录下文件的前提下，提供两个辅助引理，分别处理 tree edge 和 back edge 的 min 集合更新，并用更简单的方式处理 cross edge。

### 建议加入 `Tarjan_scc_basics.v`

在 `Tarjan_scc_basics.v` 顶部引入：

```coq
From MaxMinLib Require Import MaxMin Interface.
```

然后加入以下 helper 引理：

```coq
Section NestedMinUpdateNat.

Theorem min_value_of_subset_nested_update_left_nat
  {A B: Type}
  (f: A -> nat) (P: A -> Prop) (a: A)
  (g: B -> nat) (Q: B -> Prop)
  (n: nat):
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le P f ∪ min_value_of_subset Nat.le Q g) id n ->
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le (P ∪ [a]) f ∪ min_value_of_subset Nat.le Q g) id
    (Nat.min n (f a)).

Theorem min_value_of_subset_nested_update_right_nat
  {A B: Type}
  (f: A -> nat) (P: A -> Prop)
  (g: B -> nat) (Q: B -> Prop) (b: B)
  (n: nat):
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le P f ∪ min_value_of_subset Nat.le Q g) id n ->
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le P f ∪ min_value_of_subset Nat.le (Q ∪ [b]) g) id
    (Nat.min n (g b)).

End NestedMinUpdateNat.
```

证明思路（`left` 版）：

1. 用 `min_union_1_right'` 把旧外层集合 `(L ∪ R)` 加上新元素 `[f a]` 的最小值计算为 `Nat.min n (f a)`。
2. 用 `min_eq_forward` 证明 `(L' ∪ R)` 与 `((L ∪ R) ∪ [f a])` 在最小值意义下等价——其中每个元素都能被对方集合中的某个元素控制。
3. 这样无需讨论 `children_done` 是否为空，也无需显式构造 witness。

`right` 版可由 `left` 版结合集合交换得到。

### 建议补全 `low` 保持性引理

`process_edge_keep_low_forset_inv` 的旧 `Hmin` 前提依赖 `low s0 u`。在 tree edge 分支中，先执行 `set_fa v u` 再递归调用 `W v`，`low u` 在 `W v` 期间应保持不变。因此建议补充：

```coq
Theorem tarjan_scc_keep_low_other (u w: V) (loww: nat):
  u <> w ->
  Hoare (fun s => w ∈ visited s /\ low s w = loww)
        (tarjan_scc ... g u)
        (fun _ s => w ∈ visited s /\ low s w = loww).
```

证明用 `Hoare_fix`，归纳假设取为：

```coq
forall x, Hoare (fun s => x <> w /\ w ∈ visited s /\ low s w = loww)
                (W x)
                (fun _ s => w ∈ visited s /\ low s w = loww)
```

然后依次拼接 `preloop_keep_low`、`forset_process_edge_keep_low`、`pop_scc_keep_low`。

### 在 `process_edge_keep_low_forset_inv` 中的使用方式

#### Tree edge

```coq
assert (Hchild_add:
  children_done s0 u (done ∪ [v]) == children_done s0 u done ∪ [v]).
{ apply children_done_add; auto. }

assert (Hmin_child_new:
  min_value_of_subset Nat.le (children_done s0 u (done ∪ [v])) (low s0) ==
  min_value_of_subset Nat.le (children_done s0 u done ∪ [v]) (low s0)).
{ apply min_value_of_subset_congr; [exact Hchild_add | reflexivity | reflexivity]. }

eapply min_value_of_subset_congr.
- exact Hmin_child_new.
- reflexivity.
- reflexivity.
- apply min_value_of_subset_nested_update_left_nat with (a := v).
  exact Hmin.
```

结合 `update_low` 的定义可得 `low s u = Nat.min (low s0 u) (low s0 v)`。

#### Back edge

```coq
assert (Hback_add:
  (fun w => back_edges_done s0 u (done ∪ [v]) w \/ w = u) ==
  (fun w => back_edges_done s0 u done w \/ w = u) ∪ [v]).
{ (* 用 back_edges_done_add 展开，再 sets_unfold 验证 *) }

assert (Hback_min_new:
  min_value_of_subset Nat.le (fun w => back_edges_done s0 u (done ∪ [v]) w \/ w = u) (dfn s0) ==
  min_value_of_subset Nat.le ((fun w => back_edges_done s0 u done w \/ w = u) ∪ [v]) (dfn s0)).
{ apply min_value_of_subset_congr; [exact Hback_add | reflexivity | reflexivity]. }

eapply min_value_of_subset_congr.
- reflexivity.
- exact Hback_min_new.
- reflexivity.
- apply min_value_of_subset_nested_update_right_nat with (b := v).
  exact Hmin.
```

#### Cross edge

直接用 `children_done_no_add` / `back_edges_done_no_add` 加 `min_value_of_subset_congr`：

```coq
eapply min_value_of_subset_congr.
- apply children_done_no_add; auto.
- apply back_edges_done_no_add; auto.
- reflexivity.
- exact Hmin.
```

## 设计决策

- **不修改 `MaxMinLib`**：这两个引理依赖 `nat` 上的 `min_nonempty_exists`，对任意全序不成立；目前仅 `Tarjan` 使用。先局部化到 `Tarjan_scc_basics.v`，待模式成熟且有复用需求时再 upstream。
- **不引入 `min_value_of_subset_with_default`**：改用 helper 引理的方式更贴近现有 `MaxMinLib` 的接口，避免大范围重写 `low_forset_inv` 的定义。

## 验收标准

- [ ] `Tarjan_scc_basics.v` 中加入 `min_value_of_subset_nested_update_left_nat` 和 `min_value_of_subset_nested_update_right_nat` 并通过编译。
- [ ] `Tarjan_scc_basics.v` 中加入 `tarjan_scc_keep_low_other` 并通过编译。
- [ ] `Tarjan_scc_is_low.v` 中 `process_edge_keep_low_forset_inv` 的三个 `admit` 被替换为完整证明。
- [ ] `Tarjan_scc_is_low.v` 整体通过 `coqc` / `rocq compile` 编译。
- [ ] 无新增 `Admitted` 或额外 `Axiom`。

## 备注

- `min_value_of_subset_congr` 在类型推断失败时，可显式使用 `@min_value_of_subset_congr ...` 或 `(min_value_of_subset_congr (A:=V) (le:=Nat.le))`。
- 若证明过程中发现 `low` / `dfn` 相关的不变式还需要额外 helper，应优先放在 `Tarjan_scc_basics.v`，不进入 `MaxMinLib` 或 `common_case_formal_lib`。
