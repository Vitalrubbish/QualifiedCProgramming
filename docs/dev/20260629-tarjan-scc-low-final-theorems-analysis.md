# Tarjan-SCC-Low-Final-Theorems-Analysis
**Author**: Codex
**Date**: 2026-06-29

## 1. 背景

本文档评估 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`
中最后两个尚未关闭的定理：

```coq
tarjan_scc_keep_low_valid
tarjan_scc_keep_is_low
```

评估目标是判断关闭证明的工作量、是否需要修改公开 statement、以及是否应补充中间
lemma。本文档只记录分析结论，不包含证明推进。

当前已完成的关键基础包括：

- `preloop_establishes_low_iteration_entry`
- `process_edge_preserves_low_iteration`
- `forset_preserves_low_iteration`
- `low_frontier_and_src_imply_low_valid`
- `if_pop_preserves_low_valid_post`
- `tarjan_scc_keep_fa_stable_unvisited`
- `tarjan_scc_preserves_Q_active_stack_frame`
- `tarjan_scc_preserves_active_base`

其中 `forset_preserves_low_iteration` 已经通过通用 `Hoare_forset` 关闭，循环不变量为：

```coq
fun done s =>
  low_iteration_inv g root u done s /\
  stack_dfn_order s /\
  dfn_injective s
```

## 2. `tarjan_scc_keep_low_valid`

### 2.1 当前 statement

```coq
Theorem tarjan_scc_keep_low_valid (u: V):
  Hoare (fun s => low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
        (tarjan_scc g u)
        (fun _ s => low_valid_post g root u s /\
                    u ∈ visited s /\
                    stack_dfn_order s /\
                    dfn_injective s).
```

该公开 statement 基本合理，暂不建议修改。它正好表达“从未访问顶点 `u` 出发，
执行 Tarjan 后得到当前根的 `scc_low_valid_v`、保持全局良构性并访问 `u`”。

### 2.2 主证明形状

展开 `tarjan_scc_f` 后，证明应按三段组合：

```coq
preloop u;;
forset (fun v => dg_step g u v) (process_edge u W);;
If (fun s => low s u = dfn s u) (pop_scc u)
```

预期管道为：

1. `preloop_establishes_low_iteration_entry` 建立 `low_iteration_entry g root u`。
2. `forset_preserves_low_iteration` 将 entry 推进到 `low_iteration_done g root u`。
3. `low_frontier_and_src_imply_low_valid` 从 done invariant 得到 `scc_low_valid_v g root s u`。
4. `if_pop_preserves_low_valid_post` 处理最后的 `pop_scc`。

### 2.3 主要缺口

关键缺口不在三段主合约本身，而在调用 `forset_preserves_low_iteration` 时需要提供：

```coq
forall a done s0,
  dg_step g u a ->
  ~ done a ->
  low_continuation_contract W u a done s0
```

`low_continuation_contract` 覆盖 tree-edge 分支整段：

```coq
set_fa a u;;
W a;;
lv <- get' (fun s => low s a);;
update_low u lv
```

仅使用普通 `Q_low_valid` 作为 LFix IH 不足以关闭该 contract。原因是 child 递归返回后，
父节点 `u` 的 `low_iteration_inv` 仍需要以下 frame 信息：

- `fa` 对旧 visited / done 顶点稳定；
- `u` 仍在栈中；
- `u` 与更老 ancestor 的 `dfn` 保持；
- `stack_dfn_order` 与 `dfn_injective` 保持；
- child `a` 返回后具备 `scc_low_valid_v g root s a`；
- `set_fa a u` 后进入 child 递归的 `low_pre g root a` 能建立。

这些信息分别来自当前已有的 `Q_fa_stable`、`Q_active_stack_frame`、`active_base`
和 `Q_low_valid`，但目前还缺一个面向 `low_continuation_contract` 的集成 helper。

### 2.4 建议补充的 helper

建议新增一个桥接 lemma，而不是把所有 frame 组合内联到顶层 theorem：

```coq
Lemma low_continuation_contract_from_recursive_frames
      (u a: V) (done: V -> Prop) (s0: @SCCSt V)
      (W: V -> program (@SCCSt V) unit):
  (* assumptions: dg_step g u a, ~ done a, and suitable IHs for W *)
  low_continuation_contract W u a done s0.
```

该 helper 内部应组合：

- `set_fa_establishes_low_iteration_before_new_child`
- child 调用的 `Q_low_valid`
- child 调用对 parent `u` 的 `Q_active_stack_frame`
- child 调用的 `Q_fa_stable`
- `stack_dfn_order` / `dfn_injective` 保持性

此外，tree-edge 返回后的最后一步可能还需要一个更小的专用 lemma：

```coq
Lemma get_low_update_low_tree_child_extends_low_iteration
      (u a: V) (done: V -> Prop):
  Hoare
    (fun s =>
       low_iteration_inv g root u done s /\
       stack_dfn_order s /\
       dfn_injective s /\
       dg_step g u a /\
       ~ done a /\
       a ∈ visited s /\
       fa s a = u /\
       fa s a <> a /\
       scc_low_valid_v g root s a)
    (lv <- get' (fun s => low s a);; update_low u lv)
    (fun _ s =>
       low_iteration_inv g root u (done ∪ [a]) s /\
       stack_dfn_order s /\
       dfn_injective s).
```

当前已有 `get_dfn_update_low_current_extends_low_iteration_stack` 处理 back-edge /
stack 分支；tree-child 分支需要对应的 `get low child` 版本。

### 2.5 工作量评估

`tarjan_scc_keep_low_valid` 属于中等偏大的证明：

- 顶层结构清楚；
- 大部分 primitive 和 frame theorem 已存在；
- 主要工作是补 1-2 个桥接 helper，并把 LFix IH 整理成 `low_continuation_contract`；
- 预计证明脚本规模为数百行，风险主要在 frame adapter 的 precondition 对齐。

## 3. `tarjan_scc_keep_is_low`

### 3.1 当前 statement

```coq
Theorem tarjan_scc_keep_is_low (u: V):
  Hoare (fun s => low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
        (tarjan_scc g u)
        (fun _ s => low_post g root u s /\
                    u ∈ visited s /\
                    stack_dfn_order s /\
                    dfn_injective s).
```

其中：

```coq
low_post g root u s :=
  wf_scc_state g root s /\ scc_is_low_v g root s u.
```

该公开 statement 也可以保留，但不能期望它直接由
`tarjan_scc_keep_low_valid` 一步推出。

### 3.2 现有 bridge 的粒度问题

当前主要 pure bridge 是全局形式：

```coq
scc_low_valid_implies_is_low :
  dfn_valid g s root ->
  dfn_inv s ->
  scc_low_valid g root s ->
  scc_is_low g root s.
```

它要求：

```coq
scc_low_valid g root s :=
  forall v, v ∈ visited s -> scc_low_valid_v g root s v
```

而 `tarjan_scc_keep_low_valid` 的 postcondition 只提供单点事实：

```coq
scc_low_valid_v g root s u
```

因此，当前 `tarjan_scc_keep_low_valid` 不足以推出
`scc_is_low_v g root s u`。

另一个可用 lemma：

```coq
scc_is_low_induction_is_low
```

也需要当前节点所有 DFS-tree child 的 `scc_is_low_v_val` 信息；单点
`scc_low_valid_v u` 仍然不够。

### 3.3 建议路线

不建议修改公开 theorem statement，而应补充一个内部 strengthened theorem 或 pure bridge。

可选路线有两类。

路线 A：证明本次调用覆盖的 DFS subtree closure。

新增内部规格描述“本轮递归中新访问 / 当前 DFS subtree 中的顶点都具备
`scc_low_valid_v`”，然后用局部 pure bridge 推出 root `u` 的 `scc_is_low_v`。
这与设计文档中“程序阶段先证明 `scc_low_valid_v`，强数学语义由 pure bridge 推出”
的方向最一致。

路线 B：单独做 `is_low` LFix 证明。

该路线在 LFix 后置中直接携带足够的 child `scc_is_low_v_val` 信息，然后在 root
处调用 `scc_is_low_induction_is_low`。缺点是会让程序证明重新接触数学规格，
与当前分层设计相冲突，且容易把 `scc_is_low_v` 重新塞回 forset invariant。

建议优先采用路线 A。

### 3.4 可能需要的中间 statement

可以考虑新增内部 theorem，例如：

```coq
Definition low_valid_subtree_post (u: V) (s: @SCCSt V): Prop := ...

Theorem tarjan_scc_keep_low_valid_subtree (u: V):
  Hoare
    (fun s => low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
    (tarjan_scc g u)
    (fun _ s =>
       low_valid_subtree_post u s /\
       u ∈ visited s /\
       stack_dfn_order s /\
       dfn_injective s).
```

具体 `low_valid_subtree_post` 不宜直接等同全局 `scc_low_valid`，否则会要求所有旧
visited 顶点也满足 low-valid。更合理的是描述从 `u` 的 DFS subtree 可达的新增顶点，
或描述 `scc_is_low_induction_is_low` 对 root 所需的 child facts。

## 4. 是否需要改 statement

### 4.1 `tarjan_scc_keep_low_valid`

不建议修改公开 statement。

它作为单点程序递推规格是合理的。若证明时发现 LFix IH 太弱，应新增内部 strengthened
lemma，再把当前 theorem 作为投影推论，而不是扩张公开 postcondition。

### 4.2 `tarjan_scc_keep_is_low`

也不建议立即修改公开 statement。

当前 statement 表达的是最终用户关心的 root-level 数学 low-link 正确性。真正缺失的是
从程序级 `scc_low_valid_v` 到数学级 `scc_is_low_v` 的局部 closure bridge，而不是
公开 theorem 的目标本身错误。

如果后续证明发现必须持有全图 `scc_low_valid`，可以新增一个 stronger theorem，但应让
当前 theorem 作为 corollary 保持稳定。

## 5. 风险与建议顺序

建议后续按以下顺序推进：

1. 补 `get_low_update_low_tree_child_extends_low_iteration`。
2. 补 `low_continuation_contract_from_recursive_frames`。
3. 用上述 helper 关闭 `tarjan_scc_keep_low_valid`。
4. 设计并证明局部 subtree / child closure bridge。
5. 最后关闭 `tarjan_scc_keep_is_low`。

最大风险是第 4 步：现有 pure bridge 主要是全局 `scc_low_valid -> scc_is_low`，
而当前公开 low-valid theorem 是单点的。若没有合适的局部 closure 规格，
`tarjan_scc_keep_is_low` 会被迫回到较重的程序后置条件。

