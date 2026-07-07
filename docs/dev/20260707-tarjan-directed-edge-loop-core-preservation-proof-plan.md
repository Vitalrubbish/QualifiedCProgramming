# Tarjan-Directed-Edge-Loop-Core-Preservation-Proof-Plan
**Author**: Codex
**Date**: 2026-07-07

## 1. 目标范围

本计划覆盖 `preloop u` 之后、`maybe_pop u` 之前的邻居循环：

```coq
forset (edge_set u) (process_edge u W)
```

证明目标不是最终 SCC 正确性，而是证明 `chain.md` 中的核心联合不变量在 edge loop 中保持：

```coq
LoopCoreInv u done s :=
  LoopCoreShape u done s /\
  Closed s /\
  LowCorrect u done s.
```

实际 `process_edge` 证明仍需要携带完整循环上下文：

```coq
LoopInv u done s :=
  LoopAuxFacts u s /\ LoopCoreInv u done s.
```

原因是 tree-child 分支需要 `Active u`、`OrderFacts`、`NoUnvisitedReach` 来恢复父调用 frame、构造 child 入口，并在递归返回后继续执行 `update_low u ...`。但这些字段只作为程序辅助事实使用，不进入 `LowCorrect` 和 `Closed` 的数学定义。

建议先证明单步保持：

```coq
ProcessEdgePreservesLoopInv:
  forall u v done W,
    Edge u v ->
    ~ done v ->
    RecursiveChildContract u v done W ->
    Hoare (LoopInv u done)
          (process_edge u W v)
          (fun _ s => LoopInv u (done_after done v) s).
```

然后用 `Hoare_forset` 推出整轮循环：

```coq
EdgeLoopPreservesLoopInv:
  RecursiveContracts W ->
  Hoare (LoopInv u done0)
        (forset (edge_set u) (process_edge u W))
        (fun _ s => LoopInv u (edge_set u) s).
```

其中 `done0` 在当前调用中通常是 `∅`，最终 `done = edge_set u`。

## 2. 当前谓词与 `chain.md` 的对应关系

当前设计已经与 `chain.md` 对齐：

```coq
PartialActiveTarget u done s b
```

对应：

```text
Targets(PartialTree(u, i))
```

```coq
PartialLowCandidate u done s b :=
  b = u \/ PartialActiveTarget u done s b.
```

对应：

```text
{u} ∪ Targets(PartialTree(u, i))
```

```coq
LowCorrect u done s :=
  LowSound u done s /\ LowComplete u done s.
```

关系化表达：

```text
low[u] = min({dfn[u]} ∪ Targets(PartialTree(u, done))).
```

因此 edge loop 的核心任务是证明每处理一条边 `u -> v` 后：

```coq
LowCorrect u done s
```

变为：

```coq
LowCorrect u (done_after done v) s'
```

并同时保持：

```coq
Closed s'
LoopCoreShape u (done_after done v) s'
```

## 3. 第一 proof gate：visited-active 分支的非树边事实

visited-active 分支要把 `v` 加入新的 direct target：

```coq
partial_active_target_direct:
  Edge u v ->
  Active v s ->
  ~ tree_edge s u v ->
  PartialActiveTarget u (done_after done v) s v.
```

因此必须先证明：

```coq
current_active_edge_not_tree:
  LoopInv u done s ->
  Edge u v ->
  ~ done v ->
  Visited v s ->
  Active v s ->
  ~ tree_edge s u v.
```

这是本阶段最重要的早期检查。

如果该 lemma 不能从当前 `LoopCoreShape` / `LoopAuxFacts` 推出，说明当前 invariant 仍缺少一个非常小的 loop-progress 事实。最小补充应当是 visited-only 的 child accounting，而不是上一版危险的 pending-child 全局约束：

```coq
ProcessedTreeChild u done s :=
  forall child,
    Visited child s ->
    fa s child = u ->
    fa s child <> child ->
    done child.
```

这个字段与 `set_fa v u` 后的临时状态兼容：`set_fa` 时 `v` 仍未 visited，所以不会立刻要求 `done v`。它只在 child 完成 `preloop v` 之后生效，正好表达“已经成为正式 DFS tree child 的点必然来自已处理过的边”。

若需要加入该字段，优先放入 `LoopCoreShape`，因为它服务于 `PartialActiveTarget` 的数学分支判定；不要放入 `Closed` 或 `LowCorrect`。

### 3.1 展开 `tree_edge` 后能得到什么

目标是证明：

```coq
~ tree_edge s u v
```

按当前定义：

```coq
tree_edge s x y :=
  dg_step (state_to_dfs_tree g s root) x y.
```

而 `state_to_dfs_tree` 的边由 child witness 给出：

```coq
exists z,
  z ∈ visited s /\
  fa s z <> z /\
  original_step_fst g e = fa s z /\
  original_step_snd g e = z.
```

因此从：

```coq
tree_edge s u v
```

最多可以推出：

```coq
Visited v s
fa s v = u
fa s v <> v
```

加上 `dfn_valid` 还能推出：

```coq
dfn s u < dfn s v
```

这些事实说明 `v` 是 `u` 的 DFS-tree child，但它们本身不能推出 `done v`。

### 3.2 当前 `LoopInv` 不足以证明该 gate

当前：

```coq
LoopCoreShape u done s :=
  wf_scc_state g root s /\
  TreeEdgesAreGraphEdges s /\
  Visited u s /\
  (forall a, done a -> Edge u a) /\
  (forall a, done a -> Visited a s).
```

和：

```coq
LoopAuxFacts u s :=
  NoUnvisitedReach s /\
  Active u s /\
  OrderFacts s.
```

都没有记录：

```text
如果某个 visited 点已经以 fa child = u 成为 u 的 DFS child，
那么处理 u 的邻居循环时，该 child 所对应的边已经在 done 中。
```

因此下面这种状态形状不会被当前 invariant 排除：

```text
stack = v :: u :: rest
Visited u, Visited v
Active u, Active v
fa[v] = u, fa[v] <> v
tree_edge s u v
done = ∅
low[u] = dfn[u]
```

在这个状态中：

```coq
LoopInv u ∅ s
Edge u v
~ done v
Visited v s
Active v s
tree_edge s u v
```

可以同时成立。`Closed` 也不会反驳它，因为 `v` 是 active；`NoUnvisitedReach` 也不会反驳它，因为它只约束 inactive/settled 点到 unvisited 点的可达性；`OrderFacts` 只给出栈顺序和 dfn 唯一性，不表达 edge-loop progress。

所以：

```coq
current_active_edge_not_tree
```

不能从当前 `LoopInv` 直接证明。

### 3.3 最小补充字段

需要加入的不是全局 frame 谓词，而是一个只描述正式 tree child 与 `done` 关系的小字段：

```coq
ProcessedTreeChild u done s :=
  forall child,
    Visited child s ->
    fa s child = u ->
    fa s child <> child ->
    done child.
```

然后把 `LoopCoreShape` 调整为：

```coq
LoopCoreShape u done s :=
  wf_scc_state g root s /\
  TreeEdgesAreGraphEdges s /\
  Visited u s /\
  (forall a, done a -> Edge u a) /\
  (forall a, done a -> Visited a s) /\
  ProcessedTreeChild u done s.
```

它的职责非常窄：

1. 只区分当前 active 邻居是 back/cross edge 还是已处理 tree child。
2. 只服务 `partial_active_target_direct` 所需的 `~ tree_edge s u v`。
3. 不参与 `Closed` 和 `LowCorrect` 的定义。
4. 不涉及未访问 pending child，因此不会复现 `set_fa` 后 invariant 临时破坏的问题。

### 3.4 加入该字段后的 gate 证明骨架

目标：

```coq
current_active_edge_not_tree:
  LoopInv u done s ->
  Edge u v ->
  ~ done v ->
  Visited v s ->
  Active v s ->
  ~ tree_edge s u v.
```

证明：

1. 展开 `tree_edge s u v`，从 `state_to_dfs_tree` 的 witness 得到：

```coq
fa s v = u
fa s v <> v
Visited v s
```

2. 从 `LoopInv` 取出 `LoopCoreShape` 中的：

```coq
ProcessedTreeChild u done s
```

3. 套用它得到：

```coq
done v
```

4. 与前提：

```coq
~ done v
```

矛盾。

注意：`Active v s` 在这个证明中不是核心使用点；它属于 visited-active 分支的程序条件，并会在构造 direct target 时使用。proof gate 本身主要依赖 `~ done v` 与 `ProcessedTreeChild`。

### 3.5 该字段的保持义务

加入 `ProcessedTreeChild` 后，需要证明它在以下阶段保持：

1. `preloop u` 初始化：

```coq
ProcessedTreeChild u ∅ s'
```

若 `fa s' child = u` 且 `child` visited，则不能是新 `u` 自己；旧 visited child 若已有 `fa child = u`，这会意味着入口前已经存在以未访问 `u` 为 parent 的正式 tree child，通常应由 `fa_visited` 和 `~ Visited u` 反驳。若该反驳不够，需要把入口条件加强为 pending child 不可能已有 visited child。

2. visited-active / visited-inactive 分支：

状态不变，`done` 扩大为 `done_after done v`，旧 child 用旧字段，新 child 由 `done_after_intro_new` 或仍由旧字段得到。

3. `set_fa v u` pending 阶段：

字段保持，因为 `v` 尚未 visited；对其它 child，`fa` 不变。

4. child 递归返回后：

此时 `v` 已 visited 且 `fa v = u`，在把 parent `done` 更新为 `done_after done v` 后，新 child `v` 由 `done_after_intro_new` 覆盖，其它 child 由旧字段和 frame preservation 覆盖。

这些义务是局部的、可控的；它们不会要求记录完整调用栈，也不会把 pop-local 事实混入核心 invariant。

## 4. 通用状态保持 cut lemma

先补一组不展开 low 语义的 frame lemma，避免三个分支重复证明。

### 4.1 `update_low` 的结构保持

需要证明：

```coq
update_low_preserves_LoopCoreShape_base:
  Hoare (LoopCoreShape u done)
        (update_low u n)
        (fun _ s => LoopCoreShape u done s).
```

实际可拆为：

```coq
update_low_preserves_wf_scc_state
update_low_preserves_tree_edges_are_graph_edges
update_low_keep_visited_forall
```

`update_low` 只改 `low`，所以 `Closed` 也应有直接保持：

```coq
update_low_preserves_Closed:
  Hoare Closed (update_low u n) (fun _ s => Closed s).
```

`LoopAuxFacts` 同理保持：

```coq
update_low_preserves_LoopAuxFacts:
  Hoare (LoopAuxFacts u) (update_low u n) (fun _ s => LoopAuxFacts u s).
```

其中 `OrderFacts` 使用已有 `update_low_keep_stack_dfn_order`、`update_low_keep_dfn_injective`，`StackNoDup` 直接由 stack 不变得到。

### 4.2 `update_low` 的数值 cut

低链接更新证明需要一个明确的数值 lemma：

```coq
update_low_value:
  Hoare (fun s => low s u = old)
        (update_low u n)
        (fun _ s => low s u = Nat.min old n).
```

也可以拆成两个分支：

```coq
n < old  -> post low[u] = n
old <= n -> post low[u] = old
```

但建议统一成 `Nat.min`，因为 `LowSound` 正好按 min 来源拆分。

同时需要 dfn 不变：

```coq
update_low_preserves_dfn_all:
  Hoare (fun s => forall x, dfn s x = dfn0 x)
        (update_low u n)
        (fun _ s => forall x, dfn s x = dfn0 x).
```

证明中通常只需要点态版本：

```coq
update_low_keep_dfn
```

### 4.3 `set_fa` 的 pending-child 保持

tree branch 中先执行：

```coq
set_fa v u
```

由于 `v` 尚未 visited，此时 `state_to_dfs_tree` 不会把 `v` 纳入 DFS tree。因此 parent 的核心不变量应保持：

```coq
set_fa_pending_preserves_parent_core:
  ~ Visited v s ->
  Hoare (fun s => LoopCoreInv u done s /\ Edge u v /\ Active u s)
        (set_fa v u)
        (fun _ s => LoopCoreInv u done s).
```

关键证明点：

1. `Closed` 不变，因为 `visited` 和 `stack` 不变。
2. `LowCorrect u done` 不变，因为 pending child 未 visited，不会新增 `PartialActiveTarget`。
3. `TreeEdgesAreGraphEdges` 不变，因为 `state_to_dfs_tree` 的 vertex set 仍是旧 `visited`。
4. 若加入 `ProcessedTreeChild`，它也不被破坏，因为新 `fa[v] = u` 的 `v` 仍未 visited。

## 5. 分支一：visited-active

程序路径：

```coq
If (fun s => In v (stack s))
  (dv <- get' (fun s => dfn s v);;
   update_low u dv)
```

前提：

```coq
LoopInv u done s
Edge u v
~ done v
Visited v s
Active v s
```

目标：

```coq
LoopInv u (done_after done v) s'
```

### 5.1 `LoopCoreShape`

`update_low` 不改 `visited/stack/fa/dfn`，旧字段保持。

新增 done 元素需要证明：

```coq
Edge u v
Visited v s'
```

分别来自当前处理边和 visited 分支。

如果加入 `ProcessedTreeChild`，还要证明它对 `done_after done v` 保持；新元素直接由 `done_after_intro_new`，旧元素由单调性。

### 5.2 `Closed`

`update_low` 不改 `visited`、`stack`、图结构，因此直接保持。

### 5.3 `LowCorrect`

记旧值为：

```coq
old := low s u
```

更新后：

```coq
low s' u = Nat.min old (dfn s v)
```

证明 `LowComplete`：

1. 旧 candidate：由 `partial_low_candidate_done_mono` 和旧 `LowComplete`，再用 `Nat.min_le_iff` 得到。
2. 新 direct candidate `v`：由 `partial_low_candidate_direct_active`，再由 `Nat.min` 得到 `low s' u <= dfn s v`。
3. 新 child candidate 不应出现；若出现，必须来自 `v` 作为 tree child，这与 `current_active_edge_not_tree` 或 `ProcessedTreeChild` + `~ done v` 矛盾。

证明 `LowSound`：

1. 若 `Nat.min old (dfn v) = old`，沿用旧 sound witness，并用 `partial_low_candidate_done_mono` 提升到新 done。
2. 若 `Nat.min old (dfn v) = dfn v`，取 witness `v`，由 active direct target 构造 candidate。

需要一个纯 lemma：

```coq
LowCorrect_add_active_direct:
  LoopCoreShape u done s ->
  LowCorrect u done s ->
  Edge u v ->
  Visited v s ->
  Active v s ->
  ~ tree_edge s u v ->
  low' = Nat.min (low s u) (dfn s v) ->
  LowCorrect u (done_after done v) (set_low_value u low' s).
```

实际 Rocq 中不必真的定义 `set_low_value`，可以写成 Hoare 版本。

## 6. 分支二：visited-inactive

程序路径：

```coq
skip
```

前提：

```coq
LoopInv u done s
Edge u v
~ done v
Visited v s
~ Active v s
```

目标：

```coq
LoopInv u (done_after done v) s
```

### 6.1 `LoopCoreShape`

状态不变。

新增 done 元素仍只需要：

```coq
Edge u v
Visited v s
```

### 6.2 `Closed`

状态不变，直接保持。

### 6.3 `LowCorrect`

这是 `chain.md` 中 “Low 依赖 Closedness” 的关键点。

需要证明 newly done 的 `v` 不贡献任何 active target：

```coq
inactive_done_no_new_target:
  Closed s ->
  TreeEdgesAreGraphEdges s ->
  Visited v s ->
  ~ Active v s ->
  Edge u v ->
  forall b,
    PartialLowCandidate u (done_after done v) s b ->
    PartialLowCandidate u done s b.
```

证明分解：

1. 新 direct target 要求 `Active v s`，与 `~ Active v s` 矛盾。
2. 新 child target 只能是 child = `v`。
3. 对 child target，有：

```coq
dg_reachable (state_to_dfs_tree g s root) v x
Edge x b
Active b s
```

4. 用 `TreeEdgesAreGraphEdges` 把 tree reachability 提升为原图 reachability：

```coq
dg_reachable g v x
```

再接一步 `Edge x b` 得到：

```coq
dg_reachable g v b
```

5. 由 `Closed s v b`、`Visited v s`、`~ Active v s`、`Active b s` 反驳。

于是：

```coq
LowCorrect u done s ->
LowCorrect u (done_after done v) s
```

其中 `LowSound` 沿用旧 witness；`LowComplete` 把新 candidate 反向化为旧 candidate。

## 7. 分支三：unvisited tree-child

程序路径：

```coq
set_fa v u;;
W v;;
lv <- get' (fun s => low s v);;
update_low u lv
```

这是最复杂分支，建议不要直接证明整个 `process_edge`，而是拆成 4 个 cut。

### 7.1 pending `set_fa` 阶段

先证明 parent core 不变：

```coq
set_fa_pending_preserves_parent_loop:
  Hoare
    (fun s =>
       LoopInv u done s /\
       Edge u v /\
       ~ Visited v s)
    (set_fa v u)
    (fun _ s =>
       LoopInv u done s /\
       EntryPre v s /\
       fa s v = u /\
       fa s v <> v).
```

`EntryPre v` 的构造：

1. `wf_scc_state_pre v` 用已有 `set_fa_preserves_wf_scc_state_pre`。
2. `NoUnvisitedReach`、`Closed`、`OrderFacts` 由 `set_fa` 保持。
3. `TreeEdgesAreGraphEdges` 因 `v` 仍未 visited 而保持。
4. `fa s v <> v -> Edge (fa s v) v` 由 `fa[v]=u` 和 `Edge u v` 得到。

这里正是当前设计避免上一版卡点的地方：pending child 不会破坏 parent 的 `LoopCoreInv`。

### 7.2 递归调用 contract

当前 `process_edge` 中的 `W v` 是完整 `tarjan_scc v`，包含 child 自己的 `maybe_pop`。因此不能简单假设返回：

```coq
RootLowCorrect v s_mid
```

因为若 child 被 pop，`RootLowCorrect` 的 active-target 语义会变。

建议为父节点更新 low 定义一个专门 contract：

```coq
ChildContributionContract u v s_before s_after :=
  FramePreservedForParent u s_before s_after /\
  Closed s_after /\
  NoUnvisitedReach s_after /\
  TreeEdgesAreGraphEdges s_after /\
  OrderFacts s_after /\
  Visited v s_after /\
  ChildLowContribution u v s_after.
```

其中：

```coq
ChildLowContribution u v s :=
  (Active v s /\ RootLowCorrect v s)
  \/
  (~ Active v s /\ dfn s u < dfn s v /\ ChildNoActiveTarget v s).
```

含义：

1. child 未弹栈：`low[v]` 正是 child subtree 对当前 active stack 的贡献。
2. child 已弹栈：由 child 的 low/closedness 证明它不再贡献任何 active target；同时 `dfn[u] < dfn[v]` 保证 `min(low[u], dfn[v])` 不会错误降低 parent low。

这比把 `RootLowCorrect v` 强行塞进最终 `RootAfterMaybePop` 更安全，也符合当前 `RootAfterMaybePop` 不携带 `RootLowCorrect` 的设计。

### 7.3 child target 提升到 parent target

需要两个纯 lemma。

child active 时：

```coq
child_candidate_lifts_to_parent:
  Edge u v ->
  fa s v = u ->
  fa s v <> v ->
  RootLowCorrect v s ->
  PartialLowCandidate v (edge_set v) s b ->
  b = v \/
  PartialActiveTarget u (done_after done v) s b \/
  dfn s u <= dfn s b.
```

解释：

1. child 的 active target 可以作为 parent 的 child target。
2. child 自己 `b = v` 时不需要加入 parent target；由 `dfn_valid` 得到 `dfn[u] < dfn[v]`，旧 parent candidate `u` 已经给出更小上界。

child inactive 时：

```coq
inactive_child_no_parent_target:
  ChildNoActiveTarget v s ->
  forall b,
    newly_from_child u v done s b ->
    False.
```

这与 visited-inactive 分支的 `Closed` 用法相同，只是证明来源来自 child 返回后的 closedness / pop 结论。

### 7.4 `low[u] := min(low[u], low[v])`

证明 `LowComplete`：

1. 旧 candidate：沿用旧 `LowComplete`，再用 `Nat.min`。
2. 新 child target：由 child `RootLowCorrect` 或 `ChildLowContribution` 给出 `low[v] <= dfn b`，再用 `Nat.min`。
3. child 自己 `v` 不作为 parent target 时，用 `dfn[u] < dfn[v]` 和旧 candidate `u` 覆盖。

证明 `LowSound`：

1. 若 min 选择旧 `low[u]`，沿用旧 witness 并用 done monotonicity。
2. 若 min 选择 `low[v]`：
   - child active：用 child sound witness，经过 `child_candidate_lifts_to_parent` 得到 parent witness；若 witness 是 child root `v` 且不能成为 parent target，则该 case 需要由 `dfn[u] < dfn[v]` 证明 min 不会真正选择 `low[v] = dfn[v]`。
   - child inactive：`low[v]` 不应小于旧 `low[u]`；否则会产生 active escape，与 child pop/closedness 结论矛盾。因此 sound 仍沿用旧 witness。

建议先证明一个合并 lemma：

```coq
LowCorrect_add_child_contribution:
  LoopInv u done s_before ->
  Edge u v ->
  fa s_after v = u ->
  fa s_after v <> v ->
  ChildLowContribution u v s_after ->
  low_after = Nat.min (low s_before u) (low s_after v) ->
  LowCorrect u (done_after done v) s_after.
```

实际证明中还需要 parent frame preservation 来连接 `s_before` 与 `s_after` 上的旧 candidates。

## 8. `LoopAuxFacts` 的保持计划

虽然本计划的主题是核心 invariant，但 `ProcessEdgePreservesLoopInv` 必须同时恢复 `LoopAuxFacts`：

```coq
NoUnvisitedReach s
Active u s
OrderFacts s
```

建议复用已有库：

1. `NoUnvisitedReach`：

```coq
process_edge_keep_settled_closed
```

2. `Active u`：

```coq
process_edge_keep_in_stack
```

递归 contract 必须保证 child 调用不弹出 parent `u`。

3. `OrderFacts`：

```coq
process_edge_preserves_stack_dfn_order
process_edge_keep_dfn_injective
StackNoDup preservation
```

`StackNoDup` 可能需要补一个 `process_edge_preserves_stack_nodup`。证明方式与已有 stack/visited preservation 类似：`set_fa/update_low` 不改 stack，递归 contract 负责保持，`pop_scc` 只删除元素不会引入重复。

## 9. `Hoare_forset` 组合计划

`forset` 的 invariant 取：

```coq
P done s := LoopInv u done s
```

需要证明 Proper：

```coq
done1 == done2 ->
LoopInv u done1 s ->
LoopInv u done2 s
```

这要求以下 setoid morphism lemma：

```coq
LoopCoreShape_done_equiv
PartialActiveTarget_done_equiv
PartialLowCandidate_done_equiv
LowCorrect_done_equiv
LoopInv_done_equiv
```

已有的是 monotonic lemma：

```coq
partial_tree_done_mono
partial_active_target_done_mono
partial_low_candidate_done_mono
low_complete_done_mono
```

还需要补等价版本，或在 `Hoare_forset` 的 Proper proof 中分别使用双向 included。

循环 step：

```coq
intros done v Hdone_sub Hedge Hnot_done.
apply ProcessEdgePreservesLoopInv; auto.
```

循环结束时，`done == edge_set u`，得到：

```coq
LoopInv u (edge_set u) s
```

从而建立：

```coq
RootPrePop u s
```

还需额外证明：

```coq
StackRestOlderThanRoot u s
```

它属于 pop 前辅助目标，不属于本计划的核心 low/closedness 保持；应在 edge loop 后由 `OrderFacts`、`Active u` 和 parent frame 事实单独推出。

## 10. 建议实现顺序

1. 补 `update_low_value` 和 `update_low` 对 `Closed`、`TreeEdgesAreGraphEdges`、`StackNoDup` 的保持 lemma。
2. 尝试证明 `current_active_edge_not_tree`。
3. 如果第 2 步不可证，最小加入 `ProcessedTreeChild u done s`，并证明它在 `preloop`、`set_fa pending`、visited 分支、tree child 返回后保持。
4. 证明 visited-inactive 的 `inactive_done_no_new_target`，这是 `Closed` 支持 Low 的核心 lemma。
5. 证明 visited-active 的 `LowCorrect_add_active_direct`。
6. 设计并证明 child recursion 的 `ChildContributionContract`。
7. 证明 `LowCorrect_add_child_contribution`。
8. 组合 `ProcessEdgePreservesLoopCoreInv`。
9. 补 `LoopAuxFacts` 的对应保持，组合成 `ProcessEdgePreservesLoopInv`。
10. 用 `Hoare_forset` 组合出 `EdgeLoopPreservesLoopInv`。

## 11. 风险与阻塞条件

1. 当前最大风险是 `~ tree_edge s u v` 的来源。如果不能证明，必须补 visited-only child accounting；不要回到上一版会被 `set_fa` 临时破坏的强 `fa_not_done_implies_eq_u`。
2. tree-child 分支不能直接要求递归后仍有 `RootLowCorrect v`，因为 `W v` 包含 `maybe_pop`。必须把 child 对 parent 的贡献分成 active / inactive 两种 postcondition。
3. `Closed` 只应在 visited-inactive 和 child-popped/no-target 证明中使用；不要把 `NoUnvisitedReach` 混入核心 closedness。
4. `LoopCoreInv` 不应新增 stack order、NoDup、pop segment 等字段；这些仍属于 `LoopAuxFacts` 或 pop-local proof cut。
5. 若某个证明必须修改 `PartialActiveTarget` 的语义，必须先回到 `chain.md` 重新讨论，因为它已经被确定为 `Targets(PartialTree(u,i))` 的正式对应物。

## 12. 完成标准

本阶段完成时应至少得到：

```coq
ProcessEdgePreservesLoopCoreInv
ProcessEdgePreservesLoopInv
EdgeLoopPreservesLoopInv
```

并满足：

1. `Closed` 在 edge loop 内只作为已有事实使用，不被替换为其它 closedness 定义。
2. `LowCorrect` 的三个分支证明分别对应 `chain.md` 的 active target、inactive skip、tree child contribution。
3. 没有重新引入上一版的大型 suspended/frame predicate。
4. 不新增 `Admitted` 或 `Axiom`。
5. `Tarjan_scc_is_low.v` 仍可由 `_tarjan_is_low_only.mk` 编译通过。
