# Tarjan-Directed-Recursive-Contract-Design
**Author**: Codex
**Date**: 2026-07-07

## 1. 目标

递归层不能只证明当前调用的公开后置条件：

```coq
EntryPre u -- W u --> RootFinal u
```

在 parent 的 unvisited tree-child 分支中，递归调用还必须返回 child 对 parent low 的贡献：

```coq
ParentRecursivePre parent child done
-- W child -->
ChildContributionContract parent child done s_before s_after
```

同时，为了在证明 child 的 edge loop 时处理 nested recursive call，还需要一条 frame-preservation 线：当正在证明 child 调用时，grandchild 的递归调用不能破坏外层 parent-child frame。

因此递归层 contract 应是三条线的合取：

```text
main correctness
immediate-child contribution
outer parent-frame preservation
```

这三条线都是递归层接口；它们不应加入 `LoopInv`。

## 2. 不变量边界

核心循环不变量保持不变：

```coq
LoopCoreInv u done s :=
  LoopCoreShape u done s /\
  Closed s /\
  LowCorrect u done s.

LoopInv u done s :=
  LoopAuxFacts u s /\
  LoopCoreInv u done s.
```

其中 `LoopInv` 只描述当前 vertex 的 neighbour loop。父调用 frame、递归返回贡献、pop-local cut 都不属于 `LoopInv`。

递归层新增 predicate 的职责是桥接不同阶段的 Hoare 前后条件：

```text
set_fa -> preloop -> edge_loop -> maybe_pop -> recursive postcondition
```

## 3. 当前已有接口

当前调用入口：

```coq
EntryPre u s.
```

edge loop 后进入 maybe_pop 的当前调用前置条件：

```coq
RootPrePop u s :=
  LoopInv u (edge_set u) s /\
  StackRestOlderThanRoot u s.
```

当前调用公开后置条件：

```coq
RootFinal u s :=
  wf_scc_state g root s /\
  NoUnvisitedReach s /\
  Closed s /\
  scc_is_low_v s u.
```

父调用消费的递归返回接口：

```coq
ChildContributionContract parent child done s_before s_after.
```

当前 `ChildContributionContract` 必须保留：

```coq
LoopCoreShape parent (done_after done child) s_after
```

而不是 `LoopCoreShape parent done s_after`。原因是 child 返回后已经 `Visited child` 且 `fa child = parent`，parent 的 shape 必须已经把 child 计入 processed tree child；parent 的 low 更新则仍由返回后的 `update_low parent low[child]` 完成。

## 4. 阶段 predicate 设计

### 4.1 `ParentRecursivePre`

`set_fa child parent` 后，调用 `W child` 前的前置条件：

```coq
Definition ParentRecursivePre
  (parent child: V) (done: V -> Prop) (s: St): Prop :=
  LoopInv parent done s /\
  Edge parent child /\
  EntryPre child s /\
  fa s child = parent /\
  fa s child <> child.
```

这个 predicate 对应 process-edge unvisited 分支中：

```coq
set_fa child parent;;
W child;;
```

它既提供 child 的 `EntryPre`，也保留 parent low 更新后续需要的 `LoopInv parent done` 与 `Edge parent child`。

### 4.2 `ParentFrameForChild`

child 已经过 `preloop` 进入自己的调用后，外层 parent 需要被保留的 frame：

```coq
Definition ParentFrameForChild
  (parent child: V) (done: V -> Prop)
  (s_before s: St): Prop :=
  ParentLowFrame parent done s_before s /\
  LoopCoreShape parent (done_after done child) s /\
  LoopAuxFacts parent s /\
  Closed s /\
  TreeEdgesAreGraphEdges s /\
  Edge parent child /\
  Visited child s /\
  fa s child = parent /\
  fa s child <> child /\
  dfn s parent < dfn s child /\
  ~ done child.
```

`Edge parent child` 放在 frame 中是为了让后续 `ChildReturnPreMaybePop` 和 `ChildContributionContract` 的组合不再依赖外层散落字段。即使现有 `process_edge` theorem 的 postcondition 仍额外携带 `Edge parent child`，这个冗余是无害的，并且有利于局部证明。

`~ done child` 是 frame 的 freshness 字段：`done` 表示 parent 在调用当前 child 之前已经处理过的 outgoing edge 集合，当前 child 尚未被计入这部分。它用于构造 immediate nested call 的 `NestedFrameDisjoint parent child child done s`，避免旧 sibling 子树和当前 child 子树在 frame-preservation 证明中被混淆。

`ParentLowFrame` 的职责不是证明 parent 旧 candidate 集完全双向不变。它应表达两件足以服务 parent low 更新的事实：

```text
1. pre-state 中已有的 parent old candidates 在 post-state 中仍存在，且 dfn 不变；
2. post-state 中任何 parent old candidate，其 dfn 不小于旧 low[parent]。
```

这样可以覆盖 `preloop child` 后 child 新入栈造成的新 active target：即使它是新的 candidate，只要它不会低于旧 `low[parent]`，就不会破坏 parent old part 的 `LowComplete`。

这个 predicate 不能要求：

```coq
LoopInv parent (done_after done child) s
```

因为 child 返回前 parent 尚未执行：

```coq
low[parent] := min(low[parent], low[child])
```

所以 parent 的 `LowCorrect parent (done_after done child)` 还不成立。

### 4.3 `ChildReturnPreMaybePop`

child 的 edge loop 结束后，进入 child 自己的 maybe_pop 前：

```coq
Definition ChildReturnPreMaybePop
  (parent child: V) (done: V -> Prop)
  (s_before s: St): Prop :=
  RootPrePop child s /\
  ParentFrameForChild parent child done s_before s.
```

这是 `maybe_pop` 产生 `ChildContributionContract` 的直接前置条件。

### 4.4 `NestedFramePre`

证明 `ParentFrameForChild parent child done s_before` 在 edge loop 中保持时，当前 loop root 可能继续递归调用一个未访问 child。此时需要给这次 `W next` 一条 frame-preservation 前置条件：

```coq
Definition NestedFramePre
  (ancestor current loop_root next: V)
  (ancestor_done loop_done: V -> Prop)
  (s_before s: St): Prop :=
  LoopInv loop_root loop_done s /\
  ParentFrameForChild ancestor current ancestor_done s_before s /\
  NestedFrameDisjoint ancestor current loop_root ancestor_done s /\
  Edge loop_root next /\
  ~ loop_done next /\
  EntryPre next s /\
  fa s next = loop_root /\
  fa s next <> next.
```

这里：

```text
ancestor = 外层 parent
current  = frame 中需要保护的 ancestor 的 child
loop_root = 当前正在跑 edge loop 的 vertex
next     = loop_root 的 unvisited child, 即 nested recursive call 的 root
```

其中 `NestedFrameDisjoint ancestor current loop_root ancestor_done s` 是 proof-only 的外层 frame 分离条件：

```coq
dg_reachable (state_to_dfs_tree g s root) current loop_root /\
forall old_child,
  ancestor_done old_child ->
  fa s old_child = ancestor ->
  fa s old_child <> old_child ->
  ~ dg_reachable (state_to_dfs_tree g s root) old_child loop_root
```

第一部分说明当前递归调用发生在被保护的 `current` 子树内部；第二部分说明 `ancestor_done` 的旧 child 子树没有与这条 nested 调用路径合并。它不属于 `LoopInv`，只服务于递归 frame-preservation 线。没有这个条件，若 `loop_root = ancestor` 或旧 sibling 子树能经新 `preloop` 边到达 `next`，`preloop next` 后外层 `ParentFrameForChild ancestor current ...` 的 `ProcessedTreeChild` / `ParentLowFrame` 都可能变假。

`NestedFramePre` 不产生 child contribution。它只声明：在递归访问 `next` 的过程中，外层 `ParentFrameForChild ancestor current ...` 应被保留。

当用于 immediate parent frame 时，取 `loop_root = current`。当用于更深层的 frame preservation 时，`loop_root` 是当前更深的调用根，而 `current` 仍是被保护 frame 中的 child。

## 5. Strengthened `VisitContract`

当前调用主线：

```coq
Definition VisitMainContract (W: RecProgram): Prop :=
  forall u,
    Hoare
      (EntryPre u)
      (W u)
      (fun _ s => RootFinal u s).
```

immediate-child 返回线：

```coq
Definition VisitChildContract (W: RecProgram): Prop :=
  forall parent child done,
    Hoare
      (ParentRecursivePre parent child done)
      (W child)
      (fun _ s =>
         exists s_before,
           LoopInv parent done s_before /\
           Edge parent child /\
           ChildContributionContract parent child done s_before s).
```

保留 `exists s_before` 是为了直接匹配当前已经实现的：

```coq
unvisited_tree_child_branch_preserves_loop_inv
edge_loop_preserves_loop_inv
```

outer frame preservation 线：

```coq
Definition VisitFrameContract (W: RecProgram): Prop :=
  forall ancestor current loop_root next ancestor_done loop_done s_before,
    Hoare
      (NestedFramePre ancestor current loop_root next
         ancestor_done loop_done s_before)
      (W next)
      (fun _ s =>
         ParentFrameForChild ancestor current ancestor_done s_before s /\
         NestedFrameDisjoint ancestor current loop_root ancestor_done s).
```

后条件同时保留 `NestedFrameDisjoint`，因为 caller 的 `edge_loop loop_root` 还要继续处理后续 outgoing edge；下一次 unvisited 分支构造新的 `NestedFramePre ancestor current loop_root next2 ...` 仍需要这个 disjoint context。它仍然不属于 `LoopInv`，只属于递归 frame-preservation 线。

合并：

```coq
Definition VisitContract (W: RecProgram): Prop :=
  VisitMainContract W /\
  VisitChildContract W /\
  VisitFrameContract W.
```

`VisitFrameContract` 是递归证明需要的 proof-only contract。它不改变 parent low，不产生 `ChildContributionContract`，只服务于证明 child edge loop 保持外层 parent frame。

## 6. 三条 pipeline

当前调用主线：

```text
EntryPre u
  -- preloop u -->
LoopInv u ∅
  -- edge_loop u, using VisitChildContract W -->
LoopInv u (edge_set u)
  -- stack bridge -->
RootPrePop u
  -- maybe_pop u -->
RootFinal u
```

immediate-child 返回线：

```text
ParentRecursivePre parent child done
  -- preloop child -->
LoopInv child ∅
ParentFrameForChild parent child done s_before
  -- edge_loop child, using VisitChildContract W and VisitFrameContract W -->
LoopInv child (edge_set child)
ParentFrameForChild parent child done s_before
  -- stack bridge -->
ChildReturnPreMaybePop parent child done s_before
  -- maybe_pop child -->
ChildContributionContract parent child done s_before
```

outer frame preservation 线：

```text
NestedFramePre ancestor current loop_root next ancestor_done loop_done s_before
  -- preloop next -->
LoopInv next ∅
ParentFrameForChild ancestor current ancestor_done s_before
NestedFrameDisjoint ancestor current next ancestor_done
  -- edge_loop next, using VisitChildContract W and VisitFrameContract W -->
LoopInv next (edge_set next)
ParentFrameForChild ancestor current ancestor_done s_before
NestedFrameDisjoint ancestor current next ancestor_done
  -- maybe_pop next -->
ParentFrameForChild ancestor current ancestor_done s_before
NestedFrameDisjoint ancestor current loop_root ancestor_done
```

这里 `NestedFrameDisjoint ... next ...` 是 callee 自己的 edge-loop local context；`VisitFrameContract` 的最终 post 仍要求保留 caller 提供的 `NestedFrameDisjoint ... loop_root ...`。因此后续组合阶段需要并行处理这两个 disjoint：一个服务 callee 的 grandchild 递归调用，一个服务返回 caller 后继续 edge loop。

第三条线是第二条线能够穿过 nested recursive call 的关键。没有它，`edge_loop_preserves_parent_frame_for_child` 在 unvisited grandchild 分支只能假设 `W grandchild` 正确返回给 `current`，却无法说明它保持了外层 `ancestor-current` frame。

## 7. 与现有 theorem 的关系

已有：

```coq
preloop_initializes_loop_inv:
  Hoare (EntryPre u) (preloop u) (fun _ s => LoopInv u ∅ s).
```

已有：

```coq
edge_loop_preserves_loop_inv:
  (forall done v, ... ChildContributionContract u v done ...) ->
  Hoare
    (fun s => LoopInv u ∅ s)
    (forset (edge_set u) (process_edge u W))
    (fun _ s => LoopInv u (edge_set u) s).
```

应补包装：

```coq
edge_loop_preserves_loop_inv_from_visit_contract:
  VisitChildContract W ->
  Hoare
    (fun s => LoopInv u ∅ s)
    (forset (edge_set u) (process_edge u W))
    (fun _ s => LoopInv u (edge_set u) s).
```

还应补 frame 侧 theorem：

```coq
edge_loop_preserves_parent_frame_for_child:
  VisitChildContract W ->
  VisitFrameContract W ->
  Hoare
    (fun s =>
       LoopInv child ∅ s /\
       ParentFrameForChild parent child done s_before s)
    (forset (edge_set child) (process_edge child W))
    (fun _ s =>
       LoopInv child (edge_set child) s /\
       ParentFrameForChild parent child done s_before s).
```

## 8. 冻结建议

在实现 maybe_pop 之前，建议先冻结以下接口：

```coq
ParentRecursivePre
ParentFrameForChild
ChildReturnPreMaybePop
NestedFramePre
VisitMainContract
VisitChildContract
VisitFrameContract
VisitContract
```

冻结后，每个阶段只证明相邻 predicate 的桥接，而不是临时拼接长 conjunction。

## 9. 风险与处理策略

1. `ParentLowFrame` 在 `preloop child` 中不是纯字段保持；child 新入栈可能产生新的 active target，因此第三个字段只要求 post-state 的 parent old candidates 满足旧 `low[parent]` 下界。
2. `ParentLowFrame` 在 child edge loop 中需要 nested recursion frame preservation；这就是 `VisitFrameContract` 存在的理由。
3. `ParentFrameForChild` 不能吸收 parent 的 `LowCorrect parent (done_after done child)`，否则会在 parent 执行 `update_low` 之前要求过强结论。
4. `RootFinal` 不应携带 parent frame；否则当前调用主线和父调用返回线会被混在一起。
5. 若某个证明需要把 `ParentFrameForChild` 或 pop-local cuts 加进 `LoopInv`，说明 predicate 边界错误，应调整递归层 bridge，而不是扩大核心不变量。
