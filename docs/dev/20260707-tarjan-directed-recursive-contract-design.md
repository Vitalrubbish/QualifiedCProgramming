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
  dfn s parent < dfn s child.
```

`Edge parent child` 放在 frame 中是为了让后续 `ChildReturnPreMaybePop` 和 `ChildContributionContract` 的组合不再依赖外层散落字段。即使现有 `process_edge` theorem 的 postcondition 仍额外携带 `Edge parent child`，这个冗余是无害的，并且有利于局部证明。

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
         ParentFrameForChild ancestor current ancestor_done s_before s).
```

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
  -- edge_loop next, using VisitChildContract W and VisitFrameContract W -->
LoopInv next (edge_set next)
ParentFrameForChild ancestor current ancestor_done s_before
  -- maybe_pop next -->
ParentFrameForChild ancestor current ancestor_done s_before
```

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

1. `ParentLowFrame` 在 `preloop child` 中不是纯字段保持；必须证明 child 新入栈不会改变 parent 旧 `done` 的 candidate 集合。
2. `ParentLowFrame` 在 child edge loop 中需要 nested recursion frame preservation；这就是 `VisitFrameContract` 存在的理由。
3. `ParentFrameForChild` 不能吸收 parent 的 `LowCorrect parent (done_after done child)`，否则会在 parent 执行 `update_low` 之前要求过强结论。
4. `RootFinal` 不应携带 parent frame；否则当前调用主线和父调用返回线会被混在一起。
5. 若某个证明需要把 `ParentFrameForChild` 或 pop-local cuts 加进 `LoopInv`，说明 predicate 边界错误，应调整递归层 bridge，而不是扩大核心不变量。
