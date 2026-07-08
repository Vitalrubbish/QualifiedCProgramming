# Tarjan-Directed-SCC-Output-Correctness-Proof-Plan
**Author**: Codex
**Date**: 2026-07-08

## 1. 目标范围

本文档覆盖 Tarjan directed Monad 程序的下一层正确性：从已经完成的 low-link / closedness 证明，推进到 `sccs` 输出列表满足数学 SCC 规格。

当前已经完成的基础结论是：

```coq
tarjan_scc_satisfies_visit_contract:
  VisitContract (tarjan_scc g).
```

其中 `VisitMainContract` 给出：

```coq
Hoare
  (EntryPre u)
  (tarjan_scc g u)
  (fun _ s => RootFinal u s).
```

而：

```coq
RootFinal u s :=
  wf_scc_state g root s /\
  NoUnvisitedReach s /\
  Closed s /\
  scc_is_low_v s u.
```

下一层不应继续加强 `LoopInv` 或 `RootFinal` 来携带输出列表性质。输出正确性应作为独立层，复用 low-link 层给出的 `RootPopBranchPre`、`RootPopCuts`、`Closed`、`NoUnvisitedReach` 和 `scc_is_low_v`。

最终目标建议为：

```coq
tarjan_scc_all_outputs_scc_partition:
  Hoare
    (fun s => s = initSt)
    (tarjan_scc_all g)
    (fun _ s => scc_partition g (sccs s)).
```

如果后续 C refinement 只需要单次 DFS root 的局部输出，也可以先证明一个局部版本；但完整 Tarjan SCC 输出正确性应以 `tarjan_scc_all` 和 `scc_partition` 为最终规格。

## 2. 已有可复用定义

SCC 数学规格已经在 `SCC_basic.v` 中给出：

```coq
is_SCC g C :=
  (exists v, C v /\ original_vvalid g v) /\
  (forall u v, C u -> C v -> mutually_reachable g u v) /\
  (forall u v, C u -> original_vvalid g v -> mutually_reachable g u v -> C v).

scc_partition g sccs :=
  (forall v, original_vvalid g v -> exists C, In C sccs /\ C v) /\
  (forall C, In C sccs -> is_SCC g C) /\
  (forall C1 C2 v,
     In C1 sccs -> In C2 sccs -> C1 v -> C2 v ->
     forall w, C1 w = C2 w).
```

Tarjan 程序中 `pop_scc_state` 新增的 SCC 正是 pre-pop 栈段：

```coq
pop_scc_state s u :=
  let '(popped, rest) := stack_split_at (stack s) u in
  s <| stack ::= fun _ => rest |>
    <| sccs ::= fun sccs0 => (fun v => In v popped) :: sccs0 |>.
```

在 low-link 层已经定义：

```coq
PoppedSegment u s x
RestStack u s x
RootPopBranchPre u s
RootPopCuts u s
PoppedSegmentClosed u s
PoppedSegmentNoActiveReach u s
RootTraversalComplete u s
```

这些定义应作为输出正确性的桥接入口。

## 3. 输出层核心谓词

建议新增输出层谓词，而不是污染 low-link 核心不变量：

```coq
Definition SCCsSound (s: St): Prop :=
  forall C, In C (sccs s) -> is_SCC g C.

Definition SCCsCoverSettled (s: St): Prop :=
  forall v,
    Visited v s ->
    ~ Active v s ->
    exists C, In C (sccs s) /\ C v.

Definition SCCsOutputInv (s: St): Prop :=
  SCCsSound s /\
  SCCsCoverSettled s.
```

可选地，若证明 `scc_partition` 的第三项时需要局部化，也可以加入：

```coq
Definition SCCsDisjoint (s: St): Prop :=
  forall C1 C2 v,
    In C1 (sccs s) ->
    In C2 (sccs s) ->
    C1 v ->
    C2 v ->
    forall w, C1 w = C2 w.
```

但推荐优先不把 `SCCsDisjoint` 放入循环不变量。原因是 `SCCsSound` 已给出每个输出集合都是 `is_SCC`，两个 `is_SCC` 若有公共顶点，则可由 SCC 的 maximality / mutual reachability 推出 extensional equality。这样可以把 disjointness 放在最终组合阶段证明。

## 4. 第一关键桥：单次 pop 产出 SCC

最核心 theorem：

```coq
popped_segment_is_scc:
  forall u s,
    RootPopBranchPre u s ->
    RootPopCuts u s ->
    is_SCC g (PoppedSegment u s).
```

该 theorem 是输出正确性的中心。它应拆成三个方向。

### 4.1 非空性

目标：

```coq
popped_segment_nonempty_valid:
  RootPopBranchPre u s ->
  exists x, PoppedSegment u s x /\ original_vvalid g x.
```

证明思路：

1. `RootPopBranchPre` 包含 `RootPrePop`。
2. `RootPrePop` 包含 `LoopInv u (edge_set u) s` 和 `StackRestOlderThanRoot u s`。
3. `StackRestOlderThanRoot` 给出 `Active u s`。
4. `Active u s` 与 `PoppedSegment` 的 `stack_split_at` 结构推出 `PoppedSegment u s u`。
5. `LoopCoreShape` 中 `wf_scc_state` / `Visited u s` 加上图有效性辅助 lemma，推出 `original_vvalid g u`。

如果当前库没有 `Visited -> original_vvalid`，应从 `dfn_valid` / `state_to_dfs_tree_vvalid` / DFS tree validity 中补一个纯 helper。

### 4.2 内部互达

目标：

```coq
popped_segment_mutually_reachable:
  RootPopBranchPre u s ->
  RootPopCuts u s ->
  forall x y,
    PoppedSegment u s x ->
    PoppedSegment u s y ->
    mutually_reachable g x y.
```

推荐拆成两个 root-relative lemma：

```coq
popped_segment_reachable_from_root:
  RootPopBranchPre u s ->
  forall x,
    PoppedSegment u s x ->
    dg_reachable g u x.

popped_segment_reaches_root:
  RootPopBranchPre u s ->
  RootPopCuts u s ->
  forall x,
    PoppedSegment u s x ->
    dg_reachable g x u.
```

然后用 `dg_reachable_trans` 组合：

```coq
x -> u -> y
y -> u -> x
```

其中 `popped_segment_reachable_from_root` 应较直接：

1. `PoppedSegment u s x` 表示 `x` 在 `u` 到栈顶的 segment 中。
2. 对 Tarjan DFS 栈结构证明：该 segment 中每个点属于 `u` 的 DFS 子树。
3. 从 `dg_reachable (state_to_dfs_tree g s root) u x` 用 `TreeEdgesAreGraphEdges` 提升到 `dg_reachable g u x`。

难点是 `popped_segment_reaches_root`。

关键思路：

1. 若 `x = u`，显然成立。
2. 若 `x <> u`，证明 `low s x < dfn s x`，并利用 `scc_is_low_v s x` 的 attained minimum 语义提取一个实际 low target。
3. 该 target 必须是 active，且不能落到 `RestStack u s`，否则与 `PoppedSegmentNoActiveReach` 或 `low[u] = dfn[u]` 的 cut 矛盾。
4. 因此 target 仍在 `PoppedSegment u s` 中，且 dfn 更小。
5. 沿 dfn 严格下降迭代，最终到达 dfn 最小的 segment root `u`。

这一步建议不要直接做“递归链”证明。更稳的形式是先证明一个局部下降 lemma：

```coq
popped_nonroot_has_lower_popped_target:
  RootPopBranchPre u s ->
  RootPopCuts u s ->
  forall x,
    PoppedSegment u s x ->
    x <> u ->
    exists y,
      PoppedSegment u s y /\
      dfn s y < dfn s x /\
      dg_reachable g x y.
```

再用 `dfn` 良基下降推出 `x` 可达某个没有更低 popped target 的点；最后由 `StackRestOlderThanRoot` 和 stack dfn order 证明该点只能是 `u`。

这是整个输出正确性层的最大风险点，应优先实现。

### 4.3 极大性

目标：

```coq
popped_segment_maximal:
  RootPopBranchPre u s ->
  RootPopCuts u s ->
  forall x y,
    PoppedSegment u s x ->
    original_vvalid g y ->
    mutually_reachable g x y ->
    PoppedSegment u s y.
```

证明思路：

1. 由 `mutually_reachable g x y` 得到 `dg_reachable g x y`。
2. 由 `PoppedSegmentClosed u s` 得到 `Visited y s`。
3. 对 `y` 分类：
   - 若 `Active y s`，由栈分段和 `PoppedSegmentNoActiveReach` 排除 `RestStack u s y`，所以 `y` 必在 popped segment。
   - 若 `~ Active y s`，由 `Closed s` 或已 settled 的覆盖/封闭事实排除其与 active popped 点互达但不在 segment 的情况。
4. 若需要处理 “visited inactive 但不是当前 segment” 的旧 SCC，使用 `Closed`：inactive visited 点若可达 active popped 点，与 `Closed` 矛盾。

注意：这里正是 low-link 层已经证明的 `RootPopCuts` 发挥输出语义作用的地方。

## 5. 第二关键桥：pop_scc 保持输出不变量

证明：

```coq
pop_scc_preserves_sccs_sound:
  Hoare
    (fun s =>
       SCCsSound s /\
       RootPopBranchPre u s /\
       RootPopCuts u s)
    (pop_scc u)
    (fun _ s => SCCsSound s).
```

证明思路：

1. 展开 `pop_scc_state`。
2. 新 cons 的集合是 `PoppedSegment u s_before`。
3. 用 `popped_segment_is_scc` 证明新集合是 `is_SCC`。
4. 旧 `sccs` 元素由 `SCCsSound s_before` 保持。

覆盖 settled：

```coq
pop_scc_preserves_cover_settled:
  Hoare
    (fun s =>
       SCCsCoverSettled s /\
       RootPopBranchPre u s /\
       RootPopCuts u s)
    (pop_scc u)
    (fun _ s => SCCsCoverSettled s).
```

证明思路：

1. pop 后 inactive 的点分两类。
2. 若在新 popped segment 中，则由新 cons 的 SCC 覆盖。
3. 若不在新 segment 中，则它在 pop 前已经 inactive，用旧 `SCCsCoverSettled` 覆盖。
4. 需要 stack split 的 membership lemma：pop 后不 active 且不是新 popped segment 的 visited 点，pop 前也不 active。

组合：

```coq
pop_scc_preserves_output_inv:
  Hoare
    (fun s =>
       SCCsOutputInv s /\
       RootPopBranchPre u s /\
       RootPopCuts u s)
    (pop_scc u)
    (fun _ s => SCCsOutputInv s).
```

## 6. 非 pop 操作保持输出不变量

这些证明应简单：

```coq
preloop_preserves_output_inv:
  Hoare SCCsOutputInv (preloop u) (fun _ s => SCCsOutputInv s).

set_fa_preserves_output_inv:
  Hoare SCCsOutputInv (set_fa v p) (fun _ s => SCCsOutputInv s).

update_low_preserves_output_inv:
  Hoare SCCsOutputInv (update_low u n) (fun _ s => SCCsOutputInv s).
```

注意 `preloop` 会让一个新点从 unvisited 变成 active，所以它不会新增 settled 点；`SCCsCoverSettled` 保持。

`maybe_pop` 的输出不变量保持应复用 low-link 层的分支结构：

```coq
maybe_pop_preserves_output_inv:
  Hoare
    (fun s =>
       SCCsOutputInv s /\
       RootPreMaybePop u s)
    (If (fun s => low s u = dfn s u) (pop_scc u))
    (fun _ s => SCCsOutputInv s).
```

pop 分支通过：

```coq
root_pre_maybe_pop_low_eq_derives_pop_cuts:
  RootPreMaybePop u s ->
  low s u = dfn s u ->
  RootPopCuts u s.
```

skip 分支状态不变。

## 7. Visit 层输出 contract

新增输出层递归 contract：

```coq
Definition VisitOutputContract (W: RecProgram): Prop :=
  forall u,
    Hoare
      (fun s => EntryPre u s /\ SCCsOutputInv s)
      (W u)
      (fun _ s => RootFinal u s /\ SCCsOutputInv s).
```

然后证明：

```coq
tarjan_scc_f_preserves_output_contract:
  VisitContract W ->
  VisitOutputContract W ->
  VisitOutputContract (tarjan_scc_f g W).

tarjan_scc_satisfies_output_contract:
  VisitOutputContract (tarjan_scc g).
```

证明结构与 `VisitContract` 类似：

1. `preloop` 保持 `SCCsOutputInv`。
2. edge loop 中：
   - visited-active / visited-inactive 分支不改 `sccs`；
   - unvisited child 分支由 `VisitOutputContract W` 保持输出不变量。
3. maybe_pop 阶段由 `maybe_pop_preserves_output_inv` 保持输出不变量，同时已有 `maybe_pop_produces_root_final` 给出 `RootFinal`。
4. 最后用 finite approximation induction 关闭 `Lfix`，与 `tarjan_scc_satisfies_visit_contract` 的证明模式一致。

## 8. Outer loop：从 visit 正确性到全图 partition

`tarjan_scc_all` 的定义是：

```coq
forset (fun v => original_vvalid g v)
       (fun v => If (fun s => ~ v ∈ visited s) (tarjan_scc v)).
```

最终组合需要一个 outer-loop invariant：

```coq
Definition AllOutputInv (s: St): Prop :=
  wf_scc_state_all_roots s /\
  NoUnvisitedReach s /\
  Closed s /\
  TreeEdgesAreGraphEdgesAllRoots s /\
  OrderFacts s /\
  SCCsOutputInv s /\
  stack s = nil.
```

这里不一定真的要定义 `wf_scc_state_all_roots` 或 `TreeEdgesAreGraphEdgesAllRoots`；如果当前库的 `wf_scc_state g root` 仍带固定 root，则 outer loop 证明可能需要把 low-link 层定理以每次启动 root `u` 的方式实例化，而不是维护一个全局固定 root。

关键新增 lemma：

```coq
outer_root_visit_returns_empty_stack:
  Hoare
    (fun s => EntryPre u s /\ SCCsOutputInv s /\ stack s = nil)
    (tarjan_scc g u)
    (fun _ s => RootFinal u s /\ SCCsOutputInv s /\ stack s = nil).
```

原因：

1. 递归 child 调用返回时 child 可能仍 active，因为 parent 还在栈下方。
2. outer root 启动时栈为空；若 root 没有被 pop，则 root 仍 active，和 `RootFinal` 中 `Closed` / `scc_is_low_v` 并不能直接矛盾。
3. 需要证明 outer root 最终满足 pop 条件，或证明从空栈启动后若 root active 则 `low[root] = dfn[root]`。

完成 outer root empty-stack 后，`tarjan_scc_all` 维护：

```coq
SCCsOutputInv s /\ stack s = nil
```

同时复用已有：

```coq
tarjan_scc_all_visited_all:
  Hoare
    (fun _ => True)
    (tarjan_scc_all g)
    (fun _ s => forall v, original_vvalid g v -> Visited v s).
```

## 9. 从输出不变量到 scc_partition

最终 bridge：

```coq
output_inv_to_scc_partition:
  (forall v, original_vvalid g v -> Visited v s) ->
  stack s = nil ->
  SCCsOutputInv s ->
  scc_partition g (sccs s).
```

证明：

1. Coverage：
   - `original_vvalid g v` 推出 `Visited v s`。
   - `stack s = nil` 推出 `~ Active v s`。
   - 用 `SCCsCoverSettled` 得到 `exists C, In C (sccs s) /\ C v`。
2. Correctness：
   - 直接用 `SCCsSound`。
3. Disjointness：
   - 若 `C1 v` 且 `C2 v`，由 `SCCsSound` 得到 `is_SCC g C1` 和 `is_SCC g C2`。
   - 对任意 `w`，由 `C1 w` 和 `C1 v` 得到 `mutually_reachable g w v`，再用 `C2 v` 和 `is_SCC_closed_under_mr` 得到 `C2 w`。
   - 反向同理。
   - 用 propositional extensionality 或 `is_SCC_extensional` 得到 `forall w, C1 w = C2 w`。

## 10. 推荐实现顺序

1. `[done]` 新建输出正确性文件。实际文件名为 `Tarjan_scc_correctness.v`，已导入 `SCC_basic`、`Tarjan_scc`、`Tarjan_scc_basics`、`Tarjan_scc_is_dfn`、`Tarjan_scc_is_low`。
2. `[done]` 定义 `SCCsSound`、`SCCsCoverSettled`、`SCCsOutputInv`。实现中额外定义了输出层所需的 `VisitedValid`、`AllVerticesVisited`、`SCCsPartitionReady`。
3. `[done]` 证明 `PoppedSegment u s u`、`PoppedSegment` 非空、segment 内顶点 active / visited / valid 的基础栈 lemma。非空和 valid 证明依赖输出层新增的 `VisitedValid`。
4. `[done as bridge]` 证明 `popped_segment_reachable_from_root`。实现中新增 `PoppedSegmentInPartialTree`，并证明了 `popped_segment_tree_reachable_from_partial_tree`、`popped_segment_in_partial_tree_from_tree_reachable` 与 `popped_segment_tree_reachable_lifts_to_graph`；后续输出层只需维护更直接的 `PoppedSegmentTreeReachableFromRoot` 字段。
5. `[done as bridge]` 证明 `popped_nonroot_has_lower_popped_target`。实现中新增 `PoppedSegmentPendingLow`，并证明 `popped_nonroot_has_lower_popped_target_from_pending_low`：从每个非 root popped 成员的 `scc_is_low_v` 且 `low <> dfn` 产生更低的 popped target。
6. `[done]` 证明 `popped_segment_reaches_root`。实现为 `popped_segment_reaches_root_from_lower_targets`，用 dfn 良基下降把第 5 步的局部下降 cut 提升为全段到 root 的可达性。
7. `[done under cuts]` 组合 `popped_segment_mutually_reachable`。实现为 `popped_segment_members_mutually_reachable`，前提为 `PoppedSegmentReachableFromRoot` 与 `PoppedSegmentReachesRoot`。
8. `[done]` 证明 `popped_segment_maximal`。实现为 `popped_segment_maximal`，由 `RootPopBranchPre`、`RootPopCuts`、`Closed` 和栈分段分类推出。
9. `[done under cuts]` 组合 `popped_segment_is_scc`。实现为 `popped_segment_is_scc_from_reachability_cuts`，前提为 `VisitedValid`、`RootPopBranchPre`、`PoppedSegmentReachableFromRoot`、`PoppedSegmentReachesRoot`、`PoppedSegmentMaximal`。
10. `[done under cuts]` 证明 `pop_scc_preserves_sccs_sound`。实现包括 `pop_scc_preserves_sccs_sound_from_new_scc`、`pop_scc_preserves_sccs_sound_from_reachability_cuts`、`pop_scc_preserves_sccs_sound_from_tree_reachability_cuts`、`pop_scc_preserves_sccs_sound_from_core_cuts`，以及面向后续递归输出层字段的 `pop_scc_preserves_sccs_sound_from_tree_and_pending_low`。
11. `[done]` 证明 `pop_scc_preserves_cover_settled`。该证明只依赖 `pop_scc_state` 的栈分段效果：popped 段内顶点由新 cons 的集合覆盖，popped 段外且 pop 后 inactive 的顶点在 pop 前已 inactive，由旧 `SCCsCoverSettled` 覆盖。
12. `[done as consumer]` 组合 `maybe_pop_preserves_output_inv`。实现为 `maybe_pop_preserves_output_inv_from_tree_and_pending_low`：pop 分支用 `root_pre_maybe_pop_low_eq_derives_pop_cuts` 产生 `RootPopCuts`，再消费 `PoppedSegmentTreeReachableFromRoot` 与 `PoppedSegmentPendingLow`；skip 分支状态不变。后续递归 / edge-loop 层仍需生产这两个输出层字段。
13. `[done]` 证明 `tarjan_scc_f_preserves_output_contract`。当前已在实现中补出输出层 producer 字段：
    `LoopOutputReady`、`RootOutputReady`、`RootActiveOutputReady`、`VisitOutputContract`、`VisitChildOutputContract`、`VisitOutputFrameContract`；
    已证明 preloop 初始化 `LoopOutputReady u ∅`，`process_edge` 在加强后的 `VisitChildOutputContract` 假设下保持输出字段，edge-loop 产出 `RootOutputReady`，并组合出 `tarjan_scc_f_produces_root_output_post`。实现中新增并加强 `ParentOutputFrameForChild`，加入“旧 parent segment 不含递归 child”的保护字段，以及“child 仍 active 时旧 parent partial-tree 成员位于 child 下方”的 rest 保护字段；同时新增 `NestedOutputFramePre` 中“旧 ancestor segment 不含当前 loop_root”的保护字段。已证明 `set_fa` / `update_low` / `process_edge` / `edge_loop` 对 direct 与 external output-frame 的保持；同时补出 `pop_scc_state_preserves_scc_is_low_v_for_rest_low`，证明 pop root 时 rest 中 pending-low 顶点的 low witness 仍留在 rest 中，并据此完成 direct 与 external `maybe_pop` 对 `ParentOutputFrameForChild` 的保持。本轮已补出 direct preloop output-frame 建立、external/nested preloop output-frame 保持、`tarjan_scc_f_produces_child_output_contract` / `tarjan_scc_f_preserves_child_output_contract`、`tarjan_scc_f_preserves_output_frame_contract`，以及 root+child+frame aggregate theorem `tarjan_scc_f_preserves_output_contracts`。
14. `[done]` 用 finite approximation induction 证明 `tarjan_scc_satisfies_output_contract`。实现中新增 `empty_rec_program_satisfies_output_contracts`、`tarjan_scc_iter_satisfies_output_contracts` 与 `tarjan_scc_satisfies_output_contracts`，结构镜像 low 层 `tarjan_scc_iter_satisfies_visit_contract`。
15. `[done]` 证明 outer root empty-stack lemma。实现中新增 `RootBottom` proof-only cut、`VisitChildRootBottomContract`，并证明 `outer_root_visit_returns_empty_stack`。
16. `[done]` 证明 `tarjan_scc_all` 保持 `SCCsOutputInv /\ stack = nil`。实现中新增 `FaEdges`、`OuterShape`，并证明 `tarjan_scc_all_preserves_output_inv_and_empty_stack`。
17. `[done]` 证明 `output_inv_to_scc_partition`。
18. `[done]` 组合 `tarjan_scc_all_outputs_scc_partition`。

## 11. 风险与边界

1. 最大风险是 `popped_segment_reaches_root`。如果这一步直接证明困难，应先证明 dfn 下降链，而不是把新字段加入 low-link `LoopInv`。
2. `RootFinal` 不建议增加 `SCCsOutputInv`。这会混淆“单次 visit 的 low-link postcondition”和“输出列表全局不变量”。
3. `SCCsDisjoint` 不建议先加入 invariant。优先在最终 `scc_partition` bridge 中由 `SCCsSound` 和 `is_SCC` maximality 推出。
4. outer loop 不应复用固定 `root` 的全局定理强行证明全图。每次启动 `tarjan_scc u` 时，应以当前 `u` 作为本轮 DFS root 实例化 low-link theorem。
5. 如果证明需要修改 `SCC_basic.v` 中 `is_SCC` 或 `scc_partition` 的定义，应先暂停评估。输出正确性层应适配已有数学规格，而不是重定义 SCC。

## 12. Monad 层完成标准

抽象 Monad 程序正确性完成应至少包含：

```coq
tarjan_scc_satisfies_visit_contract:
  VisitContract (tarjan_scc g).

tarjan_scc_all_outputs_scc_partition:
  Hoare
    (fun s => s = initSt)
    (tarjan_scc_all g)
    (fun _ s => scc_partition g (sccs s)).
```

第一条说明 low-link / closedness / recursion contract 正确；第二条说明最终输出 `sccs` 是原图的 SCC partition。

完成这两条后，Monad 算法层的数学正确性可以视为闭合。后续 C refinement proof 只需要证明 C 程序的具体状态、数组、栈、输出编码 refinement 到该 Monad 程序及其状态字段。
