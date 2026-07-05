# Tarjan-Directed-Low-Sound-Complete-Loop-Invariant
**Author**: Codex
**Date**: 2026-07-05

## 1. 结论

`Tarjan_scc_is_low.v` 的 Phase 9 应按 `chain.md` 的联合归纳路线重构：

```text
preloop 初始化
  -> 边循环中证明 partial low_correctness
  -> loop done 得到 full low_correctness
  -> maybe_pop 用 full low_correctness 证明新弹出段 closed
  -> RootFinal 同时携带 low correctness 和 closedness
```

其中第二阶段的核心证明目标不是旧的
`LowFrontierCandidate + LowSourceCandidate` 弱组合，而是文档中所说的
`low_correctness`：

```text
low_correctness_partial u done s
  := low_is_sound_partial u done s /\
     low_is_complete_partial u done s
```

循环遍历过程中必须引入 `chain.md` 的 partial-tree 不变量：

```text
low[u] =
  min ({dfn[u]} union Targets(PartialTree(u, done)))
```

在 Coq 中不必一开始用集合最小值等式编码，可以先用等价的
sound/complete 双谓词编码，降低证明负担。

## 2. 旧实现的问题

当前 `LoopInvLowCandidate` 的 low 部分是：

```coq
PartialRootLowEquationCandidate u done s :=
  LowFrontierCandidate u done s /\
  LowSourceCandidate u done s.
```

这个设计只表达了两个弱事实：

- `LowFrontierCandidate`: 当前 `low u` 对已处理直接边的若干贡献是下界。
- `LowSourceCandidate`: 当前 `low u` 来自 `u`、某个已处理树孩子的 `low`，或某个已处理 active 边目标的 `dfn`。

它没有直接表达 `chain.md` 需要的完整 partial-tree 语义：

```text
所有已经被 PartialTree(u, done) 覆盖的 active target
都已经被 low[u] 吸收。
```

因此 active-child branch 被迫转向
`SegmentEscapeAccountingCandidate`、`ActiveTargetBlocksEscapeAccountedCandidate`
和 last-exit/path-exit accounting。这个方向可以证明某些局部 escape
事实，但它不是 low 计算本身的主不变量。它导致
`get_low_update_low_produces_phase7_accounting_after_child` 中的循环：

```text
要证明 active processed child 的 anchor 已经被 parent low 吸收，
又必须从 child summary 中取另一个 anchor，
如果这个 anchor 不比 parent 老，就继续需要路径截断。
```

这个循环说明缺少的是 partial low completeness，而不是还缺一个更复杂的
active-child accounting producer。

## 3. 新的 low_correctness 定义方向

先定义 partial-tree target。概念上：

```coq
PartialLowTargetCandidate u done s b :=
  b = u \/
  exists x,
    ProcessedTreeReachableFromCandidate u done s x /\
    dg_step g x b /\
    Active b s /\
    ~ dg_step (state_to_dfs_tree g s root) x b.
```

这里：

- `ProcessedTreeReachableFromCandidate u done s x` 是当前代码中已有的
  partial DFS tree 近似，可以作为 `PartialTree(u, done)` 的第一版实现。
- `b = u` 表示 `{dfn[u]}` 这个基础目标。
- 后半部分表示从 partial tree 中某个点走一条非 tree edge 到当前栈上点，
  即 `chain.md` 中的 `Targets(PartialTree(u, done))`。

然后定义两个方向：

```coq
LowIsCompletePartialCandidate u done s :=
  forall b,
    PartialLowTargetCandidate u done s b ->
    low s u <= dfn s b.

LowIsSoundPartialCandidate u done s :=
     low s u = dfn s u
  \/ exists b,
       PartialLowTargetCandidate u done s b /\
       low s u = dfn s b.

LowCorrectnessPartialCandidate u done s :=
  LowIsSoundPartialCandidate u done s /\
  LowIsCompletePartialCandidate u done s.
```

含义如下：

- `low_is_complete`: 没有漏掉任何 partial tree 已经能看到的 active target。
- `low_is_sound`: `low u` 不是伪造出来的过小值，它一定来自 `dfn u` 或一个合法 target。

这两个谓词合起来就是集合最小值等式的关系化版本：

```text
low[u] == min({dfn[u]} union Targets(PartialTree(u, done)))
```

## 4. 循环不变量

第二阶段的循环不变量应扩展为：

```coq
LoopInvLowCandidate u done s :=
  LoopInvDoneCandidate u done s /\
  LowCorrectnessPartialCandidate u done s.
```

Phase 6/7 仍然可以保留其他 closedness、child post、frame resume 字段：

```coq
LoopInvPhase6Candidate u done s :=
  LoopInvLowCandidate u done s /\
  ParentFrameResumeCandidate u done s /\
  DoneClosednessCandidate u done s /\
  ProcessedTreeChildrenCorrectCandidate u done s /\
  ActiveProcessedChildSegmentSummaryCandidate u done s.
```

但 `LoopInvLowCandidate` 的语义必须从旧的 frontier/source 替换为
partial low_correctness。旧字段最多作为兼容投影或中间 lemma，不应继续作为
Phase 9 主证明目标。

## 5. 边循环三个分支

### 5.1 visited-active 分支

程序执行：

```text
low[u] := min(low[u], dfn[v])
```

证明责任：

- `v` active 且 `u -> v`，所以 `v` 是新的合法
  `PartialLowTargetCandidate u (done_after done v) s v`。
- complete: 旧 target 用旧 complete；新 target 用 update 后的
  `low[u] <= dfn[v]`。
- sound: update 后的 `low[u]` 要么仍来自旧 sound，要么等于 `dfn[v]`。

### 5.2 visited-non-active 分支

程序跳过。

证明责任：

- 必须用 closedness 证明该边不会增加新的 active target。
- 当前代码里的 `settled_closed` / `DoneClosednessCandidate` 主要表达
  “reachable endpoint 已访问”，并不直接等于“不能 reach current stack”。
- 因此 combined closedness 需要增加或导出一个 no-active-reach 形态：

```coq
SettledNoActiveReachCandidate s :=
  forall v b,
    Visited v s ->
    ~ Active v s ->
    dg_reachable g v b ->
    Active b s ->
    False.
```

如果不保存这个形态，visited-non-active skip 的 low completeness 证明仍会卡住。
这个 no-active-reach 事实应由第三阶段 pop 通过 full low correctness 产生，
并作为后续循环的 closedness 输入使用。

### 5.3 unvisited tree-child 分支

程序执行：

```text
set_fa child u;;
visit child;;
low[u] := min(low[u], low[child])
```

递归调用的 postcondition 必须包含 child 的 full low_correctness：

```coq
LowCorrectnessDoneCandidate child s :=
  LowCorrectnessPartialCandidate child (edge_set child) s.
```

证明责任：

- complete:
  - 属于旧 `PartialTree(u, done)` 的 target，由 parent 旧 complete 处理。
  - 属于 child 完整 DFS tree 的 target，由 child complete 处理，再通过
    `low[u] := min(low[u], low[child])` 得到 parent complete。
- sound:
  - 如果 update 后仍取旧 `low[u]`，沿用 parent 旧 sound。
  - 如果 update 后取 `low[child]`，用 child sound 找到 child tree 中的合法 target，
    再用 bridge lemma 把它提升成
    `PartialLowTargetCandidate u (done_after done child) s b`。

这里需要的路径分解没有消失，但它只应出现在结构 bridge lemma 中：

```text
child target
  -> parent partial target after done_after child
```

不应继续埋在 active-child combined producer 内反复 last-exit。

## 6. loop done 到 root low_correctness

当 `done = edge_set u` 时，循环不变量给出：

```text
LowCorrectnessPartialCandidate u (edge_set u) s
```

这就是 root 的 full low correctness。后续可证明两个投影：

```coq
RootLowValidPrePopCandidate u s
RootIsLowPrePopCandidate u s
```

也就是当前公开 low spec：

```coq
scc_low_valid_v g root s u
scc_is_low_v g root s u
```

这一步需要把 `PartialLowTargetCandidate u (edge_set u) s` 与
`Tarjan_scc_low_defs.v` 中的 `scc_low_reachable` / `scc_low_tree` 对齐。
建议先证明双向 bridge lemma，再由 sound/complete 得到现有 public spec。

## 7. maybe_pop 中 closedness 依赖 low_correctness

第三阶段正是 `chain.md` 中 “Closedness 依赖 Low” 的位置。

若 `low[u] = dfn[u]`，并且要弹出以 `u` 为根的段，证明新 settled 段 closed：

1. 如果存在从 popped segment 到未访问点的路径，使用循环遍历完所有出边和
   visited-closure 类 closedness 反驳。
2. 如果存在从 popped segment 到更老 active 栈点 `b` 的路径，则由
   full `low_is_complete` 得到：

```text
low[u] <= dfn[b]
```

又由 stack order 得到：

```text
dfn[b] < dfn[u]
```

与 pop guard：

```text
low[u] = dfn[u]
```

矛盾。

因此 pop 后可产生更强的 closedness：

```text
new settled segment cannot reach unvisited vertices
new settled segment cannot reach remaining active stack vertices
```

后一个事实就是下一轮 visited-non-active skip 所需的
`SettledNoActiveReachCandidate`。

## 8. RootFinal 和 recursive postcondition

`RootFinalCandidate` 不应只携带旧的：

```coq
RootLowPrePopCandidate u s
SettledClosedCandidate s
```

它还应直接或间接携带：

```coq
LowCorrectnessDoneCandidate u s
SettledNoActiveReachCandidate s
```

推荐形状：

```coq
RootFinalCandidate u s :=
  GlobalShapeCandidate s /\
  SettledClosedCandidate s /\
  SettledNoActiveReachCandidate s /\
  Visited u s /\
  LowCorrectnessDoneCandidate u s /\
  RootLowPrePopCandidate u s /\
  OrderFactsCandidate s.
```

其中 `RootLowPrePopCandidate` 可以由 `LowCorrectnessDoneCandidate` 投影得到。
如果为了减少改动，也可以先保留现有字段，并新增一个
`RootLowCorrectnessCandidate u s` 字段。

## 9. 与 Phase 7 accounting 的关系

`SegmentEscapeAccountingCandidate`、`SegmentTreeCoverageByDoneCandidate` 和
`ActiveTargetBlocksEscapeAccountedCandidate` 不必立即删除，但它们不再是证明
low 的主路线。

新的职责划分是：

- low 主线由 `LowCorrectnessPartialCandidate` 负责。
- path decomposition 只服务于 target bridge：
  - old parent target 保持；
  - active direct target 加入；
  - child full target 提升为 parent partial target；
  - settled target 通过 no-active-reach 排除。
- Phase 7 accounting 若后续 SCC 输出正确性仍需要，可以在 low correctness
  完整闭合后作为下游证明继续使用。

这样 active-child branch 不再需要在 producer 中直接证明所有 escape accounting。
它只需要证明 child target 到 parent target 的结构提升，以及 `min` 更新对
sound/complete 的保持。

## 10. 实施顺序

1. 在 def 层新增 partial target 和 sound/complete 谓词：
   `PartialLowTargetCandidate`、`LowIsSoundPartialCandidate`、
   `LowIsCompletePartialCandidate`、`LowCorrectnessPartialCandidate`。
2. 新增 full 版本：
   `LowCorrectnessDoneCandidate u s :=
    LowCorrectnessPartialCandidate u (edge_set u) s`。
3. 新增或导出 closedness 的 no-active-reach 形态：
   `SettledNoActiveReachCandidate`，并把它纳入 combined invariant/post。
4. 将 `LoopInvLowCandidate` 的主语义替换为
   `LoopInvDoneCandidate /\ LowCorrectnessPartialCandidate`。
5. 分别证明三个循环分支的 low_correctness step：
   - empty/base；
   - visited-active；
   - visited-non-active；
   - unvisited tree-child。
6. 在 recursive postcondition 和 child contract 中加入
   `LowCorrectnessDoneCandidate child`。
7. 证明 loop done bridge：
   `LowCorrectnessPartialCandidate u (edge_set u) -> RootLowPrePopCandidate u`。
8. 重写 maybe_pop bridge：
   用 full `low_is_complete` 和 pop guard 产生 popped segment 的
   no-active-reach closedness。
9. 最后再决定是否将旧 `LowFrontierCandidate` / `LowSourceCandidate` 保留为
   投影 lemma，或从主线中移除。

## 11. 主要风险

1. `ProcessedTreeReachableFromCandidate` 是否足够精确表达
   `PartialTree(u, done)` 需要审计。如果不够，应新增更 path-sensitive 的
   partial tree predicate，而不是退回 readiness 路线。
2. 当前 `settled_closed` 只保证 settled 点可达处已访问，不足以直接证明
   visited-non-active 分支无 low 贡献。必须保存或导出 no-active-reach。
3. `LowIsSoundPartialCandidate` 在 tree-child 分支需要 child target 到 parent
   target 的 bridge lemma，这是路径分解真正应该出现的位置。
4. `LowIsCompletePartialCandidate` 在 pop 时需要 stack order 和 dfn injectivity
   来把 “remaining stack anchor” 转成 `dfn[b] < dfn[u]`。
5. 不应重新引入 readiness。child 的信息必须来自递归 postcondition 中的
   full low_correctness 和 closedness，而不是从一个尾部桥接猜测出来。

## 12. 判断标准

Phase 9 完成时应满足：

- 循环不变量中有 `chain.md` 的 partial low 不变量；
- 第二阶段已经证明 `low_correctness`，且显式拆成
  `low_is_sound` 和 `low_is_complete`；
- visited-active、visited-non-active、unvisited tree-child 三个分支都通过
  sound/complete step 证明；
- loop done 能推出 root full low correctness；
- maybe_pop 能用 full low correctness 产生后续循环需要的 closedness；
- 最终 low theorem 仍能投影到 `scc_low_valid_v` 和 `scc_is_low_v`，
  供后续 SCC 输出正确性证明使用。

## 13. 2026-07-05 实现同步

已落地到 `Tarjan_scc_is_low.v` 的 def 层：

```coq
SettledNoActiveReachCandidate
DoneNoActiveReachCandidate
PartialLowTreeReachableCandidate
PartialLowTargetCandidate
LowIsSoundPartialCandidate
LowIsCompletePartialCandidate
LowCorrectnessPartialCandidate
RootLowCorrectnessCandidate
LoopInvLowCorrectnessCandidate
LoopInvCombinedLowClosedCandidate
ChildLowCorrectnessForParentCandidate
ChildPostWithLowCorrectnessCandidate
```

`PartialLowTargetCandidate` 当前采用显式两类 target：

- 已处理的 root 直接 active edge；
- 已处理 tree child 的 DFS subtree 中的非 tree edge active target。

这比“任意 partial tree 点加 root 特判”的编码更适合当前证明，因为它不会把
child 的基础目标 `dfn[child]` 错误提升成 parent target。

已证明的基础 step：

- empty/base low correctness；
- old target 保持；
- visited-active 分支的 target 加入；
- visited-active 分支的 `LowIsSound` / `LowIsComplete` Hoare producer；
- visited-non-active 分支在 `SettledNoActiveReachCandidate` 前提下保持
  `LowCorrectnessPartialCandidate`；
- child back target 提升为 parent partial target。

## 14. 2026-07-05 后续实现同步

当前已继续落地以下主线证明，并且
`make -B -f _tarjan_is_low_only.mk SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.vo`
可通过：

- `set_fa_unvisited_preserves_low_correctness_partial_candidate`
- `set_fa_unvisited_preserves_tree_edges_are_graph_edges_candidate`
- `set_fa_unvisited_preserves_settled_no_active_reach_candidate`
- `set_fa_unvisited_preserves_loop_inv_done_candidate`
- `set_fa_unvisited_preserves_loop_inv_low_correctness_candidate`
- `set_fa_unvisited_creates_suspended_parent_frame_resume_candidate`
- `set_fa_unvisited_creates_suspended_loop_inv_combined_low_closed_candidate`
- `GetLowUpdateLowExtendsSuspendedLoopInvCombinedTreeCandidate_proof`
- `ProcessEdgeUnvisitedExtendsLoopInvCombinedLowClosedCandidate_proof`
- `ProcessEdgeExtendsLoopInvCombinedLowClosedCandidate_proof`
- `EdgeLoopDoneCombinedLowClosedCandidate_proof`

关键修正是把 suspended parent invariant 改成 path-sensitive 形态：

```coq
SuspendedLoopInvCombinedLowClosedCandidate parent child done s :=
  Edge parent child /\
  ~ done child /\
  fa s child = parent /\
  fa s child <> child /\
  LoopInvLowCorrectnessCandidate parent done s /\
  ...
```

原因是 `set_fa child parent` 之后、`child` 尚未加入 parent 的 `done` 时，
普通的

```coq
fa_not_done_implies_eq_u parent done
```

必然为假：`child` 是 `done` 外的唯一例外，但 `fa child = parent`。因此 tree
branch 不能先恢复普通 `LoopInvCombinedLowClosedCandidate parent done` 再执行
`low[parent] := min(low[parent], low[child])`。正确做法是新增 suspended 版
tree update：

```coq
GetLowUpdateLowExtendsSuspendedLoopInvCombinedTreeCandidate_proof
```

它从 `SuspendedLoopInvCombinedLowClosedCandidate parent child done` 直接产生

```coq
LoopInvCombinedLowClosedCandidate parent (done_after done child)
```

这样在 `done_after` 中 child 已经不再是例外，普通 frame 才能恢复。

当前仍未证明的 combined 入口是：

```coq
PreloopProducesLoopInvCombinedLowClosedInitialCandidate_statement
```

这不是战术问题，而是前提设计问题。现有 `EntryPreCandidate` 只有：

```coq
GlobalShapePreCandidate u s /\
SettledClosedCandidate s /\
OrderFactsCandidate s
```

它不足以推出 combined invariant 需要的两个字段：

```coq
TreeEdgesAreGraphEdgesCandidate s
SettledNoActiveReachCandidate s
```

两个错误路线必须避免：

- 不能从 `wf_scc_state` / `GlobalShapeCandidate` 推出
  `TreeEdgesAreGraphEdgesCandidate`。`wf_scc_state` 中的 `dfn_valid` 只说明 DFS
  tree edge 的 dfn 单调，不说明所有 `fa` tree edge 都是原图边；这个性质必须由
  `set_fa` 分支从 `Edge parent child` 维护，或作为入口前提给出。
- 不能从 `SettledClosedCandidate` 推出 `SettledNoActiveReachCandidate`。
  `settled_closed` 只保证 settled 点可达处已访问，不排除可达处仍在当前 stack 上。
  no-active-reach 必须由 pop 阶段结合 full low correctness 产生，或作为初始入口前提
  单独携带。

所以下一步正确方向不是回到旧 Phase7 accounting producer，而是选择一个入口方案：

1. 将 combined 入口改为更强 precondition，显式要求
   `TreeEdgesAreGraphEdgesCandidate` 和 `SettledNoActiveReachCandidate`；
2. 或证明/引入一个全局 root-level 初始化定理，说明初始状态或外层调用上下文已经满足这两个字段；
3. 然后再把最终 fixpoint interface 从旧 `LoopInvPhase7Candidate` 切到
   `LoopInvCombinedLowClosedCandidate`，并把 maybe_pop 的 closedness producer 接上。

## 15. 2026-07-05 最新实现同步：pop no-active producer

当前 `Tarjan_scc_is_low.v` 已经继续推进到 pop 阶段的 no-active closedness
producer，并且如下命令可通过：

```bash
eval "$(opam env)" && make -B -f _tarjan_is_low_only.mk SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.vo
```

已完成的 combined 主线包括：

- `CombinedEntryPreCandidate`
- `CombinedChildEntryCandidate`
- `PreloopProducesLoopInvCombinedLowClosedInitialCandidate_proof`
- `ProcessEdgeExtendsLoopInvCombinedLowClosedCandidate_proof`
- `EdgeLoopDoneCombinedLowClosedCandidate_proof`
- `LoopDoneProvidesRootLowCorrectnessCandidate_proof`

因此早先“preloop combined 入口尚未证明”的记录已经过期。正确状态是：
`EntryPreCandidate` 没有被错误加强；combined 入口使用单独的
`CombinedEntryPreCandidate` 携带：

```coq
EntryPreCandidate u s /\
TreeEdgesAreGraphEdgesCandidate s /\
SettledNoActiveReachCandidate s /\
(fa s u <> u -> Edge (fa s u) u)
```

新增并证明的 pop-stage 桥包括：

- `StackRestOlderThanRootCandidate`
- `PoppedSegmentNoActiveReachFromLowCandidate_statement/proof`
- `ProcessedTreeReachableFromCandidate_dfn_ge_root`
- `ProcessedTreeExitActiveBuildsPartialLowTargetCandidate`
- `StackRestOlderThanRootCandidate_from_nodup`
- `RootPopPreservesSettledNoActiveReachFromLowCandidate_statement/proof`

核心证明逻辑与 `chain.md` 的第三阶段一致：

1. 对从 popped segment 中 active `x` 到 rest 中 active `b` 的路径取
   `ProcessedTreeReachableFromCandidate u (edge_set u)` 的 last exit。
2. last exit 边若落到 active 点 `c`，则该边构造出
   `PartialLowTargetCandidate u (edge_set u) s c`。
3. full low completeness 给出 `low[u] <= dfn[c]`。
4. 若 `dfn[u] <= dfn[c]`，segment tree coverage 会推出 `c` 仍在 processed
   tree 中，和 last-exit 的 outside 条件矛盾；因此 `dfn[c] < dfn[u]`。
5. 与 pop guard `low[u] = dfn[u]` 矛盾。
6. last exit 边若落到 visited non-active 点，则由
   `SettledNoActiveReachCandidate` 反驳它继续到达 rest active target。
7. 若落点可能未访问，则由已有 `PoppedSegmentClosedCandidate` 把它转成 visited。

这个 producer 需要一个结构前提：

```coq
StackRestOlderThanRootCandidate u s
```

它表达 `stack_split_at (stack s) u = (popped, rest)` 后，`rest` 中所有节点的
`dfn` 都严格小于 `dfn[u]`。当前 `wf_scc_state` 并不包含 `NoDup (stack s)`，
所以不能从 `GlobalShapeCandidate` 和 `OrderFactsCandidate` 单独推出这个事实。
已经证明了一个局部入口：

```coq
NoDup (stack s) ->
StackRestOlderThanRootCandidate u s
```

后续闭合完整 maybe_pop / final interface 时，需要二选一：

- 将 stack no-dup 作为正式全局/顺序不变量的一部分并证明各 primitive 保持；
- 或沿现有 frame/progress 边界，为每个 pop 调用点直接提供
  `StackRestOlderThanRootCandidate`。

这不是 low correctness 定义的问题，而是 pop 后 closedness 所需的栈结构事实必须
在前提中显式可见。
