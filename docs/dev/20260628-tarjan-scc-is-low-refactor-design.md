# Tarjan-SCC-is-low-Refactor-Design
**Author**: Codex
**Date**: 2026-06-28

## 1. 目标

本文档给出 `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`
的重构设计。目标是仿照 `SeparationLogic/algorithms/Kosaraju/Kosaraju.v`
的证明工作模式，把 Tarjan SCC 的 low-link 证明从“一个巨型归纳后置条件
和大量 frame 线程”重构为更小、更局部、更容易维护的证明管道。

重构后的完成标准：

1. `Tarjan_scc_is_low.v` 的顶层证明不再依赖临时 `Admitted`。
2. 程序证明中的递归 IH 采用 Kosaraju 风格的 singleton-state normal form：
   `forall s0 a, Hoare (fun s => s = s0) (W a) (Q a s0)`。
3. `forset` 循环只维护局部 low-link 迭代不变量；复杂的图论等价证明移到纯逻辑 lemma。
4. `pop_scc` 之后不再要求证明所有栈相关 witness 的强保持性。
5. 顶层文件只负责编排，底层定义、纯图论、primitive frame、forset body 分别放入小模块。

## 2. 现状问题

当前 `Tarjan_scc_is_low.v` 已经包含不少正确方向的设计：

- `wf_scc_state` 把全局良构性打包；
- `forset_inv` 使用不等式而不是精确等式，适合 `low u` 单调下降；
- `low_src` 记录 `low u` 的来源，用来把下界反向推出精确最小值；
- 已经迁移到 `Hoare_normal_LFix` 风格的一部分证明；
- 已经有 `scc_low_valid_v` 与 `scc_is_low_v` 两层规格。

但当前证明复杂度仍然集中在以下几点：

1. `Q_low` 太重  
   当前主递归后置同时包含 SELF、ancestor FRAME、fa 保持、child low 正确性、done 访问性、`low_src`、`fa_child_of_u` 等大量合取。每次递归调用都要重新组装这些信息，导致证明脚本膨胀。

2. 程序证明过早追求 `scc_is_low_v`  
   `scc_is_low_v` 直接基于 `scc_low_tree`，其中 `scc_back_edge` 依赖 `In y (stack s)`。这使 `pop_scc` 后的保持性非常麻烦。程序阶段更适合证明局部递推式 `scc_low_valid_v`，最终再用纯逻辑桥接到 `scc_is_low_v`。

3. `fa` 稳定性与 low 正确性互相缠绕  
   当前已经意识到需要 `Q_fa_rich`，但主证明中仍然大量把 `fa` frame 嵌入 `Q_low`。这会造成循环依赖：low 证明需要 fa 稳定，fa 稳定又被迫穿过 low 的重后置。

4. `pop_scc` 证明承担了错误的职责  
   `pop_scc` 修改 `stack`，因此任何直接依赖 stack membership 的 witness 都可能失效。让 `pop_scc` 保持 `scc_is_low_v` 是可证的，但会把证明推向 stack split 细节。更好的做法是在 `pop_scc` 前完成所有 low-link 语义证明，`pop_scc` 后只保留不依赖当前 stack 的交付结论。

5. 单文件承担了过多层次  
   当前一个文件内混合了定义、纯图论、state update frame、forset 不变量、Lfix 编排和最终 theorem。证明失败时很难判断是 spec 问题、frame 问题还是循环不变量问题。

## 3. Kosaraju 可复用模式

`Kosaraju.v` 的核心模式不是某个具体 lemma，而是一套证明分层方式：

1. 程序体展开后使用 `Hoare_normal_LFix`  
   递归 IH 总是可以在当前状态直接实例化：

   ```coq
   IH : forall s0 a,
     Hoare (fun s => s = s0) (W a) (Q a s0)
   ```

2. 每个 DFS phase 有自己的轻量 `Q`  
   例如 phase 1 单独证明 visited 增长、邻居访问、finish order；phase 2 单独证明 SCC id、可达性、partition 性质。它没有把最终 correctness 全塞进一个 IH。

3. 循环不变量只描述当前循环真正需要的信息  
   Kosaraju 的 `repeat_break` / DFS 证明中，loop invariant 通常只维护 visited subset、当前点已访问、已探索边集合等局部事实。

4. 纯逻辑结论后置桥接  
   程序证明负责产生结构化事实；强语义定理通过纯逻辑 lemma 从这些事实推出。

5. helper Hoare lemma 以 primitive operation 为单位  
   `visit1`、`set_finish`、`set_scc_id` 等操作先有小 Hoare lemma，主证明只组合它们，而不是反复展开 record update。

Tarjan low-link 重构应复用这些原则，而不是复刻 Kosaraju 的具体不变量。

## 4. 重构后的规格层次

建议把 low-link 规格拆成三层。

### 4.1 层 A：程序递推规格 `scc_low_valid_v`

这是程序证明的主规格：

```coq
scc_low_valid_v s u :=
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le
       (dg_step (state_to_dfs_tree g s root) u) (low s)
     ∪ min_value_of_subset Nat.le
       (scc_back_edge s u ∪ [u]) (dfn s))
    (fun x => x) (low s u).
```

它直接对应 Tarjan 更新规则：

- 初始 `low u = dfn u`；
- 树边 `u -> v` 返回后，用 `low v` 更新 `low u`；
- 回边 `u -> w` 且 `w` 在栈中，用 `dfn w` 更新 `low u`；
- 交叉边不影响 `low u`。

程序阶段优先证明：

```coq
low_valid_post u s := wf_scc_state s /\ scc_low_valid_v s u
```

而不是直接证明 `scc_is_low_v s u`。

### 4.2 层 B：完成边扫描后的局部语义

`forset` 完成后，证明：

```coq
low_frontier_and_src_imply_low_valid :
  I u (dg_step g u) s ->
  scc_low_valid_v s u.
```

这里 `I` 只服务于边扫描，不包含 Lfix 的 ancestor frame。推荐结构：

```coq
I u done s :=
  wf_scc_state s /\
  u ∈ visited s /\
  In u (stack s) /\
  done_visited done s /\
  low_frontier u done s /\
  low_src u done s /\
  children_low_valid u done s /\
  fa_child_of_u u s /\
  fa_not_done_implies_eq_u u done s.
```

其中：

- `low_frontier` 是当前 `forset_inv` 中的不等式部分；
- `low_src` 记录 `low u` 来源；
- `children_low_valid` 只记录已处理树孩子的 `scc_low_valid_v`，不直接记录 `scc_is_low_v`；
- `fa_child_of_u` 与 `fa_not_done_implies_eq_u` 约束 DFS-tree parent 字段和 `done` 集合的关系，是 tree-edge / cross-edge 分支分类时需要的局部 fa 事实。

### 4.3 层 C：最终数学规格 `scc_is_low_v`

`scc_is_low_v` 保持为公开数学规格：

```coq
scc_is_low_v s u :=
  min_value_of_subset Nat.le (scc_low_tree s u) (dfn s) (low s u).
```

但只在纯逻辑桥接中使用：

```coq
scc_low_valid_implies_is_low :
  dfn_valid g s root ->
  dfn_inv s ->
  (forall v, v ∈ visited s -> scc_low_valid_v s v) ->
  scc_is_low s.
```

建议把当前已有的 `scc_low_valid_implies_is_low` 作为最终桥接主 lemma，
不要在 `forset` body 或 `Q_low` 中传播 `scc_is_low_v`。

该 bridge 不是一步完成。纯逻辑层应显式保留两个中间 lemma：

```coq
scc_is_low_induction :
  (forall v,
    dg_step (state_to_dfs_tree g s root) u v ->
    scc_is_low_v_val s v (low s v)) ->
  min_value_of_subset Nat.le
    (dg_step (state_to_dfs_tree g s root) u) (low s) ==
  min_value_of_subset Nat.le
    (fun w => exists v,
      dg_step (state_to_dfs_tree g s root) u v /\
      scc_low_tree s v w)
    (dfn s).

scc_is_low_induction_is_low :
  u ∈ visited s ->
  (forall v,
    dg_step (state_to_dfs_tree g s root) u v ->
    scc_is_low_v_val s v (low s v)) ->
  scc_low_valid_v s u ->
  scc_is_low_v s u.
```

`scc_low_valid_implies_is_low` 再对 visited 顶点按 `timer s - dfn s u`
做 well-founded induction，每一步调用 `scc_is_low_induction_is_low`。

## 5. 文件拆分方案

建议从当前单文件拆为 5 个文件。拆分顺序可以逐步进行，先复制移动已完成 lemma，再改主证明。

跨文件参数化采用显式参数方案：`Tarjan_scc_low_defs.v` 与
`Tarjan_scc_low_pure.v` 各自打开独立 Section，导出的定义和 lemma 都显式带
`g`、`root` 参数，例如 `scc_low_valid_v g root s u`。因此
`Tarjan_scc_is_low.v` 不再复制这些定义，而是在自己的 Section 中 import
`Tarjan_scc_low_defs` / `Tarjan_scc_low_pure` 并显式传入当前 context 中的
`g root`。这样避免同名概念在不同文件中变成类型不兼容的重复定义。

### 5.1 `Tarjan_scc_low_defs.v`

只放定义，不放程序证明：

- `scc_back_edge`
- `scc_low_reachable`
- `scc_low_tree`
- `scc_is_low_v_val`
- `scc_is_low_v`
- `scc_low_valid_v`
- `scc_is_low`
- `done_visited`
- `low_src`
- `low_frontier`
- `children_low_valid`
- `fa_child_of_u`
- `fa_not_done_implies_eq_u`
- `low_iteration_inv`
- `low_iteration_entry`
- `low_iteration_done`

该文件不应包含程序证明。

### 5.2 `Tarjan_scc_low_pure.v`

只放纯逻辑 lemma：

- reachability first-step decomposition；
- `scc_low_tree_decompose`；
- `scc_low_witness`；
- `scc_low_bound`；
- `scc_is_low_induction`；
- `scc_is_low_induction_is_low`；
- `scc_low_valid_implies_is_low`；
- `low_src` 与 min-value 的桥接；
- `done_visited_proper`、`low_src_proper`、`low_iteration_inv_proper` 等 setoid 支持；
- `stack_split_at` 相关纯 list lemma；
- `pop_scc` shrink-stack 对 back-edge 集合的影响。

该文件的证明应尽量不出现 `Hoare`。

### 5.3 `Tarjan_scc_low_primitives.v`

只放 low-specific primitive 组合 lemma。通用 primitive frame 继续复用
`Tarjan_scc_is_dfn.v` 和 `Tarjan_scc_basics.v`，不要在这里重复定义：

- `preloop_establishes_low_iteration_entry`
- `preloop_low_eq_dfn`
- `update_low_preserves_done_visited`
- `update_low_other_preserves_low_iteration_frame`
- `set_low_preserves_scc_low_valid_v_when_not_child`
- `update_low_preserves_children_low_valid_when_not_tree_child`
- `update_low_other_preserves_low_iteration_inv_when_not_child`
- `set_fa_unvisited_preserves_tree_step`
- `set_fa_preserves_scc_low_valid_v_when_unvisited`
- `set_fa_establishes_new_child_parent`
- `set_fa_visit_establishes_new_child_tree_edge`
- `set_fa_establishes_low_iteration_before_new_child`
- `pop_scc_preserves_low_valid_post_when_root`
- `if_pop_preserves_low_valid_post`
- 尚未被 `Tarjan_scc_is_dfn.v` 覆盖的 `get_low_preserves_*` / `update_low_preserves_*`
  低链路专用保持性。
- `update_low_other_preserves_low_iteration_inv_when_not_child` 只能用于更新非当前顶点、
  非 `done` 顶点、且不是任何已处理 child 的 DFS-tree child 的 low 值；仅有
  `a <> u` 和 `~ done a` 不足以保持 `children_low_valid`。
- `set_fa_establishes_low_iteration_before_new_child` 作为 tree-edge 分支中
  `set_fa a u` 之后进入子递归前的 low-specific setup contract。注意
  `set_fa a u` 本身不会建立 `dg_step (state_to_dfs_tree ...) u a`，因为此时
  `a` 尚未 visited；tree edge 只有在后续 `visit a` 之后才成立，对应
  `set_fa_visit_establishes_new_child_tree_edge`。

约束：这里可以展开 `visit/set_dfn/set_low/set_fa/update_low/pop_scc`，
但主定理文件不应再反复展开这些操作。

截至当前版本，`Tarjan_scc_low_primitives.v` 已经没有 `Admitted` / `admit`，
并且可独立编译。后续证明应优先复用这些 primitive contracts，而不是在
`Tarjan_scc_is_low.v` 或未来的 `Tarjan_scc_low_forset.v` 中重新展开 record update。

### 5.4 `Tarjan_scc_low_forset.v`

只证明边扫描：

- `I` 的 Proper；
- tree-edge branch；
- back-edge branch；
- self-loop branch；
- cross-edge branch；
- `process_edge_preserves_I`；
- `forset_preserves_I`；
- `low_frontier_and_src_imply_low_valid`。

概念上，该文件只需要递归调用提供“子调用 low 正确 + ancestor 稳定”的
continuation spec：

```coq
HW_low :
  forall s0 v,
    ~ v ∈ visited s0 ->
    wf_scc_state_pre v s0 ->
    Hoare (fun s => s = s0) (W v)
      (fun _ s => low_valid_post v s /\
                  v ∈ visited s /\
                  stable_for_ancestor u done s0 s)
```

其中 `stable_for_ancestor` 应拆成只和当前 ancestor 相关的最小 frame，
不要复用当前巨型 `Q_low`。

实际骨架中使用更完整的 `low_continuation_contract`：

```coq
Q_low_valid a s0 tt s /\
Q_fa_stable a s0 tt s /\
Q_stack_frame a s0 tt s /\
low_iteration_inv u done s /\
(fa s0 a = u -> fa s a = u)
```

`Q_fa_stable` 和 `Q_stack_frame` 分别用于维持 parent 稳定性和 ancestor
不被子递归弹出；它们不属于 low 正确性本身，但 tree-edge 分支需要它们来恢复
`low_iteration_inv u done`。

当前实现进一步引入了 `Q_active_stack_frame`，用于表达“当前仍活跃的递归栈帧”
不仅保留更老 ancestor 的栈成员关系，还保留 frame root 自身仍在栈中、root 的
`dfn` 不变、以及更老 ancestor 的 `dfn` 不变。它对应 forset / recursive-call
阶段真正需要的 stronger frame：

```coq
Q_active_stack_frame u s0 _ s :=
  In u (stack s) /\
  dfn s u = dfn s0 u /\
  Q_stack_frame u s0 tt s /\
  (forall anc,
     In anc (stack s0) ->
     dfn s0 anc < dfn s0 u ->
     dfn s anc = dfn s0 anc).
```

`tarjan_scc_preserves_Q_active_stack_frame` 已完成。该 theorem 的入口条件需要
显式包含：

```coq
dfn s cur < timer s
```

原因是 child 递归入口发生在 child 还未 visited 时；只有 child 的 `preloop`
之后，`dfn child` 才等于旧 `timer`，从而可推出外层 active frame 的 root
满足 `dfn cur < dfn child`，保证 child 的最终 `pop_scc child` 不会弹出外层
frame。为支持递归证明，当前实现使用 list 版 active frame 聚合：

- `active_stack_frames`
- `active_stack_frames_below`
- `active_stack_frames_below_timer`
- `active_base`

并先证明更强的 `tarjan_scc_preserves_active_base`，再用 singleton frame 投影出
`tarjan_scc_preserves_Q_active_stack_frame`。后续 low-iteration 证明应优先复用
这些 active-frame theorem，而不是重新展开 `pop_scc` 的 stack split 细节。

### 5.5 `Tarjan_scc_is_low.v`

最终文件只保留：

- `Q_low_valid`；
- `Q_fa_stable`；
- `Q_stack_frame`；
- `Hoare_normal_LFix` 编排；
- `tarjan_scc_keep_low_valid`；
- 若需要，再用纯逻辑桥接导出 `tarjan_scc_keep_is_low`。

目标是让顶层文件像 Kosaraju 的最后阶段一样，只做 phase 组合。

## 6. 新的递归后置条件

当前 `Q_low` 过重，建议拆成三个独立 Lfix 后置。

### 6.1 `Q_fa_stable`

只证明 fa 对旧 visited 顶点稳定：

```coq
Q_fa_stable u s0 _ s :=
  (forall w, w ∈ visited s0 -> w ∈ visited s) /\
  (forall w, w ∈ visited s0 -> fa s w = fa s0 w).
```

这应最先证明，供后续证明引用。它不应依赖 low-link 语义。

当前实现中，`Q_fa_stable` 已经完成。证明没有重新展开整个
`tarjan_scc_f` 的 low-link 语义，而是拆成两类事实：

1. 旧 visited 集合的保持性直接复用
   `Tarjan_scc_basics.tarjan_scc_keep_visited_forall`；
2. 旧 visited 顶点的 `fa` 保持性逐点复用
   `Tarjan_scc_basics.tarjan_scc_keep_fa`。由于该 lemma 的前提要求
   递归入口 `u <> w`，`tarjan_scc_keep_fa_stable_unvisited` 保留
   `~ u ∈ visited s0` 作为入口条件，并对 `w = u` 的情况由矛盾排除。

因此当前可用的主 frame theorem 是：

```coq
tarjan_scc_keep_fa_stable_unvisited :
  Hoare (fun s => s = s0 /\ ~ u ∈ visited s0)
        (tarjan_scc g u)
        (Q_fa_stable u s0).
```

兼容用的 `tarjan_scc_keep_fa` 也应只作为该 theorem 的投影推论保留，
不要再维护一套独立证明。

证明过程中还发现一个重要边界：`process_edge_keep_fa_forall` 不能使用
`P : SCCSt -> V -> Prop` 这种状态依赖谓词作为完全泛型参数。tree-edge
分支执行 `set_fa v u` 后，递归调用前后的 snapshot 改变；若 `P` 依赖
`fa`，一般无法证明 `P s0 w -> P s_mid w`。因此可证明的 forset frame
helper 应采用固定顶点谓词：

```coq
Q : V -> Prop
```

并把 `fa s0` 作为固定参考快照。若未来需要状态依赖谓词，必须额外提供
该谓词在 `set_fa` / primitive frame 下的稳定性前提，不能直接沿用泛型
`P : SCCSt -> V -> Prop`。

### 6.2 `Q_stack_frame` / `Q_active_stack_frame`

只证明 ancestor 不会被子递归错误弹出：

```coq
Q_stack_frame u s0 _ s :=
  forall anc,
    In anc (stack s0) ->
    dfn s0 anc < dfn s0 u ->
    In anc (stack s).
```

这对应当前证明中隐含的关键事实：递归调用 `tarjan_scc v` 只会弹出
`dfn >= dfn v` 的栈顶片段，不会弹出更早入栈的祖先。这个性质应独立成 lemma，
不要混在 low-link correctness 中。

### 6.3 `Q_low_valid`

主 low-link 后置只描述当前顶点：

```coq
Q_low_valid u s0 _ s :=
  wf_scc_state s /\
  u ∈ visited s /\
  low_valid_post u s /\
  stack_dfn_order s /\
  dfn_injective s.
```

如果 `forset` 需要 ancestor frame，应通过 `Q_stack_frame`、`Q_fa_stable`
和一个局部 `stable_for_ancestor` lemma 组合得到，而不是把 frame 全塞进
`Q_low_valid`。

## 7. `forset` 不变量重写

### 7.1 当前保留的核心

当前 `forset_inv` 中这部分应保留：

```coq
wf_scc_state s /\
u ∈ visited s /\
In u (stack s) /\
low s u <= dfn s u /\
(forall v, done v -> dg_step g u v ->
  (fa s v = u -> low s u <= low s v) /\
  (In v (stack s) -> low s u <= dfn s v))
```

它是正确的，因为 `low u` 下降时不等式单调保持。

### 7.2 替换 child IH

当前不变量中类似下面的部分：

```coq
forall v, done v -> dg_step g u v ->
  fa s v = u -> fa s v <> v -> scc_is_low_v s v
```

建议替换为：

```coq
forall v, done v -> dg_step g u v ->
  fa s v = u -> fa s v <> v -> scc_low_valid_v s v
```

原因：

- `scc_low_valid_v` 与程序更新规则直接匹配；
- 不需要在循环体中展开整棵 `scc_low_tree`；
- 不需要在 `pop_scc` 后维持 stack-dependent tree witness；
- 最终 `scc_is_low_v` 可由统一 bridge 推出。

### 7.3 `low_src` 保留但弱化

`low_src` 仍然有价值，但应只用于证明 `scc_low_valid_v`，而不是直接证明
`scc_is_low_v`。建议定义：

```coq
low_src u done s :=
    low s u = dfn s u
 \/ (exists v, done v /\ dg_step g u v /\
       fa s v = u /\ fa s v <> v /\ low s u = low s v)
 \/ (exists w, done w /\ dg_step g u w /\
       In w (stack s) /\ fa s w <> u /\ low s u = dfn s w).
```

保留当前三分支，但桥接目标改为：

```coq
low_frontier_and_src_imply_low_valid :
  I u (dg_step g u) s ->
  scc_low_valid_v s u.
```

## 8. `pop_scc` 的职责调整

`tarjan_scc_f` 的最后一步是：

```coq
If (fun s => low s u = dfn s u) (pop_scc u)
```

建议在证明结构上拆成：

1. `forset` 后先得到 `scc_low_valid_v s u`；
2. 在 `pop_scc` 前，如需 `scc_is_low_v s u`，由纯逻辑 bridge 得到；
3. `pop_scc` 后主 post 只要求：
   - `wf_scc_state`；
   - `u ∈ visited`；
   - `scc_low_valid_v` 或一个不依赖当前 stack 的历史结论；
   - `stack_dfn_order`、`dfn_injective`。

不要让 `pop_scc` 承担“所有 `scc_low_tree` witness 在缩栈后仍保持”的职责。
如果最终 theorem 必须陈述 `scc_is_low_v` 在 pop 后成立，则单独给一个极窄 lemma：

```coq
pop_scc_preserves_root_is_low_when_low_eq_dfn :
  low s u = dfn s u ->
  scc_is_low_v s u ->
  Hoare (fun s' => s' = s) (pop_scc u)
    (fun _ s' => scc_is_low_v s' u).
```

该 lemma 只用于 root `u`，不要泛化到所有 child 或所有 done 顶点。

当前重构选择路径 (1)：在 pop 前先用单点 bridge
`scc_is_low_induction_is_low` 得到 root 的 `scc_is_low_v`，再用
`pop_scc_preserves_root_is_low_when_low_eq_dfn` 穿过 `pop_scc`。路径 (2)
也可行，但需要在最终状态持有全图 `scc_low_valid`，不适合作为当前单点
`tarjan_scc_keep_is_low` 的主路线。

## 9. 主证明管道

重构后的主证明应呈现为以下形状：

```coq
Theorem tarjan_scc_keep_low_valid (u: V):
  Hoare (fun s => low_pre u s /\ stack_dfn_order s /\ dfn_injective s)
        (tarjan_scc g u)
        (fun _ s => low_valid_post u s /\
                    u ∈ visited s /\
                    stack_dfn_order s /\
                    dfn_injective s).
Proof.
  apply Hoare_normalize. intros s0 Hpre.
  apply (Hoare_normal_LFix Q_low_valid tarjan_scc_f).
  intros W IH s_cur a.
  unfold tarjan_scc_f.
  eapply Hoare_bind.
  - apply preloop_establishes_forset_entry.
  - intros [].
    eapply Hoare_bind.
    + apply forset_preserves_I.
      (* use IH only through small adapters:
         IH_low_valid, IH_fa_stable, IH_stack_frame *)
    + intros [].
      apply if_pop_preserves_low_valid_post.
Qed.
```

其中 `forset_preserves_I` 的调用不应暴露 `Q_low` 的全部内容，只接收
已经整理好的 continuation frame adapter。

## 10. 迁移步骤

### Step 1：冻结并复制当前可用定义

新建 `Tarjan_scc_low_defs.v`，只迁移定义，不改语义。

完成后 `Tarjan_scc_is_low.v` 必须 import 新文件并删除重复定义；后续所有引用都显式写
`scc_low_valid_v g root s u`、`low_iteration_inv g root u done s` 等参数化形式。

### Step 2：迁移纯逻辑 bridge

新建 `Tarjan_scc_low_pure.v`，迁移并整理：

- `scc_low_witness`
- `scc_low_bound`
- `dg_reachable_first_step`
- `scc_low_tree_decompose`
- `scc_is_low_induction`
- `scc_is_low_induction_is_low`
- `scc_low_valid_implies_is_low`
- `done_visited_proper`
- `low_src_proper`
- `low_iteration_inv_proper`
- `low_frontier_and_src_imply_low_valid`

目标是该文件能独立编译，且没有 `Hoare` 证明。

### Step 3：完成 primitive 层

`Tarjan_scc_low_primitives.v` 当前已经完成，覆盖 preloop、update-low、
set-fa tree-edge setup、pop-scc root preservation 和对应的 low-valid 保持性。
该步骤不再是阻塞项。后续若新增 primitive 合同，必须保持同一边界：
只处理 low-specific operation contract，不把递归 frame 或 forset 分支证明放回这里。

### Step 4：独立证明 `Q_fa_stable`（已完成）

把 fa/visited 稳定性作为第一个 Lfix theorem 完成。这个证明应只用：

- `preloop` 不改旧 fa；
- `set_fa v u` 只改未访问 `v`；
- 递归调用保持旧 visited 的 fa；
- `update_low`、`pop_scc` 不改 fa/visited。

该步骤完成后，主 low 证明不得再内联 fa 稳定性。
主要依赖来自 `Tarjan_scc_basics.v` 中的 primitive 保持性，以及
`Tarjan_scc_is_dfn.v` 中已有的 `wf_scc_state` / `dfn` / stack 保持性。

实际完成路线做了两点调整：

- `process_edge_keep_fa_forall` / `forset_process_edge_keep_fa_forall` 采用固定
  `Q : V -> Prop`，而不是状态依赖的 `P : SCCSt -> V -> Prop`；
- `tarjan_scc_keep_fa_stable_unvisited` 最终由已有基础 theorem 组合证明：
  用 `tarjan_scc_keep_visited_forall` 证明第一个 conjunct，用
  `tarjan_scc_keep_fa` 逐点证明第二个 conjunct。

这意味着后续 tree-edge continuation 可直接依赖
`tarjan_scc_keep_fa_stable_unvisited`，不应再回到旧的泛型 `P` 版本 frame。

### Step 5：独立证明 `Q_stack_frame` / `Q_active_stack_frame`（已完成）

证明子递归不会弹出更老的 ancestor。建议先证明纯 lemma：

```coq
pop_scc_keeps_older_stack_vertex :
  stack_dfn_order s ->
  In anc (stack s) ->
  In u (stack s) ->
  dfn s anc < dfn s u ->
  In anc (stack (pop_scc_state s u)).
```

然后提升到 `tarjan_scc` 的 Lfix frame。
该步骤依赖 `stack_dfn_order`、`dfn_injective`、`pop_scc_state` 和
`stack_split_at` 的纯 list 性质；先证明 pure lemma，再包装成 Hoare / Lfix frame。

当前实现已经完成这一阶段，并额外证明了 active-frame 版本。关键结论包括：

- `tarjan_scc_keep_stack_frame`：保留较老 ancestor 的 stack membership；
- `if_pop_preserves_Q_active_stack_frame`：当外层 frame root 的 `dfn` 小于 pop root
  的 `dfn` 时，`pop_scc` 不会破坏该 active frame；
- `tarjan_scc_preserves_Q_active_stack_frame`：child 递归完整保持外层 active frame；
- `tarjan_scc_preserves_active_base`：list 化的 active frames 可穿过递归和 forset。

因此 Step 6 的 tree-edge 分支不应再把 ancestor-stack 细节作为主要证明负担；
它只需要在调用 child continuation 前建立相应 active-base / timer-below 前置。

### Step 6：重写 `forset` branch lemmas

在 `Tarjan_scc_low_forset.v` 中按四类边证明：

- tree edge：`set_fa ;; W ;; get low ;; update_low`；
- proper back edge：`update_low u (dfn v)`；
- self-loop：`update_low u (dfn u)` no-op；
- cross edge：skip。

每个 branch 的 post 都是 `I u (done ∪ [v])`。

tree-edge 分支应按如下顺序使用 primitive 层：

1. `set_fa_establishes_low_iteration_before_new_child` 建立进入子递归前的 parent
   和 low-iteration frame；
2. 调用 continuation / IH，取得 child 的 `Q_low_valid`、`Q_fa_stable`、
   `Q_stack_frame` 以及 ancestor frame；
3. 读取 child low 后用 `update_low_other_preserves_low_iteration_inv_when_not_child`
   或当前顶点 `u` 的专用 low 更新分支 lemma 恢复 `I u (done ∪ [a])`。

back-edge / self-loop 分支应只更新当前顶点 `u` 的 low，因此不能直接使用
`update_low_other_preserves_low_iteration_inv_when_not_child`；它们需要专门的
“更新 current low 并扩展 done/source/frontier”的 branch lemma。

### Step 7：证明 `forset_done_low_valid`

把 `I u (dg_step g u)` 纯逻辑转成 `scc_low_valid_v s u`。该 lemma 是重构成败的关键，应单独放在 forset 文件末尾。

### Step 8：重写顶层 `tarjan_scc_keep_low_valid`

顶层只串联：

```text
preloop
  -> forset_preserves_I
  -> low_frontier_and_src_imply_low_valid
  -> if_pop_preserves_low_valid_post
```

避免在顶层展开 `set_fa_state`、`stack_split_at` 或 `min_value_of_subset`。

### Step 9：清理旧巨型 frame

逐步删除或降级以下对象：

- 巨型 `Q_low`；
- `Q_low_to_HW_frame`；
- 只为 `Q_low` 形状服务的 wrapper lemma；
- 在主证明中重复展开 record update 的局部片段。

必要时保留兼容 lemma，但应改成由新小 lemma 推出。

## 11. 风险与处理

| 风险 | 处理 |
|------|------|
| `scc_low_valid_v` 不能满足最终 theorem | 保留 `scc_low_valid_implies_is_low` 作为唯一桥接，并明确最终 theorem 的前提需要 `forall visited, scc_low_valid_v` |
| `Q_stack_frame` 难证 | 先只证明当前 ancestor 的 frame，不泛化到任意 stack relation |
| 文件拆分导致循环 import | `defs -> pure -> primitives -> forset -> is_low` 单向依赖；`pure` 不 import `primitives` |
| `Tarjan_scc_low_primitives.v` 与 `Tarjan_scc_is_dfn.v` 职责边界模糊 | `primitives.v` 只放 low-specific 组合 lemma；通用 primitive frame 继续留在 `is_dfn.v` / `basics.v` 中复用；`is_dfn.v` 不 import `primitives.v` |
| `pop_scc` 后 `scc_low_valid_v` 仍受 stack 影响 | 对 root 单独证明 narrow preservation；不要要求所有 child 保持 |
| 状态依赖泛型 frame 谓词不可保持 | `process_edge_keep_fa_forall` 这类 helper 使用固定 `Q : V -> Prop`；若必须使用 `P : SCCSt -> V -> Prop`，需显式提供 primitive-stability 前提 |
| 当前已有证明脚本大量失效 | 先迁移可独立编译的小 lemma，再替换主 theorem，避免一次性大改 |

## 12. 推荐优先级

当前 primitive 层、`Q_fa_stable`、`Q_stack_frame` 和
`Q_active_stack_frame` 均已完成。下一步优先级应调整为：

1. 先证明 `process_edge_preserves_low_iteration`。这是当前最小的关键闭环：
   tree-edge 分支应组合 `set_fa_establishes_low_iteration_before_new_child`、
   child continuation 的 `Q_low_valid / Q_fa_stable / Q_stack_frame /
   Q_active_stack_frame`，以及 child 返回后的 `update_low` 恢复。
2. 再证明 `forset_preserves_low_iteration`。完成单步 branch 后，forset 层应主要
   是 `done` 扩展和 Proper / setoid plumbing，不应再展开 primitive state update。
3. 把当前 `Tarjan_scc_is_low.v` 中的这两个 lemma 迁移到新的
   `Tarjan_scc_low_forset.v`，按
   tree/back/self/cross 四个 branch 独立证明。
4. 最后重写 `tarjan_scc_keep_low_valid`，只串联 preloop、forset、done-to-low-valid
   和 if-pop primitive contract。

完成这些步骤后，`Tarjan_scc_is_low.v` 的证明复杂度会从“维护一个全局巨型后置条件”下降为：

```text
primitive frame lemmas
  + local forset invariant
  + independent recursive frame lemmas
  + pure low-link bridge
```

这与 Kosaraju 的工作模式一致：程序证明只产出局部结构化事实，最终正确性由纯逻辑桥接组合出来。
