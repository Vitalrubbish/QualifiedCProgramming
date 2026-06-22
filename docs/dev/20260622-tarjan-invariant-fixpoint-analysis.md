# Tarjan_scc_is_low.v 不变式与不动点设计分析

**Author**: Kimi Code CLI  
**Date**: 2026-06-22

## 1. 总体评价

当前文件的不变式与不动点设计**方向正确，但存在局部冗余和未完成的抽象**。核心思路是：

1. 用 `low_forset_inv u done` 描述“已处理子节点集合 `done` 下，顶点 `u` 的 low 值正确”。
2. 用 `Hoare_forset` 把 `done` 从 `∅` 迭代到 `dg_step g u`。
3. 用 `Hoare_fix_logicv_conj` 对递归的 `tarjan_scc` 做不动点归纳，同时证明 low-link 性质与 visitedness。

这一框架符合 Tarjan 算法的证明结构，但具体实现上有三处明显问题：

- `visited_tag` 抽象被定义却未被使用，是死代码；
- `low_forset_inv` 把全局不变式（`dfn_inv`、`dfn_valid`、`fa_visited`）与局部 low 不变式打包在一起，导致重复和可读性下降；
- `wf_scc_state` 抽象只出现一次，没有形成系统性的“良态状态”层；
- 缺少对“pending 树边”状态的抽象：`set_fa v u` 把未访问顶点 `v` 接到已访问父节点 `u` 上时，全局 `dfn_valid` 不成立（因为新边 `u -> v` 的 dfn 顺序要在 `preloop v` 后才满足），原框架错误地要求 `set_fa` 保持完整 `wf_scc_state`。

下面分别讨论。

---

## 2. 不变式层级分析

### 2.1 `low_forset_inv u done s` — 核心局部不变式

```coq
low_forset_inv u done s :=
  stack_in_visited s /\
  dfn_inv s /\
  dfn_valid g s root /\
  fa_visited s /\
  u ∈ visited s /\
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
     min_value_of_subset Nat.le (fun w => back_edges_done s u done w \/ w = u) (dfn s))
    (fun x => x) (low s u).
```

**合理性**：
- `done` 表示已经处理完的子节点集合，从 `∅` 逐步扩张到 `dg_step g u`。这是 forset 循环不变式的标准形式，设计合理。
- 用 `children_done` 和 `back_edges_done` 分别刻画树边子节点和回边，与最终目标 `scc_low_valid_v` 的分解一致。
- low 值的 min 定义直接对应 Tarjan 算法中 `low[u] = min(dfn[u], min low[v], min dfn[w])` 的语义。

**问题**：
- 前五个合取支（`stack_in_visited`、`dfn_inv`、`dfn_valid`、`fa_visited`、`u ∈ visited`）是**全局或半全局不变式**，在 `low_forset_inv` 的每一次使用中都重复出现。它们与 `done` 无关，却随着 `done` 参数被反复提及。
- 后果：
  1. `low_forset_inv_proper` 的证明必须同时处理这些全局不变式的 properness；
  2. 每个保持 `low_forset_inv` 的引理都要重新证明这些全局不变式没有被破坏；
  3. 阅读时难以快速定位“真正与 `done` 相关的部分”。

**建议**：
把 `low_forset_inv` 拆成两层的合取：

```coq
Definition low_forset_inv_core (u: V) (done: V -> Prop) (s: SCCSt): Prop :=
  min_value_of_subset Nat.le
    (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
     min_value_of_subset Nat.le (fun w => back_edges_done s u done w \/ w = u) (dfn s))
    (fun x => x) (low s u).

Definition low_forset_inv (u: V) (done: V -> Prop) (s: SCCSt): Prop :=
  wf_scc_state s /\ u ∈ visited s /\ low_forset_inv_core u done s.
```

其中 `wf_scc_state` 已经包含 `stack_in_visited`、`dfn_inv`、`dfn_valid`、`fa_visited`。这样：
- 与 `done` 相关的核心不变式更突出；
- 全局不变式的保持可以统一用 `wf_scc_state` 的保持引理处理；
- `low_forset_inv_proper` 只需关注 `low_forset_inv_core` 的 properness。

### 2.2 `low_pre` / `low_post` — 单顶点规格

```coq
low_pre u s := wf_scc_state_pre u s.
low_post u s := wf_scc_state s /\ scc_low_valid_v s u.
```

其中

```coq
wf_scc_state s := stack_in_visited s /\ dfn_inv s /\ dfn_valid g s root /\ fa_visited s.
wf_scc_state_pre u s := wf_scc_state s /\ ~ u ∈ visited s.
```

**合理性**：
- `low_pre` 表示调用 `tarjan_scc g u` 前的状态：全局不变式成立，且 `u` 尚未访问。
- `low_post` 表示调用后的状态：`u` 的 low-link 正确，且全局不变式保持。
- 引入 `wf_scc_state_pre u` 显式刻画“存在 pending 树边指向未访问顶点 `u`”的状态。`set_fa u p` 产生这种状态，`preloop u` 将其消去并恢复完整 `wf_scc_state`。

**问题**：
- 最初 `low_pre` 写成 `wf_scc_state s /\ ~ u ∈ visited s`，与 `wf_scc_state_pre u s` 等价，但没有把“pre-state”提升为独立抽象。
- 原框架错误地认为 `set_fa v u` 保持完整 `wf_scc_state`；实际上它只保持 `wf_scc_state_pre v`。

**建议**：
- 保留 `wf_scc_state_pre` 作为一级抽象；
- `preloop_preserves_wf_scc_state` 的 precondition 用 `wf_scc_state_pre u`；
- 用 `set_fa_preserves_wf_scc_state_pre` 替代 `set_fa_preserves_wf_scc_state`。

### 2.3 `scc_low_valid_v` / `scc_low_valid` / `scc_is_low` — 目标层级

```coq
scc_low_valid_v s u := min over tree-children low  ∪  min over back-edges dfn  = low s u.
scc_low_valid s := forall v, v ∈ visited s -> scc_low_valid_v s v.
scc_is_low s := forall v, v ∈ visited s -> low s u = min dfn over scc_low_tree s u.
```

**合理性**：
- `scc_low_valid_v` 直接对应算法语义；
- `scc_low_valid` 是局部正确性的全局化；
- `scc_is_low` 是最终要证明的“low-link 值正确”的表述。
- 三者之间的连接由 `scc_low_valid_implies_is_low` 完成，依赖 DFS 树归纳，结构正确。

**问题**：
- `scc_low_valid` 和 `scc_is_low` 的区别较微妙。`scc_low_valid` 强调“low 是 tree-child low 与 back-edge dfn 的最小值”，而 `scc_is_low` 强调“low 是从 `u` 经树边可达再经一条回边可达的所有顶点的 dfn 最小值”。两者等价由 `scc_low_valid_induction` / `scc_low_valid_induction_is_low` 给出。
- 这种分层是合理的，但在教学/维护时可能需要更多注释说明二者的语义差异。

---

## 3. 不动点设计分析

### 3.1 `Hoare_forset` 用于子节点迭代

`forset (fun v => dg_step g u v) (process_edge u W)` 遍历 `u` 的所有出边邻居。`Hoare_forset` 要求：
- 一个关于 `done` 的不变式 `P(done, s)`；
- `P` 对 `done` 的集合等价是 proper 的；
- 对任意 `done` 外的邻居 `a`，`body a` 把 `P(done)` 变为 `P(done ∪ [a])`。

**合理性**：
- 这是处理“遍历集合并逐步积累信息”的标准方法，完全适合 Tarjan 的子节点循环。
- `done` 从 `∅` 到 `dg_step g u` 的演化自然对应算法执行过程。

**问题**：
- 当前 `forset_keep_low_forset_inv` 的不变式是一个六元组，包含 `low_forset_inv`、`dfn_valid`、`dfn_inv`、`fa_visited`、`done_visited`、以及 `fa-child ⇒ in done`。这个不变式“过大”，导致 `process_edge` 分支需要同时保持多个性质。
- 虽然每个子性质都有对应引理，但把它们硬塞进一个 `P` 里，使得 `Hoare_forset` 的应用步骤很长，且容易因某个合取支的 properness 失败而卡住。

**建议**：
如果按 2.1 的建议把全局不变式抽成 `wf_scc_state`，则 `forset` 的不变式可以简化为：

```coq
P(done, s) := wf_scc_state s /\ low_forset_inv_core u done s /\ done_visited done s /\ fa_children_in_done u done s.
```

其中：
- `wf_scc_state s` 的保持由一组统一的 primitive-operation 引理处理；
- `low_forset_inv_core` 的保持是核心；
- `done_visited` 和 `fa_children_in_done` 是为了最终调用 `low_forset_inv_to_scc_low_valid` 所需的前提。

### 3.2 `Hoare_fix_logicv_conj` 用于递归 `tarjan_scc`

`tarjan_scc` 是通过 `Lfix` 定义的递归程序。`Hoare_fix_logicv_conj` 允许同时证明两个性质：
- `P1(a, c, s) -> Q1(a, c, s')`：主性质（low-link）；
- `P2(a, d, s) -> Q2(a, d, s')`：辅助性质（visitedness）。

当前用法：
```coq
P1(a, _, s) := low_pre a s,    Q1(a, _, s') := low_post a s'
P2(a, w, s) := w ∈ visited s,  Q2(a, w, s') := w ∈ visited s
```

**合理性**：
- 递归调用 `W x` 在树边分支中需要保证：
  1. `W x` 保持 `low_forset_inv u done`（主性质）；
  2. `W x` 保持某些顶点的 visitedness（辅助性质，用于 `done_visited` 和 fa-child 推理）。
- `Hoare_fix_logicv_conj` 正好支持这种“主 + 辅”的联合归纳，设计合理。

**问题**：
- 辅助性质只选了 `w ∈ visited s`，但实际上 `forset_keep_low_forset_inv` 还需要：
  - `forall w, done' w -> w ∈ visited s`（任意 done 集合的 visitedness）；
  - `forall v, fa s v = u /\ fa s v <> v -> dg_step g u v`（fa-children 在图边中）。
- 这两个性质**不是直接从 `Hoare_fix_logicv_conj` 的辅助参数得到**，而是需要额外的引理 `tarjan_scc_keep_visited_forall` 和 `tarjan_scc_keep_fa_children_in_universe`。
- 这意味着不动点归纳的“辅助通道”设计得不够强，实际证明中不得不在循环外再套一层引理来补充。

**建议**：
考虑把 `Hoare_fix_logicv_conj` 的辅助参数扩展为更强的统一性质，例如：

```coq
P2(a, t: visited_tag, s) := visited_tag_pre a t s
Q2(a, t: visited_tag, s') := visited_tag_post a t s'
```

这正是 `visited_tag` 抽象试图做的事情！它预见了需要把“visitedness of a single vertex / of a set / of fa-children”统一起来。但当前 `visited_tag` 被定义后完全没有使用，说明这个抽象没有被正确落地。

**更优设计**：
要么彻底删除 `visited_tag`（因为它目前是死代码），要么真正用它重构不动点归纳。如果重构，大致结构如下：

```coq
Theorem tarjan_scc_keep_low_valid_and_tag (u: V) (t: visited_tag):
  Hoare (fun s => low_pre u s /\ visited_tag_pre u t s)
        (tarjan_scc g u)
        (fun _ s => low_post u s /\ visited_tag_post u t s).
Proof.
  apply Hoare_fix_logicv_conj with
    (P2 := fun a t s => visited_tag_pre a t s)
    (Q2 := fun a t s' => visited_tag_post a t s').
  - (* base: visitedness of tag is preserved by tarjan_scc — one lemma per tag constructor *)
    destruct t; simpl; [apply tarjan_scc_self_visited | apply tarjan_scc_keep_visited | ...].
  - (* induction step: prove both low and tag preservation for F W *)
    ...
Qed.
```

这样 `forset_keep_low_forset_inv` 所需的四个 W-假设都可以从这个统一定理派生出来，而不需要单独维护四条辅助引理。

---

## 4. `visited_tag` 的死代码问题

当前定义：

```coq
Inductive visited_tag :=
  | VSelf | VKeep (w: V) | VKeepAll (done: V -> Prop)
  | VKeepFaChildren (parent: V).
```

但在当前文件和原始 `.orig` 文件中，它**从未被任何证明使用**。原始证明直接在 `Hoare_fix_logicv_conj` 中用了 `w ∈ visited s` 作为辅助性质，没有用到 `visited_tag`。

**影响**：
- 增加阅读负担：读者会以为这是核心抽象，实际上它不参与任何推理。
- 增加维护成本：如果后续修改 `visited` 相关定义，需要同步维护 `visited_tag_pre/post`。

**建议**：
- **方案 A（推荐）**：删除 `visited_tag`，因为它目前没有任何用途。这是最小改动。
- **方案 B（重构）**：如 3.2 所述，用它重构不动点归纳的辅助通道。这是更大但更有结构价值的改动。

如果暂时不想做方案 B，应先执行方案 A，避免死代码。

---

## 5. `wf_scc_state` / `wf_scc_state_pre` 抽象的机会

当前 `wf_scc_state` 只在文件开头出现一次，证明了 `pop_scc_preserves_wf_scc_state`，之后再也没有被使用。

**问题**：
- 如果 `wf_scc_state` 只是孤立的定义 + 一个引理，它对证明结构没有实质帮助，反而多了一层概念。
- 更深层的问题：`set_fa v u` 把未访问顶点 `v` 接到已访问父节点 `u` 时，会创建一条“pending 树边”。此时全局 `dfn_valid g s root` 不成立，因为新边 `u -> v` 要求 `dfn u < dfn v`，而 `v` 尚未被 `preloop` 赋予 dfn。原框架若要求 `set_fa` 保持完整 `wf_scc_state`，则引理不成立。

**机会**：
- 把 `low_forset_inv`、`low_pre`、`low_post` 都基于 `wf_scc_state` 定义；
- 引入 `wf_scc_state_pre u s := wf_scc_state s /\ ~ u ∈ visited s` 来刻画 pending 树边状态；
- 补充以下保持引理：
  - `preloop_preserves_wf_scc_state`：从 `wf_scc_state_pre u` 到 `wf_scc_state`；
  - `set_fa_preserves_wf_scc_state_pre`：从 `wf_scc_state /\ u ∈ visited /\ ~ v ∈ visited` 到 `wf_scc_state_pre v /\ u ∈ visited`；
  - `set_low_preserves_wf_scc_state`、`update_low_preserves_wf_scc_state`、`pop_scc_preserves_wf_scc_state`：保持完整 `wf_scc_state`。

这样：
- 大量重复的 `dfn_valid / dfn_inv / fa_visited` 合取支可以消去；
- 全局不变式的保持证明会更系统化；
- 文件结构会更接近“先建立全局良态（或 pre-良态），再证明局部 low 性质”的分层思想。

**建议**：
把 `wf_scc_state` 和 `wf_scc_state_pre` 发展成系统抽象（推荐）。

---

## 6. 跨子树保持的薄弱环节

`tarjan_scc_establishes_and_preserves_scc_low_valid` 的证明思路中提到：

> “对祖先用 `W_preserves_ancestor_inv` / `set_fa_W_preserves_low_forset_inv` + `low_forset_inv_to_scc_low_valid` 做跨子树保持。”

这是整个证明中最复杂的部分，也是当前框架下最薄弱的环节。问题包括：

1. `W_preserves_ancestor_inv` 保持的是 `low_forset_inv u done`，而不是直接的 `scc_low_valid_v u`。当 `a` 的子树处理完毕后，`done` 是否等于 `dg_step g u`？这需要额外论证。
2. 祖先链上的 `done` 集合不是全局的 `dg_step g u`，而是相对于当前 forset 迭代进度的局部 `done`。当子树 `a` 返回时，祖先 `u` 的 forset 的 `done` 已经扩张到包含 `a`，但不一定包含 `u` 的所有子节点。因此 `low_forset_inv_to_scc_low_valid` 不能直接在子树返回时应用，必须等到 `u` 自己的 forset 结束后才应用。
3. 这意味着 `tarjan_scc_establishes_and_preserves_scc_low_valid` 的“跨子树保持”不能简单地逐顶点验证，而需要区分：
   - 顶点 `a` 自身：由 `tarjan_scc_keep_low_valid` 保证；
   - `a` 的祖先 `u`：在 `a` 的子树返回时，`low_forset_inv u (done_currently)` 被保持，但 `scc_low_valid_v u` 尚未成立；
   - 当 `u` 的 forset 全部结束后，`scc_low_valid_v u` 才成立。

因此，`tarjan_scc_establishes_and_preserves_scc_low_valid` 实际上需要一个**两阶段论证**：
- 阶段一（子树返回时）：所有祖先的 `low_forset_inv` 对当前 `done` 保持；
- 阶段二（祖先的 forset 结束时）：`scc_low_valid_v` 对每个祖先成立。

当前证明思路把这个两阶段论证压缩成一句话，实际形式化时需要更细致的中间引理。

**建议**：
补充一个显式引理，例如：

```coq
Lemma forset_end_implies_scc_low_valid_v (u: V) (s: SCCSt):
  low_forset_inv u (dg_step g u) s ->
  done_visited (dg_step g u) s ->
  (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) ->
  (forall v, In v (stack s) -> fa s v <> v) ->
  scc_low_valid_v s u.
```

这其实就是 `low_forset_inv_to_scc_low_valid` 的特例，但把它作为独立步骤写出来会更清晰。

---

## 7. 已应用的修改

根据上述分析，已对 `Tarjan_scc_is_low.v` 做如下重构：

1. **系统化 `wf_scc_state` / `wf_scc_state_pre` 抽象**
   - 新增 `wf_scc_state_pre u s := wf_scc_state s /\ ~ u ∈ visited s`。
   - 新增/调整保持引理：
     - `preloop_preserves_wf_scc_state`：precondition 改为 `wf_scc_state_pre u`，postcondition 为 `wf_scc_state`。
     - `set_fa_preserves_wf_scc_state_pre`：替代原 `set_fa_preserves_wf_scc_state`；`set_fa` 只保持 pre-state，不保持完整 `wf_scc_state`。
     - `set_low_preserves_wf_scc_state`
     - `update_low_preserves_wf_scc_state`
     - 原有 `pop_scc_preserves_wf_scc_state`
   - 用 `wf_scc_state` / `wf_scc_state_pre` 重新定义 `low_pre` / `low_post`。
   - 对 `set_fa_preserves_wf_scc_state_pre` 的证明建议：不要拆分 `dfn_pre` 的 4 个分量，而是把它当作一个整体与 `stack_in_visited` 做 `Hoare_conj`：
     - `Q1 := dfn_pre v s root /\ u ∈ visited s`，直接用 `Tarjan_scc_is_dfn.v` 的 `set_fa_preserves_dfn_pre_child_rich`；
     - `Q2 := stack_in_visited s`，由 `set_fa` 不改变 `stack`/`visited` 直接得到；
     - 合并后 `dfn_pre v /\ stack_in_visited` 即 `wf_scc_state_pre v`。

2. **拆分 `low_forset_inv`**
   - 新增 `low_forset_inv_core u done s`，仅包含与 `done` 相关的 min 条件。
   - 重新定义 `low_forset_inv u done s := wf_scc_state s /\ u ∈ visited s /\ low_forset_inv_core u done s`。
   - 删除冗余的 `set_low_keep_low_forset_inv_components`。

3. **删除 `visited_tag` 死代码**
   - 移除了 `visited_tag`、`visited_tag_pre`、`visited_tag_post` 定义。

4. **补充跨子树两阶段引理**
   - 新增 `forset_end_implies_scc_low_valid_v`，显式刻画 forset 结束时从 `low_forset_inv` 到 `scc_low_valid_v` 的转换。

5. **更新高层主定理证明思路**
   - `tarjan_scc_keep_low_valid`、`tarjan_scc_establishes_and_preserves_scc_low_valid`、`tarjan_scc_all_scc_low_valid`、`tarjan_scc_all_scc_is_low` 均改为基于 `wf_scc_state` 的表述，并反映两阶段跨子树论证。

文件仍可编译。

---

## 8. 总体建议（剩余工作）

| 问题 | 优先级 | 状态 |
|------|--------|------|
| `visited_tag` 死代码 | 高 | ✅ 已删除 |
| `low_forset_inv` 过于臃肿 | 高 | ✅ 已拆分 |
| `wf_scc_state` 孤立 | 中 | ✅ 已系统化，并补充 `wf_scc_state_pre` |
| 跨子树保持论证不足 | 中 | ✅ 已补充显式引理 |
| `low_pre`/`low_post` 重复 | 低 | ✅ 已用 `wf_scc_state` / `wf_scc_state_pre` 简化 |
| `set_fa` 错误要求保持完整 `wf_scc_state` | 高 | ✅ 已改为 `set_fa_preserves_wf_scc_state_pre` |

### 重构后的文件结构（已实现）

1. **全局良态层**：
   - `wf_scc_state` 及其保持引理（`set_low`、`update_low`、`pop_scc`）；
   - `wf_scc_state_pre u` 及其保持引理（`preloop`、`set_fa`）。
2. **局部 low 核心层**：`low_forset_inv_core u done` 仅包含与 `done` 相关的 min 条件。
3. **局部 low 层**：`low_forset_inv u done := wf_scc_state /\ u ∈ visited /\ low_forset_inv_core u done`。
4. **单顶点规格层**：`low_pre u := wf_scc_state_pre u`，`low_post u := wf_scc_state /\ scc_low_valid_v u`。
5. **forset 循环层**：用简化后的 `P(done) := wf_scc_state /\ low_forset_inv_core /\ done_visited /\ fa_children_in_done` 应用 `Hoare_forset`。
6. **递归不动点层**：用 `Hoare_fix_logicv_conj` 证明 `low_pre -> low_post`，辅助通道保留 `w ∈ visited s`（`visited_tag` 已删除）。
7. **全局目标层**：`scc_low_valid` / `scc_is_low`。

这种结构使每个引理的职责更单一，证明思路更清晰。

---

## 9. 未来可选改进

- **不动点辅助通道统一化**：当前仍用 `w ∈ visited s` 作为 `Hoare_fix_logicv_conj` 的辅助性质，并在外部通过 `tarjan_scc_keep_fa_children_in_universe` 等引理补充 fa-children 性质。如果希望进一步简化，可以设计一个统一的“标签”类型（比已删除的 `visited_tag` 更精简）来同时携带 visitedness 和 fa-children 信息，但这需要权衡抽象复杂度。
- **`low_forset_inv_proper` 简化**：由于 `low_forset_inv` 现在基于 `wf_scc_state`，其 properness 证明可以更专注于 `low_forset_inv_core`，`wf_scc_state` 部分可自动处理。
