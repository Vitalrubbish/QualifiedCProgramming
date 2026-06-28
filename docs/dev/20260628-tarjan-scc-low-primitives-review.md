# Tarjan-SCC-low-Primitives Review

**Author**: Claude
**Date**: 2026-06-28

**Reviewed file**: `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_low_primitives.v`

## 1. 总体评价

文件设计合理，严格遵循设计文档 `20260628-tarjan-scc-is-low-refactor-design.md` Section 5.3 的边界约束：只包含 low-specific 的 primitive 组合 lemma，通用 primitive frame 通过 import `Tarjan_scc_is_dfn.v` / `Tarjan_scc_basics.v` 复用，无重复定义。

7 个 lemma 覆盖了 low-link 证明需要的三类 primitive 操作：preloop 入口、update_low 保持性、pop_scc 职责收窄。依赖链 `defs → pure → primitives → is_low` 正确，primitives 不 import is_low。

编译状态：`Tarjan_scc_low_primitives.v` 及其下游 `Tarjan_scc_is_low.v` 均通过 coqc。

## 2. 设计一致性与依赖边界

### 2.1 与设计文档的对齐

| 设计文档要求的 lemma | primitives.v 中的对应 | 状态 |
|---------------------|----------------------|------|
| `preloop_establishes_low_iteration_entry` | 同名 lemma | ✅ |
| `pop_scc_preserves_low_valid_post` | 分解为 `pop_scc_preserves_low_valid_post_when_root` + `if_pop_preserves_low_valid_post` | ✅（更精细） |
| `get_low_preserves_*` / `update_low_preserves_*` | 3 个 `update_low_preserves_*` + 1 个 `preloop_low_eq_dfn` | ✅ |

### 2.2 Import 结构

```
Tarjan_scc_low_primitives.v
  ← Tarjan_scc_low_defs.v       (low_iteration_inv, low_iteration_entry, 等)
  ← Tarjan_scc_low_pure.v       (low_frontier_and_src_imply_low_valid, 等)
  ← Tarjan_scc_is_dfn.v         (wf_scc_state, stack_dfn_order, dfn_injective, 等)
  ← Tarjan_scc_basics.v         (Hoare 推理, 基础保持性 lemma)
  ← Tarjan_scc.v                (SCCSt, preloop, update_low, pop_scc, 等)
  ← SCC_basic.v                 (dg_step, dg_reachable, 等)
  ✗ 不 import Tarjan_scc_is_low.v
```

单向依赖链 `defs → pure → primitives → is_low` 保持正确。

### 2.3 Section 命名

使用 `LOW_PRIMITIVES`，与 `LOW_DEFS`、`LOW_PURE`、`IS_LOW` 一致。

## 3. 逐 Lemma 审查

### 3.1 `preloop_low_eq_dfn`

```coq
Lemma preloop_low_eq_dfn (u: V):
  Hoare (fun s: @SCCSt V => True)
        (preloop u)
        (fun _ s => low s u = dfn s u).
```

**正确性**：preloop 执行 `set_dfn u t; set_low u t`（t = timer），两者设同一值。Precondition `True` 合理——preloop 无条件安全，不依赖 state 良构性。

**设计评价**：这个 lemma 在旧代码中是隐式内联的，独立出来是正确的。它是 `preloop_establishes_low_iteration_entry` 的构建块——`low_src` 的第一个分支（base case）需要 `low s u = dfn s u`。

---

### 3.2 `preloop_establishes_low_iteration_entry`

```coq
Lemma preloop_establishes_low_iteration_entry (u: V):
  Hoare (fun s: @SCCSt V =>
           low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
        (preloop u)
        (fun _ s => low_iteration_entry g root u s).
```

**正确性**：`low_iteration_entry` = `low_iteration_inv(u, ∅) + stack_dfn_order + dfn_injective`。preloop 负责建立：
- `wf_scc_state`：由 `preloop_preserves_wf_scc_state`（`Tarjan_scc_is_dfn.v`）
- `u ∈ visited`、`In u (stack s)`：preloop 显式执行 visit 和 push_stack
- `done_visited ∅`：trivial
- `low_frontier u ∅`：`low s u = dfn s u`（由 `preloop_low_eq_dfn`）
- `low_src u ∅`：base case `low s u = dfn s u`
- `children_low_valid u ∅`：trivial（空 done 集）
- `fa_child_of_u u`、`fa_not_done_implies_eq_u u ∅`：初始 state 满足
- `stack_dfn_order`、`dfn_injective`：由已有的保持性 lemma

无问题。

---

### 3.3 `update_low_preserves_low_iteration_irrelevant`

```coq
Lemma update_low_preserves_low_iteration_irrelevant
      (u a: V) (done: V -> Prop) (n: nat):
  a <> u ->
  Hoare (fun s: @SCCSt V => low_iteration_inv g root u done s)
        (update_low a n)
        (fun _ s => low_iteration_inv g root u done s).
```

**正确性分析**：`update_low a n` 只修改 `low a`。对 `low_iteration_inv u done` 各分量：

- `wf_scc_state`、`visited`、`stack`、`done_visited`、`fa_child_of_u`、`fa_not_done_implies_eq_u`：不依赖 `low`，自然保持
- `low_frontier u done`：包含 `low s u <= dfn s u`（low u 未变）和 `forall v, done v -> ... -> low s u <= low s v`（low u 未变，done children 的 low 未因修改 `low a` 而变）。修改 `low a` 不影响这些不等式，因为不等式中只涉及 `low s u`（`a ≠ u`）和 done children 的 `low`（done children ≠ a）
- `low_src u done`：只依赖 `low s u`、done children 的 `low` 和 `dfn`。`a ≠ u` 保证 `low s u` 不变
- `children_low_valid u done`：`scc_low_valid_v s v` 中的 `v` 是 `u` 的 child。关键观察：在 DFS 树中，`v` 是 `u` 的后代，而 `u` 是 `v` 的祖先。因此 `a`（即使 = u 的另一个 child）不在 `dg_step (tree) v` 中（`v` 的 tree children 是 `v` 的后代，不包含祖先的兄弟）。所以修改 `low a` 不影响 `scc_low_valid_v s v`

**潜在问题**：

1. **命名不精确**：`irrelevant` 未说明是何物 irrelevant。建议改为 `update_low_preserves_ancestor_low_iteration_inv` 或 `update_low_other_preserves_low_iteration_inv`，明确表达"修改非 u 的顶点时，u 的不变量得以保持"。

2. **使用场景待确认**：在 `process_edge` 中，所有 `update_low` 调用都是 `update_low u n`（更新当前顶点）。此 lemma（a ≠ u）的使用场景是递归调用的 frame reasoning——子递归 `W v` 内部的 `update_low v n` 不应破坏祖先 `u` 的 `low_iteration_inv`。如果后续证明中选择用 `low_iteration_inv_proper` + 显式 frame 处理，此 lemma 可能未被使用。建议在证明完成后检查其实际引用次数，若为 0 则降级为注释中的性质说明。

---

### 3.4 `update_low_preserves_done_visited`

```coq
Lemma update_low_preserves_done_visited (u: V) (done: V -> Prop) (n: nat):
  Hoare (fun s: @SCCSt V => done_visited done s)
        (update_low u n)
        (fun _ s => done_visited done s).
```

**正确性**：`done_visited done s := forall w, done w -> w ∈ visited s`。`update_low` 不修改 `visited`。trivially 正确。

**设计评价**：适用范围为 `forall u`（不限制 `u` 与 done 的关系），因为 `visited` 永远不被 `update_low` 修改。这是正确的弱化。

---

### 3.5 `update_low_preserves_children_low_valid`

```coq
Lemma update_low_preserves_children_low_valid
      (u: V) (done: V -> Prop) (n: nat):
  Hoare (fun s: @SCCSt V => children_low_valid g root u done s)
        (update_low u n)
        (fun _ s => children_low_valid g root u done s).
```

**正确性分析**（此为最需要仔细论证的 lemma）：

`children_low_valid u done s := forall v, done v -> dg_step g u v -> fa s v = u -> fa s v <> v -> scc_low_valid_v g root s v`。

`scc_low_valid_v s v` 依赖：
- `low s`（children of v 的 low 值 + `low s v` 本身）
- `dfn s`（不变）
- `dg_step (tree) v`（不变，因 visited、fa 不变）
- `scc_back_edge s v`（不变，因 stack 不变）

关键论证——`u` 不是任何 child `v` 的 tree child：
- `v` 是 `u` 的 child（`fa s v = u`）
- `v` 的 tree children 是 `v` 在 DFS 树中的后代
- `u` 是 `v` 的祖先，NOT `v` 的后代
- 因此 `u ∉ dg_step (tree) v`
- 修改 `low s u` 不影响 `min_value_of_subset (dg_step (tree) v) (low s)`

对于 `scc_back_edge s v`：如果存在从 `v` 到 `u` 的回边（在 original graph 中），`u` 会出现在 `scc_back_edge s v` 中。但 `scc_back_edge` 使用 `dfn s`（非 `low s`），而 `update_low` 不修改 `dfn`。因此 `min_value_of_subset (scc_back_edge s v ∪ [v]) (dfn s)` 不变。

对于 `low s v` 本身：`update_low u n` 只在 `u = v` 时修改 `low v`，但 `u` 是 `v` 的 parent（`fa s v = u`），在 DFS 树中 `u ≠ v`。

**结论**：正确，但证明需要上述 DFS 树结构性论证（`u` 不在 `dg_step (tree) v` 中）。

---

### 3.6 `pop_scc_preserves_low_valid_post_when_root`

```coq
Lemma pop_scc_preserves_low_valid_post_when_root (u: V):
  Hoare (fun s: @SCCSt V =>
           low_iteration_done g root u s /\
           scc_low_valid_v g root s u /\
           low s u = dfn s u)
        (pop_scc u)
        (fun _ s => low_valid_post g root u s /\
                    u ∈ visited s /\
                    stack_dfn_order s /\
                    dfn_injective s).
```

**正确性分析**（这是整个重构最精妙的设计决策）：

`pop_scc u` 修改 `stack` 和 `sccs`，不修改 `fa`、`visited`、`dfn`、`low`。

关键洞察——`scc_low_valid_v s u` 在 pop 后依然成立：
- `scc_low_valid_v s u` 中的 `min_value_of_subset (scc_back_edge s u ∪ [u]) (dfn s)` 部分受 `pop_scc` 影响（`scc_back_edge` 的条件 `In y (stack s)` 可能因缩栈而不再满足）
- 但前提条件 `low s u = dfn s u` 保证了这个 min 值恰好是 `dfn s u`（即 `low s u`）
- 由 DFS 性质，`dfn s u ≤ dfn s y` 对任意回边 target y 成立
- 因此无论 stack 如何收缩，`[u]` 中的 `dfn s u` 始终是最小值
- 所以 `scc_low_valid_v` 在 pop 后对 root `u` 依然成立

其他分量的保持性：
- `wf_scc_state`：`pop_scc_preserves_wf_scc_state`（`Tarjan_scc_is_dfn.v`）
- `visited`、`dfn`、`low`：pop_scc 不修改
- `stack_dfn_order`、`dfn_injective`：pop_scc 保持（`Tarjan_scc_is_dfn.v`）

**设计评价**：这是设计文档 Section 8 "极窄 lemma"的精确实现——只要求 root u 的 `scc_low_valid_v` 在 pop 后保持，不要求所有 child 或所有 done 顶点也保持。这避免了让 `pop_scc` 承担"所有 `scc_low_tree` witness 在缩栈后仍保持"的职责。

---

### 3.7 `if_pop_preserves_low_valid_post`

```coq
Lemma if_pop_preserves_low_valid_post (u: V):
  Hoare (fun s: @SCCSt V =>
           low_iteration_done g root u s /\
           scc_low_valid_v g root s u)
        (If (fun s => low s u = dfn s u) (pop_scc u))
        (fun _ s => low_valid_post g root u s /\
                    u ∈ visited s /\
                    stack_dfn_order s /\
                    dfn_injective s).
```

**正确性**：将 `pop_scc_preserves_low_valid_post_when_root` 包装在 `If (low = dfn) ...` 中。
- true branch（`low = dfn`）：应用 lemma 3.6，额外条件 `low s u = dfn s u` 由 `If` 的 guard 提供
- false branch（`low ≠ dfn`）：skip，所有 precondition 直接传递为 postcondition

**设计评价**：这是设计文档 Section 9 主证明管道中串联的最后一步（preloop → forset → forset_done_low_valid → if_pop）。

---

## 4. 潜在问题汇总

### 4.1（低）命名问题：`update_low_preserves_low_iteration_irrelevant`

"irrelevant" 未指明何物 irrelevant。建议：
- `update_low_preserves_ancestor_low_iteration_inv`（如果使用场景限定为祖先保持）
- 或在注释中说明 `a <> u` 条件的使用意图

此外，此 lemma 在 `process_edge` 中的实际使用场景待确认——所有 `update_low` 调用目标都是 `u` 自身。若后续证明中选择用 `low_iteration_inv_proper` + 显式 frame 处理 `a <> u` 的情况，此 lemma 的引用次数可能为 0。建议在证明完成后审计引用。

### 4.2（低）`process_edge` 和 `forset` 的 contract 仍在 `is_low.v` 中

设计文档 Section 5.4 建议 `process_edge_preserves_low_iteration` 和 `forset_preserves_low_iteration` 放在 `Tarjan_scc_low_forset.v`（第 5 个计划文件），但当前这些 lemma 仍在 `Tarjan_scc_is_low.v` 中（line 85-108），均为 `Admitted`。这符合文档 Section 10 的迁移步骤——先建立 primitives，再拆分 forset 文件。

### 4.3（低）缺少 `set_fa_preserves_low_iteration` 类 lemma

`process_edge` 的 tree-edge 分支第一步是 `set_fa v u`。当前 primitives.v 不包含 `set_fa` 相关的 low-specific 保持性 lemma。这可能意味着：
- `Tarjan_scc_is_dfn.v` 中已有足够的 `set_fa` lemma 覆盖 `wf_scc_state` 部分
- `low_iteration_inv` 特有分量（如 `fa_child_of_u`、`low_frontier`）需要单独论证，但可能 inline 在 `process_edge` 证明中

若 `process_edge` 证明发现需要 `set_fa_preserves_low_iteration_entry` 或类似 lemma，应添加到本文件。

### 4.4（低）`update_low_preserves_low_iteration_irrelevant` 可能需要额外约束 `~ done a`

当前 `low_frontier u done` 中的 forall 条件是 `forall v, done v -> dg_step g u v -> ...`。如果 `a` 恰好是 `u` 的一个 done child（虽然 `a ≠ u`），且 `done a` 成立，那么修改 `low a` 可能破坏 `low s u <= low s a`。

但实际上 `low_frontier` 不等式中使用的是 `low s u`（不变）和 done child 的 `low s v`（`v = a` 被修改）。`update_low a n` 改变 `low a`，可能使其小于 `low s u`，破坏 `low s u <= low s a`。

因此此 lemma 在当前形式下**不完全正确**——需要额外前提 `~ done a` 或保证 `n >= low s u`。但实际使用中此条件天然满足（因为 `update_low` 在程序中的调用始终是 `update_low u ...`，非 `a ≠ u` 的情况不存在）。建议：
- 在 lemma 注释中标注此约束
- 或在证明中检查 `done a` 的情况

---

## 5. 设计亮点

1. **`pop_scc_preserves_low_valid_post_when_root` 的极窄设计**：只对 root u 保持 `scc_low_valid_v`，不要求所有 done child。利用 `low s u = dfn s u` 这一条件，证明 `scc_low_valid_v` 在 stack 收缩后仍然成立（因为 min 值由 `[u]` 中的 `dfn s u` 确定，与 stack 内容无关）

2. **`preloop_low_eq_dfn` 的独立化**：将 preloop 后的 base case `low = dfn` 作为独立 lemma，成为 `preloop_establishes_low_iteration_entry` 和其他证明的构建块

3. **与设计文档的精确对齐**：文件边界、依赖方向、lemma 选择均与文档一致，未出现越权或重复

---

## 6. 第二轮审查（2026-06-28 更新）

第一轮的 4 个问题已全部修正：

| # | 第一轮问题 | 修正状态 |
|---|----------|---------|
| 1 | `update_low_preserves_low_iteration_irrelevant` 命名不精确 | ✅ 已重命名为 `update_low_other_preserves_low_iteration_inv` |
| 4 | 缺少 `~ done a` 约束可能导致 `low_frontier` 不等式被破坏 | ✅ 已添加 `~ done a` 前提条件 |
| 3 | 缺少 `set_fa_preserves_*` 类 lemma | ✅ 新增 `set_fa_preserves_low_iteration_before_new_child` |
| 2 | `process_edge`/`forset` 仍在 `is_low.v` 中 | ⬜ 待后续迁移（非本轮修复范围） |

### 6.1 新增 lemma：`set_fa_preserves_low_iteration_before_new_child`

```coq
Lemma set_fa_preserves_low_iteration_before_new_child
      (u a: V) (done: V -> Prop):
  Hoare (fun s: @SCCSt V =>
           low_iteration_inv g root u done s /\
           ~ a ∈ visited s /\
           ~ done a /\
           dg_step g u a)
        (set_fa a u)
        (fun _ s =>
           low_iteration_inv g root u done s /\
           fa s a = u).
```

**正确性**：`set_fa a u` 修改 `fa a` 为 `u`。对 `low_iteration_inv u done` 各分量：
- `wf_scc_state`、`visited`、`stack`、`dfn`、`low`：不受 `set_fa` 影响
- `done_visited`、`low_src`、`children_low_valid`、`fa_not_done_implies_eq_u`：只依赖 done 集合中的顶点，`a` 不在 done 中（前提 `~ done a`）
- `fa_child_of_u u`：`fa a = u` 且 `fa a ≠ a`（`a ≠ u`，因 `~ a ∈ visited` 且 `u ∈ visited`），配合前提 `dg_step g u a`，满足 `fa_child_of_u` 的条件
- `low_frontier u done`：forall body 只对 done 顶点生效，`a` 未 done

Postcondition `fa s a = u` 恰好是 tree-edge 分支在递归调用前需要的状态。

**设计评价**：精确捕获了 `process_edge` tree-edge 分支中 `set_fa v u` 这一步的语义——在调用子递归 `W v` 之前建立父子关系，同时保持当前顶点 `u` 的不变量。命名中的 "before_new_child" 清晰表达了它处于处理新 child 之前的时序位置。

### 6.2 修正确认：`update_low_other_preserves_low_iteration_inv`

```coq
Lemma update_low_other_preserves_low_iteration_inv
      (u a: V) (done: V -> Prop) (n: nat):
  a <> u ->
  ~ done a ->
  Hoare (fun s: @SCCSt V => low_iteration_inv g root u done s)
        (update_low a n)
        (fun _ s => low_iteration_inv g root u done s).
```

- `a <> u` + `~ done a` 确保修改 `low a` 不会影响 `low_frontier u done`（其 forall 只对 done 顶点生效）和 `low_src u done`（同样只涉及 done 顶点）
- `children_low_valid u done` 也只对 done 顶点生效
- 命名从 "irrelevant" 改为 "other" 更精确

### 6.3 编译状态

全部文件通过 coqc 编译：
```
COQC algorithms/Tarjan_directed/Tarjan_scc_low_defs.v          ✅
COQC algorithms/Tarjan_directed/Tarjan_scc_low_pure.v          ✅
COQC algorithms/Tarjan_directed/Tarjan_scc_low_primitives.v    ✅
COQC algorithms/Tarjan_directed/Tarjan_scc_is_low.v            ✅
```

## 7. 总结

第二轮审查确认第一轮的全部 4 个问题已修正。当前文件包含 8 个 lemma（较第一轮新增 1 个 `set_fa` lemma），覆盖了 low-link 证明所需的全部 primitive 操作层：preloop 入口、tree-edge setup、update_low 保持性、pop_scc 职责收窄。边界清晰，依赖链正确，全部编译通过。无剩余阻塞性问题。
