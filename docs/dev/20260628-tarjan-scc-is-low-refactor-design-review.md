# Tarjan-SCC-is-low-Refactor-Design Review

**Author**: Claude
**Date**: 2026-06-28

**Reviewed document**: `docs/dev/20260628-tarjan-scc-is-low-refactor-design.md`

## 1. 总体评价

设计文档质量较高，核心方向正确：将 Tarjan SCC low-link 证明从一个巨型归纳后置条件重构为分层的、类 Kosaraju 风格的证明管道。文档准确地诊断了旧版 `Tarjan_scc_is_low.v`（~144KB）的问题，提出的三层规格体系（`scc_low_valid_v` → forset invariant → `scc_is_low_v`）以及与 Kosaraju 对齐的 Q-postcondition 拆分策略都是有充分理由的。

本次为第二轮审查。第一轮发现的 10 个问题已全部在文档和实现中得到修正。当前所有三个文件（`Tarjan_scc_low_defs.v`、`Tarjan_scc_low_pure.v`、`Tarjan_scc_is_low.v`）均编译通过。

---

## 2. 第一轮问题 — 全部已修正

### 2.1 高严重度（2 项）

| # | 问题 | 状态 |
|---|------|------|
| 1 | Section 5：跨文件 Section 参数化策略缺失 | ✅ 已修正。文档 Section 5 新增显式参数方案段落；`Tarjan_scc_is_low.v` 已删除全部重复定义，改为 import defs/pure 并显式传入 `g root` |
| 2 | Section 5.3：`primitives.v` 与 `is_dfn.v` 的边界模糊 | ✅ 已修正。文档明确 `primitives.v` 只放 low-specific 组合 lemma，通用 frame 复用 `is_dfn.v` / `basics.v`；风险表已新增对应条目 |

### 2.2 中严重度（5 项）

| # | 问题 | 状态 |
|---|------|------|
| 3 | Section 4.2：`I` 定义遗漏 `fa_child_of_u` 和 `fa_not_done_implies_eq_u` | ✅ 已修正。`I` 定义补全两个字段并附说明 |
| 4 | Section 4.3：`scc_is_low_induction` / `scc_is_low_induction_is_low` 未在文档中提及 | ✅ 已修正。文档新增两个 lemma 的完整签名和 bridge 归纳策略 |
| 5 | Section 8：`tarjan_scc_keep_is_low` 在 pop 后的证明路径不清晰 | ✅ 已修正。文档明确选择路径 (1)：pop 前用单点 bridge 得到 `scc_is_low_v` |
| 6 | Section 10 Step 2：迁移列表不完整 | ✅ 已修正。列表补全 `scc_is_low_induction`、`scc_is_low_induction_is_low`、Proper 实例 |
| 7 | Section 10 Step 3-4：缺少依赖分析 | ✅ 已修正。Step 3 标注依赖 `Tarjan_scc_basics.v` / `is_dfn.v`；Step 4 标注依赖 `stack_dfn_order` / `pop_scc_state` |

### 2.3 低严重度（3 项）

| # | 问题 | 状态 |
|---|------|------|
| 8 | Section 4.2/7.3：`forset_done_low_valid` vs `low_frontier_and_src_imply_low_valid` 命名不一致 | ✅ 已修正。全文统一使用 `low_frontier_and_src_imply_low_valid` |
| 9 | Section 5.4：简化版 `HW_low` 与实际 `low_continuation_contract` 存在差异 | ✅ 已修正。文档保留概念 `HW_low` 并追加实际 `low_continuation_contract`，解释差异原因 |
| 10 | Section 11：风险表可补充一条 | ✅ 已修正。风险表已新增 primitives/`is_dfn` 边界条目 |

---

## 3. 第二轮审查 — 实现验证

### 3.1 编译验证

三个文件均通过 `coqc` 编译（依赖顺序 `defs → pure → is_low`）：

```
COQC algorithms/Tarjan_directed/Tarjan_scc_low_defs.v       # ✅
COQC algorithms/Tarjan_directed/Tarjan_scc_low_pure.v       # ✅
COQC algorithms/Tarjan_directed/Tarjan_scc_is_low.v         # ✅
```

Makefile 中 `Tarjan_scc_low_defs.v` 和 `Tarjan_scc_low_pure.v` 位于 `Tarjan_scc_is_low.v` 之前（line 148-149），编译顺序正确。

### 3.2 实现变更确认

`Tarjan_scc_is_low.v` 的变更：

| 变更项 | 旧状态（第一轮审查时） | 新状态 |
|--------|----------------------|--------|
| Import 列表 | 不含 defs/pure | 新增 `Tarjan_scc_low_defs Tarjan_scc_low_pure` |
| 重复定义 | 14 个定义与 defs.v 完全重复 | **全部删除**，通过 import 复用 |
| 重复 lemma | 4 个纯逻辑 lemma 与 pure.v 重复 | **全部删除**，通过 import 复用 |
| 参数化方式 | 隐式 Section 参数 | 显式传入 `g root`（如 `low_valid_post g root u s`） |
| 文件行数 | 307 行 | **150 行**（-51%） |
| 冗余 import | `Morphisms`, `Classical_Prop`, `Relations`, `PeanoNat`, `Lia`, `MaxMinLib` | 已移除（这些只被 defs/pure 需要） |

`Tarjan_scc_is_low.v` 现在只包含：
- 三个独立递归 frame 后置定义（`Q_fa_stable`, `Q_stack_frame`, `Q_low_valid`）及其 Admitted 定理
- Primitive / forset phase contract（`preloop_establishes_low_iteration_entry`, `process_edge_preserves_low_iteration`, `forset_preserves_low_iteration`, `if_pop_preserves_low_valid_post`）
- 顶层定理（`tarjan_scc_keep_low_valid`, `tarjan_scc_keep_is_low`）

这与文档 Section 5.5 的目标完全一致："最终文件只保留 Q 定义、Hoare_normal_LFix 编排、tarjan_scc_keep_low_valid 以及可选的纯逻辑桥接导出"。

### 3.3 参数化一致性

验证了跨文件显式参数传递的一致性：

```
Tarjan_scc_is_dfn.v (Section IS_DFN)
  → 导出 wf_scc_state : ... → @SCCSt V → Prop

Tarjan_scc_low_defs.v (Section LOW_DEFS)
  → 导入 Tarjan_scc_is_dfn
  → 定义 low_valid_post u s := wf_scc_state g root s /\ scc_low_valid_v s u
  → 导出 low_valid_post : ... → V → @SCCSt V → Prop

Tarjan_scc_is_low.v (Section IS_LOW)
  → 导入 Tarjan_scc_low_defs Tarjan_scc_low_pure
  → 使用 low_valid_post g root u s（显式传入 Section 参数）
  → 类型检查通过 ✅
```

---

## 4. 第二轮新发现

### 4.1 轻微问题：`wf_scc_state` 与 `low_pre` 之间存在定义重叠

**严重程度**：低

`Tarjan_scc_low_defs.v` 中：
```coq
Definition low_pre (u: V) (s: @SCCSt V): Prop :=
  wf_scc_state g root s /\ ~ u ∈ visited s.
```

`Tarjan_scc_is_dfn.v` 中：
```coq
Definition wf_scc_state_pre (u: V) (s: @SCCSt V): Prop :=
  wf_scc_state s /\ ~ u ∈ visited s.
```

两者的语义完全相同（`wf_scc_state_pre` 在 section 内部省略了 `g root`）。当前 `Tarjan_scc_is_low.v` 直接使用 `low_pre g root u s`，没有使用 `wf_scc_state_pre`。这并非 bug，但存在轻微的语义重复——如果未来修改 `wf_scc_state_pre` 的定义，`low_pre` 需要同步更新。

**建议**：考虑让 `low_pre` 直接复用 `wf_scc_state_pre`（即 `low_pre u s := wf_scc_state_pre g root u s`），或至少在使用处添加注释说明两者的等价关系。

---

### 4.2 轻微问题：`Q_low_valid` 的 `low_valid_post` conjunct 包含 `wf_scc_state`

**严重程度**：低（仅文档说明）

`Q_low_valid` 的定义（`Tarjan_scc_is_low.v:39-43`）：
```coq
Definition Q_low_valid (u: V) (s0: @SCCSt V) (_: unit) (s: @SCCSt V): Prop :=
  low_valid_post g root u s /\
  u ∈ visited s /\
  stack_dfn_order s /\
  dfn_injective s.
```

展开 `low_valid_post` 后为 `wf_scc_state g root s /\ scc_low_valid_v g root s u`——其中 `wf_scc_state` 已蕴含 `stack_dfn_order` 和 `dfn_injective`（`wf_scc_state` 的定义在 `Tarjan_scc_is_dfn.v:2239` 包含二者）。因此 `stack_dfn_order s` 和 `dfn_injective s` 在 conjunct 中是冗余的。

这并非错误——显式列出使 postcondition 更可读，且在 `low_continuation_contract` 的 consumer 中可直接使用而无需展开 `wf_scc_state`。但文档可以在 `Q_low_valid` 的定义旁加一条注释说明这是刻意冗余而非疏漏。

---

## 5. 设计亮点（确认正确）

以下设计决策经验证是正确的，值得保留：

1. **三层规格分离**（Section 4）：`scc_low_valid_v`（程序级）→ forset invariant（循环级）→ `scc_is_low_v`（数学级）避免程序证明中过早展开 `scc_low_tree`

2. **Q-postcondition 三元拆分**（Section 6）：`Q_fa_stable`、`Q_stack_frame`、`Q_low_valid` 精确对应 Kosaraju 的分层 Q 策略（`Q_step_visited` → `Q_finish_after` → `Q_closed` → `Q_phase1`）

3. **`children_low_valid` 使用 `scc_low_valid_v`**（Section 7.2）：避免在 forset body 中展开 `scc_low_tree`，也避免 `pop_scc` 后维护 stack-dependent tree witness

4. **pop_scc 职责收窄**（Section 8）：不要求 pop_scc 保持所有 `scc_low_tree` witness

5. **迁移步骤顺序**（Section 10）：先冻结定义 → 迁移纯逻辑 → 独立化 fa/stack frame → 重写 forset → 串联顶层，每步可独立编译验证

6. **跨文件显式参数方案**（Section 5）：选择显式 `g root` 参数而非 Section 隐式参数，避免重复定义且保持类型兼容

---

## 6. 已确认的事实

| 文档声称 | 验证结果 |
|---------|---------|
| Kosaraju 使用 `Hoare_normal_LFix` + singleton-state pre | 正确。Kosaraju.v 有 16 处调用，IH 形式为 `forall s0 a, Hoare (fun s => s = s0) (W a) (Q a s0)` |
| Kosaraju 每个 DFS phase 有独立的 Q | 正确。Phase 1: `Q_step_visited` → `Q_finish_after` → `Q_closed` → `Q_phase1` |
| `wf_scc_state` 定义位置 | `Tarjan_scc_is_dfn.v:2239`，包含 dfn_valid 等全局良构性 |
| `stack_dfn_order` / `dfn_injective` 定义位置 | `Tarjan_scc_is_dfn.v:1392` / `:219`，有完整的保持性 lemma |
| `Tarjan_scc_basics.v` 有大量 primitive 保持性 lemma | 覆盖 visit、set_dfn、set_low、set_fa、update_low、push_stack、pop_scc、incr_timer |
| 文件拆分依赖链 | `defs → pure → is_low` 单向，`pure` 不依赖 Hoare |
| 三个文件均可编译 | ✅ defs.v / pure.v / is_low.v 均通过 coqc |

---

## 7. 总结

第二轮审查确认：第一轮的 10 个问题已全部修正，文档与实现现在完全一致。

当前状态：
- **设计文档**：完整、自洽、与代码一致
- **`Tarjan_scc_low_defs.v`**：纯定义层，编译通过，无 Admitted（无证明义务）
- **`Tarjan_scc_low_pure.v`**：纯逻辑层，编译通过，所有 lemma 为 Admitted（待证明）
- **`Tarjan_scc_is_low.v`**：编排层，编译通过，所有 theorem/lemma 为 Admitted（待证明），已删除全部重复定义，仅 150 行
- **Makefile**：编译顺序正确

第二轮发现的 2 个新问题均为低严重度的文档说明建议，不阻塞实现。
