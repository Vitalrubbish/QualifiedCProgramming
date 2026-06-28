# Q_stack_frame 审查
**Author**: Claude
**Date**: 2026-06-28

## 本轮变更

**`is_dfn.v`** 新增 5 个引理签名：
`get_dfn_update_low_keep_in_stack`、`get_low_update_low_keep_stack_dfn_order`、
`get_dfn_update_low_keep_stack_dfn_order`、`process_edge_preserves_stack_dfn_order`、
`forset_preserves_stack_dfn_order`

**`is_low.v`** 修改 1 个引理签名：
`if_pop_preserves_Q_stack_frame` 改为无条件携带 `stack_dfn_order s`

## 对上一轮两个问题的回应

| 问题 | 状态 |
|------|------|
| `stack_dfn_order` 的 forset 级保持引理缺失 | ✅ `process_edge_preserves_stack_dfn_order` + `forset_preserves_stack_dfn_order` 已添加 |
| `if_pop_preserves_Q_stack_frame` 的 `cur ≠ u` 前提不足 | ⚠️ 添加了 `stack_dfn_order`，但同时**丢失了 `In u (stack s)`** |

---

## 当前问题：`if_pop_preserves_Q_stack_frame` 缺少 `In u (stack s)` 前提

当前签名：

```coq
Lemma if_pop_preserves_Q_stack_frame (u cur: V) (s0: @SCCSt V):
  Hoare (fun s => Q_stack_frame cur s0 tt s /\ stack_dfn_order s)
        (If (fun s => low s u = dfn s u) (pop_scc u))
        (Q_stack_frame cur s0).
```

对比上一版：

```coq
(* 上一版 *)
Hoare (fun s => Q_stack_frame cur s0 tt s /\
                (cur = u -> stack_dfn_order s /\ In u (stack s)))
```

改动分析：
- `stack_dfn_order s` 改为无条件携带 ✅（修复了 `cur ≠ u` 情形）
- `In u (stack s)` **被完全移除** ❌

`In u (stack s)` 是必需的——在 pop_scc 分支中，无论是 `cur = u`（使用 `pop_scc_establishes_stack_frame_for_root`）还是 `cur ≠ u`（使用 `pop_scc_keeps_older_stack_vertex`），都需要知道 `u` 在栈上。`pop_scc_keeps_older_stack_vertex` 的签名明确要求 `In u (stack s)`：

```coq
Lemma pop_scc_keeps_older_stack_vertex (s: @SCCSt V) (u anc: V):
  stack_dfn_order s ->
  In anc (stack s) ->
  In u (stack s) ->           (* ← 必需 *)
  dfn s anc < dfn s u ->
  In anc (stack (pop_scc_state s u)).
```

在 Lfix 使用场景中，`In u (stack s)` 由 `preloop u` 保证（preloop 推入 `u`），因此应作为前提纳入。

**建议**：恢复 `In u (stack s)`：

```coq
Hoare (fun s => Q_stack_frame cur s0 tt s /\ stack_dfn_order s /\ In u (stack s))
      (If (fun s => low s u = dfn s u) (pop_scc u))
      (Q_stack_frame cur s0).
```

---

## 支架完整性评估

以下为 Lfix 归纳证明 `tarjan_scc_keep_stack_frame` 所需的完整引理矩阵（`u` = 最外层调用顶点，`x` = 当前 Lfix 顶点）：

| 步骤 | `Q_stack_frame u s0` | `stack_dfn_order` | `dfn_injective` |
|------|---------------------|-------------------|-----------------|
| `preloop x` | `preloop_preserves_Q_stack_frame` + `preloop_establishes_Q_stack_frame_entry` | `preloop_preserves_stack_dfn_order` | is_dfn 中已存在 |
| `forset` | `forset_preserves_Q_stack_frame` | `forset_preserves_stack_dfn_order` | is_dfn 中已存在 |
| `If (pop_scc x)` | `if_pop_preserves_Q_stack_frame` | `pop_scc_preserves_stack_dfn_order` | is_dfn 中已存在 |

**结论**：除上述 `In u (stack s)` 问题外，支架引理的签名覆盖完整。`tarjan_scc_keep_stack_frame` 可用 `Hoare_fix_logicv_conj` 组合证明（主属性 `Q_stack_frame u s0`，辅助属性 `stack_dfn_order /\ dfn_injective`）。
