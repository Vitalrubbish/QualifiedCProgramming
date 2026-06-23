# Tarjan SCC Monad 程序阶段分析

**Author**: Vitalrubbish
**Date**: 2026-06-23

## 1. 程序结构

```
tarjan_scc_f W a :=           (* 单个顶点的处理 *)
  (1) preloop a ;;
  (2) forset (dg_step g a) (process_edge a W) ;;
  (3) If (low a = dfn a) (pop_scc a)

tarjan_scc u := Lfix tarjan_scc_f u    (* 不动点递归 *)
```

---

## 2. 阶段概览

| 阶段 | 程序 | 图论含义 |
|------|------|----------|
| 0 | `tarjan_scc g u` | 以 `u` 为根的 DFS 子树，结束后 `u` 的 low-link 值正确 |
| 1 | `preloop a` | 给 `a` 分配 dfn（发现时间），初始化 low，入栈 |
| 2 | `forset` | 遍历 `a` 的所有出边邻居，逐步扩展 done 集 |
| 2a | 树边 (v 未访问) | DFS 树中添加孩子 `v`，递归处理，用 `low v` 更新 `low a` |
| 2b | 非树边 (v 已访问) | 回边：`low a := min(low a, dfn v)`；cross edge：跳过 |
| 3 | `If (low a = dfn a)` | 判断 `a` 是否为 SCC 根，若是则弹出 SCC |

---

## 3. 各阶段的前条件、后条件与不变量

### 3.0 顶层 `tarjan_scc g u`

| | 形式定义 | 图论含义 |
|---|---|---|
| **前** `low_pre u` | `wf_scc_state_pre u s`，即 `wf_scc_state s ∧ ~u ∈ visited s` | `u` 未被访问；全局状态满足 `wf_scc_state` |
| | 额外要求 `original_vvalid g u` | `u` 必须是图 `g` 中的合法顶点（该条件在 `low_pre` 定义之外单独给出） |
| **后** `low_post u` | `wf_scc_state s ∧ scc_low_valid_v s u` | 全局 DFS 森林合法；`low s u` 等于 min{ `dfn u`, `low c`(树孩子), `dfn b`(回边目标) } |

其中全局良构谓词沿用 `Tarjan_scc_is_low.v` 中的定义：

```
wf_scc_state s := stack_in_visited s ∧ dfn_inv s ∧ dfn_valid g s root ∧ fa_visited s
```

（注：当前实现把 `stack_dfn_order` 与 `dfn_injective` 放在 `wf_scc_state` 之外单独携带；为表述简洁，下文在 forset 不变量中显式列出二者。也可选择把它们并入 `wf_scc_state`。）

### 3.1 阶段 1：`preloop a`

| | 形式定义 | 图论含义 |
|---|---|---|
| **前** | `low_pre a s` | `a` 未被访问，是父顶点的一个新孩子 |
| **后** | `low_forset_inv a ∅ s`<br>`∧ (∀v, fa s v = a → v = a)`<br>`∧ In a (stack s)`<br>`∧ stack_dfn_order s`<br>`∧ dfn_injective s` | `dfn a` = 当前时钟；`low a` = `dfn a`；`a` 入栈并 visited；尚无其他顶点以 `a` 为父；栈上保持 dfn 递减序与单射性 |

### 3.2 阶段 2：`forset` — 核心循环

**不变量 P(done, s)**：遍历 `a` 的所有邻居，done 从 `∅` 逐步扩展到 `dg_step g a`。

```
P(done, s) :=
  ① low_forset_inv a done s                     (* low a 对已处理邻居 done 正确 *)
  ∧ ② done_visited done s                        (* done 中顶点均已 visited *)
  ∧ ③ done ⊆ dg_step g a                         (* done 是 a 的出边邻居子集 *)
  ∧ ④ (∀v, fa s v = a ∧ fa s v ≠ v → v ∈ done)   (* a 的 fa-孩子全在 done 中 *)
  ∧ ⑤ In a (stack s)                             (* a 仍在栈上 *)
  ∧ ⑥ stack_dfn_order s                          (* 栈自上而下按 dfn 递减 *)
  ∧ ⑦ dfn_injective s                            (* 已访问顶点 dfn 互不相同 *)
```

各 conjunct 的图论含义：

| # | 图论含义 |
|---|----------|
| ① | `low a` = min{ `dfn a`, `low c`（已处理的树孩子 c∈done），`dfn b`（已处理的回边目标 b∈done）} |
| ② | 所有已处理的邻居都已 visited |
| ③ | `done` 只包含 `a` 在图 `g` 中的出边邻居 |
| ④ | `a` 在 DFS 树中的所有 fa-孩子都已处理完毕 |
| ⑤ | 当前顶点 `a` 尚未被弹出，仍在栈上 |
| ⑥ | 栈中顶点自上而下 dfn 严格递减；这保证栈上顶点都在当前 DFS 路径上，且栈顶下方任意顶点都是其祖先 |
| ⑦ | 不同已访问顶点的 `dfn` 不同，保证栈序与发现序一一对应 |

**关于旧版不变量 ④ 的修正**：此前版本要求“栈上所有顶点满足 `fa v ≠ v`”，这过强了——DFS 树根节点满足 `fa root = root` 且会被压栈。正确的性质已由 `wf_scc_state` 中的 `fa_visited` 捕获：若 `fa v ≠ v`，则 `fa v` 必已 visited。因此新版 P 删去了这条过强公式，并显式加入 `In a (stack s)`、`stack_dfn_order` 与 `dfn_injective` 来弥补原先漏掉的栈序与单射条件。

**关于 conjunct ⑤ 的独立性**：`wf_scc_state` 中只有 `stack_in_visited` 涉及栈，它要求“栈上顶点都已 visited”，但反向不成立——一个 visited 顶点可能已经被 `pop_scc` 弹出而不再在栈上。因此 `a ∈ visited`（含在 ① 的 `low_forset_inv` 中）并不能推出 `In a (stack s)`；后者必须作为独立 conjunct 显式携带。

**不变量推进**：`P(done)` → 处理一个邻居 `v` → `P(done ∪ [v])`

#### 3.2a 树边 `a → v`（v ∉ visited）

程序：`set_fa v a ;; W v ;; lv ← get' (low v) ;; update_low a lv`

**图论含义**：`v` 是 `a` 在 DFS 树中的新孩子。递归处理 `v` 的子树，然后用 `low v` 更新 `low a`。

为什么更新 `low a`？这是 Tarjan 算法的核心：`v` 的子树内可能通过回边到达某个 dfn 更小的祖先 `w`。`low v` 记录了 `v` 能到达的最小 dfn。把 `low v` 传给 `a`，就实现了"`a` 能通过树边 `a→v` 间接到达 `w`"。

图例：

```
     a (dfn=5)
     │ 树边
     v (dfn=6)
     │ 回边
     w (dfn=2, 在栈上)

low v = 2 (v→w 的回边) → update_low a → low a = 2
```

| 子步骤 | 前条件 | 后条件 |
|--------|--------|--------|
| `set_fa v a` | `P(done) ∧ ~v∈visited ∧ dg_step g a v` | `P^-(done, v) ∧ fa v = a ∧ low_pre v` |
| `W v` | `P^-(done, v) ∧ fa v = a ∧ low_pre v` | `P^-(done, v) ∧ fa v = a ∧ low_post v`（递归保持父层 low-link 与栈序） |
| `update_low a (low v)` | `P^-(done, v) ∧ fa v = a ∧ low_post v` | `P(done ∪ [v])` (via `low_forset_inv_expand_child_done`) |

其中 **中间不变量 `P^-(done, v)`** 表示：除新发现的孩子 `v` 可暂不在 `done` 中（它马上会被递归处理并加入 `done`）外，`P(done)` 的其余 conjunct 均成立。形式化地：

```
P^-(done, v) :=
  ① low_forset_inv a done s
  ∧ ② done_visited done s
  ∧ ③ done ⊆ dg_step g a
  ∧ ④' (∀w, fa s w = a ∧ fa s w ≠ w ∧ w ≠ v → w ∈ done)
  ∧ ⑤ In a (stack s)
  ∧ ⑥ stack_dfn_order s
  ∧ ⑦ dfn_injective s
```

#### 3.2b 非树边 `a → v`（v ∈ visited）

程序：`If (In v (stack s)) (dv ← get' (dfn v) ;; update_low a dv) (skip)`

**图论含义**：`a` 和 `v` 之间不是父子关系（此时 `v` 已在 `done` 的处理范围内或本次将被加入 `done`）。

**入口条件**：`P(done) ∧ v∈visited ∧ dg_step g a v`。

| 情况 | 图论含义 | 操作 | 结果 |
|------|----------|------|------|
| **回边**：v 在栈上 | `a → v` 是后代向祖先的回边。v 在 a 的 DFS 路径上，a 和 v 属于同一 SCC | `low a := min(low a, dfn v)` | `P(done ∪ [v])` (via `update_low_back_edge`) |
| **cross edge / forward edge**：v 不在栈 | `a → v` 不是回边（v 不是 a 的祖先）。v 要么属于已弹出的 SCC，要么是 a 的后代但已随子 SCC 弹出。无论哪种情况都不会让 `a` 通过该边到达更小 dfn 的祖先 | skip | `P(done ∪ [v])`：done_visited 因 `v∈visited` 成立；`low_forset_inv a (done ∪ [v])` 也成立，因为 cross-edge 顶点既不是 `a` 的 fa-孩子（不满足 `fa s v = a`），也不在栈上（不满足 `In v (stack s)`），因此把它加入 `done` 不改变 `children_done` 和 `back_edges_done` |

**为什么回边取 `dfn v` 而不是 `low v`？** 回边只能跨一步——从 `a` 直接回到 `v`。不能"借用" `v` 已经算好的 `low v` 再往上跳，因为那可能需要多步回边。`low v` 的信息已经通过 `v` 的父顶点向上传递了。

图例：

```
     w (dfn=2)
     │
     u (dfn=3)
     │
     a (dfn=5) ──── 回边 ────→ u (dfn=3, 在栈上)

low a = min(low a, dfn u) = min(5, 3) = 3
→ a, u, w 在同一 SCC
```

#### 3.2c 循环结束

当 `done = dg_step g a`（所有邻居处理完毕），调用 `forset_end_implies_scc_low_valid_v`：

```
① low_forset_inv a (dg_step g a)    }
② done_visited (dg_step g a)         }
③ done ⊆ dg_step g a  (此时取等)      }  P(dg_step g a)
④ fa-child ⊆ done                    }
⑤ In a (stack s)                     }
⑥ stack_dfn_order s                  }
⑦ dfn_injective s                    }
    ↓ (forset_end_implies_scc_low_valid_v)
scc_low_valid_v s a
```

`forset_end_implies_scc_low_valid_v` 实际用到的是 ①、② 与 `∀v, fa s v = a ∧ fa s v ≠ v → dg_step g a v`（由 ③④ 及树边构造保证）。结合 `wf_scc_state s`（含在 ① 中）→ `low_post a s`。

### 3.3 阶段 3：`If (low a = dfn a) (pop_scc a)`

| | 形式定义 | 图论含义 |
|---|---|---|
| **前** | `low_post a s` = `wf_scc_state ∧ scc_low_valid_v s a` | `a` 的 low-link 值已正确 |
| **后** | `low_post a s` | 保持不变 |
| **条件** `low a = dfn a` | `a` 及其子树内所有顶点无法通过回边到达 dfn **严格小于** `dfn a` 的顶点 | `a` 是 SCC 根 |
| **pop_scc a** | 弹出栈上从 `a` 到栈顶的所有顶点 | 这些顶点构成一个 SCC |

**`low_post a s` 的保持性**：`low_post a s = wf_scc_state s ∧ scc_low_valid_v s a`。`pop_scc a` 修改 `stack`（截断）和 `sccs`（追加新 SCC），但不修改 `visited`、`dfn`、`fa`、`low`。`wf_scc_state` 的四个子项——`stack_in_visited`（截断后的栈仍是 `visited` 子集）、`dfn_inv`、`dfn_valid`、`fa_visited`——都只依赖 `visited`、`dfn`、`fa`，不依赖 `stack` 的具体内容，因此均被保持；`scc_low_valid_v s a` 的保持由 `pop_scc_keep_scc_low_valid_v` 给出。

**SCC 判断图例：**

```
     w (dfn=2, SCC 根)  ← 已弹出
     │
     u (dfn=3) ──── 回边 ────→ w
     │
     a (dfn=5) ──── 回边 ────→ u
     │
     v (dfn=6)

遍历到 a: low a = 3 (a→u→w), dfn a = 5. low a ≠ dfn a → a 不是 SCC 根
遍历到 u: low u = 2 (u→w),   dfn u = 3. low u ≠ dfn u → u 不是 SCC 根
遍历到 w: low w = 2 = dfn w. → w 是 SCC 根 → pop 出 {w, u, a, v}
```

---

## 4. 整体不变量流

```
                         low_forset_inv u done s
                              ↓
              low u = min{ dfn u,     (* u 自身 *)
                           low c,     (* 树孩子 c 的 low 值 *)
                           dfn b }    (* 回边目标 b 的 dfn 值 *)

                        done 逐步扩大
              ∅ → {c₁} → {c₁,c₂} → ... → dg_step g u
                        ↓
              forset_end_implies_scc_low_valid_v
                        ↓
              low u 正确 → low u = dfn u ?
                        ↓ yes              ↓ no
                   pop_scc u           返回父顶点
                   (找到 SCC)          继续遍历
```

在整个过程中，以下全局/栈上性质由 `wf_scc_state`、`stack_dfn_order` 与 `dfn_injective` 共同维护：

- `wf_scc_state`：保证 `visited`/`stack`/`dfn`/`fa` 的基本一致性；
- `stack_dfn_order`：保证栈上顶点按 dfn 自上而下递减，因此“v 在栈上”等价于“v 是当前顶点的 DFS 祖先”；
- `dfn_injective`：保证不同已访问顶点 dfn 不同，使栈序与发现序严格对应。

`fa_visited`（已含于 `wf_scc_state`）替代了旧版过强的“栈上顶点必满足 `fa v ≠ v`”：它只要求非根顶点的父顶点已被 visited，而允许 DFS 根满足 `fa root = root`。

---

## 5. 关键引理依赖

| 阶段 | 关键引理 | 文件 | 作用 |
|------|----------|------|------|
| 0 | `original_vvalid g u`（顶层前提） | `graph_basic.v` | 保证 `u` 是合法顶点，避免对非顶点调用 |
| 1 | `preloop_establishes_low_forset_inv` | `Tarjan_scc_is_low.v` | `preloop a` 建立 `low_forset_inv a ∅` |
| 1 | `preloop_keeps_fa` | `Tarjan_scc_is_low.v` | `preloop` 不改变已赋值的 `fa` |
| 1 | `preloop_in_stack` | `Tarjan_scc_basics.v` | `preloop a` 后 `a ∈ stack` |
| 1 | `preloop_preserves_stack_dfn_order` | `Tarjan_scc_is_dfn.v` | `preloop` 保持栈上 dfn 递减序 |
| 1 | `preloop_preserves_dfn_injective` | `Tarjan_scc_is_dfn.v` | `preloop` 保持已访问顶点 dfn 互异 |
| 2a | `set_fa_preserves_wf_scc_state_pre` | `Tarjan_scc_is_low.v` | `set_fa v a` 后为 `v` 建立 `low_pre v` |
| 2a | `set_fa_W_preserves_low_forset_inv` | `Tarjan_scc_is_low.v` | 树边分支保持父层 `low_forset_inv` 并完成递归 |
| 2a | `W_preserves_ancestor_inv` | `Tarjan_scc_is_low.v` | 递归调用 `W v` 保持祖先 `u` 的 `low_forset_inv` 与 dfn 序 |
| 2a | `low_forset_inv_expand_child_done` | `Tarjan_scc_is_low.v` | 把孩子 `v` 从 `done` 外移入 `done` 时更新 low-link 不变量 |
| 2a | `update_low_tree_edge` | `Tarjan_scc_is_low.v` | 用 `low v` 更新 `low a` 保持 `low_forset_inv` |
| 2b | `update_low_back_edge` | `Tarjan_scc_is_low.v` | 用 `dfn v` 更新 `low a` 保持 `low_forset_inv` |
| 2c | `children_done_full_eq` | `Tarjan_scc_is_low.v` | `done = dg_step g u` 时 `children_done` 等于 DFS 树孩子集 |
| 2c | `back_edges_done_full_eq` | `Tarjan_scc_is_low.v` | `done = dg_step g u` 时 `back_edges_done ∪ [u]` 等于 `scc_back_edge s u ∪ [u]` |
| 2c | `forset_end_implies_scc_low_valid_v` | `Tarjan_scc_is_low.v` | 循环结束时从 `low_forset_inv` 推出 `scc_low_valid_v` |
| 3 | `pop_scc_keep_scc_low_valid_v` | `Tarjan_scc_is_low.v` | `pop_scc` 保持 `scc_low_valid_v` |
| 3 | `pop_scc_preserves_stack_dfn_order` | `Tarjan_scc_is_dfn.v` | `pop_scc` 保持栈上 dfn 递减序 |
| P | `low_forset_inv_proper` | `Tarjan_scc_is_low.v` | `low_forset_inv` 对 `done` 的 Setoid  Properness |
| P | `done_visited_proper` | `Tarjan_scc_is_low.v` | `done_visited` 对 `done` 的 Properness |
| 不动点 | `Hoare_fix_logicv_conj` | `StateRelHoare.v` | 对 `tarjan_scc` 做带辅助不变量的不动点归纳 |
| visited | `tarjan_scc_keep_visited` / `_self_visited` / `_forall` | `Tarjan_scc_basics.v` | visited 集合的单调/保持性 |
| fa-孩子 | `process_edge_keep_fa_children` | `Tarjan_scc_is_low.v` | `process_edge` 保持“fa-孩子必是 g 中邻居” |
| fa-孩子 | `tarjan_scc_keep_fa_children_in_universe` | `Tarjan_scc_is_low.v` | 递归调用保持上述 fa-孩子性质 |
