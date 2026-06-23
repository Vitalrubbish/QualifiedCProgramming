# Tarjan SCC Monad 程序阶段分析

**Author**: Vitalrubbish & Claude  
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
| **前** `low_pre u` | `~u∈visited ∧ stack_in_visited ∧ dfn_inv ∧ dfn_valid ∧ fa_visited` | `u` 未被访问；栈中顶点均已 visited；fa 指针形成合法 DFS 森林 |
| **后** `low_post u` | `wf_scc_state s ∧ scc_low_valid_v s u` | 全局 DFS 森林合法；`low s u` 等于 min{ `dfn u`, `low c`(树孩子), `dfn b`(回边目标) } |

### 3.1 阶段 1：`preloop a`

| | 形式定义 | 图论含义 |
|---|---|---|
| **前** | `low_pre a s` | `a` 未被访问，是父顶点的一个新孩子 |
| **后** | `low_forset_inv a ∅ s ∧ (∀v, fa s v = a → v = a)` | `dfn a` = 当前时钟；`low a` = `dfn a`（尚未处理任何邻居）；`a` 入栈；没有其他顶点误将 `a` 当作父顶点 |

### 3.2 阶段 2：`forset` — 核心循环

**不变量 P(done, s)**：遍历 `a` 的所有邻居，done 从 `∅` 逐步扩展到 `dg_step g a`。

```
P(done, s) :=
  ① low_forset_inv a done s       (* low a 对已处理邻居 done 正确 *)
  ∧ ② done_visited done s          (* done 中顶点均已 visited *)
  ∧ ③ (∀v, fa s v = a ∧ fa s v ≠ v → v ∈ done)  (* a 的 fa-孩子全在 done 中 *)
  ∧ ④ (∀v, In v (stack s) → fa s v ≠ v)         (* 栈上顶点有合法父顶点 *)
```

各 conjunct 的图论含义：

| # | 图论含义 |
|---|----------|
| ① | `low a` = min{ `dfn a`, `low c`（已处理的树孩子 c∈done），`dfn b`（已处理的回边目标 b∈done）} |
| ② | 所有已处理的邻居都已 visited |
| ③ | `a` 在 DFS 树中的所有孩子都已处理完毕 |
| ④ | 栈上每个顶点都有自己的 DFS 父顶点（不是自环 root） |

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
| `set_fa v a` | `P(done) ∧ ~v∈visited` | `P(done) ∧ fa v = a ∧ low_pre v` |
| `W v` | `low_pre v ∧ a∈visited` | `low_post v ∧ a∈visited` + v∈visited + done_visited 保持 + fa-child 保持 |
| `update_low a (low v)` | `P(done) ∧ low v 已知` | `P(done ∪ [v])` (via `low_forset_inv_expand_child_done`) |

#### 3.2b 非树边 `a → v`（v ∈ visited）

程序：`If (In v (stack s)) (dv ← get' (dfn v) ;; update_low a dv) (skip)`

**图论含义**：`a` 和 `v` 之间不是父子关系。

| 情况 | 图论含义 | 操作 | 结果 |
|------|----------|------|------|
| **回边**：v 在栈上 | `a → v` 是后代向祖先的回边。v 在 a 的 DFS 路径上，a 和 v 属于同一 SCC | `low a := min(low a, dfn v)` | `P(done ∪ [v])` (via `update_low_back_edge`) |
| **cross edge**：v 不在栈 | `a → v` 跨越不同子树。v 属于已弹出的 SCC | skip | `P(done ∪ [v])` (done_visited 因 v∈visited 成立) |

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
② done_visited (dg_step g a)         }  P(dg_step g a)
③ fa-child ⊆ dg_step g a             }
④ stack_fa_neq                      }
    ↓ (forset_end_implies_scc_low_valid_v)
scc_low_valid_v s a
```

结合 `wf_scc_state s`（从 ① 拆出）→ `low_post a s`。

### 3.3 阶段 3：`If (low a = dfn a) (pop_scc a)`

| | 形式定义 | 图论含义 |
|---|---|---|
| **前** | `low_post a s` = `wf_scc_state ∧ scc_low_valid_v s a` | `a` 的 low-link 值已正确 |
| **后** | `low_post a s` | 保持不变 |
| **条件** `low a = dfn a` | `a` 及其子树内所有顶点无法通过回边到达 dfn **严格小于** `dfn a` 的顶点 | `a` 是 SCC 根 |
| **pop_scc a** | 弹出栈上从 `a` 到栈顶的所有顶点 | 这些顶点构成一个 SCC |

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

---

## 5. 关键引理依赖

| 阶段 | 关键引理 | 文件 |
|------|----------|------|
| 1 | `preloop_establishes_low_forset_inv` | `Tarjan_scc_is_low.v` |
| 1 | `preloop_keeps_fa` | `Tarjan_scc_is_low.v` |
| 2a | `set_fa_W_preserves_low_forset_inv` | `Tarjan_scc_is_low.v` |
| 2a | `low_forset_inv_expand_child_done` | `Tarjan_scc_is_low.v` |
| 2a | `update_low_tree_edge` | `Tarjan_scc_is_low.v` |
| 2b | `update_low_back_edge` | `Tarjan_scc_is_low.v` |
| 2c | `forset_end_implies_scc_low_valid_v` | `Tarjan_scc_is_low.v` |
| 3 | `pop_scc_keep_scc_low_valid_v` | `Tarjan_scc_is_low.v` |
| P | `low_forset_inv_proper` | `Tarjan_scc_is_low.v` |
| 不动点 | `Hoare_fix_logicv_conj` | `StateRelHoare.v` |
| visited | `tarjan_scc_keep_visited` / `_self_visited` / `_forall` | `Tarjan_scc_basics.v` |
