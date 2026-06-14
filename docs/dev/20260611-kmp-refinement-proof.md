# KMP Refinement Proof 全流程解析

**Author**: Vitalrubbish
**Date**: 2026-06-11

## 概述

`kmp_rel.c` 是 QCP 框架中一个完整的 refinement proof 案例，它演示了如何将 C 程序的符号执行验证与纯 monad 程序的数学正确性证明**解耦**。与普通直接证明（如 `array_auto.c`、`bst_insert.c`）不同，refinement proof 将验证任务拆分为三个独立层次：

1. **Monad 抽象算法层**：在 `MonadLib/Examples/kmp.v` 中用 Hoare 三元组证明算法数学正确性
2. **safeExec 精化层**：通过 C annotation 中的双层规格和 symexec 生成的 VC 建立 C 与 monad 之间的对应
3. **高层调用层**：在 `main()` 中仅使用数学谓词推理，不接触 `safeExec` 细节

本文档结合具体 KMP 实现，逐层解析整个 refinement proof 的工作流。

---

## 1. KMP 算法原理

在深入 refinement proof 之前，先回顾 KMP（Knuth-Morris-Pratt）字符串匹配算法的核心思想。

### 1.1 问题描述

给定一个**模式串** `patn`（长度为 n）和一个**文本串** `text`（长度为 m），在 `text` 中寻找 `patn` 的**首次出现**位置。如果未出现，返回 -1（或 None）。

### 1.2 朴素算法的困境

朴素算法对 `text` 的每个起始位置逐一尝试匹配：

```
text:  A B A B A B A C
patn:  A B A B A C
       ✓ ✓ ✓ ✓ ✓ ✗  → 失败，右移一位重来
        A B A B A C
         ✗           → 失败，右移一位重来
          ...
```

最坏情况下，每个起始位置都需要比较 n 个字符，总时间复杂度为 O(n·m)。例如 `patn = "AAAAB"` 对 `text = "AAAAA...A"` 时，每次匹配都在最后一个字符才失败。

### 1.3 KMP 的关键洞察

KMP 的核心观察是：**当一次匹配失败时，我们已经成功匹配了前缀 `patn[0..j)`，这些信息不应该被浪费。**

考虑一次失败：

```
text:  ... A B A B A B ? ...
patn:       A B A B A C
            [--已匹配--]✗
            j=5 处失败，已成功匹配 5 个字符 "ABABA"
```

朴素算法会将 `patn` 右移一位重新开始。但 KMP 问：**已匹配的前缀 "ABABA" 中，有没有一个真前缀同时也是它的后缀？** 如果有，我们可以直接把 `patn` 滑动到那个位置，跳过已知不可能匹配的尝试。

对 "ABABA"：
- 前缀 "ABA" 也是 "ABABA" 的后缀 ✓
- 前缀 "A" 也是 "ABABA" 的后缀 ✓
- 最长的这种前后缀是 "ABA"，长度为 3

这意味着我们可以安全地保持 `text` 指针不动，只把 `patn` 的匹配位置从 j=5 回退到 j=3：

```
滑动前:  ... A B A B A B ? ...
patn:         A B A B A C
              [--ABA--]   ← 这 3 个字符不需要重新比较！
滑动后:  ... A B A B A B ? ...
patn:             A B A B A C
                  j=3，继续比较 text当前位置 与 patn[3]
```

这就是 **next 表**（又称前缀函数 / failure function）的作用：**`vnext[j-1]` 记录了当 `patn[0..j)` 在位置 j 失配时，`patn[0..j)` 的最长真前后缀长度——即下一个应该继续比较的位置。**

### 1.4 前缀函数的定义

形式化地，对模式串 `patn`，定义前缀函数 π（即 `vnext`）：

> `vnext[i]` = `patn[0..i+1)` 这个前缀的**最长真前后缀**的长度

其中"真前后缀"指既是前缀又是后缀，且不等于原串本身。

**示例**：计算 `patn = "ABABAC"` 的 next 表

| i | 前缀 `patn[0..i+1)` | 最长真前后缀 | vnext[i] |
|---|---------------------|-------------|----------|
| 0 | "A" | (空串) | 0 |
| 1 | "AB" | (空串) | 0 |
| 2 | "ABA" | "A" | 1 |
| 3 | "ABAB" | "AB" | 2 |
| 4 | "ABABA" | "ABA" | 3 |
| 5 | "ABABAC" | (空串) | 0 |

所以 `vnext = [0, 0, 1, 2, 3, 0]`。

### 1.5 算法两个阶段

KMP 算法分为两个阶段：

#### 阶段一：构造 next 表（`constr` 函数）

next 表的构造本身也使用 KMP 思想——**模式串和自己匹配自己**：

```
i 从 1 到 n-1 扫描 patn:
  j = inner(patn, vnext, patn[i], j)   // 用已构建的 next 表做失配跳转
  vnext[i] = j                          // 记录当前位置的部分匹配长度
```

这里 `inner`（即 `inner_loop`）正是 KMP 的**核心字符匹配逻辑**：给定当前部分匹配长度 j 和新字符 ch，返回更新后的部分匹配长度。

#### `inner_loop` 的逻辑

```
输入: 当前匹配长度 j, 新字符 ch
while true:
  if patn[j] == ch:  return j+1    // 匹配成功，匹配长度+1
  if j == 0:         return 0      // 已退到开头，匹配长度为0
  j = vnext[j-1]                    // 失配跳转：回退到上一个可能匹配的位置
```

这就是 KMP 的**失配跳转**：不是回退到 0 重来，而是根据 next 表跳到上一个可能继续匹配的位置。

#### 阶段二：搜索（`match` 函数）

在 text 中扫描，每读入一个字符就调用 `inner_loop` 更新部分匹配长度 j：

```
j = 0
for i in 0..m-1:
  j = inner(patn, vnext, text[i], j)   // 更新部分匹配长度
  if j == n:  return i - n + 1          // 完全匹配，返回起始位置
return -1                                // 未找到
```

### 1.6 完整搜索示例

```
patn = "ABABAC", vnext = [0,0,1,2,3,0]
text = "ABABABAC"

i=0: ch='A', j=0→inner→patn[0]=='A' → j=1
i=1: ch='B', j=1→inner→patn[1]=='B' → j=2
i=2: ch='A', j=2→inner→patn[2]=='A' → j=3
i=3: ch='B', j=3→inner→patn[3]=='B' → j=4
i=4: ch='A', j=4→inner→patn[4]=='A' → j=5
i=5: ch='B', j=5→inner→patn[5]=='C'≠'B', j≠0 → j=vnext[4]=3
           →再比较 patn[3]='B'=='B' → j=4
i=6: ch='A', j=4→inner→patn[4]=='A' → j=5
i=7: ch='C', j=5→inner→patn[5]=='C' → j=6
     j==6==n → 返回 7-6+1=2 (即 text[2]="ABABAC")
```

注意 i=5 处的失配跳转：已匹配 "ABABA"，失配后利用 `vnext[4]=3` 直接跳到继续比较 `patn[3]`，跳过了不可能匹配的起始位置 1，避免了朴素算法中的冗余比较。

### 1.7 时间复杂度

- **构造 next 表**：O(n)。指针 i 只增不减，j 每次最多 +1，回退总次数不超过前进总次数。
- **搜索**：O(m)。同理，text 指针 i 只增不减，j 回退次数有界。
- **总计**：O(n + m)，线性时间。

### 1.8 与 Refinement Proof 的对应

现在可以理解为什么 refinement proof 用三个 monad 程序来建模 KMP：

| Monad 程序 | KMP 中的角色 | 核心性质 |
|-----------|-------------|---------|
| `inner_loop` | 失配跳转引擎 | 给定当前部分匹配长度 j 和字符 ch，返回更新后的 j'，保证 j' 是 `patn[0..j')` 作为已扫描 text 后缀的最长匹配 |
| `constr_loop` | 构造 next 表 | 用 `inner_loop` 完成模式串自匹配，输出满足 `is_prefix_func` 的 next 表 |
| `match_loop` | 主搜索 | 用 `inner_loop` 扫描 text，找到匹配时返回 `Some(位置)`，否则返回 `None` |

这三个 monad 程序之间的依赖关系（`constr` 和 `match` 都 `bind` 了 `inner_loop`）正好反映了 KMP 算法的结构：**失配跳转是核心原语，构造 next 表和主搜索都建立在它之上。**

---

## 2. 整体架构

```
层1: Monad 抽象算法 (kmp.v, ~1500行)
  ├── inner_loop: repeat_break 实现的 KMP 失配跳转
  ├── constr_loop: range_iter 实现的前缀函数构造
  └── match_loop: range_iter_break 实现的 KMP 搜索
        │
        │ 每个 monad 程序附带 Hoare 三元组正确性证明
        │ 证明的是纯数学性质：is_prefix_func, first_occur, no_occurance
        ▼
层2: safeExec 精化桥梁 (由 symexec 自动生成 + manual proof)
  ├── low_level_spec: 将 C 函数行为嵌入 safeExec(ATrue, <monad程序>, X)
  ├── _entail_wit / _return_wit / _safety_wit: 传统 VC
  └── _derive_high_level_spec_by_low_level_spec: 连接层1和层3的关键 VC
        │
        │ 证明 low_level_spec + MonadLib 定理 ⇒ high_level_spec
        ▼
层3: 高层调用接口 (high_level_spec / bind_spec)
  └── main() 仅用数学谓词推理，不接触 safeExec
```

---

## 3. 第一层：Monad 抽象算法 (`MonadLib/Examples/kmp.v`)

### 3.1 `inner_loop` — KMP 最内层字符匹配循环

#### Monad 程序定义

```coq
(* kmp.v:26-48 *)
Section inner_loop_monad.
Context {A: Type} (default: A) (str: list A) (vnext: list Z) (ch: A).

Definition inner_body: Z -> program unit (CntOrBrk Z Z) :=
  fun j =>
    assert (0 <= j < Zlength str);;       (* 安全检查：j 不越界 *)
    assert (j < Zlength vnext);;          (* 安全检查：j 在 vnext 范围内 *)
    choice
      (assume!!(ch = Znth j str default);; (* 情况1：字符匹配 *)
       break (j + 1))                      (* → 返回 j+1 *)
      (assume!!(ch <> Znth j str default);;(* 情况2：字符不匹配 *)
       choice
         (assume!!(j = 0);;                (* 情况2a：已回到开头 *)
          break (0))                       (* → 返回 0 *)
         (assume!!(j <> 0);;               (* 情况2b：可以跳转 *)
          continue (Znth (j-1) vnext 0))). (* → 按 next 表回退 *)

Definition inner_loop: Z -> program unit Z :=
  repeat_break inner_body.
End inner_loop_monad.
```

#### 对应 C 代码

```c
/* kmp_rel.c:76-83 */
while (1) {
    /*@ 0 <= j && j < m */
    if (str[j] == ch) return j + 1;   // 对应 break (j+1)
    if (j == 0) return 0;             // 对应 break (0)
    j = vnext[j-1];                   // 对应 continue (vnext[j-1])
}
```

**关键**：monad 程序用 `choice` + `assume!!` 显式编码分支条件，用 `break`/`continue` 显式编码控制流。C 代码用 `if`/`return`/赋值隐式实现相同逻辑。两者**结构同构**。

#### 核心不变量定义

```coq
(* kmp.v:737-738 *)
Definition partial_match_inv (j: Z) :=
  partial_match_result patn (sublist 0 i text) (sublist 0 j patn).
  (* "patn[0..j) 是 patn[0..i) 的一个部分匹配结果" *)
```

这里 `partial_match_result patn text res` 定义为 `res is_a_suffix_of text /\ res is_a_prefix_of patn`——即 `res` 既是 `text` 的后缀，又是 `patn` 的前缀。这正是 KMP 算法的核心不变量：**当前匹配长度 j 所对应的 patn 前缀必然是已扫描文本的后缀**。

```coq
(* kmp.v:875-876 *)
Definition inner_inv (j: Z) :=
  jrange j vnext /\ partial_match_inv j /\ presuffix_inv j.
```

#### 正确性定理

```coq
(* kmp.v:1005-1024 *)
Lemma inner_loop_prop (j: Z):
  inner_pre j ->
    (* 前置：Zlength vnext <= Zlength patn
           ∧ vnext is_prefix_func_of patn
           ∧ 0 <= i < Zlength text
           ∧ 0 <= j < Zlength vnext
           ∧ best_partial_match_result patn (sublist 0 i text) (sublist 0 j patn) *)
  Hoare (fun _ => True)
        (inner_loop default patn vnext (Znth i text default) j)
        (fun j' _ => inner_post j').
    (* 后置：0 <= j' <= Zlength vnext
           ∧ best_partial_match_result patn (sublist 0 (i+1) text) (sublist 0 j' patn) *)
```

这个定理的含义是：**如果调用前 next 表合法、j 是当前最优部分匹配长度，那么调用后返回的 j' 仍然在合法范围内，且是扫描到下个字符后的最优部分匹配长度**。

#### 证明结构

1. `inner_pre` → 可导出 `inner_inv`（不变量 = jrange ∧ partial_match_inv ∧ presuffix_inv）
2. 用 `Hoare_repeat_break` 将循环归纳为：continue 路径保持 `inner_inv`，break 路径建立 `inner_post`
3. 核心引理：
   - `inner_body_prop_brk1`：匹配成功时证明 `best_partial_match_result ... (sublist 0 (j+1) patn)`
   - `inner_body_prop_brk2`：失配且 j=0 时证明 `best_partial_match_result ... (sublist 0 0 patn)`（即空匹配）
   - `inner_presuffix_inv`：失配且 j>0 时，利用 `is_prefix_func` 性质将 `vnext[j-1]` 对应的部分匹配转化为新的 presuffix_inv

### 3.2 `constr_loop` — 构造前缀函数 next 表

#### Monad 程序定义

```coq
(* kmp.v:51-70 *)
Section constr_loop_monad.
Context {A: Type} (default: A) (str: list A).

Definition constr_body: Z -> list Z * Z -> program unit (list Z * Z) :=
  fun i => fun '(vnext, j) =>
    assert (i < Zlength str);;
    let ch := Znth i str default in
    j' <- inner_loop default str vnext ch j;;  (* ← 复用 inner_loop *)
    ret (vnext ++ [j'], j').

Definition constr_loop: program unit (list Z) :=
  '(vnext, j) <- range_iter 1 (Zlength str) constr_body ([0], 0);;
  ret vnext.
End constr_loop_monad.
```

#### 对应 C 代码

```c
/* kmp_rel.c:108-139 */
int len = strlen(patn);
int *vnext = malloc_int_array(len);
vnext[0] = 0;
int j = 0;
int i = 1;          // range_iter from 1
for (; i < len; i++) {
    j = inner(patn, vnext, patn[i], j);   // j' <- inner_loop ...
    vnext[i] = j;                         // vnext ++ [j']
}
return vnext;
```

#### 正确性定理

```coq
(* kmp.v:1294-1314 *)
Theorem constr_loop_sound:
  patn <> [] ->
  Hoare (fun _ => True)
        (constr_loop default patn)
        (fun vnext _ =>
          vnext is_prefix_func_of patn /\ Zlength vnext = Zlength patn).
```

**这个定理就是 `constr` 函数高层规格中 `is_prefix_func(vnext, str)` 的来源。** `is_prefix_func` 是 next 表正确性的数学刻画——对每个位置 i，`vnext[i]` 是 `patn[0..i+1)` 的最长真前后缀的长度。

#### 证明关键步骤

1. `constr_pre_derive_inv`：初始状态 `([0], 0)` 满足不变量
2. `inner_loop_prop_vnext`：利用 `inner_loop_prop` 推导每次 `inner_loop` 调用后 `vnext ++ [j']` 仍是合法的前缀函数
3. `constr_body_prop`：将 `constr_inv` 推进一步（i → i+1）
4. 用 `Hoare_range_iter` 将 body 性质提升为整个循环的性质

### 3.3 `match_loop` — KMP 主搜索

#### Monad 程序定义

```coq
(* kmp.v:72-98 *)
Section match_loop_monad.
Context {A: Type} (default: A) (patn text: list A) (vnext: list Z).

Definition match_body: Z -> Z -> program unit (CntOrBrk Z Z) :=
  fun i j =>
    assert (i < Zlength text);;
    let ch := Znth i text default in
    j' <- inner_loop default patn vnext ch j;;  (* ← 复用 inner_loop *)
    choice
      (assume!! (j' = Zlength patn);;           (* 完全匹配！ *)
       break (i - Zlength patn + 1))             (* → 返回匹配位置 *)
      (assume!! (j' < Zlength patn);;            (* 未完全匹配 *)
       continue (j')).                           (* → 继续 *)

Definition match_loop: program unit (option Z) :=
  res <- range_iter_break 0 (Zlength text) match_body 0;;
  match res with
  | by_continue _ => ret None     (* 遍历完未找到 *)
  | by_break i => ret (Some i)    (* 找到，返回位置 *)
  end.
End match_loop_monad.
```

#### 对应 C 代码

```c
/* kmp_rel.c:171-196 */
int j = 0;
int i = 0;
for (; i < text_len; i++) {
    j = inner(patn, vnext, text[i], j);
    if (j == patn_len) return i - patn_len + 1;  // break (位置)
}
return -1;  // None → -1 via option_int_repr
```

#### 正确性定理

```coq
(* kmp.v:1531-1560 *)
Theorem match_loop_sound:
  patn <> [] ->
  Zlength vnext = Zlength patn ->
  vnext is_prefix_func_of patn ->
  Hoare (fun _ => True)
        (match_loop default patn text vnext)
        (fun res _ =>
          match res with
          | Some r => first_occur patn text r
          | None   => no_occurance patn text
          end).
```

**这就是 KMP 搜索的终极正确性定理**：给定合法的 next 表，搜索要么返回 `Some r` 且 r 是 `patn` 在 `text` 中的首次出现位置（`first_occur`），要么返回 `None` 表示未出现（`no_occurance`）。

### 3.4 关键数学定义

`kmp.v` 中定义了一套完整的字符串学（stringology）谓词体系：

| 谓词 | 定义 | 用途 |
|------|------|------|
| `is_prefix l1 l2` | `exists l, l2 = l1 ++ l` | l1 是 l2 的前缀 |
| `is_suffix l1 l2` | `exists l, l2 = l ++ l1` | l1 是 l2 的后缀 |
| `presuffix l1 l2` | `is_prefix l1 l2 /\ is_suffix l1 l2` | 同时是前后缀 |
| `proper_presuffix l1 l2` | `presuffix l1 l2 /\ Zlength l1 < Zlength l2` | 真前后缀 |
| `max_proper_presuffix l1 l2` | l1 是最长真前后缀 | KMP next 表的核心 |
| `is_prefix_func vnext patn` | 每个 vnext[i] 给出 patn[0..i+1) 的最长真前后缀长度 | next 表正确性 |
| `partial_match_result patn text res` | res 既是 text 的后缀又是 patn 的前缀 | 循环不变量 |
| `best_partial_match_result patn text res` | 最长的 partial_match_result | 最优性 |
| `first_occur patn text z` | z 是 patn 在 text 中首次出现的位置 | 最终正确性 |
| `no_occurance patn text` | patn 不出现在 text 中 | 未找到 |

---

## 4. 第二层：C Annotation 中的双层规格

每个函数都有两个规格声明，规格间用 `<=` 声明导出关系。

### 4.1 `inner()`: `bind_spec <= low_level_spec`

#### low_level_spec（kmp_rel.c:58-68）

```c
/*@ low_level_spec
    With str0 vnext0 n m X
    Require safeExec(ATrue, inner_loop(0, str0, vnext0, ch, j), X) &&
            m <= n && n < INT_MAX &&
            CharArray::full(str, n + 1, app(str0, cons(0, nil))) *
            IntArray::full(vnext, m, vnext0)
    Ensure safeExec(ATrue, return(__return), X) && 0 <= __return && __return < m + 1 &&
           CharArray::full(str, n + 1, app(str0, cons(0, nil))) *
           IntArray::full(vnext, m, vnext0)
*/
```

#### bind_spec（kmp_rel.c:47-56）

```c
/*@ bind_spec <= low_level_spec
    With {B} str0 vnext0 n m X (f: Z -> program unit B)
    Require safeExec(ATrue, bind(inner_loop(0, str0, vnext0, ch, j), f), X) &&
            ...
    Ensure safeExec(ATrue, applyf(f, __return), X) && 0 <= __return && ...
*/
```

`bind_spec` 比 `low_level_spec` 多了一个类型参数 `B` 和一个 continuation `f: Z -> program unit B`。它允许调用者把 `inner_loop` 的结果"接"到更大的 monad 程序中——这正是 monad 的 `bind` 操作。

在 `constr()` 中调用 `inner` 时使用了 `bind_spec`（kmp_rel.c:124-126）：

```c
j = inner(patn, vnext, patn[i], j)
  /*@ where (bind_spec) str0 = str, vnext0 = vnext0, m = i, n = n,
      X = X, f = constr_loop_from_after(0, str, i, vnext0); B = list Z */;
```

这里 `f` 被实例化为 `constr_loop_from_after`——即 "inner 返回后还要把结果写入 vnext[i] 并继续循环"。`B = list Z` 说明整个 bind 的最终返回类型是 `list Z` 列表。

对应的导出证明（proof_manual.v:543-567）：

```coq
Lemma proof_of_inner_derive_bind_spec_by_low_level_spec.
Proof.
  pre_process.
  prop_apply CharArray.full_Zlength; Intros.
  prop_apply IntArray.full_Zlength; Intros.
  apply string_Zlength in H2.
  apply safeExec_bind in H as (X' & H7 & H8).  (* 展开 safeExec_bind *)
  Exists str0_bind_spec vnext0_bind_spec n_bind_spec m_bind_spec X'.
  split_pure_spatial.
  - ... apply derivable1_wand_sepcon_adjoint.   (* 将 low_level_spec 的后条件提升 *)
  - ...
Qed.
```

### 4.2 `constr()`: `high_level_spec <= low_level_spec`

#### low_level_spec（kmp_rel.c:98-106）

```c
/*@ low_level_spec
    With str n X
    Require safeExec(ATrue, constr_loop(0, str), X) && n > 0 && n < INT_MAX &&
            CharArray::full(patn, n + 1, app(str, cons(0, nil)))
    Ensure exists (vnext: list Z),
             safeExec(ATrue, return(vnext), X) &&
             IntArray::full(__return, n, vnext) *
             CharArray::full(patn, n + 1, app(str, cons(0, nil)))
*/
```

#### high_level_spec（kmp_rel.c:87-94）

```c
/*@ high_level_spec <= low_level_spec
    With str n
    Require n > 0 && n < INT_MAX && CharArray::full(patn, n + 1, app(str, cons(0, nil)))
    Ensure exists vnext,
             is_prefix_func(vnext, str) &&
             IntArray::full(__return, n, vnext) *
             CharArray::full(patn, n + 1, app(str, cons(0, nil)))
*/
```

**关键区别**：`high_level_spec` 的 Ensure 不含 `safeExec`——它直接用数学谓词 `is_prefix_func(vnext, str)` 描述结果。这是给 `main` 用的高层接口。

对应的导出证明（proof_manual.v:508-541）：

```coq
Lemma proof_of_constr_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  prop_apply CharArray.full_Zlength; Intros.
  apply string_Zlength in H1.
  ...
  pose proof constr_loop_sound 0 str_high_level_spec H2.  (* ← 引用 kmp.v 的定理 *)
  ...
  destruct (@Hoare_safeexec_compose unit (list Z)
              ATrue (constr_loop 0 str_high_level_spec)
              (fun vnext _ => is_prefix_func vnext str_high_level_spec /\
                             Zlength vnext = Zlength str_high_level_spec)
              H3 ATrue vnext tt H4 I) as [σ [[Hprefix _] _]].
  exact Hprefix.  (* is_prefix_func vnext str_high_level_spec *)
Qed.
```

证明流程：`low_level_spec 的 safeExec 前提` → `constr_loop_sound (from kmp.v)` → `Hoare_safeexec_compose` 将 Hoare 三元组转化为 safeExec 性质 → `is_prefix_func` 结论。

### 4.3 `match()`: 同为双层结构

#### high_level_spec（kmp_rel.c:143-155）

```c
/*@ high_level_spec <= low_level_spec
    With patn0 text0 vnext0 n m
    Require is_prefix_func(vnext0, patn0) && n > 0 && n < INT_MAX && m < INT_MAX &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil))) *
            IntArray::full(vnext, n, vnext0)
    Ensure ((__return >= 0 && first_occur(patn0, text0, __return)) ||
            (__return == -1 && no_occurance(patn0, text0))) &&
            ...
*/
```

#### low_level_spec（kmp_rel.c:158-170）

```c
/*@ low_level_spec
    With patn0 text0 vnext0 n m X
    Require safeExec(ATrue, match_loop(0, patn0, text0, vnext0), X) && ...
    Ensure exists ret,
             safeExec(ATrue, return(ret), X) &&
             __return == option_int_repr(ret) && ...
*/
```

这里出现了 `option_int_repr`（定义于 kmp_rel_lib.v:31-35）：

```coq
Definition option_int_repr (x: option Z): Z :=
  match x with
  | Some n => n
  | None => -1
  end.
```

这是 monad 层的 `option Z`（`Some r` 表示找到位置 r，`None` 表示未找到）和 C 层 `int`（用 -1 表示没找到）之间的类型转换。

对应的导出证明（proof_manual.v:451-506）的精髓：

```coq
Lemma proof_of_match_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  ...
  pose proof match_loop_sound 0 patn0_high_level_spec text0_high_level_spec
                vnext0_high_level_spec H6 ltac:(lia) H.
  ...
  destruct (@Hoare_safeexec_compose ... H7 ATrue ret tt H8 I) as [σ [Hpost _]].
  destruct ret; simpl in H9.
  + Right; Exists z.               (* Some z → first_occur 路径 *)
    split_pure_spatial.
    ... exact Hpost.                (* match_loop_sound 给出的 first_occur *)
  + Left; Exists (-1).              (* None → no_occurance 路径 *)
    split_pure_spatial.
    ... exact Hpost.                (* match_loop_sound 给出的 no_occurance *)
Qed.
```

---

## 5. 第三层：`main()` — 纯高层推理

```c
int main(char *patn, char *text)
/*@
    With patn0 text0 n m
    Require n > 0 && n < INT_MAX && m < INT_MAX &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil)))
    Ensure ((__return >= 0 && first_occur(patn0, text0, __return)) ||
            (__return == -1 && no_occurance(patn0, text0))) &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil)))
*/
{
    int *vnext = constr(patn) /*@ where (high_level_spec) str = patn0, n = n */;
    /*@ Assert exists vnext0,
            is_prefix_func(vnext0, patn0) &&
            n > 0 && n < INT_MAX && m < INT_MAX &&
            patn == patn@pre && text == text@pre &&
            CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
            CharArray::full(text, m + 1, app(text0, cons(0, nil))) *
            IntArray::full(vnext, n, vnext0)
    */
    /*@ Given vnext0 */
    int r = match(patn, text, vnext)
        /*@ where (high_level_spec) patn0 = patn0, text0 = text0,
            vnext0 = vnext0, n = n, m = m */;
    free_int_array(vnext) /*@ where n = n, l = vnext0 */;
    return r;
}
```

`main` 全程使用 `high_level_spec`：

1. 调用 `constr` 时指定 `where (high_level_spec)`——得到 `is_prefix_func(vnext0, patn0)` 
2. 将 `is_prefix_func` 作为前提传给 `match` 的 `high_level_spec`
3. `match` 的 `high_level_spec` 直接给出 `first_occur` / `no_occurance` 结论

**`main` 不出现 `safeExec`，不出现 monad 程序，完全在数学谓词层推理。** 这正是 refinement proof 的核心价值——调用方只需要理解数学接口，不需要理解实现细节。

---

## 6. Symexec 生成的 VC 与 Manual Proof

Symexec 为每个带 `low_level_spec` 的函数生成了三类 VC。

### 6.1 安全 VC (`_safety_wit_*`)

例如 `inner_safety_wit_2`（goal.v:45-56），检查当 `str[j] == ch` 时：

```
CharArray.full(str_pre, n+1, ...) * IntArray.full(...) * ...
|-- (j+1 <= INT_MAX) && (INT_MIN <= j+1)
```

即验证 `return j+1` 不会整数溢出。这类 VC 通常在 `*_proof_auto.v` 中自动解决（通过 `safeexecE_strategy_proof` 中预置的 tactic）。

### 6.2 不变量 VC (`_entail_wit_*`, `_return_wit_*`)

例如 `proof_of_inner_entail_wit_2`（proof_manual.v:38-75），处理循环体某条路径后的不变量保持。证明策略：

```coq
Lemma proof_of_inner_entail_wit_2 : inner_entail_wit_2.
Proof.
  pre_process.                          (* 规范化前提 *)
  ...
  pose proof PreH1 as H'.
  unfold inner_loop in PreH1.           (* 展开 monad 程序定义 *)
  unfold_loop in PreH1.                 (* 展开 repeat_break → 一次循环迭代 *)
  unfold inner_body at 1 in PreH1.      (* 展开循环体 *)
  safe_step PreH1.                      (* safeExec 符号执行一步 *)
  split_pure_spatial.                   (* 分解纯量/空间合取 *)
  - Intros_p H4. Intros_p H5. cancel.   (* 空间部分：SL 谓词匹配 *)
  - split_pures.                        (* 纯量部分：整数范围断言 *)
    + ... lia.
    + ... exact H'.                     (* safeExec 前提传递 *)
    ...
Qed.
```

这些证明的核心是**展开 monad 程序并符号执行**——将 `safeExec` 中的 monad 程序一步步展开，使 symexec 生成的 VC 前提与 C 代码的执行路径对应上。

### 6.3 导出 VC (`_derive_*_by_*`，refinement 独有）

这是 refinement proof **独有**的 VC。前面已在 3.2、3.3 节详细分析。

---

## 7. 完整数据流图

```
kmp.v (手工编写，纯数学)
│
├── inner_body / inner_loop
│       │ inner_loop_prop (Hoare 三元组)
│       ↓ (被 bind 复用于)
├── constr_body / constr_loop
│       │ constr_loop_sound (Hoare 三元组)
│       ↓
├── match_body / match_loop
│       │ match_loop_sound (Hoare 三元组)
│       │
│   定义: is_prefix_func, first_occur, no_occurance,
│         best_partial_match_result, presuffix, ...
│
└──────────────────────────────────────────────────┐
                                                   │
kmp_rel.c (手工 annotation)                         │
│                                                  │
├── Extern Coq 声明 ←────────────────────────────────┘
│    引用 kmp.v 中的 monad 程序和数学谓词
│
├── inner() 的双层规格
│   ├── low_level_spec: safeExec(ATrue, inner_loop(...), X)
│   └── bind_spec:      safeExec(ATrue, bind(inner_loop(...), f), X)
│       ↓ symexec 生成
│       ├── inner_safety_wit_1..6          →  proof_auto.v (自动)
│       ├── inner_entail_wit_2,3           →  proof_manual.v (L38-95)
│       ├── inner_return_wit_1,2           →  proof_manual.v (L97-135)
│       └── inner_derive_bind_spec_by_low_level_spec
│                                          →  proof_manual.v (L543-567)
│
├── constr() 的双层规格
│   ├── low_level_spec:  safeExec(ATrue, constr_loop(...), X)
│   └── high_level_spec: is_prefix_func(vnext, str) && ...
│       ↓ symexec 生成
│       ├── constr_entail_wit_1,2,3        →  proof_manual.v (L137-260)
│       ├── constr_return_wit_1            →  proof_manual.v (L262-286)
│       ├── constr_partial_solve_wit_5_pure→  proof_manual.v (L288-320)
│       └── constr_derive_high_level_spec_by_low_level_spec
│                                          →  proof_manual.v (L508-541)
│
├── match() 的双层规格
│   ├── low_level_spec:  safeExec(ATrue, match_loop(...), X)
│   └── high_level_spec: first_occur / no_occurance
│       ↓ symexec 生成
│       ├── match_entail_wit_1,2           →  proof_manual.v (L322-369)
│       ├── match_return_wit_1,2           →  proof_manual.v (L371-421)
│       ├── match_partial_solve_wit_4_pure →  proof_manual.v (L423-449)
│       └── match_derive_high_level_spec_by_low_level_spec
│                                          →  proof_manual.v (L451-506)
│
└── main()
    仅使用 high_level_spec，不生成 safeExec VC
```

---

## 8. 相关文件清单

| 文件 | 路径 | 说明 |
|------|------|------|
| C 源码 | `QCP_examples/QCP_demos_LLM/kmp_rel.c` | 带 annotation 的 KMP C 程序 |
| 抽象算法 | `SeparationLogic/MonadLib/Examples/kmp.v` | 三个 monad 程序 + Hoare 三元组证明 |
| C 侧 lib | `SeparationLogic/examples/QCP_demos_LLM/kmp_rel_lib.v` | `applyf`, `option_int_repr`, 辅助定义和引理 |
| C 侧 lib（无 _rel） | `SeparationLogic/examples/QCP_demos_LLM/kmp_lib.v` | 独立 kmp 相关库（如有） |
| 生成 goal | `SeparationLogic/examples/QCP_demos_LLM/kmp_rel_goal.v` | Symexec 生成的 VC 定义 |
| 自动证明 | `SeparationLogic/examples/QCP_demos_LLM/kmp_rel_proof_auto.v` | 自动 tactic 解决的 VC |
| 手工证明 | `SeparationLogic/examples/QCP_demos_LLM/kmp_rel_proof_manual.v` | Manual witness proof（~570行） |
| 最终检查 | `SeparationLogic/examples/QCP_demos_LLM/kmp_rel_goal_check.v` | 组合所有模块的最终编译检查 |

---

## 9. 与普通直接证明的核心差异总结

| 维度 | 直接证明 | Refinement Proof (KMP) |
|------|----------|------------------------|
| **算法正确性证明位置** | 混在 C VC 的 proof manual 中 | 独立在 `kmp.v` 的 Hoare 三元组中 |
| **C 规格语言** | SL 谓词（IntArray::full, CharArray::full 等）| `safeExec(ATrue, <monad程序>, X)` + SL 谓词 |
| **VC 种类** | safety + entail + return | **额外**有 `_derive_*_by_*` 桥梁 VC |
| **MonadLib 依赖** | 无 | 必需（SafeRelMonadErr, Hoare, choice/break/continue） |
| **抽象层可复用性** | 不可复用 | `inner_loop` 被 constr 和 match 共同 bind |
| **调用方可见性** | 直接看到实现细节（循环、数组访问） | `main` 只看到 `is_prefix_func` 等数学接口 |
| **证明总行数估算** | ~200-500 行 manual proof | kmp.v ~1500 + proof_manual.v ~570 |
| **关注点分离** | 算法正确性 + C 实现正确性在同一层证明 | 两者独立证明，通过 `_derive_*` VC 缝合 |
| **Extern Coq 声明** | 通常不需要 | 必须在 C 文件顶部声明 monad 程序和谓词的外部引用 |

核心洞见：**refinement proof 把"算法为什么正确"和"C 代码为什么实现了这个算法"拆成两个独立证明义务**。前者在纯 monad 中完成（不涉及指针、内存、溢出），后者通过 safeExec 框架将 C 代码的每一步与 monad 程序的每一步对应起来。`_derive_*_by_*` VC 则是把两条证明线缝合在一起的桥梁。
