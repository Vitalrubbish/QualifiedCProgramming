---
name: annotation-checking
description: 由 annotation-subagent 在 annotation-filling 之后调用，检查 annotation_scratch_lib 中 spec 定义、函数规格和 loop invariant 的数学语义质量；只有通过后主 agent 才能回填正式 `.c` / common_case_formal_lib 并运行 symexec。
---

# Annotation Checking

这个 skill 固定绑定给 `annotation-subagent`，并且只能在同一轮 `annotation` phase 中由 `annotation-subagent` 调用。
它是 `annotation-filling` 后、正式 symexec 前的质量门：先检查 Rocq spec 定义是否正确，再检查 C annotation 是否正确调用这些 spec。

## 何时使用

- `annotation-subagent` 已通过 `annotation-filling` 在 annotation C scratch 上得到候选 annotation。
- `annotation-subagent` 已从 `common_case_formal_lib` 创建本轮 `annotation_scratch_lib`；若 `common_case_formal_lib` 不存在，应创建本轮空 / 最小 `annotation_scratch_lib`。
- 候选 annotation 和候选 spec 定义已在 scratch 上完成必要的 `qcp-mcp` 交互检查。
  这里的“完成”要求 `qcp-mcp` 本身成功跑到文件尾；若只是 direct `symexec` 成功而 `qcp-mcp` 没有成功，则不能作为 `passed` 进入正式 symexec。
- 主 agent 尚未把候选 annotation 回填到正式 `.c`。
- 主 agent 尚未把候选 spec 定义回填到 `common_case_formal_lib`。
- 主 agent 尚未运行正式 symexec。

## 进入前提

- 当前调用者必须是 `annotation-subagent`。
- 当前 case 仍处于 `annotation` phase。
- 当前 annotation C scratch 是本轮最新 scratch，且没有被标记为 stale。
- 当前 `annotation_scratch_lib` 是本轮最新 scratch，且没有被标记为 stale。
- 当前候选 patch / spec 定义来自本轮 `annotation-filling`，不是主状态文件上的临时改动。

## 检查顺序

1. 检查 `annotation_scratch_lib` 在仓库 `_CoqProject` flags 下是否可编译。
   - 若 import、语法或依赖解析失败，应返回 `failed`，要求回到 `annotation-filling` 修正 `annotation_scratch_lib`。
   - 这一条是进入正式 symexec / `goal-frozen` 前的 compile gate，不能省略。
2. 检查 `qcp-mcp` requirement 是否满足。
   - 若 `qcp-mcp` 在 scratch C 上成功跑到文件尾，则记 `qcp_mcp_requirement_satisfied: yes`。
   - 若 direct wrapper 遇到 `Permission denied` 但同一个 `qcp-mcp` 链路通过 loader fallback 成功，也记为 `yes`。
   - 若只有 direct `symexec` fallback 成功而 `qcp-mcp` 仍失败，则必须记 `qcp_mcp_requirement_satisfied: no`，且本次 checking 不能返回 `passed`。
3. 检查 `annotation_scratch_lib` 中是否已有目标 spec 的 Rocq 定义。
   - 如果不存在，应回到 `annotation-filling` 在 `annotation_scratch_lib` 中补充严格数学定义。
   - 如果存在但含义不正确、过弱、过强或是 C 算法镜像（在rocq中对算法进行定义然后建立映射），应回到 `annotation-filling` 修正 `annotation_scratch_lib`。
4. 检查函数级 `Require` / `Ensure`。
   - 重点看逻辑性质部分是否准确描述函数数学语义。
   - 变量范围约束和内存谓词只做必要性 / 一致性检查，不应替代数学语义。
5. 检查内部 assertion，特别是 `Inv Assert`。
   - loop invariant 必须表达循环保持的核心逻辑性质。
   - 普通 `Assert` 应服务于函数调用、分支连接或退出证明，不应堆砌无关事实。
6. 检查 C annotation 是否使用已确认正确的 spec 定义。
   - 先确认 `annotation_scratch_lib` spec，再确认 C 如何调用。
   - 如果 C annotation 暴露出 spec 定义不合理，允许回流修改 `annotation_scratch_lib`，然后重新 filling 和 checking。

## Annotation 三分法

检查时把 annotation 信息分成三类：

- 变量范围约束：例如 `1 <= n && n <= 100000`，用于支撑整数安全、数组下标和循环边界。
- 内存相关部分：例如 `IntArray::full(arr, n, l)` / `store_int_array`，用于描述分离逻辑资源和内存形状。
- 逻辑性质部分：例如 `MinimizedMaxSegmentSum(l, m, ans)`、`CanSplit(l, m, cap)`、`Permutation l l0`，用于表达程序本身的数学性质。

`annotation-checking` 的重点是第三类。变量范围和内存形状齐全但缺少逻辑性质时，不能算通过。

数组 / 字符串相关的内存部分还要额外检查：

- 是否优先使用了 `IntArray` / `UIntArray` / `CharArray` / `PtrArray` / `store_string` / `store_stringLit` / `GlobalStrings` 等 builtin 谓词。
- `store_string` 是否只用于可读写 C 字符串缓冲区，逻辑内容为不含结尾 `0` 的 `list Z`。
- `store_stringLit` 是否只用于字符串字面量 / 只读全局字符串常量，逻辑内容为 Rocq `string`。
- 局部 `char a[] = "..."` 或可写 buffer 不应被误标成 `store_stringLit`。
- 如果 `annotation_scratch_lib` 新增了 array/string 内存谓词，应质疑是否重复了 builtin；只有算法数学性质才适合最终集成到 `common_case_formal_lib`。

## 关键判定

通过检查前，至少回答：

1. 目标函数的数学规格是什么？它是否已在 `annotation_scratch_lib` 中以严格数学定义表达？
2. 这个定义描述的是性质，还是把 C 程序 / loop body 在 Rocq 中重写了一遍？
3. 函数 `Ensure` 是否使用该数学定义表达最终结果，而不是只保留 range / memory？
4. `check` / helper 函数的 `Ensure` 是否输出调用方真正需要的判定性质？
5. 每个核心循环 invariant 是否包含能连接初始化、单步保持和退出结论的逻辑性质？
6. 如果某个 invariant 只有变量范围和内存资源，它缺少的数学状态是什么？
7. 若 checking 失败，应该修 C annotation、修 `annotation_scratch_lib` spec，还是二者都修？

若第 2 个问题答案接近“在重放算法”，必须返回 `failed` 并要求回到 `annotation-filling` 重设 spec。

## 参考文档

1. `../annotation-filling/docs/predicate-first-annotation.md`
2. `../annotation-filling/docs/common-annotation-errors.md`（检查完整 `Assert` / `Inv Assert` 的常见缺陷时参考）
3. `../annotation-filling/docs/builtin-array-string-support.md`（检查数组 / 字符串 annotation 是否复用了 builtin 谓词）
4. `../annotation-filling/docs/reference-cases.md`
5. `../annotation-filling/docs/split_array_largest_sum/binary-search-annotation.md`
6. `docs/spec-quality-checklist.md`

## 输出

`annotation-subagent` 应产出一份 `Annotation Checking Report`：

```md
## Annotation Checking Report

- status: passed | failed | blocked | stale
- checked_scope:
- qcp_mcp_requirement_satisfied: yes | no
- annotation_scratch_lib_coqc_status: passed | failed
- spec_definition_status:
- function_spec_status:
- invariant_status:
- annotation_scratch_lib_changes:
- summary:
- failed_checks:
- required_annotation_rework:
- required_annotation_scratch_lib_rework:
- ready_for_main_common_case_formal_lib_update: yes | no
- ready_for_main_symexec: yes | no
- timing_summary:
- timing_gaps:
```

含义：

- `passed`：允许 `annotation-subagent` 把本轮结果作为 `completed` 交回主 agent；主 agent可正式回填 `.c` / `common_case_formal_lib` 并运行 symexec。
- `failed`：不允许进入 symexec；`annotation-subagent` 必须回到 `annotation-filling` 修正 annotation C scratch 或 `annotation_scratch_lib`，并在修正后再次调用本 skill。
- `blocked`：检查发现缺少上游信息、规格决策或用户确认，当前轮次不能继续。
- `stale`：本轮 scratch 或输入已过期，不能继续复用。

## 边界

- 本 skill 不修改正式 `.c`、`*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v` 或 `common_case_formal_lib`。
- 本 skill 不运行正式 symexec。
- 本 skill 不替代 `vc-checking`，也不对生成后的 Rocq witness 做可证性分诊。
- 本 skill 可以要求 `annotation-subagent` 回到 `annotation-filling` 修改本轮 `annotation_scratch_lib`，但不能直接改 `common_case_formal_lib`。
- 检查未通过时，不能把候选 annotation 或 `annotation_scratch_lib` 变更交给主 agent 回填；必须先回到 `annotation-filling`。

## 通过标准

只有同时满足以下条件，才能返回 `passed`：

- spec 定义存在，且是严格数学性质定义。
- `qcp_mcp_requirement_satisfied: yes`。
- `annotation_scratch_lib_coqc_status: passed`。
- spec 定义没有把 C 程序本体、循环状态转移或二分过程重写为 Rocq 算法镜像。
- 函数规格的逻辑性质部分足以表达函数真正要证明的数学语义。
- 核心 invariant 含有能解释循环正确性的逻辑性质，而不是只有变量范围和内存资源。
- scratch C 和 `annotation_scratch_lib` 之间引用一致。
- 本轮需要回填到 `common_case_formal_lib` 的变更已经在 report 中列出，由主 agent 正式集成。
