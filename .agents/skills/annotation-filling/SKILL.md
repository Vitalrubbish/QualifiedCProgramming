---
name: annotation-filling
description: 为 QCP C 程序填写或修正 annotation；annotation-subagent 在隔离 scratch C / annotation_scratch_lib 上设计数学 spec 与 C annotation，使用 qcp-mcp 持续交互检查，主 agent 负责回填正式 `.c` / common_case_formal_lib 并刷新 symexec 生成文件。
---

# Annotation Filling

这个 skill 只负责 annotation filling 的 domain 工作、`annotation_scratch_lib` 中 spec 定义的设计 / 修正，以及 scratch 上的 `qcp-mcp` 交互检查。
正式 `.c` / `common_case_formal_lib` 回填和 symexec 刷新仍由主 agent 独占执行。
它固定绑定给 `annotation-subagent`；完成候选 annotation 后，必须由同一 `annotation-subagent` 调用 `annotation-checking` 质量门。
phase、工件模板、delegation 和失效传播规则统一由 `verification-orchestrator` 定义；本 skill 不再重复定义它们。

## 何时使用

- case 已由 `verification-orchestrator` 置于 `annotation` 阶段。
- 主 agent 已为当前 annotation 轮次启动 `annotation-subagent`。
- 需要为 C 文件补充 `Require`、`Ensure`、`Assert`、`Inv Assert`。
- 需要在 `annotation_scratch_lib` 中补充或修正 C annotation 所依赖的数学 spec 定义。
- symbolic execution 失败，需要定位并修正 annotation。
- QCP 在 `return`、函数结束或局部 scope 结束处报 `remove permission failed` / 局部变量内存回收失败，需要检查 annotation 是否遗漏局部变量、局部数组或完整数组段的 ownership。
- 上游判定某些 witness 属于 `annotation-bug`，需要返工 annotation。

## 进入前提

- 当前 case 的目标 C 文件、输出目录、验证函数和 proof 类型已经明确。
- 主 agent 已确定这是当前 case 的正式 annotation 轮次。
- 当前 delegation ticket 的 `subagent_name` 固定为 `annotation-subagent`。
- 当前 delegation ticket 已给出最新正式 `.c` / `common_case_formal_lib` 快照和本轮 annotation C scratch / `annotation_scratch_lib` 路径；若路径已被旧轮次占用，必须先删除旧 scratch。
- 当前 delegation ticket 已明确：本轮 `annotation` 的 `iteration_owner` 是 `annotation-subagent`，main 线程不会在等待一段时间后接管本轮 domain 工作。
- 当前 delegation ticket 已明确本轮 `annotation_focus`、`preferred_hidden_properties` 和 `forbidden_annotation_patterns`；如果这些字段缺失，应以 `blocked` 返回主 agent 要求补全，而不是自行默许算法镜像方案。
- 若来自返工，主 agent 已明确哪些 witness / VC 暴露了 annotation 层问题。
- 若来自返工或下游回流，当前 ticket 还必须附带 `Re-entry Brief`，说明为什么会再次进入 `annotation`。

## 直接输出

- 已在 annotation C scratch 上验证过的 annotation patch / block rewrite。
- 已在 `annotation_scratch_lib` 上完成的 spec definition patch；如果不需要 `common_case_formal_lib` 变更，应明确写 `empty`。
- `qcp-mcp` 交互检查摘要、案例映射和风险分析。
- `annotation-checking` 的检查结果；只有 `passed` 时，本轮 annotation / lib patch 才可作为 ready-for-main-symexec 交回主 agent。
- 本轮 annotation 总耗时、关键 `qcp-mcp` symbolic/check/step 耗时、annotation 分析/编辑/失败归因/patch 整理等 activity 耗时、最慢 annotation 迭代点，以及主要耗时原因。
- 主 agent 正式回填 annotation 并刷新生成文件时所需的执行建议。
- `Subagent Return Report`，其 `round_outcome` 只能是 `completed`、`blocked` 或 `stale`。

## 会使哪些产物失效

- annotation 一旦变化，旧 witness 分析、旧 proof skeleton、旧 proving 计划和旧 final-check 结论都会失效。
- 具体 stale 标记与 phase 迁移规则，按 `verification-orchestrator` 执行。

## 主 / 子 Agent 局部边界

- `annotation-subagent` 拥有 annotation C scratch、`annotation_scratch_lib` 和该 C scratch 上的 `qcp-mcp` 会话。
- `annotation-subagent` 负责在 scratch 上持续试改 spec 定义和 C annotation，直到跑通或明确确认必须继续返工。
- 主 agent 独占正式 `.c` / `common_case_formal_lib` 写入、symexec 和 phase 状态提交。
- `annotation-subagent` 不直接提交当前 case 的正式 annotation 或 `common_case_formal_lib`。
- 本轮 `annotation` 一旦交给 `annotation-subagent`，main 线程不得因为等待较久而强行打断并自己完成 annotation。

## 参考文档

1. 先读 `../verification-orchestrator/SKILL.md`
2. `docs/use-notes.md`
3. `docs/annotation-rules.md`
4. `docs/common-annotation-errors.md`（写完整 `Assert` / `Inv Assert` 时必须先对照这里的常见错误）
5. `docs/predicate-first-annotation.md`
6. `docs/builtin-array-string-support.md`（遇见数组、字符数组、C 字符串或字符串字面量时必须阅读）
7. `docs/array-predicate-selection.md`（只在遇见与数组相关问题时阅读）
8. `docs/qcp-resource-reclaim-errors.md`（遇见 `remove permission failed`、return / scope 结束处局部变量回收失败时必须阅读）
9. `docs/reference-cases.md`
10. `docs/split_array_largest_sum/binary-search-annotation.md`（只在遇见二分答案、`check` 判定函数、单调可行性区间时阅读）
11. `../annotation-checking/SKILL.md`
12. `../annotation-checking/docs/spec-quality-checklist.md`
13. `docs/symexec-refresh.md`

## 工作步骤

1. 读取当前 annotation 轮次的 delegation ticket，确认目标 C 文件、`common_case_formal_lib`、输出目录、验证函数、proof 类型、本轮 annotation C scratch 路径、`annotation_scratch_lib` 路径、`timing_required` / `timing_log_path`，以及是否附带 `Re-entry Brief`；记录本轮 `phase_started_at`。
2. 若存在 `Re-entry Brief`，先根据其中的失败原因、受影响 witness / 文件和本轮重点，决定本轮优先修正的 annotation 点。
3. 若旧的 annotation C scratch 或 `annotation_scratch_lib` 仍存在，先删除；随后从最新正式 `.c` 复制出 fresh annotation C scratch，从最新 `common_case_formal_lib` 复制出 fresh `annotation_scratch_lib`。若 `common_case_formal_lib` 尚不存在，创建本轮空 / 最小 `annotation_scratch_lib`。
4. 先做 spec-first 设计：阅读 C 程序和 `annotation_scratch_lib`，确认目标数学 spec 是否存在、是否正确。缺失时先在 `annotation_scratch_lib` 中补充严格数学定义；不合理时先修正 `annotation_scratch_lib`。定义必须描述数学性质，不能在 Rocq 中重写 C 程序本体或 loop 状态机。
5. 再做一轮 predicate-first annotation 设计：优先选局部隐藏性质、直观谓词和子区间语义，并让 C annotation 调用已经确认正确的 `annotation_scratch_lib` spec。若涉及数组、字符数组、C 字符串或字符串字面量，必须先按 `docs/builtin-array-string-support.md` 判断能否直接使用 builtin 谓词和策略，不要在 `common_case_formal_lib` 中重复定义同类内存谓词。
6. 参考 ticket 中给出的正例 / 反例以及 `reference-cases.md`，在 scratch 上补充或修正函数规格、断言和循环不变式；函数 spec 重点补足逻辑性质，内部 assertion 重点检查 `Inv Assert`。
7. 若发现自己正在依赖“Rocq 中的递归算法定义 / 状态机定义”来推动 annotation，应先回退并重新组织 `annotation_scratch_lib` spec 与 annotation；只有 refinement proof 所必需的 `safeExec` / monad 规格可以保留。
8. 在 scratch 上反复运行 `qcp-mcp`，持续迭代 annotation；每次关键 `symbolic` / `check` / `step` / 重新验证都记录耗时、结果和对应 C 行号、annotation 区块或 `annotation_scratch_lib` spec 定义。若目标是 `QCP_examples/LLM_bench` case 且源码使用 `QCP_demos_LLM` 公共头文件的裸 include，本轮 `qcp-mcp` 启动 / wrapper 配置必须能在 C include search path 中解析 `QCP_examples/QCP_demos_LLM/`；头文件解析失败时修工具 include 配置，不改源码 include 形态。若 direct wrapper 因仓库 ELF 无执行位报 `Permission denied`，应优先确认同一 `qcp-mcp` 链路是否能通过 loader fallback 成功；只有 `qcp-mcp` 本身跑通，才算满足本轮 `qcp_mcp_requirement_satisfied`。仅有 direct `symexec` 成功不能替代这一要求。若 QCP 在 `return`、函数结束或局部 scope 结束处报 `remove permission failed` / 局部变量内存回收失败，按 `docs/qcp-resource-reclaim-errors.md` 检查失败点上一句的 symbolic state，优先补齐漏掉的局部变量权限或完整数组资源。不要在第一次尝试后就返回，只有在本轮达到 `completed`、`blocked` 或 `stale` 时才结束。
9. 标出哪些 annotation 点和 `annotation_scratch_lib` spec 定义最可能影响 witness 结构、后续 proving，或暴露出 manual VC 语义不可证的问题。
10. 当 scratch 上的候选 annotation 通过 `qcp-mcp` 后，立即由同一 `annotation-subagent` 调用 `annotation-checking`。如果检查结果是 `failed`，不得把本轮作为 `completed` 返回；必须回到步骤 4/5/6 修正 `annotation_scratch_lib` 或 annotation C scratch，并在修正后重新运行必要的 `qcp-mcp` 与 `annotation-checking`。
11. 只有当 `annotation-checking` 返回 `passed`，并且 report 中明确给出 `qcp_mcp_requirement_satisfied: yes` 与 `annotation_scratch_lib_coqc_status: passed` 时，才以 `Subagent Return Report` 的形式，把已经在 scratch 上验证并通过质量门的 C patch、`annotation_scratch_lib` spec patch、风险点、最终采用的隐藏性质、参考案例映射、`Annotation Checking Report` 和 timing 摘要交给主 agent；timing 摘要至少包含本轮总耗时、命令耗时、非命令 activity 耗时、最慢 `qcp-mcp` 检查或 annotation 区块、spec definition 设计 / 修改耗时、annotation-checking 耗时、主要耗时原因和无法精确统计的 timing gaps。由主 agent 先运行 annotation gate 校验，再回填正式 `.c` / `common_case_formal_lib`，更新 lib frozen prefix，并在正式文件上执行 symexec 刷新。
12. 当本轮结束、返工或输入 stale 时，删除 annotation C scratch 和 `annotation_scratch_lib`，并把 phase 切换建议交回 `verification-orchestrator`。
