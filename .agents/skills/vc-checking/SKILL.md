---
name: vc-checking
description: 判断 QCP 生成的 separation logic VC 是否语义可证，并区分问题来自 annotation、witness 结构、group-local helper lemma 需求还是 manual proof；helper lemmas 先由 vc-proving 迁入本轮 task_local_scratch_lib，所有目标 VC 完成后再批量回填 common_case_formal_lib。
---

# VC Checking

这个 skill 只负责 witness / VC 的可证性分诊。它固定绑定给 `vc-checking-subagent`；phase、`Witness Ledger` 字段、状态枚举和 stale 规则统一由 `verification-orchestrator` 定义，本 skill 不再重复这些基础合同。


## 何时使用

- case 已由 `verification-orchestrator` 置于 `vc-checking` 阶段。
- 主 agent 已为当前 vc-checking 轮次启动 `vc-checking-subagent`。
- 需要判断某个 witness 是否语义可证。
- 需要判断问题更像 annotation bug、lemma 缺失还是 proof gap。

## 进入前提

- 当前 `goal` / witness 集合对应最新冻结版本。
- 主 agent 已确认本轮分诊不是基于过期生成文件。
- 当前 delegation ticket 的 `subagent_name` 固定为 `vc-checking-subagent`。

## 直接输出

- 对目标 witness 或 witness 集的分诊结论。
- 对应的失败信号、证明难点以及后续 proving / annotation 建议。
- `witness_group_plan`：按自然语言证明思路归类的 proving 分组计划。每组至少包含 `proof_group_id`、`members`、`representative_witness`、`natural_language_proof_pattern`、`shared_helper_candidates`、`proving_hints`、`grouping_confidence`。
- 本轮 vc-checking 总耗时、每个 witness 或 witness cluster 的分析耗时、最慢分诊点以及主要耗时原因。
- 若本轮返回 `blocked` 或总耗时超过 600 秒，必须额外输出 blocked / long-duration 诊断：blocked reason、long-duration reason、具体证据、受影响 witness/cluster、已经尝试过的判断路径、下一步建议。
- 若结论是 `needs-lemma`，必须明确该 helper lemma 先由 `vc-proving` group worker 在 `worker_helper_scratch_lib` 中证明，再通过 helper migration 迁入本轮 `task_local_scratch_lib` 后缀；不要建议在 vc-checking 或单个 witness 证明期间直接修改 `common_case_formal_lib`。

## Informal Proof 判定规则

1. 先把每个目标写成 `P |-- Q`，明确当前 VC 前条件 `P` 中的空间资源、纯事实、存在量词、数学 spec 假设和局部变量关系。
2. 给出足够具体的 informal proof，说明从 `P` 如何构造 `Q` 中要求的资源和纯结论。
3. 每个 proof 使用的 lemma 都必须逐条列出，且来源只能是现有项目 library / 当前 case 已存在的 `*_lib.v`，或本轮显式列入 `candidate_lib_lemmas` 的候选 helper。
4. 对每个 lemma 的每个 premise，必须逐项说明它如何由当前 VC 的前条件推出；可以来自 `P` 中已有纯事实、空间资源解释、已展开的数学 spec，或可安全实例化的存在量词。
5. 如果某个 lemma 不在现有 library，也没有列入 candidate lib；或某个 premise 需要额外假设、需要改写冻结前缀、或无法由当前 VC 前条件推出，则该 VC 不能判为 `proofable` / `needs-lemma`，必须返回 `annotation-bug` 或 `blocked`。
6. 只有所有目标 VC 的 judgment 都是 `proofable` 或 `needs-lemma`，且所有 lemma 来源 / premise discharge 都可审计时，才能建议进入 `vc-proving`。

## 会使哪些产物失效

- 本 skill 本身不刷新 `goal`，但一旦它得出 `annotation-bug` 结论，主 agent 必须把 case 退回 annotation，并按 orchestrator 规则使下游 proving 计划失效。

## 主 / 子 Agent 局部边界

- `vc-checking-subagent` 负责给出 witness 分诊建议与关键依据。
- 主 agent 负责确认最终分诊结论、更新 ledger，并决定后续 phase 去向。
- `vc-checking-subagent` 不直接改写当前 case 的 annotation 或 `*_proof_manual.v`。

## 参考文档

1. 先读 `../verification-orchestrator/SKILL.md`
2. `docs/use-notes.md`
3. `docs/checking-workflow.md`
4. `docs/informal-proof-analysis.md`
5. `docs/common-failure-signals.md`

## 工作步骤

1. 读取当前 vc-checking 轮次的 delegation ticket，确认目标 witness 集、`source_goal_version`、输出格式和 timing 要求，并记录本轮 `phase_started_at`。
2. 取当前 witness 或 VC，先识别其形状，重点分析 `P |-- Q` 中前后条件分别表达什么；对每个 witness 或 witness cluster 记录分析开始 / 结束时间。
3. 判断该目标在当前 annotation 下是否语义可证。
4. 如果目标不可证，明确说明应回到 `annotation-filling` / `annotation-checking` 修正 C annotation 或 `annotation_scratch_lib` spec，而不是继续堆 Rocq tactic。
5. 如果目标可证，再判断缺的是证明结构、group-local helper lemma，还是 tactic 选择；若结论是 `needs-lemma`，明确指出该 lemma 应由 `vc-proving` worker 在组内 `worker_helper_scratch_lib` 中证明，再通过 `migrate_helpers_to_lib.py` 迁入本轮 `task_local_scratch_lib` 后缀，而不是修改冻结前缀，也不是提前追加到 `common_case_formal_lib`。
6. 基于自然语言证明思路构造 `witness_group_plan`：把证明模式、关键前后条件、可能共享的 helper 和 tactic 入口相似的 witness 放进同一组；每组指定一个代表 witness。不要把“一条 witness 一个 group”当作默认策略，除非这些 witness 的证明形状确实无法共享。
7. 把分诊结论、`witness_group_plan` 和 timing 摘要交回主 agent，由主 agent 更新 ledger、决定 phase 去向，并在必要时刷新生成文件后重新进入 vc-checking。若本轮 `elapsed_seconds > 600`，必须提供 `long_duration_reason`；若本轮 `round_outcome = blocked`，必须提供 `blocking_reason`、证据和 recommended next phase/action。