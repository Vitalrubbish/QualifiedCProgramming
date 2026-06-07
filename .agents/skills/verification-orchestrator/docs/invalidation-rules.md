# 失效传播规则

本文件定义当前 case 中哪些变化会让下游结论失效。

## 总规则

- 一旦命中以下任一上游变化，必须立即把对应下游分析标记为 `stale` 或 `invalidated`。
- 失效后只能重做，不能靠删除正式文件来假装“未发生”。
- phase subagent 的结果与主 agent 的 ledger 结论遵守同一套失效传播规则。
- 对 annotation / proving phase 来说，标记 stale 之外，还必须删除对应 scratch。
- 如果某个 phase 是从下游失败后重新进入，则下一轮 ticket 必须带 `Re-entry Brief`，明确说明为什么回流、哪些输入变化了。
- 如果 `Case Brief` 中冻结的 `common_case_formal_lib` 前缀定义或 `proof_manual_scope` 变化，所有基于旧 formal 文件边界的 proving / final-check 结论都必须失效。
- 失效的 formal 结论、旧 scratch、旧 proof skeleton 不能继续作为当前 proof 结果使用；但 `.agents/reports` 中的 `partial_proof_packet.json` 若通过 schema / hash / safety 检查，可以在 direct-reuse 条件不满足、helper payload 冲突或 direct candidate compile gate 失败时转成显式标注的 proof-pattern reference，让 worker 阅读 per-goal candidates、完整 proof reference pool、旧 helper block 的证明形状并重新适配当前 VC。pattern reference 不是复用旧结论，不能移除 worker scope，也不能跳过当前 proof 的 compile / merge / helper-migration / verify gate。

## scratch 生命周期总规则

- annotation C scratch 在以下任一情况发生时必须删除：
  - phase 完成
  - phase 输入 stale
  - 主 agent 已回填正式 `.c`
  - case 回退或重开新轮次
- `annotation_scratch_lib` 在以下任一情况发生时必须删除：
  - phase 完成
  - phase 输入 stale
  - 主 agent 已回填 `common_case_formal_lib`
  - case 回退或重开新轮次
- annotation-checking 结果只绑定当前 annotation C scratch、`annotation_scratch_lib` 和当前 filling report；C scratch、`annotation_scratch_lib`、candidate patch、spec definition patch 或 filling report 任一变化，旧 checking 结果立即 stale。
- proving scratch 在以下任一情况发生时必须删除：
  - phase 完成
  - phase 输入 stale
  - 主 agent 已正式集成新的 `*_proof_manual.v` / `common_case_formal_lib`
  - symexec 刷新出新的正式 `*_proof_manual.v`
  - case 回退或重开新轮次
- `done` 前不得残留任何 phase scratch、`.tmp` worker workdir、`.aux` 文件或本轮测试 / Python 缓存。

## `Case Brief` 关键字段改动后

关键字段指：

- `c_path`
- `target_function`
- `proof_type`
- `output_path`
- `lib_frozen_prefix_end_line`
- `lib_frozen_prefix_snapshot`
- `proof_manual_scope`

以下内容全部标记为 `stale` 或 `invalidated`：

- 旧 `annotation-subagent` 输出
- 旧 `annotation-checking` 结果
- 旧 vc-checking informal proof provability report
- 旧 `vc-checking-subagent` 输出
- 旧 `vc-proving-subagent` 输出
- 当前 `Witness Ledger`
- 旧 proving 计划
- 旧 `Final Check Checklist`
- 旧 final-check 结论
- 当前 annotation C scratch
- 当前 `annotation_scratch_lib`
- 当前 proving scratch

同时要求：

- phase 退回 `intake` 或 `annotation`
- 基于旧 case identity 的 delegation ticket 全部作废
- 删除当前 case 的 phase scratch

## annotation / spec definition 改动后

以下内容全部标记为 `stale` 或 `invalidated`：

- 当前 `Witness Ledger`
- 旧 `annotation-subagent` 输出
- 旧 `annotation-checking` 结果
- 旧 vc-checking informal proof provability report
- 旧 `vc-checking-subagent` 输出
- 旧 `vc-proving-subagent` 输出
- 旧 proving 计划
- 旧 `Final Check Checklist`
- 旧 final-check 结论
- 旧 annotation C scratch
- 旧 `annotation_scratch_lib`
- 当前 proving scratch

若 annotation 或 spec definition 改动同时改变了循环结构、predicate 家族或 proof 风格判断，还要额外失效：

- 旧参考案例映射

同时要求：

- 删除旧 annotation C scratch 与 proving scratch
- 删除旧 `annotation_scratch_lib`
- annotation phase 必须重新创建新的 annotation C scratch 和 `annotation_scratch_lib`，并在新的 C scratch 上重新运行 `qcp-mcp`
- 必须重新刷新 `goal` 相关生成文件
- 重新刷新 `goal` 前，新的 annotation 候选必须先通过 `annotation-checking`
- 必须重新进入 `goal-frozen`
- 如果这是从下游 phase 回流进入的新 annotation 轮次，新的 ticket 必须补充 `Re-entry Brief`

## `goal` / `goal_check` 刷新后

以下内容失效：

- 旧 witness 列表
- 旧 vc-checking informal proof provability report
- 旧 `vc-checking-subagent` 输出
- 旧 `vc-proving-subagent` 输出
- 基于旧 witness 的 proving 计划
- 旧 `Final Check Checklist`
- 旧 final-check 结论
- 当前 proving scratch

同时要求：

- `goal-frozen` 之后重新进入 `vc-checking`
- 任何引用旧 `phase_input_version` 或旧 `source_goal_version` 的 delegation ticket 立即作废
- 若刷新同时生成了新的正式 `*_proof_manual.v`，删除旧 proving scratch，并从新的正式快照重建

## witness 状态改动后

若 witness 被标记为 `annotation-bug`、`stale` 或其 `source_goal_version` 改变，以下内容失效：

- 该 witness 的旧 proof skeleton
- 该 witness 的旧 lemma 候选
- 该 witness 的旧 `vc-proving-subagent` 分析结果
- 依赖该 witness 已完成的旧 final-check 结论

若旧 round checkpoint / packet 覆盖到该 witness：

- 不得执行 direct reuse，也不得把旧 packet proof script 直接写入当前 manual 后标记 solved。
- 若问题不是 annotation-bug，且下一轮 ticket 明确采用 `exact_or_pattern` / `pattern_reference`，允许把旧 packet 中的相似 proof script、informal proof、helper import / helper block 作为 proof-pattern reference 交给 worker；worker 必须在当前 fresh scratch 中重写或适配，并重新编译通过。
- 若 witness 被标记为 annotation-bug，旧 proof pattern 只能作为审计线索，不应自动交给 worker 当作当前证明参考。

## `*_proof_manual.v` 或 `common_case_formal_lib` 改动后

以下内容失效：

- 旧 `vc-proving-subagent` 输出
- 旧 `Final Check Checklist`
- 旧 final-check 结论
- 旧 final-check review 结论
- 基于旧正式快照的当前 proving scratch

同时要求：

- 必须重新进入 `final-check`
- 若当前仍在 `vc-proving`，则先删除旧 proving scratch，再从最新正式 `*_proof_manual.v` / `common_case_formal_lib` 重建
- 尤其当改动来自 symexec 刷新的新正式 `*_proof_manual.v` 时，禁止继续沿用旧 proving scratch
- 如果因此回流到新的 `vc-proving` 轮次，新的 ticket 必须补充 `Re-entry Brief`

## 冻结的 `common_case_formal_lib` 前缀变化后

若 `common_case_formal_lib` 中位于 `lib_frozen_prefix_end_line` 以内的内容发生变化，以下内容立即失效：

- 当前 proving scratch
- 旧 `vc-proving-subagent` 输出
- 旧 `Final Check Checklist`
- 旧 final-check 结论

同时要求：

- 立即删除旧 proving scratch
- 主 agent 必须先更新 `Case Brief` 中的 `lib_frozen_prefix_end_line` / `lib_frozen_prefix_snapshot`
- 若当前处于 `final-check`，必须回退到 `vc-proving`
- 新的 `vc-proving` ticket 必须带新的 `protected_lib_prefix_end_line`

## delegation 输入范围改动后

若以下任一内容变化，则对应子任务结果立即 `stale`：

- `subagent_name`
- `skill_name`
- allowed read set
- `allowed_tooling`
- target witness 集
- 当前 phase
- `phase_input_version`
- `scratch_seed_files`
- `scratch_owned_paths`
- `annotation_scratch_lib_seed_files`
- `annotation_scratch_lib_owned_paths`
- `post_filling_quality_gate`
- `annotation_checking_required`
- `spec_definition_review_required`
- `proof_manual_write_contract`
- `lib_write_contract`
- `protected_lib_prefix_end_line`
- stale 条件本身

同时要求：

- 删除该 ticket 拥有的 scratch

## 失效的正确处理方式

- 标记 `stale`
- 记录 stale reason
- 删除受影响的 scratch
- 重新进入正确 phase

## 明确禁止的处理方式

- 删除 `*_proof_manual.v`
- 删除 `common_case_formal_lib`
- 通过删除生成文件来掩盖 stale 状态
- 继续沿用已知过期的 witness 分析或 proof skeleton
- 把 pattern-reference JSON 当成已证明结果，或用它绕过当前 VC 的编译与 helper migration 检查
- 继续沿用已知过期的 scratch
