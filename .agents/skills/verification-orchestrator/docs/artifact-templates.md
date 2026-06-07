# 工件模板

这些模板用于稳定主 agent 与固定 phase subagent 的交接格式。
默认不强制每个 case 都落盘为单独文件，但字段和状态名必须保持一致。

## `Case Brief`

```md
## Case Brief

- case_name:
- c_path:
- target_function:
- proof_type: direct-proof | refinement-proof
- output_path:
- reference_cases:
- style_reference_cases:
- annotation_style: predicate-first | refinement-required+predicate-first
- anti_patterns:
- lib_frozen_prefix_end_line:
- lib_frozen_prefix_snapshot:
- annotation_spec_definitions_status: unchecked | scratch-proposed | integrated-and-refrozen | n/a
- proof_manual_scope: witness-proofs-after-lib-migration
- current_phase:
- main_state_files:
- persistent_report_dir:
- report_layout: run-root-snapshots-plus-round-dirs
- latest_round_report_dir:
```

## Report Folder Layout

持久 report 必须落在：

```text
.agents/reports/<relative-case-dir>/<YYYY-MM-DD>/<case-name>-<YYYYMMDDTHHMMSS>/
```

run root 保存 `case_brief.md`、输入快照、正式生成物快照和最终汇总；每个 phase 轮次新建：

```text
<YYYYMMDDTHHMMSS>-<phase>-r<N>[-<scope>]/
```

标准文件名：

- annotation: `annotation_filling_analysis.md`、`annotation_checking_report.md`、`subagent_return_report.md`、`timing_log.md`
- vc-triage: `vc_checking_informal_proof_report.md`、`timing_log.md`
- vc-proving: `proof_strategy_report.md`、`vc_proving_failure_analysis.md`、`worker_proof_report.json`、`worker_proof_strategy_report.json`、`subagent_return_report.md`、`timing_log.md`，以及可选 `reuse_checkpoints/<round-id>/vc_proving_round_checkpoint.json`、`partial_proof_packet.json`、`reuse_index.json`

历史 hyphen 命名可读，不再作为新 report 的 canonical 名称。

## `Witness Ledger`

状态枚举只允许：

- `unchecked`
- `proofable`
- `needs-lemma`
- `annotation-bug`
- `proved`
- `stale`

类别枚举建议只使用：

- `spatial`
- `pure`
- `refinement`
- `safeExec`

```md
## Witness Ledger

| witness_id | category | status | owner | source_goal_version | summary | stale_reason |
| --- | --- | --- | --- | --- | --- | --- |
|  |  | unchecked |  |  |  |  |
```

## `Phase Status`

```md
## Phase Status

- phase:
- frozen_inputs:
- active_scratch_paths:
- active_phase_owner:
- invalidated_outputs:
- blocking_reason:
- phase_started_at:
- phase_finished_at:
- phase_elapsed_seconds:
- timing_source: wall-clock | command-timer | subagent-report | unknown
- human_activity_timings:
  - analysis_seconds:
  - integration_edit_seconds:
  - proof_edit_seconds:
  - helper_cleanup_seconds:
  - subagent_wait_seconds:
  - review_seconds:
- major_time_sinks:
- next_action:
```

## `Delegation Ticket`

每次进入 `annotation`、`vc-checking`、`vc-proving` 的新轮次，都必须先构造一份 delegation ticket；可以不落盘，但字段必须完整。

```md
## Delegation Ticket

- subagent_name: annotation-subagent | vc-checking-subagent | vc-proving-subagent
- skill_name: annotation-filling | vc-checking | vc-proving
- post_filling_quality_gate: annotation-checking | n/a
- task_type: annotation-phase | vc-checking-phase | vc-proving-phase
- phase:
- phase_input_version:
- trigger_rule:
- target_scope:
- iteration_owner: main | subagent
- return_condition: completed | blocked | stale
- allowed_read_set:
- allowed_tooling: none | qcp-mcp | rocq-mcp
- scratch_seed_files:
- scratch_owned_paths:
- annotation_scratch_lib_seed_files:
- annotation_scratch_lib_owned_paths:
- witness_group_plan:
- grouping_source: vc-checking-group-plan | sort_chunk_fallback | n/a
- proof_pattern_summary:
- group_helper_policy: group-local-helper-lib | n/a
- worker_manual_workdir:
- worker_reports:
- previous_vc_proving_checkpoint: none | <vc_proving_round_checkpoint.json>
- previous_partial_proof_packet: none | <partial_proof_packet.json>
- checkpoint_reuse_policy: exact_or_pattern | exact | extended_candidate | pattern_reference | disabled | n/a
- checkpoint_stale_conditions:
- timing_required: true
- persistent_report_dir:
- round_report_dir:
- timing_log_path:
- activity_ledger_required: true
- activity_ledger_path:
- subagent_first_event_required: true
- expected_report_paths:
- proof_manual_write_contract: witness-proofs-after-lib-migration | n/a
- lib_write_contract: frozen-prefix-then-helper-imports-and-lemmas | n/a
- protected_lib_prefix_end_line: none | <line>
- allowed_write_set:
- forbidden_write_set:
- expected_output:
- handoff_format:
- annotation_focus:
- preferred_hidden_properties:
- forbidden_annotation_patterns:
- annotation_checking_required: true | false
- spec_definition_review_required: true | false
- spec_definition_focus:
- vc_informal_proof_report_path:
- cleanup_paths:
- reentry_brief:
- stale_if:
```

## `Subagent Return Report`

长时间迭代 phase 返回主 agent 时，应输出统一结构。

```md
## Subagent Return Report

- round_outcome: completed | blocked | stale
- summary:
- phase_started_at:
- phase_finished_at:
- phase_elapsed_seconds:
- timing_summary:
- command_timings:
- human_activity_timings:
- activity_ledger:
- open_or_incomplete_timing_events:
- subagent_boundary_timings:
  - launch_requested_at:
  - spawn_returned_at:
  - first_subagent_event_at:
  - finished_observed_at:
  - close_requested_at:
  - close_finished_at:
  - launch_overhead_seconds:
  - subagent_self_elapsed_seconds:
  - notification_wait_seconds:
  - close_overhead_seconds:
- slowest_steps:
- major_time_sinks:
- ready_for_main:
- annotation_checking_status: passed | failed | blocked | stale | n/a
- qcp_mcp_requirement_satisfied: yes | no | n/a
- annotation_scratch_lib_coqc_status: passed | failed | n/a
- ready_for_main_symexec: yes | no | n/a
- annotation_checking_report:
- vc_informal_proof_report:
- ready_for_main_c_patch:
- ready_for_main_common_case_formal_lib_spec_update: spec-definitions | empty | n/a
- ready_for_main_proof_manual:
- ready_for_main_common_case_formal_lib_append: migrated-helper-imports-and-lemmas | migrated-helper-lemmas | empty | n/a
- migrated_helper_imports:
- witness_group_plan:
- grouping_source:
- proof_pattern_summary:
- group_helper_policy:
- worker_reports:
- checkpoint_reuse_summary:
- round_checkpoint:
- partial_proof_packet:
- reuse_index:
- protected_prefix_respected:
- blocking_reason:
- recommended_next_phase:
- cleanup_status:
```

## `Annotation Checking Report`

`annotation-subagent` 每次完成 `annotation-filling` 后必须产出这一段；可以嵌入 `Subagent Return Report.annotation_checking_report`。

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

## `VC Informal Proof Provability Report`

`vc-checking` 在 `vc-triage` 阶段使用这一结构，作为 witness / VC 可证性分诊的正式 report。

```md
## VC Informal Proof Provability Report

- status: passed | failed | blocked | stale
- source_goal_version:
- checked_witness_scope:
- summary:
- candidate_lib_lemmas:
- existing_library_lemmas:
- failed_witnesses:
- required_annotation_rework:
- required_lib_rework:
- ready_for_vc_proving: yes | no

| witness_id | judgment | informal_proof | used_lemmas | lemma_sources | premise_discharge | missing_or_unjustified_premises | next_action |
| --- | --- | --- | --- | --- | --- | --- | --- |
|  | proofable \| needs-lemma \| annotation-bug \| blocked |  |  | existing-library \| candidate-lib | all-premises-from-vc-precondition \| not-justified |  |  |
```

`judgment` 只能是 `proofable` 或 `needs-lemma`，才能支持 `status: passed`。每个 informal proof 用到的 lemma 必须来自现有 library 或本轮明确列入 `candidate_lib_lemmas` / 后续 `*_lib.v` helper suffix 的 lemma；每个 lemma premise 都必须逐项说明由当前 VC 前条件推出。任何 lemma 来源不明、需要额外前提、或 premise 不能由当前 VC 前条件推出时，不能判为 proofable，必须返回 `failed` 并指向 annotation / lib rework。

## `Re-entry Brief`

从下游 phase 回流后重新进入 `annotation` 或 `vc-proving` 时，主 agent 必须补充这一段。

```md
## Re-entry Brief

- reentered_from_phase:
- why_reentered:
- what_failed_last_round:
- affected_witnesses_or_files:
- what_changed_since_last_round:
- must_focus_this_round:
```

## `Final Check Checklist`

`final-check` phase 由主 agent 直接执行，不使用 delegation ticket。进入 `final-check` 时，应先建立或更新这一份检查清单。

```md
## Final Check Checklist

- phase: final-check
- lib_frozen_prefix_matches_case_brief:
- proof_manual_scope_ok:
- lib_frozen_prefix_ok:
- lib_helper_suffix_imports_ok:
- lib_helper_suffix_ok:
- no_stale_scratch:
- temp_files_cleanup_status:
- symexec_status:
- coqc_status:
- timing_summary_status:
- slowest_phase:
- slowest_command_or_witness:
- major_time_sinks:
- admitted_axiom_review_status:
- blocking_reason:
- recommended_next_phase:
```

## `Timing Summary`

每个 case 在进入 `final-check` 前应已经具备跨 phase 的 timing 记录；`final-check` 负责把它整理成最终摘要。

```md
## Timing Summary

- total_elapsed_seconds:
- total_command_seconds:
- total_human_activity_seconds:
- total_subagent_wait_seconds:
- timing_gaps:

| phase | owner | started_at | finished_at | elapsed_seconds | source | notes |
| --- | --- | --- | --- | --- | --- | --- |
|  |  |  |  |  |  |  |

| phase | command_or_step | elapsed_seconds | result | notes |
| --- | --- | --- | --- | --- |
|  |  |  |  |  |

| phase | activity_kind | elapsed_seconds | source | notes |
| --- | --- | --- | --- | --- |
|  | manual-analysis |  | wall-clock |  |
|  | subagent-wait |  | wall-clock |  |
|  | subagent-launch-overhead |  | wall-clock |  |
|  | subagent-self-elapsed |  | subagent-ledger |  |
|  | subagent-notification-wait |  | wall-clock |  |
|  | subagent-close-overhead |  | wall-clock |  |
|  | annotation-edit |  | wall-clock |  |
|  | proof-edit |  | wall-clock |  |
|  | helper-cleanup |  | wall-clock |  |
|  | integration-edit |  | wall-clock |  |
|  | review-cleanup |  | wall-clock |  |

| witness_or_helper | phase | elapsed_seconds | source | notes |
| --- | --- | --- | --- | --- |
|  |  |  |  |  |

| event_id | parent_event_id | actor | round_id | witness_or_helper | activity_kind | started_at | finished_at | elapsed_seconds | status | artifact_paths | summary |
| --- | --- | --- | --- | --- | --- | --- | --- | ---: | --- | --- | --- |
|  |  |  |  |  | proof-state-reduction |  |  |  |  |  |  |
|  |  |  |  |  | spatial-proof-generation |  |  |  |  |  |  |
|  |  |  |  |  | pure-proof-generation |  |  |  |  |  |  |
|  |  |  |  |  | helper-design |  |  |  |  |  |  |
|  |  |  |  |  | helper-proof-generation |  |  |  |  |  |  |
|  |  |  |  |  | proof-script-edit |  |  |  |  |  |  |
|  |  |  |  |  | coqc-run |  |  |  |  |  |  |
|  |  |  |  |  | coqc-feedback-analysis |  |  |  |  |  |  |

- slowest_steps:
- major_time_sinks:
```

## 使用要求

- 字段名和状态名不要私自扩展或改名。
- 如果不落盘，也要在主 agent 的工作记录里保持同样的结构。
- 任何 stale 判断都必须可追溯到某个具体上游变化。
- `Delegation Ticket` 的 `subagent_name` 和 `skill_name` 必须使用固定枚举，不允许临时改名。
- `annotation` ticket 必须设置 `post_filling_quality_gate: annotation-checking` 和 `annotation_checking_required: true`；其它 phase 写 `n/a` / `false`。
- `annotation` ticket 必须设置 `spec_definition_review_required: true`，并提供 `annotation_scratch_lib_seed_files` / `annotation_scratch_lib_owned_paths`；其它 phase 写 `false` / `n/a`。
- `Delegation Ticket` 的 `forbidden_write_set` 默认至少包含当前 case 主状态集。
- `allowed_tooling` 只允许使用上面的固定枚举；`annotation-subagent` 只能拿到 `qcp-mcp`，`vc-proving-subagent` 只能拿到 `rocq-mcp`。
- `iteration_owner` 在 `annotation` / `vc-proving` 轮次中必须是 `subagent`。
- `return_condition` 不是“先给一版结果”，而是本轮 phase 何时可以从 subagent 返回 main。
- `Case Brief.annotation_style`、`style_reference_cases`、`anti_patterns` 在算法类 case 中不得留空。
- `annotation` ticket 的 `annotation_focus`、`preferred_hidden_properties`、`forbidden_annotation_patterns` 不得留空；这些字段用于把“predicate-first”约束真正传给 `annotation-subagent`。
- `annotation` 的 `Subagent Return Report.annotation_checking_status` 必须是 `passed`，且 `qcp_mcp_requirement_satisfied = yes`、`annotation_scratch_lib_coqc_status = passed`，才能把 `ready_for_main` / `ready_for_main_symexec` 标为 true；`failed` 时应继续同一轮 annotation 修正，不应返回 completed 给 main。
- `annotation` 的 `ready_for_main_common_case_formal_lib_spec_update` 如果不是 `empty` / `n/a`，main 必须先回填 `common_case_formal_lib` 并刷新 `Case Brief.lib_frozen_prefix_*`，再运行 symexec。
- `scratch_owned_paths` 和 `allowed_write_set` 在 `annotation` / `vc-proving` 轮次中应一致，并且只能指向本轮 scratch。
- `annotation` 轮次的 `allowed_write_set` 必须同时覆盖 C scratch 和 `annotation_scratch_lib`，不能覆盖正式 `.c` / `common_case_formal_lib`。
- `proof_manual_write_contract` 在 `vc-proving` 轮次中必须是 `witness-proofs-after-lib-migration`。
- `lib_write_contract` 在 `vc-proving` 轮次中必须是 `frozen-prefix-then-helper-imports-and-lemmas`。
- `protected_lib_prefix_end_line` 在 `vc-proving` 轮次中必须与 `Case Brief` 中的 frozen prefix 定义一致；若当前 case 尚无 `common_case_formal_lib`，则写 `none`。
- `witness_group_plan` 在 `vc-checking` 返回时由 `vc-checking-subagent` 产出，在 `vc-proving` ticket 中由主 agent 原样交给 `vc-proving-subagent`；每组必须包含 `proof_group_id`、`members`、`representative_witness`、`natural_language_proof_pattern`、`shared_helper_candidates`、`proving_hints` 和 `grouping_confidence`。若没有 vc-checking group plan，`vc-proving` 必须显式记录 `grouping_source: sort_chunk_fallback`。
- `group_helper_policy` 在 `vc-proving` 中固定为 `group-local-helper-lib`：worker 只能把 reusable helper 写入本组 `worker_helper_scratch_lib`，不得写 worker manual、`task_local_scratch_lib` 或 `common_case_formal_lib`。
- `worker_manual_workdir` / `worker_reports` 在 `vc-proving` 中默认指向 `.tmp` 下的 worker 目录和 report 文件；若本轮因 Codex worker 环境不可恢复而切换到串行 fallback，则它们应改为指向 `.tmp` 下的串行 proving 工作目录 / 报告文件，不能写 `n/a` 来绕过审计。
- `previous_vc_proving_checkpoint` 只能指向 `.agents/reports` 下上一轮 `vc_proving_round_checkpoint.json`；它是下一轮 fresh scratch 的 prepass 输入，不是旧 scratch 续用入口。`previous_partial_proof_packet` 默认写 `none`，由 checkpoint manifest 间接指定；只有调试脱离 checkpoint 的 packet applier 时才直接填写。`checkpoint_reuse_policy` 默认 `exact_or_pattern`：若当前 manifest 缺少 case id / source goal version，或 frozen prefix line/hash、source goal version、packet hash、helper payload 冲突，或 direct candidate compile gate 失败，则不得 direct reuse，但应在存在相似 witness 时生成 proof-pattern reference 交给 worker 学习。
- 每个 phase 都必须记录 wall-clock 开始/结束时间和 elapsed seconds；如果只能从 subagent report 或命令输出推断，应在 `timing_source` 中说明。phase elapsed 是总墙钟时间，不能只用命令耗时代替。
- 主 agent 在进行非命令工作时也必须开闭计时并写入 `human_activity_timings` / activity 表：至少覆盖规格/annotation 人工分析、等待 subagent 返回、正式文件回填或合并、proof 修改、helper lemma 清理、冗余 lemma 清理、Makefile/依赖集成、final review 与 cleanup。若这些工作跨多段发生，应分段记录后汇总。
- `Delegation Ticket.timing_required` 默认必须为 `true`；delegated phase 返回的 `Subagent Return Report` 必须包含本轮总耗时、关键命令耗时、最慢 witness/helper 或步骤，以及主要耗时原因。
- `Delegation Ticket.activity_ledger_required` 默认必须为 `true`。subagent 和 worker 必须在 proof-planning / proof-generation activity 开始前写 `START`、结束后写 `END`；不得在事后用单个“proof search 约 X 分钟”替代。vc-proving 至少要按 witness/helper 拆出 `proof-state-reduction`、`spatial-proof-generation`、`pure-proof-generation`、`helper-design`、`helper-proof-generation`、`proof-script-edit`、`coqc-run`、`coqc-feedback-analysis`。
- `Subagent Return Report.subagent_boundary_timings` 必须能拆出 main 启动 subagent 的开销、subagent 自身第一条 ledger 到结束的运行时间、main 等待通知时间和 close 开销。主 agent 的最终 Timing Summary 不得只写一个合并的 `subagent-wait`。
- 主 agent 独占的 symexec、正式 coqc、final-check 扫描与 cleanup 也必须记录命令级耗时；长时间 coqc 推荐保留单文件耗时，必要时用 `coqc -time` 或等价 shell timer 辅助定位慢 tactic / 慢 theorem。
- 如果某段耗时无法精确获得，不要补猜数字；在 `timing_gaps` 或对应 notes 中写 `unknown` 及原因。最终报告必须分别说明“有精确记录的总耗时”和“无法精确统计的 gap”，不能把后者混入估算总数。
- `major_time_sinks` 应指出具体 phase、命令、witness、helper、worker 或人工活动，并说明耗时来自 proof search、编译、MCP 启动/重试、subagent 等待、人工分析、annotation 修改、proof 修改、helper cleanup、symexec、merge/migration 还是 cleanup。
- `ready_for_main_common_case_formal_lib_append` 在新合同下应记录已进入 `task_local_scratch_lib` 且可批量回填到 `common_case_formal_lib` 的 helper-suffix imports 与 helper lemmas；如果本轮没有 helper import / helper lemma，才写 `empty` 或 `n/a`。`migrated_helper_imports` 必须逐行列出脚本审计通过的 `Require Import` / `From ... Require Import` 行，不能只写未限定的 lib 引用。
- `checkpoint_reuse_summary` 在 `vc-proving` 返回时必须说明 checkpoint / packet prepass 命中数、reused witness、remaining worker goals、stale/mismatch reason。`round_checkpoint`、`partial_proof_packet`、`reuse_index` 若存在，必须指向持久 report artifact；这些字段不得作为 final-check 输入，也不得替代正式 `*_proof_manual.v` / `common_case_formal_lib`。
- `cleanup_paths` 至少覆盖 `scratch_owned_paths`；phase 结束、stale 或返工时都要按这个集合清理。
- 若当前轮次是从下游回流进入 `annotation` 或 `vc-proving`，`reentry_brief` 不得留空。
- `Final Check Checklist` 是 main-owned 工件；`final-check` phase 不生成 `Delegation Ticket`。
