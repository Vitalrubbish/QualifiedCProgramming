# Delegation 合同

本文件定义主 agent 向固定 phase subagent 下发任务时必须遵守的标准合同。

## 总规则

- 子 agent 只允许承担 3 个固定命名的 phase 角色；不在本文件中的角色一律不得创建。`annotation-checking` 不是新角色，而是 `annotation-subagent` 在 annotation phase 内调用的质量门 skill。
- 只有 `annotation`、`vc-checking`、`vc-proving` 允许分派。
- `intake`、`goal-frozen`、`final-check` 和 `done` 禁止分派。
- 进入允许分派的 phase 新轮次时，主 agent 必须先启动该 phase 绑定的 subagent，再继续本地不重叠工作。
  - 允许的不重叠工作：ticket/ledger 草稿更新、stale 标记、scratch 清理、后续命令准备。
  - 禁止的不重叠工作：在 main 线程里继续执行该 phase 已绑定给 subagent 的 domain 分析，或继续推进该 phase 的交互式 MCP 会话。
- 同一个子 agent 只服务自己绑定的 phase；phase、目标 witness 集或冻结版本变化后，必须以同名角色重新开新进程。
- stale 结果不得作为正式结论或 direct-reuse 输入复用；若只作为 proof-pattern reference，必须按 `invalidation-rules.md` 显式降级标注，并重新适配当前 VC。
- `qcp-mcp` 与 `rocq-mcp` 都按 phase owner 隔离对待；拥有本轮 scratch / worker workdir 的 subagent 是当前唯一合法 MCP 调度者。`vc-proving` 中的 proof search 默认由脚本创建的 worker-local `rocq-mcp` 会话完成；若 worker 内 `rocq-mcp` 启动或调用失败但 `coqc` 可用，则该 worker 应记录 MCP 失败并使用生成的 `coqc` 命令继续证明同一 worker-local manual；若 Codex worker 环境整体不可恢复，则可由同一 `vc-proving-subagent` 在 proving scratch / scratch-local manual 上以隔离串行 fallback 完成。
- `annotation` 与 `vc-proving` 是长时间迭代 phase；main 把轮次交给 subagent 后，应等待它以 `completed`、`blocked` 或 `stale` 返回，而不是把“还没做完”视为 main 可以接手的信号。
- `annotation-subagent` 的完整迭代必须包含 `spec-definition review/edit -> annotation-filling -> annotation-checking`。如果 checking 返回 `failed`，本轮不能返回 `completed`，必须继续在 scratch 上修正 C annotation 或 `annotation_scratch_lib` spec。
- `final-check` phase 始终由主 agent 直接执行，不生成 delegation ticket，也不创建 phase subagent。
- 对 direct proof 的算法类 case，主 agent 在下发 `annotation` ticket 时必须明确：
  - 本轮优先使用的隐藏性质
  - 不允许采用的 Rocq 算法镜像模式
  - 正例 / 反例参考
- 每份 delegation ticket 都必须要求 timing：记录本轮开始/结束时间、关键命令耗时、subagent 内部人工/脚本活动耗时、慢 witness/helper 或慢步骤，以及主要耗时原因。若某些耗时无法精确统计，应在返回报告中列为 timing gap，而不是省略。
- 每份 delegation ticket 都必须要求 `activity_ledger_required: true`，并给出 `activity_ledger_path`。subagent 必须在每段 proof-planning / proof-generation activity 前写 `START`、结束后写 `END`；vc-proving 必须按 witness/helper 拆出 proof-state reduction、空间证明生成、pure 证明生成、helper 设计/证明、proof script edit、coqc run、coqc feedback analysis。禁止只在返回报告里写“proof search 约 X 分钟”。
- 每份 delegation ticket 都必须给出持久 report 路径：`persistent_report_dir` 指向 `.agents/reports/<relative-case-dir>/<YYYY-MM-DD>/<case-name>-<YYYYMMDDTHHMMSS>/`，`round_report_dir` 指向 `<YYYYMMDDTHHMMSS>-<phase>-r<N>[-<scope>]/`，并列出 `timing_log_path` 与 expected report paths。新 report 文件名使用 snake_case。
- `vc-proving` ticket 若要复用上一轮局部成果，只能引用 `.agents/reports` 下的 `vc_proving_round_checkpoint.json` 或其 `partial_proof_packet.json`；不得引用旧 `.tmp` worker workdir 或旧 active scratch。ticket 必须写明 `checkpoint_reuse_policy` 和 direct-reuse stale 判定字段，默认策略是 `exact_or_pattern`：上下文匹配时尝试 direct reuse；上下文不匹配、helper payload 冲突或 direct candidate compile gate 失败时生成 worker proof-pattern reference。
- 主 agent 启动 subagent 后必须记录等待区间并拆开边界：`subagent-launch-requested`、`subagent-spawn-returned`、subagent 自己第一条 `subagent-start`、`subagent-finished-observed`、以及可选 close 请求/完成。最终报告要区分启动开销、subagent 自身运行时间、main 等待通知时间和关闭开销。如果等待期间主 agent 做了不重叠编排工作，应另记该活动耗时，不要把它从 wait 中扣除；最终报告可以说明二者重叠。

## 不得提前抢回 phase

- 主 agent 不得因为等待时间较长，就频繁催促 subagent 立即结束。
- 主 agent 不得因为 subagent 迭代耗时较长，就强行中断它并在 main 线程继续同一 phase 的 domain 工作。
- 当前轮次只有在以下情况发生时，才允许结束或中止：
  - subagent 显式返回 `completed`
  - subagent 显式返回 `blocked`
  - 当前输入已 `stale`
  - 用户明确取消或改向
  - 当前工具/会话已不可恢复
- 如果是工具/会话不可恢复，优先处理方式是：总结问题、生成新的 ticket、重开同名 subagent，而不是 main 线程接管。

## 永远不能分派的工作

- symexec
- 正式主状态文件上的 coqc / final-check 编译
- `Admitted` / 额外 `Axiom` review
- `final-check` 的正式执行
- phase 切换
- `Case Brief` / `Witness Ledger` / `Phase Status` 的最终写入
- 当前 case 主状态集的任何修改

## 有条件允许分派或调用的工具 / skill

- `qcp-mcp`
  - 只允许分派给 `annotation-subagent`
  - 只允许作用在 annotation C scratch `.c` 副本上
- `annotation-checking`
  - 只允许由当前 annotation 轮次的 `annotation-subagent` 调用
  - 不创建额外 subagent
  - 只检查本轮 annotation C scratch、`annotation_scratch_lib` 与 filling report；检查通过前，main 不得正式回填 `.c` / `common_case_formal_lib` 或运行 symexec
- `rocq-mcp`
  - 只允许分派给 `vc-proving-subagent`
  - 默认只允许作用在 `vc-proving` 脚本创建的 worker-local manual 上；若本轮已记录并发 worker 环境不可恢复，则允许作用在 proving scratch 或 scratch-local manual 上
- worker-local / scratch-local `coqc`
  - 只允许用于 `vc-proving` 的 worker-local manual、proving scratch manual、`task_local_scratch_lib` 和 merge/verify gate
  - 若 `rocq-mcp` 启动或调用失败，worker / `vc-proving-subagent` 必须记录失败证据并改用生成的 `coqc` 命令继续证明；不能仅因 MCP 不可用返回 proof blocker
- 主 agent 若需要复核，必须等待当前 subagent 关闭本轮会话后再串行执行；不能共享同一交互式会话，也不能用复核替代本轮 vc-proving proof search

## 主 agent 独占写集合

### 手工修改集合

- 目标 `.c`
- `*_proof_manual.v`
- `common_case_formal_lib`

### 工具刷新集合

- `*_goal.v`
- `*_proof_auto.v`
- `*_goal_check.v`

这些生成文件只允许主 agent 通过 symexec 刷新，不能手工编辑。

## Formal 文件结构合同

- 正式文件与 proving scratch 都必须遵守同一套结构边界。
- `*_proof_manual.v` 最终只允许包含当前 case 的 manual witness theorem 证明；worker-local / merged scratch manual 可暂存 proved helper lemmas。
- reusable helper lemmas 由 `vc-proving` worker 在本组 `worker_helper_scratch_lib` 中证明，经 merge gate 收集并合入 merged scratch manual 后，必须由 `migrate_helpers_to_lib.py` 连同必要且审计通过的 helper-suffix `Require Import` 行迁移到 `task_local_scratch_lib` 冻结前缀之后。worker manual 只放 witness proof，不放 helper lemma。
- 主 agent 在 `intake` 时必须冻结 `common_case_formal_lib` 的 user-owned 前缀，并把行号与快照写入 `Case Brief`。
- main 与 subagent 都不得改写冻结前缀。
- annotation phase 可通过 `annotation_scratch_lib` 提出 spec 定义新增 / 修正；只有通过 `annotation-checking` 后，主 agent 才能回填 `common_case_formal_lib`，并重新冻结 `Case Brief` 中的 lib prefix。
- `common_case_formal_lib` 在 worker proving 阶段只读；merged manual 完成后，只能通过 `task_local_scratch_lib` 后缀追加 audited helper-suffix imports 与 migrated helper lemmas，再由主 agent 批量集成。proving 阶段禁止新增顶层 `Definition` / `Fixpoint` / `Inductive` / `Notation` / `Axiom`；annotation-approved 的 spec 定义必须是严格数学性质，不得是 C 算法镜像。
- 如果当前证明确实依赖修改冻结前缀，或依赖新增上述顶层定义，则 `vc-proving-subagent` 必须返回 `blocked`。

## Phase-owned scratch 写集合

- annotation 轮次：
  - `.tmp/<relative-case-dir>/<stem>__annotation_subagent_tmp.c`
  - `.tmp/<relative-output-dir>/<stem>__annotation_subagent_tmp_lib.v`
- proving 轮次：
  - `.tmp/<relative-case-dir>/<stem>__vc_proving_subagent_tmp_proof_manual.v`
  - `.tmp/<relative-case-dir>/<stem>__vc_proving_subagent_tmp_lib.v`

规则：

- scratch 放在 `.tmp` 子目录下，并尽量保持与正式文件相同的相对目录结构。
- scratch 必须从最新正式快照重新创建。
- 若检测到上轮遗留 scratch，必须先删除，再开始本轮工作。
- 若当前 case 没有 `common_case_formal_lib`，`annotation-subagent` 应创建空 / 最小 `annotation_scratch_lib`；`vc-proving-subagent` 仍应创建最小 `task_local_scratch_lib` 作为本轮 scratch pair。

## Allowed Read Set

子 agent 可以读取：

- 当前 case 的只读上下文
- 当前 case 的最新正式快照
- 已生成的文档与教程
- 参考案例
- 主 agent 显式提供的目标 witness、目标文件片段或冻结版本信息

## Allowed Write Set

子 agent 只允许写：

- 主 agent 显式分配的 phase-owned scratch
- 与该 scratch 配套的、仅服务本轮的临时辅助文件
- 且这些文件都不属于当前 case 主状态集
- `annotation-subagent` 只能写 annotation C scratch
- `annotation-subagent` 还能写本轮 `annotation_scratch_lib`，用于新增 / 修正 spec 定义
- `annotation-checking` 不扩大 `annotation-subagent` 的写集合；checking 失败后的修正仍只能写本轮 annotation C scratch 或 `annotation_scratch_lib`
- `vc-proving-subagent` 只能写 proving scratch pair 及其 `.tmp` worker-local manuals、组内 `worker_helper_scratch_lib` / reports；helper-migration 步骤可以写 `task_local_scratch_lib` 后缀
- `vc-checking-subagent` 默认保持只读

## Forbidden Write Set

子 agent 不允许写：

- 目标 `.c`
- `*_goal.v`
- `*_proof_auto.v`
- `*_proof_manual.v`
- `*_goal_check.v`
- `common_case_formal_lib`
- 当前 case 落盘后的 `Case Brief`
- 当前 case 落盘后的 `Witness Ledger`
- 当前 case 落盘后的 `Phase Status`
- 不属于自己本轮的 scratch
- 已经 stale 的 scratch

## 固定 Phase Subagent

### 1. `annotation-subagent`

- bound_skill: `annotation-filling`
- post_filling_quality_gate: `annotation-checking`
- phase:
  - `annotation`
- goal: 在当前 annotation C scratch / `annotation_scratch_lib` 上迭代运行 `qcp-mcp` 和 spec 检查，产出已经过交互检查且通过 `annotation-checking` 质量门的 C annotation patch / `annotation_scratch_lib` spec patch
- must_spawn_if:
  - 每次进入 `annotation`
  - 从任意下游 phase 返工回到 `annotation`
  - 当前 annotation 轮次的输入版本发生变化，需要重新创建 scratch 并重新分析
- expected_output:
  - `Subagent Return Report`
  - 已在 scratch 上验证过的 annotation patch
  - 已在 `annotation_scratch_lib` 上形成的 spec definition patch；如果为空必须写 `empty`
  - `qcp-mcp` 交互结论摘要
  - `Annotation Checking Report`，且 `status` 必须为 `passed`、`qcp_mcp_requirement_satisfied: yes`、`annotation_scratch_lib_coqc_status: passed` 才能标记 `ready_for_main_symexec`
  - annotation 轮次总耗时、主要 `qcp-mcp` 检查/迭代耗时和最慢 annotation 点
  - spec definition 设计 / 修改耗时、annotation-checking 耗时、检查结论和失败后是否发生过 filling 返工
  - annotation 分析、scratch 编辑、QCP 失败归因、最终 patch 整理等 activity 耗时；无法精确拆分时必须写 timing gap
  - 参考案例与可复用模式
  - 本轮最终采用的隐藏性质 / 直观谓词列表
  - 哪些点可能影响后续 symexec / witness 结构
  - cleanup 确认
- main 在正式回填 / symexec 前必须运行 `scripts/validate_annotation_gate.py`；若脚本失败，本轮 annotation 结果不得进入 `goal-frozen`
- stale_if:
  - `Case Brief` 关键字段变化
  - 正式 annotation 已被主 agent 修改
  - 新一轮 `goal` 已刷新
  - 当前轮次的 scratch seed 或 scratch path 发生变化
  - 当前轮次的 `annotation_scratch_lib` seed 或 `annotation_scratch_lib` path 发生变化

### 2. `vc-checking-subagent`

- bound_skill: `vc-checking`
- phase:
  - `vc-checking`
- goal: 对当前冻结版本的 witness 集做可证性分诊
- must_spawn_if:
  - 每次进入基于最新冻结 `goal` 的 `vc-checking`
  - witness 集、`source_goal_version` 或 vc-checking 范围变化
- expected_output:
  - witness 级结论
  - `vc_checking_informal_proof_report.md`，其中每个 `proofable` / `needs-lemma` witness 都有 informal proof、used lemmas、lemma sources 和 premise discharge
  - 关键失败信号
  - vc-checking 轮次总耗时、单个 witness / witness cluster 的分析耗时和最慢分诊点
  - `witness_group_plan`：基于自然语言证明思路的 proof group 划分，每组包含 `proof_group_id`、`members`、`representative_witness`、`natural_language_proof_pattern`、`shared_helper_candidates`、`proving_hints` 和 `grouping_confidence`
  - 若结论是 `needs-lemma`，必须明确该 helper lemma 先由对应 group worker 在 `worker_helper_scratch_lib` 中证明，再在 merge 后迁移到 `task_local_scratch_lib` 后缀
  - 是否建议回退 `annotation`
- stale_if:
  - `goal` 已刷新
  - witness 不再来自最新冻结版本
  - `Case Brief` 关键字段变化

### 3. `vc-proving-subagent`

- bound_skill: `vc-proving`
- phase:
  - `vc-proving`
- goal: 从当前 proving scratch 出发，默认使用 `vc-proving` 脚本启动隔离 Codex worker 并发证明，先在 merged manual 中收束 helper imports / helper lemmas，再迁移到 `task_local_scratch_lib` 后缀并整理可回填结果；若本轮已记录 Codex worker 环境不可恢复，则允许在同一 proving scratch 上执行串行 fallback，并维持相同的 formal 边界与回填合同
- must_spawn_if:
  - 每次进入 `vc-proving`
  - 当前 proving 轮次的 witness 集、`source_goal_version` 或正式 proof 集成快照发生变化
  - symexec 生成了新的正式 `*_proof_manual.v`
  - `common_case_formal_lib` 在 proving 中被主 agent 改动
  - `Case Brief` 中冻结的 `common_case_formal_lib` 前缀定义已变化
- expected_output:
  - `Subagent Return Report`
  - 已在 scratch `*_proof_manual.v` 上验证过、可回填到正式 manual 的 witness proofs，以及已在 `task_local_scratch_lib` 上验证过、可回填到 `common_case_formal_lib` 的 helper-suffix imports / helper lemmas
  - worker `proof_report.json` / `proof_strategy_report.json`、merged scratch manual 路径、migrated scratch manual 路径、`task_local_scratch_lib` 路径
  - checkpoint reuse summary：`previous_vc_proving_checkpoint` 是否命中、packet applied count、reused witness、remaining worker goals、拒绝复用时的 stale / mismatch reason
  - 本轮若已产生 compile-gated 局部成果，则给出 `reuse_checkpoints/<round-id>/vc_proving_round_checkpoint.json`、`partial_proof_packet.json`、`reuse_index.json` 持久路径；若本轮是 annotation-bug / stale 或没有可复用成果，则说明未生成 checkpoint 的原因
  - split / prepare / run / validate / migrate / verify 的命令耗时、worker 耗时、最慢 witness/helper，以及主要 proof bottleneck
  - activity ledger：每个 witness/helper 的 proof-state reduction、空间证明生成、pure 证明生成、helper 设计/证明、proof script edit、coqc run、coqc feedback analysis 的 start/end/elapsed/status；无法精确拆分时必须写 open/incomplete event 或 timing gap，不能只写 proof search 总时长
  - proof search 分析、manual proof 编辑、helper lemma 设计/迁移、冗余 lemma 清理、worker 等待或 fallback 切换等 activity 耗时；无法精确拆分时必须写 timing gap
  - `protected_prefix_respected`
  - 参考案例映射
  - 集成时需要注意的依赖顺序
  - cleanup 确认
- stale_if:
  - annotation 改动
  - `goal` 刷新
  - witness 被标记为 `stale`
  - `*_proof_manual.v` 或 `common_case_formal_lib` 已出现新的正式集成
  - 新的正式 `*_proof_manual.v` 已由 symexec 刷新
  - `Case Brief` 中冻结的 `common_case_formal_lib` 前缀定义已变化

附加规则：

- 只要出现新的正式 `*_proof_manual.v`，旧 proving scratch 必须先删除，再从最新正式 `*_proof_manual.v` / `common_case_formal_lib` 重建。
- proving scratch `*_proof_manual.v` 应继续依赖最新正式 `*_goal.v` / `*_proof_auto.v`，但其 lib 依赖必须切换到本轮 `task_local_scratch_lib`。
- `vc-proving-subagent` 默认在 proving scratch manual 上运行 split / checkpoint/packet reuse prepass / prepare concurrent / run concurrent / validate / migrate helpers to lib / verify / checkpoint_round 流水线；优先消费 `vc-checking` 的 `witness_group_plan`，每个 proof group 产生一个 worker-local manual、一个组内 `worker_helper_scratch_lib` 和 worker report；没有 group plan 时才使用排序分块 fallback。若 worker 内 `rocq-mcp` 启动或调用失败但 worker-local `coqc` 可用，继续在 worker-local manual / `worker_helper_scratch_lib` 上用 `coqc` 证明并保留失败证据；若本轮已记录 Codex worker 环境整体不可恢复，则允许切换到串行 fallback，并改为在 proving scratch 上直接完成 proof / helper migration / verify，同时保留 `.tmp` 下可审计的串行报告。
- 在 proving scratch / worker manual 中写入的 helper lemma 必须是 proved lemma，且通过 merge gate 检查无 `Admitted`、无额外 `Axiom`、无 forbidden top-level definition；随后必须迁移到 `task_local_scratch_lib`。若 helper lemma 需要额外库，worker 只能在 `worker_helper_scratch_lib` 中加入最小 `Require Import` / `From ... Require Import` 行，且不能导入 `SimpleC.EE.*` 生成 case artifact。
- `task_local_scratch_lib` 的冻结前缀必须与 `common_case_formal_lib` 快照逐字一致；只有 helper-migration 步骤可以在后缀追加 audited helper-suffix imports 与 proved helper lemmas。
- checkpoint prepass 有两个合法结果：上下文匹配时，把 JSON packet 还原到 fresh proving scratch，用 packet helper payload 初始化本轮 `task_local_scratch_lib`，用当前 manual statement 加 packet proof script 重建 candidate witness proof，随后强制走 compile / merge / migration / verify gate；上下文不匹配、helper payload 冲突或 direct candidate compile gate 失败时，生成 `proof_reuse_pattern_references.json` 放入相关 worker workdir，让 worker 阅读 per-goal candidates、完整 proof reference pool、旧 informal proof / helper reference 并手动适配当前 VC。pattern reference 不能自动标记 solved，也不能替代 formal `.v` 交付物；direct candidate 失败时必须恢复 prepass 写入的 helper scratch。
- 若 proving 过程中发现必须修改冻结前缀，必须引入新的顶层 `Definition` / `Fixpoint` / `Inductive` / `Notation` / `Axiom`，或必须迁入不在 helper import allowlist 内的依赖，应立刻以 `blocked` 返回。

## 强制启动的执行时点

- 命中 delegated phase 的进入条件后，主 agent 必须先构造 `Delegation Ticket`，再启动绑定的 subagent。
- 在该 subagent 已启动之前，主 agent 不得把该 phase 的 domain 分析直接视为“已由 main 覆盖”并跳过 delegation。
- 主 agent 可以继续做不重叠的本地工作，但不能用 main 去替代已经绑定给 phase subagent 的分析职责。
- “不重叠”只指编排类动作，不包含该 phase 的 domain 分析或交互式 MCP 推进。
- main 不得用自己的人工 review 替代 `annotation-checking`，也不得在 checking 未通过时提前 symexec。
- 若输入已 stale，必须以同名角色重开新子 agent；不能继续复用旧进程或旧结论。
- 对 `annotation` / `vc-proving`，不能因为主 agent 等待一段时间后仍未收到结果，就自行接管该 phase。
- 进入 `final-check` 时不构造 `Delegation Ticket`；主 agent 直接建立或更新 `Final Check Checklist`。

## 主 agent 在下发任务时必须明确给出的信息

- subagent name
- bound skill
- 当前 case 名与 phase
- phase input version
- task goal
- 允许读取的范围
- 允许写入的文件
- 禁止触碰的主状态文件
- 期望输出格式
- 允许使用的 MCP 工具
- scratch seed 文件
- scratch 拥有路径
- `annotation_scratch_lib` seed 文件
- `annotation_scratch_lib` 拥有路径
- `proof_manual_write_contract`
- `lib_write_contract`
- `protected_lib_prefix_end_line`
- cleanup 路径
- 当前轮次是否为回流轮次，以及对应的 `Re-entry Brief`
- 当前轮次的 annotation 风格约束（例如 `predicate-first`）
- `annotation_checking_required: true`
- `spec_definition_review_required: true`
- `persistent_report_dir`、`round_report_dir`、`timing_log_path` 和 expected report paths
- 正例 / 反例参考
- 推荐隐藏性质，以及明确禁止的 annotation anti-pattern
- 何种变化会让该任务结果失效
