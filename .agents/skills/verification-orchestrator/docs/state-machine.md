# Phase 状态机

## 唯一合法 phase

- `intake`
- `annotation`
- `goal-frozen`
- `vc-checking`
- `vc-proving`
- `final-check`
- `done`

## 唯一合法转移

- `intake -> annotation`
- `annotation -> annotation`
- `annotation -> goal-frozen`
- `goal-frozen -> vc-checking`
- `vc-checking -> annotation`
- `vc-checking -> vc-proving`
- `vc-proving -> vc-proving`
- `vc-proving -> annotation`
- `vc-proving -> final-check`
- `final-check -> annotation`
- `final-check -> vc-proving`
- `final-check -> done`

## 明确禁止的转移

- `intake -> vc-checking`
- `intake -> vc-proving`
- `intake -> final-check`
- `annotation -> vc-proving`
- `annotation -> final-check`
- `goal-frozen -> final-check`
- `goal-frozen -> done`
- `done -> *`

## 固定 Phase Subagent 矩阵

- `intake`
  - 不开启 subagent。
  - 当前 phase 只由主 agent 锁定 `Case Brief` 和后续 phase 入口。
- `annotation`
  - 固定绑定 `annotation-subagent`。
  - 该 subagent 固定使用 `annotation-filling`，先在 `annotation_scratch_lib` 中确认 / 修正数学 spec，再填写 C annotation，并在每轮 filling 形成候选后调用 `annotation-checking`。
  - 每次进入 `annotation` 的新轮次，都必须先启动它，再继续本 phase。
  - 该 phase 由 `annotation-subagent` 在 annotation C scratch 上独占使用 `qcp-mcp`，并允许其写本轮 `annotation_scratch_lib`。
  - `annotation-checking` 是本 phase 内的 annotation / spec 质量门，不创建新的 phase subagent；checking 通过前不得回填正式 `.c` / `common_case_formal_lib` 或进入正式 symexec。
  - 该 phase 是长时间迭代 phase；main 线程必须等待 subagent 的显式返回，不能因等待较久而抢回。
- `goal-frozen`
  - 不开启 subagent。
  - 当前 phase 只由主 agent 冻结输入和确认生成文件版本。
- `vc-checking`
  - 固定绑定 `vc-checking-subagent`。
  - 该 subagent 固定使用 `vc-checking`。
  - 每次进入基于最新冻结 `goal` 的 `vc-checking`，都必须先启动它，再继续本 phase。
- `vc-proving`
  - 固定绑定 `vc-proving-subagent`。
  - 该 subagent 固定使用 `vc-proving`。
  - 每次进入 `vc-proving` 的新轮次，都必须先启动它，再继续本 phase。
  - 该 phase 默认由 `vc-proving-subagent` 运行脚本化并发 worker pipeline；若本轮已记录 Codex worker 环境不可恢复，则允许由同一 `vc-proving-subagent` 切换到 proving scratch 上的串行 fallback。`rocq-mcp` 只允许在当前 owner 的隔离 proving 载体上使用；如果 `rocq-mcp` 在 worker 内启动或调用失败但 worker-local `coqc` 可用，当前 worker / subagent 必须记录失败证据并改用生成的 `coqc` 命令继续证明。
  - 若存在上一轮 `vc_proving_round_checkpoint.json`，只能由本轮 `vc-proving-subagent` 在 fresh proving scratch 上执行 checkpoint/packet proof-reuse prepass；上下文匹配且 candidate 编译通过时可构造 direct reuse candidate，上下文不匹配、helper payload 冲突或 candidate 编译失败时只能生成 proof-pattern reference；不得继续使用上一轮 `.tmp` scratch 或 worker workdir。
  - 该 phase 是长时间迭代 phase；main 线程必须等待 subagent 的显式返回，不能因等待较久而抢回。
- `final-check`
  - 不开启 subagent。
  - 当前 phase 由主 agent 直接使用 `final-check` skill。
  - symexec、coqc、`Admitted` / 额外 `Axiom` review 和 formal 文件结构审计都在 main 线程完成。
- `done`
  - 不开启 subagent。
  - 当前 phase 只允许主 agent 记录最终完成状态。

## Entry / Exit Gate

### `intake`

进入条件：

- 当前 case 刚被识别，或 case 基本信息尚未结构化。

退出条件：

- `Case Brief` 已能唯一确定：
  - 目标 C 文件
  - 目标函数
  - proof 类型
  - 输出目录
  - annotation 风格（默认 `predicate-first`）
  - 风格正例 / 反例参考
  - 当前 case 需要避免的 annotation anti-pattern
  - 当前 `common_case_formal_lib` 的 frozen prefix（若不存在则记录为空）
  - `proof_manual_scope: witness-proofs-after-lib-migration`

分派规则：

- 禁止分派任何子任务。
- 该 phase 只允许主 agent 识别 case 身份、锁定参考范围并决定是否进入 `annotation`。

### `annotation`

进入条件：

- case 已完成 intake。
- 或上游判断存在 `annotation-bug`。

退出条件：

- `annotation-subagent` 已在 annotation C scratch 上把 `qcp-mcp` 稳定跑到文件尾；若无法继续，则只能以 `blocked` / `stale` 返回。
- `annotation-subagent` 已对候选 annotation / spec 定义调用 `annotation-checking`，且检查结果为 `passed`；如果结果为 `failed`，必须留在本 phase 回到 `annotation-filling` 修正 C scratch 或 `annotation_scratch_lib`，不能退出到 symexec。
- `Annotation Checking Report` 已明确给出 `qcp_mcp_requirement_satisfied: yes` 与 `annotation_scratch_lib_coqc_status: passed`。
- 主 agent 在正式回填或 symexec 前，已运行 `.agents/skills/verification-orchestrator/scripts/validate_annotation_gate.py`，且校验成功。
- 主 agent 已把被接受的 annotation 回填到正式 `.c`；若本轮修改了 `annotation_scratch_lib`，主 agent 已把 checked spec 定义回填到 `common_case_formal_lib`。
- 主 agent 已在 `common_case_formal_lib` 回填后刷新 `Case Brief` 中的 `lib_frozen_prefix_end_line` / `lib_frozen_prefix_snapshot`。
- symexec 已刷新当前 case 的正式生成文件。
- 当前 annotation C scratch 和 `annotation_scratch_lib` 已删除。

分派规则：

- 固定 subagent：`annotation-subagent`
- 绑定 skill：`annotation-filling` + post-filling `annotation-checking`
- 必须新开子 agent：
  - 每次进入 `annotation` phase 时
  - 从 `vc-checking`、`vc-proving` 或 `final-check` 返工回到 `annotation` 时
  - `annotation -> annotation` 自循环代表开始一轮新的 annotation 轮次时
- 若本轮是从下游 phase 回流进入：
  - 主 agent 必须先提供 `Re-entry Brief`
- 若当前 case 属于算法类 direct proof，进入本 phase 前还必须在 ticket 中写清：
  - 本轮要抓的隐藏性质
  - 不允许出现的 Rocq 算法镜像
  - 参考正例 / 反例
- 必须新建 scratch：
  - 从最新正式 `.c` 复制出 fresh annotation C scratch
  - 从最新 `common_case_formal_lib` 复制出 fresh `annotation_scratch_lib`；若 `common_case_formal_lib` 不存在，创建空 / 最小 `annotation_scratch_lib`
  - 若旧 scratch 仍存在，先删除再创建
- 允许分派：
  - annotation C scratch 上的 `qcp-mcp`
  - `annotation_scratch_lib` 上的 spec 定义新增 / 修正
  - 同一 `annotation-subagent` 对本轮候选 annotation 调用 `annotation-checking`
- 禁止分派：
  - symexec
  - 对目标 `.c` / `common_case_formal_lib` 的正式修改
  - 因等待过久而中断 subagent 并改由 main 接管本轮 annotation
  - 在 `annotation-checking` 未通过时进入正式 symexec

### `goal-frozen`

进入条件：

- 最新 annotation 已在 scratch 上通过 `qcp-mcp`。
- 最新 annotation / spec 定义已通过 `annotation-checking`。
- annotation gate script 已通过，确认 `qcp_mcp_requirement_satisfied: yes` 且 `annotation_scratch_lib` compile gate 通过。
- 若 annotation phase 修改过 `annotation_scratch_lib`，`common_case_formal_lib` 已由 main 集成并重新冻结。
- 最新 `goal` / witness 集合已生成。
- annotation C scratch 和 `annotation_scratch_lib` 已清理。

退出条件：

- 当前冻结版本的 witness 已准备好进入 vc-checking。

分派规则：

- 禁止分派任何子任务。
- 本 phase 只允许主 agent 冻结输入、确认生成文件版本并准备 `Witness Ledger`。

### `vc-checking`

进入条件：

- 当前 `goal` / witness 集合是最新冻结版本。

退出条件：

- 所有待处理 witness 都已获得分诊结论：
  - `proofable`
  - `needs-lemma`
  - `annotation-bug`
  - 其中 `needs-lemma` 明确表示“对应 proof group 的 `worker_helper_scratch_lib` 中需要 proved helper lemma，并在 vc-proving merge 后迁移到 `task_local_scratch_lib` 后缀”，不是修改 `common_case_formal_lib` 冻结前缀
  - `vc-checking-subagent` 已基于自然语言证明思路产出 `witness_group_plan`，用于后续 grouped parallel proving；每组包含成员、代表 witness、proof pattern、共享 helper 候选和 proving hints

分派规则：

- 固定 subagent：`vc-checking-subagent`
- 绑定 skill：`vc-checking`
- 必须新开子 agent：
  - 每次进入基于某个最新冻结 `goal` 版本的 `vc-checking` 时
  - `goal-frozen -> vc-checking` 之后开始新的 vc-checking 轮次时
  - `goal` 或 witness 集合刷新，导致旧 vc-checking 输入失效后重新进入本 phase 时
- 禁止分派：
  - 任何 witness 的最终 ledger 写入
  - phase 切换

### `vc-proving`

进入条件：

- 当前轮次需要正式进入证明的 witness 已明确。
- 这些 witness 不处于 stale 状态。
- 已从最新正式 `*_proof_manual.v` / `common_case_formal_lib` 快照创建 fresh proving scratch pair。
- `Case Brief` 已给出 `lib_frozen_prefix_end_line` / `lib_frozen_prefix_snapshot`。

退出条件：

  - 当前轮次需要处理的 witness 都已在 scratch 上证明完成，helper-suffix imports / helper lemmas 已从 merged manual 迁移到 `task_local_scratch_lib`，并可由主 agent 正式集成到 `common_case_formal_lib`，或已经把 compile-gated 局部成果固化为可审计 checkpoint 后暴露出必须返工 annotation / 必须阻塞等待用户定义调整的问题。
- 不再需要的 proving scratch 已删除。

分派规则：

- 固定 subagent：`vc-proving-subagent`
- 绑定 skill：`vc-proving`
- 必须新开子 agent：
  - 每次进入 `vc-proving` phase 时
  - `vc-proving -> vc-proving` 自循环代表新的 proving 轮次时
  - 当前 proving 的 witness 集、`source_goal_version` 或 proof 集成快照变化后重新进入本 phase 时
  - symexec 刷新出新的正式 `*_proof_manual.v` 时
  - `common_case_formal_lib` 被主 agent 改动时
  - `Case Brief` 中冻结的 `common_case_formal_lib` 前缀定义已刷新时
- 若本轮是从下游失败或上游刷新后重新进入：
  - 主 agent 必须先提供 `Re-entry Brief`
- 必须新建 scratch：
  - 从最新正式 `*_proof_manual.v` / `common_case_formal_lib` 复制出 fresh proving scratch pair
  - 若旧 proving scratch 仍存在，先删除再创建
- 允许分派：
  - Windows 下默认是 `vc-proving` 脚本创建的 worker-local manual 上的 `coqc.exe` / `coqtop.exe` 编译循环；进入串行 fallback 时，改为 proving scratch 或 scratch-local manual 上的隔离编译循环。不得调用 `rocq-mcp`。
- 禁止分派：
  - 对 `*_proof_manual.v` / `common_case_formal_lib` 的正式集成
  - witness 的 `proved` 最终确认
  - 因等待过久而中断 subagent 并改由 main 接管本轮 proving
- 附加规则：
  - 每次 symexec 刷新出新的正式 `*_proof_manual.v` 后，旧 proving scratch 必须作废并删除，再开始新的 proving 轮次
  - 本轮默认运行 split / prepare concurrent / run concurrent / validate / migrate helpers to lib / verify 流水线；优先使用 `vc-checking` 的 `witness_group_plan` 启动 grouped worker，若缺失才使用排序分块 fallback；若已记录 Codex worker 环境不可恢复，则允许改为 proving scratch 上的串行 fallback，但仍必须完成 helper migration、结构审计与 verify
  - 如果 ticket 提供上一轮 checkpoint，本轮 split 之后、prepare 之前运行 checkpoint/packet reuse prepass：若 direct-reuse 条件满足，把 helper payload 应用到 fresh `task_local_scratch_lib`，用当前 witness statement 和 packet proof script 重建 candidate manual，通过编译后才从 worker scope 移除已复用 witness；若条件不满足、helper payload 冲突或 candidate 编译失败，恢复失败写入的 helper scratch 并生成 worker proof-pattern reference，worker 可阅读 per-goal candidates、完整 proof reference pool、旧 informal proof / helper reference 并适配当前 VC，但不得自动标记 solved
  - 本轮结束时若不是 annotation-bug / stale，且存在 solved witness 或 migrated helper payload，应在持久 report 目录生成 round checkpoint；checkpoint 是下一轮 fresh scratch 的输入，不是 active scratch
  - merged proving scratch `*_proof_manual.v` 可暂存 witness theorem 证明和 proved helper lemmas；migrated handoff manual 必须只保留 witness proofs
  - `task_local_scratch_lib` 的冻结前缀不可改写；`migrate_helpers_to_lib.py` 只能在冻结前缀之后追加 audited helper-suffix imports 与 proved helper lemmas
  - 如果证明需要改写冻结前缀，需要新增顶层 `Definition` / `Fixpoint` / `Inductive` / `Notation` / `Axiom`，或需要迁入不在 helper import allowlist 内的依赖，本轮应以 `blocked` 返回

### `final-check`

进入条件：

- 当前轮 proving 已收束。
- 没有仍在处理中的有效 witness。
- annotation / proving scratch 已清理，或当前只剩待清理的过期残留等待审计。
- `Case Brief` 已记录 frozen `common_case_formal_lib` 前缀与 `proof_manual_scope`。

退出条件：

- `common_case_formal_lib` 的冻结前缀与 `Case Brief` 一致。
- `*_proof_manual.v` 只包含 manual witness theorem 证明，不含 helper lemmas、helper definitions、`Admitted` 或额外 `Axiom`。
- `common_case_formal_lib` 冻结前缀之后的 migrated helper-suffix imports 均为审计通过的 `Require Import` 行，migrated helper lemmas 均已证明，且没有新增 forbidden top-level declaration。
- 编译与 `Admitted` / 额外 `Axiom` review 全部通过，或明确定位到上游失败阶段。
- 不再残留任何 annotation / proving scratch、`.tmp` worker workdir、`.aux` 文件或本轮测试 / Python 缓存。

分派规则：

- 不开启 subagent。
- 当前 phase 由主 agent 直接使用 `final-check` skill，并维护 `Final Check Checklist`。
- 每次进入 `final-check` phase 时，主 agent 都必须先更新 checklist，再执行结构审计、symexec、coqc 和 `Admitted` / 额外 `Axiom` review。
- 禁止分派任何子任务。

### `done`

进入条件：

- 最新生成文件与当前 C 文件一致。
- 所有需要的 manual VC 已完成。
- 最终检查通过。
- `common_case_formal_lib` 的冻结前缀未被改写。
- `*_proof_manual.v` 只含 witness proofs；`common_case_formal_lib` 冻结前缀之后的 migrated helper-suffix imports 均为审计通过的 `Require Import` 行，migrated helper lemmas 均已证明，且没有混入 helper definitions、`Admitted` 或额外 `Axiom`。
- 不残留任何 phase scratch、`.tmp` worker workdir、`.aux` 文件或本轮测试 / Python 缓存。

分派规则：

- 禁止分派任何子任务。
