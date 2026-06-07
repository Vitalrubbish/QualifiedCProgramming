# 使用注意

这个文件定义编排层的总规则；其它 skill 不应重复定义这些规则。

- 单点编排：当前 case 只有一个主 agent 负责 phase 推进与最终提交。
- 单点写入：当前 case 的主状态集只能由主 agent 修改。
- `qcp-mcp` 采用 phase 独占：
  - 只允许 `annotation-subagent` 在 annotation C scratch 上使用。
- `annotation-subagent` 在 annotation phase 中同时拥有 C scratch 和 `annotation_scratch_lib`；可以在 `annotation_scratch_lib` 中补充或修正数学 spec 定义，但不得直接修改 `common_case_formal_lib`。
- `annotation-checking` 是 `annotation-subagent` 在 `annotation-filling` 之后执行的质量门；检查通过前，主 agent 不得回填正式 `.c` / `common_case_formal_lib`，也不得运行正式 symexec。
- `rocq-mcp` 采用 phase 独占：
  - 只允许 `vc-proving-subagent` 通过 `vc-proving` 脚本创建 worker-local manual / `worker_helper_scratch_lib` 后使用。
  - `vc-proving` 默认走脚本化并发 worker pipeline；若已记录 Codex CLI / transport / backend / worker 会话不可恢复，则允许保持 `vc-proving-subagent` 为 owner，回退到 proving scratch 上的串行 fallback。
- symexec、正式文件的 coqc、`Admitted` / 额外 `Axiom` review 仍由主 agent 独占。`vc-proving` worker / subagent 可以在自己的 worker-local manual、组内 `worker_helper_scratch_lib`、proving scratch 和 `task_local_scratch_lib` 上运行生成的 `coqc` 命令作为证明反馈与验证 gate；如果 `rocq-mcp` 启动或调用失败但 `coqc` 可用，应记录 MCP 失败并继续用 `coqc` 推进证明，而不是把它当作 proof blocker。
- `QCP_examples/LLM_bench` case 若复用 `QCP_demos_LLM` 公共头文件，源码统一写裸 include（例如 `#include "verification_stdlib.h"` / `#include "verification_list.h"` / `#include "int_array_def.h"`）。正式 symexec 和 annotation scratch 上的 `qcp-mcp` 都必须在 C include search path 中加入 `QCP_examples/QCP_demos_LLM/`；symexec 命令还必须同时保留 `-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM`，因为 `-I` 只负责 C 头文件查找，`-slp` 负责 strategy / generated Coq logical path。
- `final-check` phase 也由主 agent 直接执行，不再创建 subagent。
- 当前仓库只承认 3 个固定命名的 phase subagent：
  - `annotation-subagent`
  - `vc-checking-subagent`
  - `vc-proving-subagent`
- 子 agent 默认只读；只有主 agent 显式分配、且文件不属于当前 case 主状态集时，子 agent 才允许写入。
- `annotation-subagent` 只允许写本轮 annotation C scratch 和 `annotation_scratch_lib`。
- `annotation-checking` 阶段不新增正式写权限；检查失败时仍由同一 `annotation-subagent` 回到 `annotation-filling` 修正本轮 C scratch 或 `annotation_scratch_lib`。
- `vc-proving-subagent` 只允许写本轮 proving scratch 及 `.tmp` worker-local manuals、组内 `worker_helper_scratch_lib` / reports；helper-migration 步骤可写 `task_local_scratch_lib` 后缀中的 audited helper-suffix imports 与 proved helper lemmas。
- 主 agent 在 `intake` 时必须记录当前 `common_case_formal_lib` 的 user-owned 前缀，并把 `proof_manual_scope` 锁定为 `witness-proofs-after-lib-migration`；若 annotation phase 集成了 checked spec 定义变更，必须在进入 `goal-frozen` 前重新冻结 lib 前缀。
- 主 agent 在 `intake` 时还必须确定本 case 的 annotation 风格约束：
  - direct proof 默认采用 `predicate-first annotation`
  - refinement proof 若必须依赖 `safeExec` / monad 规格，也仍要优先把循环与局部状态写成隐藏性质，而不是再额外在 Rocq 中镜像一份算法实现
- `*_proof_manual.v` 最终只允许包含 manual witness theorem 证明；proved helper lemmas 必须连同必要的 audited helper-suffix imports 从 merged manual 迁移到 `task_local_scratch_lib`，再由主 agent 批量集成到 `common_case_formal_lib`。
- `common_case_formal_lib` 的冻结前缀不可修改；merged manual 完成后只允许通过 `task_local_scratch_lib` 后缀追加 audited helper-suffix `Require Import` 行与已证明 helper lemmas。
- 对 direct proof，`annotation` 轮次默认禁止“先在 Rocq 中定义算法递归 / 状态机，再让 C annotation 去追随该定义”的做法；这类模式应在 `Case Brief` / `Delegation Ticket` 中显式记为 `anti_patterns`。
- 对算法类 case，`Case Brief.reference_cases` / `style_reference_cases` 应明确区分：
  - `reference_cases`：当前 case 的主要模板来源
  - `style_reference_cases`：本轮 annotation 风格的正例 / 反例
- 其中 `style_reference_cases` 至少应包含：
  - 风格正例：当前仓库中更接近 predicate-first annotation 的案例
  - 风格反例：当前仓库中曾经出现但不应复用的 Rocq 算法镜像案例
- 进入 `annotation`、`vc-checking`、`vc-proving` 的新轮次时，必须先启动对应 subagent；`annotation-checking` 不单独创建 subagent，而是由已启动的 `annotation-subagent` 调用；`intake`、`goal-frozen`、`final-check`、`done` 不分派。
- `annotation` 与 `vc-proving` 是长时间迭代 phase；main 把轮次交给 subagent 后，必须等待其显式返回，不得因等待较久而抢回。
- 如果当前轮次需要被终止，合法原因只包括：输入 stale、用户取消/改向、或工具/会话已不可恢复；优先动作是重开同名 subagent，而不是 main 接管。
- 从下游 phase 回流重新进入 `annotation` 或 `vc-proving` 时，主 agent 必须先写 `Re-entry Brief`，让新 subagent 知道为什么回流。
- 持久 report 使用 `.agents/reports/<relative-case-dir>/<YYYY-MM-DD>/<case-name>-<YYYYMMDDTHHMMSS>/` 作为 run root，phase 轮次放在 `<YYYYMMDDTHHMMSS>-<phase>-r<N>[-<scope>]/`；canonical 文件名使用 snake_case，例如 `annotation_checking_report.md`、`vc_checking_informal_proof_report.md`、`subagent_return_report.md`、`timing_log.md`。
- 生成 VC 后的 informal proof / provable 判定由 `vc-checking` 负责；每个 proof 使用的 lemma 都必须来自现有 library 或明确列入本轮 / 后续 `*_lib.v` 的 candidate lemma，每个 lemma premise 必须由当前 VC 前条件推出。
- stale 的处理方式是标记失效，并删除对应 scratch；不是删除正式证明交付物。
- 每次 symexec 刷新出新的正式 `*_proof_manual.v` 后，旧 proving scratch 必须删除并重建。
- 所有 domain skill 都必须把 phase 切换、stale 标记和最终去向交回 orchestrator 统一记录。
- Timing 记录必须同时覆盖命令和非命令 wall-clock activity。主 agent 需要为人工分析、等待 subagent、正式文件回填/合并、annotation/proof 修改、helper lemma / 冗余 lemma 清理、Makefile/依赖维护、final review/cleanup 开闭计时；subagent report 也要提供自己内部的分析/编辑/等待/fallback activity 耗时。最终报告要区分 `total_command_seconds`、`total_human_activity_seconds`、`total_subagent_wait_seconds` 和 timing gaps。
- 所有非命令 activity 都必须采用 start/end ledger，而不是事后估算。主 agent 启动 subagent 时记录 `subagent-launch-requested` / `subagent-spawn-returned`，subagent 第一条记录必须是 `subagent-start`，返回后主 agent 再记录 `subagent-finished-observed` 和 close 开销。vc-proving 的每个 witness/helper 必须进一步拆成 proof-state reduction、空间证明生成、pure 证明生成、helper 设计/证明、proof script edit、coqc run、coqc feedback analysis 等事件。

编排层默认遵守三句话：

1. 固定 phase，隔离交互。
2. phase owner 持有完整迭代，main 不抢活；annotation 轮次必须先确认 spec、再填 annotation、再过 checking 门，才能交 main 回填和 symexec；生成 VC 后由 `vc-checking` 判断 provable。
3. scratch 过期即删，正式交付不删。

如果当前 case 有明显“想把算法直接搬进 Rocq”的诱因，再额外记住一句：

4. annotation 先抽隐藏性质，再决定需要哪些 helper lemma；不要先写 Rocq 算法。
