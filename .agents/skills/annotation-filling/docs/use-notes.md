# 使用注意

这个文件用于说明应用 `annotation-filling` 时必须优先遵守的细节。

- phase、工件、delegation 和失效传播规则统一以 `verification-orchestrator` 为准；本文件只保留 annotation 相关硬规则。
- 正式 case、symexec 输出和主要模板仍以 `QCP_examples/QCP_demos_LLM` 及对应的 `SeparationLogic/examples/QCP_demos_LLM` 为准。
- 设计 annotation 风格时，可以对照 `QCP_examples/QCP_demos_LLM` 正例学习“隐藏性质优先”的写法；不要把它们当成直接可复制的 formal 边界模板。
- `annotation-subagent` 必须先从最新正式 `.c` 创建 annotation C scratch，再在 scratch 上工作。
- `annotation-subagent` 还必须先从最新 `common_case_formal_lib` 创建 `annotation_scratch_lib`；若 `common_case_formal_lib` 不存在，则创建本轮空 / 最小 `annotation_scratch_lib`。
- annotation filling 的默认顺序是：先确认 / 修正 `annotation_scratch_lib` 中的 spec 定义，再填写 C 侧 annotation。
- spec 定义必须是严格数学性质定义，不应是在 Rocq 中把 C 程序本体、循环或状态转移重写一遍。
- `annotation-subagent` 可以在 scratch 上使用 `qcp-mcp`；不得在正式 `.c` 上做交互式实验。
- `QCP_examples/LLM_bench` case 复用 `QCP_demos_LLM` 公共头文件时，C 文件应统一保持裸 include（例如 `#include "verification_stdlib.h"` / `#include "verification_list.h"` / `#include "int_array_def.h"`）。annotation C scratch 上的 `qcp-mcp` 检查必须使用能解析 `QCP_examples/QCP_demos_LLM/` 的 include search path；若头文件解析失败，应修正 qcp-mcp wrapper / 启动配置 / include 参数，而不是把源码改成 `../../../QCP_demos_LLM/...`。
- 若 direct `qcp-mcp` wrapper 因仓库中的 ELF 缺少执行位而失败，允许使用同一 `qcp-mcp` 链路的 loader fallback；但 direct `symexec` 不能替代 `qcp-mcp` requirement。
- `annotation-subagent` 可以编辑本轮 `annotation_scratch_lib`；不得直接编辑 `common_case_formal_lib`。`common_case_formal_lib` 回填只能由主 agent 在 annotation-checking 通过后执行。
- 每轮 `annotation-filling` 得到候选 annotation 后，必须由同一 `annotation-subagent` 调用 `annotation-checking`。只有检查结果为 `passed`，本轮结果才可交给主 agent 回填并触发正式 symexec。
- 即使 `annotation-checking` 返回 `passed`，若 report 中 `qcp_mcp_requirement_satisfied != yes` 或 `annotation_scratch_lib_coqc_status != passed`，主 agent 也不得进入正式 symexec。
- 如果 `annotation-checking` 返回 `failed`，不要把候选 patch 交给主 agent；继续回到 annotation filling 修正 C scratch 或 `annotation_scratch_lib`，再重新检查。
- `annotation` 是长时间迭代 phase；本轮一旦交给 `annotation-subagent`，就应持续工作到 `completed`、`blocked` 或 `stale`，而不是只交第一版尝试。
- 如果本轮是回流轮次，先读 `Re-entry Brief`，不要自己猜测为什么再次进入 `annotation`。
- direct proof 默认使用 `predicate-first annotation`：先把“处理过的前缀 / 后缀、当前候选最优值、剩余区间、局部 shape”写成直观谓词，再决定需要哪些 helper lemma。
- 不要用“先在 Rocq 里定义算法循环 / 状态转移，再让 invariant 跟随它”的方式驱动 annotation。
- refinement proof 可以保留必要的 `safeExec` / monad 规格，但这不意味着可以额外再造一份 direct-proof 风格的 Rocq 算法镜像。
- 涉及完整 `Assert` / `Inv Assert` 时，必须先对照 `common-annotation-errors.md`，重点检查 `@pre` 桥接、读取值绑定、自反恒真式，以及 refinement case 中 invariant / high-level correctness 的分层边界。
- `loop invariant` 必须写成完整的 `Inv Assert`。
- 中间断言必须写成完整的 `Assert`。
- 不要使用 `which implies`、partial assertion 或其它替代 annotation 形态。
- 如果某个 manual VC 语义上不可证，优先修 annotation，不要把问题推给 Rocq proof。
- scratch 上不运行 symexec；正式 symexec 刷新只由主 agent 在正式 `.c` 上执行。
- phase 完成、输入 stale 或主 agent 已回填正式 `.c` 后，annotation C scratch 必须删除；若本轮创建了 `annotation_scratch_lib`，也必须同步删除。
- 如果需要改动 C 实现本身，而不只是 annotation，应先暂停并与用户确认。
