# 使用注意

这个文件补充 `vc-checking` 的使用细节，优先级低于 `verification-orchestrator`，但高于临时推断。

- phase、ledger、delegation 和 stale 规则统一以 `verification-orchestrator` 为准；本文件只补充 VC 分诊相关硬约束。
- 只围绕当前 witness 的可证性做分析，不手改生成文件 `*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`。
- 分诊顺序必须是：先判断 VC 是否语义可证，再决定应该回到 annotation，还是进入 proving。
- 当结论是 `needs-lemma` 时，helper 必须先由 `vc-proving` 的 worker 在 `worker_helper_scratch_lib` 中证明，再通过 helper migration 进入本轮 `task_local_scratch_lib`；不要建议直接修改 `common_case_formal_lib` 冻结前缀。
- 返回结果里必须包含 `witness_group_plan`，按证明模式而不是按 witness 编号机械分组，供 `vc-proving` 并行消费。
- 任何 annotation 改动后，都必须重新生成并重新检查 VC，旧分诊结论随之失效。
- annotation 约束仍然有效：只使用完整的 `Assert` / `Inv Assert`，不要引入黑盒 entailment 自动化 tactic。
- 不要通过额外导入不相关证明库来绕过项目既有证明风格。
- 如果当前看到的 VC 与预期不一致，先检查目标文件、编译路径和生成产物是否对应同一个 case。