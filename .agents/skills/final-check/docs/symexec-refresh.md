# 最终检查阶段的 symexec 刷新

假设目标文件为 `QCP_examples/QCP_demos_LLM/examples.c`，可以使用下面的模板重新生成目标文件：

```bash
linux-binary/symexec \
  --goal-file=SeparationLogic/examples/QCP_demos_LLM/examples_goal.v \
  --proof-auto-file=SeparationLogic/examples/QCP_demos_LLM/examples_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/QCP_demos_LLM/examples_proof_manual.v \
  --coq-logic-path=SimpleC.EE.QCP_demos_LLM \
  -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM \
  --input-file=QCP_examples/QCP_demos_LLM/examples.c \
  --no-exec-info
```

若最终检查对象位于 `QCP_examples/LLM_bench` 且源码使用 `QCP_demos_LLM` 公共头文件的裸 include，则 symexec 命令必须同时带：

```bash
-IQCP_examples/QCP_demos_LLM/ \
-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM
```

其中 `-I` 用于 C 头文件搜索，`-slp` 用于 strategy / generated Coq 依赖路径；二者不能互相替代，也不要在 final-check 中把源码 include 改成相对路径来规避 include path 配置。

## 这一步要确认什么

- `examples_goal.v` 已被当前 C 文件重新覆盖。
- `examples_proof_auto.v` 已同步刷新。
- `examples_proof_manual.v` 保留现有手写 witness proofs；helper lemmas 应已迁入该 case 的 `common_case_formal_lib`，二者可继续参与后续编译。
- `common_case_formal_lib` 不由 symexec 重写；刷新后仍要单独核对它的冻结前缀是否与 `Case Brief` 一致。
- symexec 完成后，主 agent 仍需重新执行 `proof_manual` 无 helper lemma / `common_case_formal_lib` helper suffix 结构检查，再进入后续编译。
