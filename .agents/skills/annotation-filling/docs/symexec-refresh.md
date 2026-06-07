# 刷新 symexec 生成文件

本文件只用于主 agent 在正式文件上刷新生成物。
`annotation-subagent` 在 scratch 上用 `qcp-mcp` 完成交互检查，并通过 `annotation-checking` 后，主 agent 需要先把被接受的 `annotation_scratch_lib` spec 变更回填到 `common_case_formal_lib`，刷新 `Case Brief` 中的 lib frozen prefix；再把被接受的 C annotation 回填到正式 `.c`，最后用 symexec 二进制完整执行一次，以刷新 Rocq 产物。

在任何正式回填或 symexec 之前，主 agent 必须先运行 annotation gate：

```sh
python3 .agents/skills/verification-orchestrator/scripts/validate_annotation_gate.py \
  --subagent-report=<annotation-round>/subagent_return_report.md \
  --checking-report=<annotation-round>/annotation_checking_report.md \
  --annotation-scratch-lib=<annotation_scratch_lib_path> \
  --coqproject=_CoqProject
```

只有当该命令返回 `0` 时，才允许正式回填和后续 symexec。

## 常规目录模板

```sh
linux-binary/symexec \
  --goal-file=SeparationLogic/examples/QCP_demos_LLM/<name>_goal.v \
  --proof-auto-file=SeparationLogic/examples/QCP_demos_LLM/<name>_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/QCP_demos_LLM/<name>_proof_manual.v \
  --coq-logic-path=SimpleC.EE.QCP_demos_LLM \
  -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM \
  --input-file=QCP_examples/QCP_demos_LLM/<name>.c \
  --no-exec-info
```

## 子目录模板

如果目标文件位于子目录，例如 `simple_arith/add.c`，对应路径需要整体带上子目录：

```sh
linux-binary/symexec \
  --goal-file=SeparationLogic/examples/QCP_demos_LLM/simple_arith/add_goal.v \
  --proof-auto-file=SeparationLogic/examples/QCP_demos_LLM/simple_arith/add_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/QCP_demos_LLM/simple_arith/add_proof_manual.v \
  --coq-logic-path=SimpleC.EE.QCP_demos_LLM.simple_arith \
  -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM \
  --input-file=QCP_examples/QCP_demos_LLM/simple_arith/add.c \
  --no-exec-info
```

## LLM_bench 复用 QCP_demos_LLM 头文件

`QCP_examples/LLM_bench` 下的 case 若写：

```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
```

则 symexec 命令必须显式提供 `QCP_examples/QCP_demos_LLM/` 作为 C include search path，同时保留 `QCP_demos_LLM` 的 strategy / Coq source logical path：

```sh
linux-binary/symexec \
  --goal-file=SeparationLogic/examples/LLM_bench/Algorithms/<case>/<case>_goal.v \
  --proof-auto-file=SeparationLogic/examples/LLM_bench/Algorithms/<case>/<case>_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/LLM_bench/Algorithms/<case>/<case>_proof_manual.v \
  --coq-logic-path=SimpleC.EE.LLM_bench.Algorithms.<case> \
  -slp QCP_examples/LLM_bench/ SimpleC.EE.LLM_bench \
  -IQCP_examples/QCP_demos_LLM/ \
  -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM \
  --input-file=QCP_examples/LLM_bench/Algorithms/<case>/<case>.c \
  --no-exec-info
```

`-I` 只解决 C 预处理器的头文件查找；`-slp` 只解决 QCP strategy / generated Coq 文件的 logical path。两者不能互相替代。不要为了让某个 scratch 跑通而把源码 include 改成 `../../../QCP_demos_LLM/...`。

## 刷新后的判断标准

- `*_goal.v` 和当前 C 文件一致。
- `*_proof_auto.v` 已更新。
- `*_proof_manual.v` 仍保留已有手动证明内容，可继续补写。
- `*_goal_check.v` 可用于后续统一编译检查。
- 如果本轮有 `annotation_scratch_lib` spec 变更，`common_case_formal_lib` 已由 main 回填，且 `Case Brief.lib_frozen_prefix_*` 已刷新。
- `validate_annotation_gate.py` 已通过；其中 `qcp_mcp_requirement_satisfied = yes`，且 `annotation_scratch_lib` 的 `_CoqProject` compile gate 为 `passed`。
- annotation C scratch 和 `annotation_scratch_lib` 不应继续保留到下一个 phase。
