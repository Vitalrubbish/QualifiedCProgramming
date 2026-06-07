# 自然语言证明分析指南

## 目标

`vc-checking-subagent` 输出的自然语言证明不是给 `vc-proving` 的一句提示，而是可审计的 proof contract。在进入 `vc-proving` 之前，它至少要说明：

1. 当前 VC 写成 `P |-- Q` 后，是否在现有 annotation / spec 下语义成立。
2. 若成立，`Q` 中每个空间资源、纯命题和存在 witness 如何从 `P` 构造出来。
3. 若需要 helper lemma，lemma 的数学陈述、来源边界、每个 premise 的 discharge 依据，以及它属于哪个 proof group。
4. 若不成立，缺口来自 C annotation、`common_case_formal_lib` 的 spec、冻结前缀边界、输入 stale，还是 witness 结构本身。

## 先读什么

1. 本轮 delegation ticket：确认 `target_witnesses`、`source_goal_version`、`common_case_formal_lib` 冻结信息、report 路径和 timing 要求。
2. `*_goal.v`：只读目标 witness 的 theorem 展开形状，不修改生成文件。
3. 当前 case 的 `common_case_formal_lib`：区分 annotation-approved spec、已存在 helper lemma、冻结前缀后的 helper 后缀。
4. `*_proof_manual.v`：只看现有 witness proof 的局部风格，不把 helper lemma 写进正式 manual。
5. 参考 Rocq 风格：优先参考 `SeparationLogic/examples/LLM_bench` 和 `QCP_demos_LLM` 中已完成的 predicate-first 证明，不参考 `QCP_demos_human`。

## 从 Rocq 证明反推自然语言 proof pattern

LLM-friendly 的 Rocq 证明通常有稳定结构。自然语言分析应把这些结构提前写清楚：

1. 空间资源阶段：`pre_process` 后先识别左侧数组段、全数组、结构谓词以及右侧需要保留或重建的资源。若证明会用 `cancel`、`sep_apply`、`IntArray.*_split*`、`undef_seg_empty` 等 tactic，要明确说明哪个资源被保留、哪个被拆分、边界为何成立。
2. 纯命题阶段：说明 `split_pures` 之后每个纯目标来自哪里。不要写“由 invariant 显然”，而要明确写出展开了哪个 invariant、得到了哪些事实、最后如何交给 `lia` 或等式推理。
3. 数学 spec 阶段：对 `MaxMin`、reachability、DP table、queue coverage、subsequence、window maximum 等抽象谓词，先说明谓词语义，再说明当前 VC 需要的是 introduction、preservation、completion 还是 contradiction。
4. Helper lemma 阶段：如果证明会在 Rocq 中使用 `eapply SomeLemma`，自然语言分析里必须提前列出 `SomeLemma` 的结论形状和所有 premise。若 lemma 尚不存在，只能列入 `candidate_lib_lemmas`，后续由 `vc-proving` 的 worker 在 `worker_helper_scratch_lib` 中证明，再迁入 `task_local_scratch_lib`。
5. 失败定位阶段：如果某个目标只有在修改冻结前缀、补新 spec 或改变 annotation 后才能成立，这不是 tactic 问题，而应返回 `annotation-bug` 或 `blocked`。

## 单个 witness 的分析模板

每个 witness 至少输出以下字段。字段可以写成 markdown 小节，也可以进入本轮 `vc_checking_informal_proof_report.md` / group plan JSON：

```text
witness_id:
judgment: proofable | needs-lemma | annotation-bug | blocked
vc_shape:
  pre_spatial:
  pre_pure:
  pre_exists:
  post_spatial:
  post_pure:
  post_exists:
witness_instantiation:
space_plan:
pure_plan:
used_existing_lemmas:
candidate_lib_lemmas:
premise_discharge:
failure_signal:
recommended_next_phase:
proof_group_candidate:
grouping_reason:
timing_seconds:
```

`vc_shape` 必须把 `P` 与 `Q` 分开写。`witness_instantiation` 要说明右侧 `EX` 的值来自旧 logical list、`replace_Znth`、`sublist`、`app ... :: nil`，还是某个 loop variable。`premise_discharge` 必须逐项对应当前 VC 的前条件，不允许省略。

## Lemma 审计标准

对每个 lemma，按下面格式写：

```text
lemma_name:
source: existing-library | current-case-lib | candidate_lib_lemmas
statement_shape:
used_by_witnesses:
premises:
  - premise:
    discharged_by:
    needs_unfold:
    arithmetic:
    spatial_resource:
helper_destination:
```

`source = candidate_lib_lemmas` 时，`helper_destination` 必须是 `worker_helper_scratch_lib -> task_local_scratch_lib helper suffix -> common_case_formal_lib after all VC complete`。不要建议在 `vc-checking` 或单个 witness 证明期间直接修改 `common_case_formal_lib`。

## 分组原则

`witness_group_plan` 应按证明模式分组，而不是按 witness 编号机械分组。

- 同一组应共享核心 proof pattern，例如相同的 invariant 展开、helper family、空间 frame 结构或数学 recurrence。
- 每组指定一个 `representative_witness`，并说明其他成员与它相比只差哪些局部条件。
- 组名应表达证明内容，例如 `dp_zero_and_copy_semantics`、`queue_drop_pending_pop`、`queue_push_current`、`final_answer_bridge`、`pure_bounds_safety`。
- 如果某个 witness 被判为 `annotation-bug`，不要把它混入 proving group；下游 `vc-proving` 输入必须失效，主流程应回到 annotation。

## 与工作流的连接

1. `goal-frozen` 后，主 agent 把最新 goal/lib/manual hash 和冻结前缀信息写入 ticket。
2. `vc-checking-subagent` 读取 ticket，按本指南为每个 witness 形成 informal proof 或失败诊断。
3. 若有 `annotation-bug`，返回主 agent；主 agent 按 orchestrator 写 `re-entry brief`，删除 stale proving scratch，重新进入 annotation。
4. 若所有 witness 都是 `proofable` 或 `needs-lemma`，返回 `witness_group_plan`、`candidate_lib_lemmas` 和 timing 摘要。
5. `vc-proving-subagent` 只消费这些 group：worker 在自己的 `worker_helper_scratch_lib` 证明候选 helper，在 worker-local manual 中证明 witness。
6. helper migration 之后，主 agent 只能在所有目标 witness 都完成时，一次性把 helper-free manual 和 `task_local_scratch_lib` 后缀集成回正式文件。

## 反例和红旗

- 不要把 C 循环直接翻译成 Rocq 函数后就声称 VC 可证；spec 必须描述数学性质，例如最大值、可达性、prefix/table relation、queue coverage。
- 不要把 `lia` 当作 proof plan。必须写出 `lia` 依赖了哪些 bound、guard、length 等事实。
- 不要用“现有 invariant 足够”代替展开分析；要写明 invariant 的具体 conjunct 和实例化参数。
- 不要把缺失 lemma 直接写入 `common_case_formal_lib` 冻结前缀。
- 不要在目标 stale、hash 不匹配、manual skeleton 与 goal witness 不一致时继续分组证明。

## 简短示例

`sliding_window_maximum` 的队列类 VC 可按如下方式分析：

- `P` 提供 `SWMQueueState l q_l head tail i k`、数组 frame 和循环 guard。
- `Q` 要求 drop-loop 后的 pending state，同时保留相同数组 frame。
- 空间资源通过 `repeat cancel` 保留；纯目标通过展开 `SWMQueueState` 得到 entries-valid、index-increasing、value-decreasing、coverage 和 front-max。
- 若从 after-drop 转为 pending state，需要 candidate/existing lemma `SWMQueueAfterDrop_to_PendingState`；其 premise `SWMQueueAfterDrop ...` 来自 loop invariant，`i < Zlength l` 来自 loop guard。
- 如果需要弹出被当前值支配的 tail，则该 lemma 属于 queue-pop helper family；前提中的 `head < tail`、last value dominated、pending state 必须分别由 branch condition、数组读取比较和 invariant 展开得到。