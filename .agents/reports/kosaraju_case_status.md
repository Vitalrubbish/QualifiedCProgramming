# Kosaraju Refinement — Case Status

**Case**: Kosaraju SCC,C-refines-monad refinement proof(low_level 优先)
**Plan**: `/home/user/.claude/plans/valiant-swimming-grove.md`

## Phase Status — annotation 全完成 + continuation 清理,goal-frozen
- annotation stage 0–4 done;**continuation 引理清理 done**(未引用的 from_step/step_prog/all_visited/pre_kosaraju_pre_dfs 已删)
- goal-frozen: **lib_frozen_prefix_end_line = 663**
- vc-checking / vc-proving / final-check: pending(阶段5)
  - **vc-proving Round 1 done (partial)**: 8/87 witness 解(均 `pre_process. Qed.`,编译过);79/87 witness + 8 lib Admitted 仍未证。关键发现:绝大多数 witness VC 的剩余 goal 落到 8 个 Admitted lib prorefine 上(见 `.agents/reports/kosaraju_vc_proving_round1_report.md`)。proving scratch 在 `.tmp/kosaraju_proving/`。
  - **vc-proving Round 2 done (partial)**: **lib 8 prorefine 中 4 个已 Qed**(adj_fwd_step_iff / adj_rev_step_iff / dfs_finish_from_cons / dfs_scc_from_cons)+ **6 个可复用 helper lemma 已 Qed**(empty_adj_no_step / assume_false_empty / bind_empty_l / bind_empty_r / dfs_finish_continue_empty / dfs_finish_body_break)。关键发现:**empty_adj 上 step_aux empty_adj 恒为 False**(无顶点无边)→ DFS 永不递归恒 break,from_cons 前提矛盾平凡证。剩余 4 个(dfs_finish_unfold / dfs_finish_from_unfold / dfs_scc_unfold / dfs_scc_from_unfold)**不 blocked**,只差 repeat_break 关系层 dead-continue 一步(需 dfs_finish_body_only_break:从 body 关系假设推出 x = by_break tt)。scratch lib 在 `.tmp/kosaraju_proving/scratch_lib/kosaraju_rel_lib_scratch.v`(coqc EXIT=0)。见 `.agents/reports/kosaraju_vc_proving_round2_report.md`。Round 3 续证剩余 4 个 + 回填。
  - **vc-proving Round 3 done (partial)**: **lib 8 prorefine 中 6 个已 Qed**(R2 的 4 + R3 新证 dfs_finish_from_unfold / dfs_scc_from_unfold)+ **3 个新 helper 已 Qed**(bind_break_only / dfs_finish_body_only_break / dfs_scc_body_only_break + dfs_scc_continue_empty / dfs_scc_body_break 对称镜像)。dead-continue 推理完全打通(body_only_break + 通用 bind_break_only)。剩余 2 个 **dfs_finish_unfold / dfs_scc_unfold 仍 Admitted,blocked 在单一 helper 缺口**:`dfs_finish u = Lfix (DFS_finish_f) u` 的单步展开需要在 **applied form** `(Lfix f) u == (f (Lfix f)) u` 上做,而 (a) `mono_cont (DFS_finish_f empty_adj)` 因 `repeat_break (...) ∅` 是 Lfix 应用形式 `mono_cont_auto` 无法自动处理,(b) 无 program-function application 的 `Proper (Sets.equiv ==> Sets.equiv)` morphism 实例。Round 4 需补 `repeat_break_proper`(经 Lfix_congr)+ `mono_cont_repeat_break_const` helper(均进 task_local helper-suffix,不动 frozen prefix)。scratch lib 仍在 `.tmp/kosaraju_proving/scratch_lib/kosaraju_rel_lib_scratch.v`(820 行,coqc EXIT=0,2 Admitted)。见 `.agents/reports/kosaraju_vc_proving_round3_report.md`。**未回填正式 lib**(orchestrator one-shot:8/8 Qed 后才批量回填)。

## common_case_formal_lib = `SeparationLogic/examples/QCP_demos_LLM/kosaraju_rel_lib.v`
- **663 行**(清理后);**Axiom 0、Parameter 0、Admitted 8**
- 8 个 Admitted 全是 dfs_finish/dfs_scc 的 prorefine(unfold/from_unfold/from_cons/方向 iff),有明确证明方向(基于 StateRelMonad 的 Lfix/repeat_break 引理)
- kosaraju_finish_from/scc_from = kosaraju_*_monad(VC 保持 opaque,不展开;C 侧纯命题带循环进度)

## 7 个 C 函数 refinement 标注完成(symexec 到尾 + goal_check 全链)
num_vertices / get_visited1 / dfs1(反图)/ dfs2(正图)/ kosaraju_finish / kosaraju_scc / kosaraju_run

## 阶段5 vc-proving 待证清单
- **lib 8 个 Admitted**:dfs_finish_unfold/from_unfold/from_cons/adj_rev_step_iff + dfs_scc 同(4)
- **proof_manual ~34 witness**:get_visited1 + dfs1(~9)+ dfs2(~8)+ 外层三函数(~16)
- 主要工具:`sllseg_sll`/`sllseg_sllseg`(sll_lib)+ SllPtrArray 策略 id 2 逆向 + re-merge entailment + Lfix/repeat_break 单步展开

## 统一 annotation 模式(验证可行)
while 循环遍历邻接表(cursor + 手动 Inv `sllseg ** sll ** 状态数组`)+ 循环内图递归 `where(low_level_spec)`(避 SIGSEGV)+ pre-call Assert re-merge 数组成 full。外层 for(i<n) + 调已验证 dfs。sllseg 增长/re-merge 都是 Inv 保持 VC(Rocq 手动),非 prefill。

## 关键技术事实
- `KSt := @St Z`;闭合包装 `@DFS_finish/@DFS_scc/... KG empty_adj ...`
- `<`/`<=` 必须 `%Z`;radj/fadj 用 `SllPtrArray`;状态数组 `IntArray::full`
- symexec 不覆盖 `proof_manual.v`;新增函数后先删再 symexec
- symexec 能力:支持"while + 手动 Inv + 循环内调用"、"静态边界 for + 循环内调用";不支持"数组下标边界 + 循环内递归"、"链表游标 sllseg 增长作为 prefill"
- symexec SIGSEGV 坑:while 内自递归 `where(low_level_spec_aux)` 崩 → 用 `where(low_level_spec)`
- qcp-mcp 包装层在本环境失效,底层 mcp/symexec 完整;annotation-checking 以 direct symexec 为准

## Commits
- e296fc9:7 函数 refinement annotation milestone
- (本轮):删未引用 continuation 引理(lib Axiom/Parameter 0,Admitted 12→8)
