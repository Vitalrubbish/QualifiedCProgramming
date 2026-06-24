# Kosaraju Refinement — Case Status

**Case**: Kosaraju SCC,C-refines-monad refinement proof(low_level 优先)
**Plan**: `/home/user/.claude/plans/valiant-swimming-grove.md`

## Phase Status — annotation 全完成 + continuation 清理,goal-frozen
- annotation stage 0–4 done;**continuation 引理清理 done**(未引用的 from_step/step_prog/all_visited/pre_kosaraju_pre_dfs 已删)
- goal-frozen: **lib_frozen_prefix_end_line = 663**
- vc-checking / vc-proving / final-check: pending(阶段5)

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
