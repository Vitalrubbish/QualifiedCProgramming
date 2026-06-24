# Kosaraju Refinement — Case Status

**Case**: Kosaraju SCC,C-refines-monad refinement proof(low_level 优先)
**Plan**: `/home/user/.claude/plans/valiant-swimming-grove.md`

## 🎯 Phase Status — annotation 全完成,已进 goal-frozen
- intake: done
- annotation: **stage 0–4 全部 done**(骨架 / 内存表示 / dfs1 反图 / dfs2 正图 / 外层循环+kosaraju_run)
- **goal-frozen: done**(lib frozen_prefix=717,已锁定)
- vc-checking / vc-proving / final-check: **pending(阶段5)**

## 7 个 C 函数全部 refinement 标注完成(symexec 到尾 + goal_check 全链编译)
`kosaraju_num_vertices` / `kosaraju_get_visited1` / `dfs1`(反图)/ `dfs2`(正图)/ `kosaraju_finish`(Phase1 外层)/ `kosaraju_scc`(Phase2 外层按 finish 降序)/ `kosaraju_run`(顶层 finish;;scc)

## common_case_formal_lib = `SeparationLogic/examples/QCP_demos_LLM/kosaraju_rel_lib.v`
- **lib_frozen_prefix_end_line: 717**(已锁定,vc-proving 只能在 717 之后)
- 阶段4 增量:`kosaraju_finish_monad`/`kosaraju_scc_monad`/`kosaraju_monad` + `kosaraju_finish_from`/`kosaraju_scc_from`(Parameter)+ step body(Axiom)+ `order_sorted` + `pre_kosaraju` + `pre_kosaraju_pre_dfs1/2`(Admitted)

## 阶段5 vc-proving 待证清单(共 ~56 个)
**lib(22 个 Admitted/Axiom/Parameter)**:
- 8 个 Admitted prorefine:dfs_finish_unfold/from_unfold/from_cons/adj_rev_step_iff + dfs_scc_*(4)
- 14 个阶段4:`kosaraju_finish_from`/`kosaraju_scc_from`(Parameter,待给真实 Lfix 定义)+ from_0/from_step/step_prog_next/all_visited(Axiom,continuation 语义)+ order_sorted(待证)+ pre_kosaraju_pre_dfs1/2(投影)
**proof_manual(34 个 Admitted witness)**:get_visited1 + dfs1(~9)+ dfs2(~8)+ kosaraju_finish/scc/run(~16)

主要 Rocq 工具:`sllseg_sll`/`sllseg_sllseg`(sll_lib)+ SllPtrArray 策略 id 2 逆向 + re-merge entailment + Lfix continuation 单步展开 + `order_sorted` 性质

## 统一 annotation 模式(全验证可行)
`while` 循环遍历邻接表(cursor `cur`)+ 手动 Inv(`sllseg(head,cur,processed) ** sll(cur,rem) ** 状态数组`)+ 循环内图递归 `dfs(v)` 用 `where(low_level_spec)`(非 `_aux`,避 SIGSEGV)+ pre-call Assert re-merge 数组成 full。外层 `for(i<n)` + 调已验证 dfs。sllseg 增长/re-merge/continuation 都是 Inv 保持 VC(Rocq 手动证),不是 prefill。

## 关键技术事实(全部经编译/symexec 验证)
- `KSt := @St Z`;闭合包装 `@DFS_finish/@DFS_scc/... KG empty_adj ...`
- `<`/`<=` 必须 `%Z`;radj/fadj 用 `SllPtrArray`;状态数组用 `IntArray::full`
- symexec 不覆盖 `proof_manual.v`;新增函数后先删再 symexec
- **symexec 能力边界**:支持"while 循环 + 手动 Inv + 循环内调用"、"静态边界 for + 循环内调用";不支持"运行时数组下标边界 + 循环内递归"、"链表游标 sllseg 增长作为 prefill"
- **symexec SIGSEGV 坑**:while 内自递归 `where(low_level_spec_aux)` 崩 → 用 `where(low_level_spec)` + pre-call Assert re-merge
- **qcp-mcp 包装层在本环境失效**(返回空),但底层 `linux-binary/mcp`/`symexec` 完整工作;annotation-checking 以 direct symexec 为准
- annotation-subagent 有时直接写正式文件(回填注意去重)

## 已回填的正式文件
- `QCP_examples/QCP_demos_LLM/kosaraju_rel.c`(544 行,7 函数)
- `SeparationLogic/examples/QCP_demos_LLM/kosaraju_rel_lib.v`(717 行)+ 生成文件(goal/proof_auto/proof_manual/goal_check)
- `sll_ptr_array` 库全套(SllPtrArrayLib + 策略 + proof)
- `SeparationLogic/Makefile`(218 + 274 + 406)
