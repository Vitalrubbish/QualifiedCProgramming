# Kosaraju vc-proving — Round 1 Subagent Return Report

**round_outcome**: `partial`

**Subagent**: vc-proving-subagent
**Date**: 2026-06-24
**Case**: Kosaraju SCC, C-refines-monad refinement proof

## Executive summary

Round 1 of Kosaraju `vc-proving` produced an **accurate, compile-verified triage** of all 87 manual witness lemmas and identified the precise blocking dependency chain. **8 / 87 witness lemmas are fully proved and compile-verified** (the only ones solvable by the auto-tactic `pre_process` alone). The remaining **79 witness VCs are not auto-solvable** and, critically, the great majority of them are **blocked on the 8 Admitted lib prorefine lemmas** (`dfs_finish_unfold` / `dfs_finish_from_unfold` / `dfs_finish_from_cons` / `adj_rev_step_iff` and the four `dfs_scc_*` analogues), which in turn require real StateRelMonad `Lfix` / `repeat_break` unfolding proofs. This is a genuine multi-round effort, not a single-round finish.

## What was completed

1. **Proving scratch + task_local_scratch_lib infrastructure built and compile-verified.**
   - `.tmp/kosaraju_proving/kosaraju_rel_proof_manual_scratch.v` (fresh copy of the real `kosaraju_rel_proof_manual.v` + a `From KosarajuHelpers Require Import kosaraju_helpers.` import line).
   - `.tmp/kosaraju_proving/helpers/kosaraju_helpers.v` = empty `task_local_scratch_lib` helper-suffix module (compiles; no helpers added yet since no helper has been needed by the 8 solved witnesses).
   - `.tmp/kosaraju_proving/coqc_scratch.sh` = coqc wrapper with the full absolute `-R`/`-Q` loadpath map (mirrors the repo `_CoqProject`) plus `-Q .../helpers KosarajuHelpers`.
   - Build verified against the real `make`-built `.vo` dependencies (base manual compiles with all-Admitted; filled manual with 8 `pre_process. Qed.` + 79 `Admitted.` compiles EXIT=0).

2. **8 witness lemmas fully proved and verified** (`pre_process. Qed.`), back-fill-ready:
   - `kosaraju_get_visited1_return_wit_1_split_goal_1`
   - `kosaraju_get_visited1_return_wit_1`
   - `dfs1_entail_wit_3_split_goal_2`
   - `dfs2_entail_wit_3_split_goal_2`
   - `kosaraju_finish_entail_wit_2_split_goal_2`
   - `kosaraju_scc_entail_wit_2_split_goal_3`
   - `kosaraju_scc_entail_wit_3`
   - `kosaraju_scc_entail_wit_3_split_goal_1`

3. **Definitive, compile-verified triage** of all 87 witnesses via a greedy classifier (scripts: `.tmp/kosaraju_proving/classify2.py`, `apply_solved.py`). Result: **8 solved by `pre_process`, 79 require manual work.** (`aggressive_pre_process` solves 0 of the 79.)

## Key finding: dependency chain (this is the real blocker)

The 79 remaining witnesses are not independently hard spatial puzzles — most reduce, after `pre_process` + providing the obvious `Exists` witnesses + `split_pure_spatial`, to **a single residual pure `safeExec` assertion** that requires a lib prorefine. Concrete example, `kosaraju_finish_entail_wit_1`:

- After `pre_process. Exists vis1_l_low_level_spec. Exists fin_l_low_level_spec. Exists timer_v_low_level_spec. repeat (split_pure_spatial || split_pures).` the spatial part is solved and only **one** goal remains:
  `... |-- " safeExec (pre_kosaraju ... timer_v_low_level_spec ...) (kosaraju_finish_from 0) X_low_level_spec "`.
- The hypothesis `PreH1` gives `safeExec (pre_kosaraju ... timer_v ...) kosaraju_finish_monad X`. Closing the residual goal needs `kosaraju_finish_monad = kosaraju_finish_from 0` (the Lfix unfolding), i.e. a lib prorefine that is currently `Admitted`.

The same shape recurs across the dfs1/dfs2/kosaraju witness families: the spatial rearrangement is mechanically doable (`SllPtrArray_full_split_to_missing_i` / `SllPtrArray_missing_i_merge_to_full` from `SllPtrArrayLib.v` line 309 / 331; `IntArray.full` unfold; `sllseg_*` from `sll_lib.v`), but the **pure `safeExec` assertion always bottoms out on one of the 8 Admitted lib prorefines**.

Therefore the dependency chain is:

```
79 witness VCs  ──(need)──>  8 Admitted lib prorefines
                                  │
                                  └──(need)──>  StateRelMonad Lfix / repeat_break
                                                 unfolding proofs (real monad work)
```

## The 8 Admitted lib prorefines (`kosaraju_rel_lib.v`, all in the frozen prefix ≤ 663)

| Lemma | Line | Statement (essence) | Proof direction |
|-------|------|----------------------|-----------------|
| `dfs_finish_unfold` | 342 | `dfs_finish u == visit1 u ;; dfs_finish_from u nil` | `dfs_finish = Lfix ...`; unfold Lfix + `repeat_break_unfold` |
| `dfs_finish_from_unfold` | 350 | `dfs_finish_from u done == (x <- loop_body ...; match x ...)` | `repeat_break_unfold` specialised to the loop body |
| `dfs_finish_from_cons` | 363 | `step_aux empty_adj e v u -> ~In e done -> dfs_finish_from u (e::done) == (assume ... ;; dfs_finish v ;; dfs_finish_from u done)` | one reverse-edge step of repeat_break |
| `adj_rev_step_iff` | 380 | `AdjGraphValid g -> 0<=u<adj_verts g -> In v (adj_rev!!u) <-> exists e, e=(v,u) /\ step_aux g e v u` | `AdjGraphValid` transpose clause |
| `dfs_scc_unfold` | 502 | `dfs_scc root u == visit2 u ;; set_scc_id u root ;; dfs_scc_from root u nil` | analog of `dfs_finish_unfold` |
| `dfs_scc_from_unfold` | 510 | analog of `dfs_finish_from_unfold` | `repeat_break_unfold` |
| `dfs_scc_from_cons` | 523 | analog of `dfs_finish_from_cons` | one forward-edge step |
| `adj_fwd_step_iff` | ~549 | analog of `adj_rev_step_iff` (forward graph) | `AdjGraphValid` forward clause |

These 8 are the unlock. They are all `==` (program equivalence in `StateRelMonad`) or iff lemmas resting on `AdjGraphValid`/`step_aux`/`adj_step_aux`. Proving them requires the `repeat_break`/`Lfix` fixed-point lemmas from `MonadLib.StateRelMonad` plus the `adj_step_aux` definition — non-trivial but each is a focused monad/equivalence proof, independent of the 87 witnesses.

## What remains (next round work)

1. **Prove the 8 lib prorefines** (highest leverage). Once these are `Qed.`, a large fraction of the 79 witness VCs close with the `pre_process. Exists <witnesses>. repeat (split_pure_spatial || split_pures). <spatial tactic>.` recipe (the residual `safeExec` assertion then follows from the now-proved prorefine + PreH).
2. **After lib unlock, prove the 79 witness VCs group-by-group**:
   - Pure-bounds residuals (`dfs1_safety_wit_6_split_goal_1/2`, `dfs2_*`, `kosaraju_scc_safety_wit_5_*`): need `timer_m < INT_MAX` bounds. These need a lib/invariant fact tying `timer_m` to `n`/`INT_MAX` (likely derivable from `pre_dfs1`/`pre_kosaraju` once unfolded, or a small helper).
   - Existential-rearrangement + array split/merge (`*_entail_wit_1`, `*_return_wit_1`, `kosaraju_run_return_wit_1`): `Exists` + `SllPtrArray_full_split_to_missing_i`/`missing_i_merge_to_full` + `IntArray.full` unfold + `cancel`.
   - sllseg grow / re-merge (dfs1/dfs2 `*_entail_wit_2/3/4/5/6`): `sllseg_len1`/`sllseg_sllseg`/`sllseg_sll` + candidate helper `sllseg_grow_step`.
3. The 5 helper lemmas listed in the delegation ticket are still **not yet needed/started** (none of the 8 solved witnesses needed a helper); they become relevant only after the lib unlock, inside the harder spatial groups.

## Files (all absolute)

- Proving scratch manual (8 proved + 79 Admitted, compiles): `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/kosaraju_rel_proof_manual_scratch.v`
- Helper lib (empty, compiles): `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/helpers/kosaraju_helpers.v`
- coqc wrapper: `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/coqc_scratch.sh`
- Triage scripts: `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/{classify2.py,apply_solved.py}`
- Solved list: `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/solved.txt` (= the 8 above)
- Remains list (79): `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/remains.txt`

## Integration guidance for main agent (the 8 proved witnesses only)

The 8 proved witnesses use identical bodies `Proof. pre_process. Qed.` and are safe to back-fill into the real `/home/user/src/tarjan-coq/SeparationLogic/examples/QCP_demos_LLM/kosaraju_rel_proof_manual.v` once the rest of the round's plan is decided. **Recommendation: do NOT back-fill the 8 in isolation yet** — because (a) the 8 alone leave the file with 79 `Admitted`, (b) no helper migration is needed for them, and (c) the case cannot pass `final-check` until the lib prorefines + the 79 are done. Better to land the 8 together with the lib unlock + the first batch of witness VCs as one integration, per the orchestrator "one-shot helper-free manual + lib back-fill" rule.

## Round did NOT modify any protected/formal file

- Real `kosaraju_rel_proof_manual.v`, `kosaraju_rel_lib.v`, and all generated `*_goal.v`/`*_proof_auto.v`/`*_goal_check.v` were left untouched (read-only this round).
- All work is in `.tmp/kosaraju_proving/` scratch + the empty `KosarajuHelpers.kosaraju_helpers` scratch module.

## Timing / why partial

Wall-clock was dominated by (a) building a reliable compile-verified classification harness (the `coqtop` interactive triage path was unreliable due to "No such goal" hard-errors on solved proofs; switched to the greedy `coqc` classifier that re-compiles the whole manual per failing witness), and (b) confirming the dependency chain by reducing representative VCs. No `Admitted`/`Axiom`/forbidden-lemma was introduced into any scratch proof (the 8 use only `pre_process`).

## Round 2 priority recommendation

Start Round 2 by proving the **8 lib prorefines** on a fresh proving scratch (they are independent of the witnesses and unlock the bulk). Re-enter `vc-proving` with a Re-entry Brief pointing at this report's "dependency chain" section.
