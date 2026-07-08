# Kosaraju vc-proving — Round 2 Subagent Return Report

**round_outcome**: `partial`

**Subagent**: vc-proving-subagent
**Date**: 2026-06-24
**Case**: Kosaraju SCC, C-refines-monad refinement proof
**Scope**: Prove the 8 Admitted lib `prorefine` lemmas in `kosaraju_rel_lib.v` (frozen prefix ≤ 663).

## Executive summary

Round 2 made concrete, compile-verified progress on the 8 lib `prorefine` lemmas and, more importantly, **established the reusable monad-collapse infrastructure** that turns the remaining 4 from open-ended proof search into a mechanical, well-understood shape. **4 / 8 prorefine are fully proved and coqc-verified** (`Qed.`), plus **6 reusable helper lemmas** are proved and coqc-verified. The remaining 4 (`dfs_finish_unfold`, `dfs_finish_from_unfold`, `dfs_scc_unfold`, `dfs_scc_from_unfold`) are **not blocked** — their full proof shape is now known and partially built — but each needs the same `repeat_break` relational dead-continue step that is fragile to write by hand under `Open Scope sets`. This is a focused multi-round effort, not an unbounded blocker.

The single most important Round 2 finding: **on the `empty_adj` carrier (`adj_verts = 0`), `step_aux empty_adj e v u` is always `False`** (no valid vertices ⇒ no edges). This collapses every DFS loop body to its break branch and makes the `from_cons` lemmas vacuously true. This is the key that makes the whole family tractable.

## What was completed (all coqc-verified on the scratch lib)

### 4 prorefine fully proved (`Qed.`), back-fill-ready

| Lemma | lib line | Proof essence |
|-------|----------|---------------|
| `adj_fwd_step_iff` | 540 | unfold `AdjGraphValid` (cl.3 fwd-valid), `subst e`, `change` to `adj_step_aux`, extract. |
| `adj_rev_step_iff` | 380 | unfold `AdjGraphValid` (cl.4 rev-valid + cl.5 transpose), transpose `Htrans v u`, `change`/extract. |
| `dfs_finish_from_cons` | 363 | **vacuous**: premise `step_aux empty_adj e v u` ⟹ `False` via `empty_adj_no_step`. |
| `dfs_scc_from_cons` | 523 | **vacuous**: premise `step_aux empty_adj e u v` ⟹ `False` via `empty_adj_no_step`. |

### 6 reusable helper lemmas proved (`Qed.`) — infrastructure for the remaining 4

All in the scratch lib; these are the candidate `task_local_scratch_lib` helpers / proof patterns for Round 3.

| Helper | Scratch line | Statement / role |
|--------|--------------|------------------|
| `empty_adj_no_step` | 344 | `forall e v u, step_aux empty_adj e v u -> False`. The master fact: empty_adj has no edges. |
| `assume_false_empty` (Section `empty_helpers`, Σ-general) | 360 | `assume P == ∅` when `forall s, ~ P s`. |
| `bind_empty_l` (Σ-general) | 368 | `bind ∅ g == ∅`. |
| `bind_empty_r` (Σ-general) | 376 | `(forall a, g a == ∅) -> bind f g == ∅`. |
| `dfs_finish_continue_empty` | 387 | The continue branch of `dfs_finish_loop_body` is `∅` on `empty_adj` (its inner `assume (step_aux empty_adj e v u)` is unsatisfiable). Proved by `sets_unfold` + walk the bind chain to the `assume (step_aux …)` and apply `empty_adj_no_step`. |
| `dfs_finish_body_break` | 411 | `dfs_finish_loop_body W u e_set == <break branch>` via `choice_r_equiv` + `dfs_finish_continue_empty`. |

## Key technical findings (load-bearing for Round 3)

1. **`empty_adj` collapses everything.** `adj_verts empty_adj = 0`, so `adj_vvalid empty_adj v := (0 <= v < 0)%Z` is always `False`; hence `step_aux empty_adj e v u = adj_step_aux empty_adj e v u` is always `False`. So on this carrier, DFS never recurses and always breaks.

2. **`step_aux` / `vvalid` projection instability.** `unfold step_aux` and direct `apply (step_vvalid1 …)` fail with `Cannot find witness` because the `Graph` / `StepValid` class projections trigger unstable instance resolution under `Open Scope sets`. The robust workaround (used in every proved lemma here) is:
   - access the instance projection as a **term** first, e.g. `pose proof (AdjGraph_stepvalid.(step_vvalid1) empty_adj e v u H) as Hvv`, then
   - `change (adj_vvalid empty_adj v) in Hvv` / `change (step_aux empty_adj e v u) in H` to convert the projection to the concrete `adj_*` `Definition`, then
   - `unfold adj_vvalid` / `unfold adj_step_aux`.
   Never `unfold step_aux` directly.

3. **`==` is `Sets.equiv`; `sets_unfold` is the workhorse.** Program equivalence is set equivalence on the `(s1,a,s2)` triples. The standard tactic is `unfold_monad. sets_unfold. intros s1 a s2. split.` then handle the two inclusions. Empty-relation reasoning: after `sets_unfold`, a hypothesis `(s1,a,s2) ∈ ∅` is definitionally `False`, so `destruct H` / `exact H` closes it.

4. **`Lfix_fixpoint'` is applied, not rewritten.** Pattern (from `mergesort.v`): `unfold dfs_finish. apply (Lfix_fixpoint' (DFS_finish_f empty_adj)). unfold DFS_finish_f. mono_cont_auto.` gives `Lfix f == f (Lfix f)`. The `mono_cont_auto` tactic discharges the monotone+continuous side condition.

5. **The `from_unfold` shape.** `dfs_finish_from u done = repeat_break body (In done)`. By `repeat_break_unfold`, this is `x <- body (In done) ;; match x with by_continue a0 => repeat_break body a0 | by_break b => ret b`. The lib's RHS replaces the continue arm with `ret tt`; on `empty_adj`, `body` only yields `by_break tt` (via `dfs_finish_body_break`), so the continue arm is dead and the two sides coincide. **The open step is the relational dead-continue argument**: from `H : dfs_finish_loop_body … s1 x sm` conclude `x = by_break tt` (a `dfs_finish_body_only_break` lemma), then the match's break arm fires and `repeat_break body a`'s single-step form equals the RHS.

## What remains (Round 3 — focused, not blocked)

4 prorefine, all of the same mechanical shape once the dead-continue step lands:

1. **`dfs_finish_from_unfold`** (lib 350): LHS = `repeat_break body (In done)` single step (continue dead); RHS = `x <- loop_body ;; match continue => ret tt | break b => ret b`. Missing piece: `dfs_finish_body_only_break : dfs_finish_loop_body W u e_set s1 x sm -> x = by_break tt` (walk the break-branch bind chain to the trailing `break tt`).
2. **`dfs_finish_unfold`** (lib 342): `dfs_finish u == visit1 u ;; dfs_finish_from u nil`. Uses `Lfix_fixpoint' (DFS_finish_f empty_adj)` + `dfs_finish_body_break` + `∅ == (fun e => In e nil)` + the from_unfold result. Also needs the `DFS_finish_f` loop body's `continue (e_set ∪ singleton e)` vs lib's `continue (fun e' => e' ∈ e_set \/ e' = e)` set-representation equivalence (they denote the same set).
3. **`dfs_scc_from_unfold`** (lib 510): symmetric to `dfs_finish_from_unfold` over `dfs_scc_loop_body` (forward `step_aux empty_adj e u v`, also `False`).
4. **`dfs_scc_unfold`** (lib 502): symmetric to `dfs_finish_unfold`.

**Round 3 recommended order**: prove `dfs_finish_body_only_break` first (it plus `dfs_finish_body_break` closes `dfs_finish_from_unfold`), then `dfs_finish_unfold`, then mirror both for `dfs_scc_*`.

### Specific fragile step to nail in Round 3
`dfs_finish_body_only_break`: given `H : (s1, x, sm) ∈ dfs_finish_loop_body W u e_set`, use `dfs_finish_body_break` (`body == break_branch`) to move to `(s1,x,sm) ∈ break_branch`, then walk the bind chain (`assume ;; get ;; set_finish ;; break tt`) to the trailing `break tt = ret (by_break tt)`, which forces `x = by_break tt`. The bind-chain walk is brittle under `sets_unfold` because intermediate existentials must be peeled with the exact nesting `sets_unfold` produces. Round 2 established the pattern works (used in `dfs_finish_continue_empty`); the only remaining task is replicating it for the break branch's deeper nesting.

## Files (all absolute)

- **Scratch lib (8 prorefine target, 4 Qed + 4 Admitted, compiles EXIT=0)**: `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/scratch_lib/kosaraju_rel_lib_scratch.v` (783 lines)
- coqc wrapper for the scratch lib: `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/coqc_scratch_lib.sh`
- Round 1 proving scratch (unchanged this round, still the witness-VC home): `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/kosaraju_rel_proof_manual_scratch.v`

## Integration guidance for main agent

- The **4 Qed prorefine** (`adj_fwd_step_iff`, `adj_rev_step_iff`, `dfs_finish_from_cons`, `dfs_scc_from_cons`) are safe to back-fill into the real `/home/user/src/tarjan-coq/SeparationLogic/examples/QCP_demos_LLM/kosaraju_rel_lib.v` (frozen prefix, lines 363/380/523/540) by replacing each `admit. Admitted.` with the scratch proof and `Qed.`. They introduce **no new top-level definitions** and no `Admitted`/`Axiom`.
- The **4 still-Admitted** should NOT be back-filled yet (Round 3 will close them).
- The **6 helper lemmas** are currently *extra* lemmas in the scratch lib that the real lib does not have. Per the orchestrator rule, helper lemmas go to `task_local_scratch_lib` suffix (after the frozen prefix) only after all target VC are done. `empty_adj_no_step`, `assume_false_empty`, `bind_empty_l`, `bind_empty_r`, `dfs_finish_continue_empty`, `dfs_finish_body_break` are the Round-3 proof-pattern / helper pool; the main agent should **not** back-fill them into the real lib's frozen prefix (they belong in the helper suffix and only if Round 3 needs them as standalone lemmas rather than inlined proofs).
- **Recommendation**: do NOT back-fill the 4 in isolation. Land them together with Round 3's remaining 4 as a single lib integration, then re-run symexec/coqc, per the orchestrator one-shot rule.

## Round did NOT modify any protected/formal file

- Real `kosaraju_rel_lib.v`, `kosaraju_rel_proof_manual.v`, and all generated files untouched (read-only).
- All work is in `.tmp/kosaraju_proving/scratch_lib/` + the existing `.tmp/kosaraju_proving/` Round-1 scratch.

## Why partial (not blocked)

The remaining 4 are **not** blocked on a missing library lemma or an unsound statement. The required lemmas all exist in `MonadLib.StateRelMonad` (`Lfix_fixpoint'`, `repeat_break_unfold`, `mono_cont_auto`, `choice_r_equiv`, `bind_equiv`, `ret_equiv`) and the key semantic fact (`empty_adj` ⇒ no edges) is proved. The open work is purely the relational dead-continue bind-chain walk, which is mechanical but brittle under `Open Scope sets`. This is a time/iteration issue, not a soundness or missing-dependency issue.
