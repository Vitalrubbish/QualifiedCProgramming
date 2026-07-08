# Kosaraju vc-proving — Round 3 Subagent Return Report

**round_outcome**: `partial`

**Subagent**: vc-proving-subagent
**Date**: 2026-06-24
**Case**: Kosaraju SCC, C-refines-monad refinement proof
**Scope**: Close the remaining 4 Admitted lib `prorefine` lemmas in `kosaraju_rel_lib.v` (frozen prefix ≤ 663), building on Round 2's 4 Qed + 6 helpers.

## Executive summary

Round 3 closed **2 of the 4 remaining prorefine** (`dfs_finish_from_unfold`, `dfs_scc_from_unfold`) and proved **2 new reusable helpers** (`dfs_finish_body_only_break`, `dfs_scc_body_only_break`) plus a **generic Σ-polymorphic `bind_break_only`**. The other 2 (`dfs_finish_unfold`, `dfs_scc_unfold`) are **blocked** on a genuine, well-characterised missing-library-lemma gap (see below), not on soundness or on the dead-continue reasoning, which is fully in hand.

**Lib prorefine scoreboard: 6 / 8 Qed, 2 / 8 Admitted.**

| Lemma | Status | Notes |
|-------|--------|-------|
| `adj_fwd_step_iff` | Qed (R2) | |
| `adj_rev_step_iff` | Qed (R2) | |
| `dfs_finish_from_cons` | Qed (R2) | vacuous |
| `dfs_scc_from_cons` | Qed (R2) | vacuous |
| `dfs_finish_from_unfold` | **Qed (R3)** | dead-continue via `dfs_finish_body_only_break` |
| `dfs_scc_from_unfold` | **Qed (R3)** | symmetric mirror |
| `dfs_finish_unfold` | **Admitted — blocked** | needs Lfix fixpoint one-step at applied form |
| `dfs_scc_unfold` | **Admitted — blocked** | symmetric mirror of above |

All of Round 3's work is coqc-verified on the scratch lib (EXIT=0).

## What was completed in Round 3 (all coqc-verified, `Qed.`)

### 2 prorefine newly Qed

- **`dfs_finish_from_unfold`** (scratch lib ~line 473). `dfs_finish_from u done` unfolds one `repeat_break` step via `Lfix_fixpoint' (repeat_break_f body)` (function-level, then specialise to `(fun e => In e done)`); the two `match` continuations are proved pointwise equal by `unfold_monad; sets_unfold; intros s1 a s2; split`, using `dfs_finish_body_only_break` to kill the dead `by_continue` arm on both sides (a body step yielding `by_continue e_set'` contradicts `body_only_break`). The `by_break` arms coincide (`return b = ret b`).
- **`dfs_scc_from_unfold`** (scratch lib ~line 755). Exact symmetric mirror over `dfs_scc_loop_body` (forward edge `step_aux empty_adj e u v`, also `False`).

### 3 new reusable helper lemmas Qed (infrastructure)

- **`bind_break_only`** (Σ-polymorphic, in `Section break_only_helpers`). `forall Ap Ab (p : program Σ Ap) s1 (x : CntOrBrk Ab unit) s2, (s1,x,s2) ∈ bind p (fun _ => break tt) -> x = by_break tt`. The generic fact that a sequence ending in `break tt` only yields `by_break tt`, regardless of `p`. This is the load-bearing helper.
- **`dfs_finish_body_only_break`** (scratch lib ~448). `forall W u e_set s1 x sm, (s1,x,sm) ∈ dfs_finish_loop_body W u e_set -> x = by_break tt`. Proof: `rewrite dfs_finish_body_break` (body == break branch) + 2 `destruct` of the break-branch bind chain (`assume ;; get ;; set_finish u t ;; break tt`) leaves `(s3,x,sm) ∈ set_finish u t ;; break tt`, then `apply bind_break_only`.
- **`dfs_scc_body_only_break`** (scratch lib ~740). Symmetric; the `dfs_scc` break branch is shallower (`assume ;; break tt`, no `get`/`set_finish`), so a single `apply bind_break_only` closes it.
- **`dfs_scc_continue_empty`**, **`dfs_scc_body_break`** (scratch lib ~699, ~724). Symmetric mirrors of `dfs_finish_continue_empty` / `dfs_finish_body_break` for the forward-graph `dfs_scc_loop_body`.

Total helper pool now (R2 + R3): `empty_adj_no_step`, `assume_false_empty`, `bind_empty_l`, `bind_empty_r`, `bind_break_only`, `dfs_finish_continue_empty`, `dfs_finish_body_break`, `dfs_finish_body_only_break`, `dfs_scc_continue_empty`, `dfs_scc_body_break`, `dfs_scc_body_only_break` — **11 helpers, all Qed**.

## Key technical finding: the dead-continue reasoning is fully cracked

Round 2 identified the missing piece as `dfs_finish_body_only_break`. Round 3 produced it via the **generic `bind_break_only`** (Σ-polymorphic, `forall Ap Ab`), which makes the relational dead-continue argument mechanical and reusable:

- `dfs_finish_loop_body W u e_set == <break branch>` (`dfs_finish_body_break`, R2), and
- any membership in `<break branch> = <prefix> ;; break tt` forces `x = by_break tt` (`bind_break_only`).

Together these close the dead-continue arm of *every* `repeat_break` from_unfold. This is why both `from_unfold` lemmas are now Qed and why `from_cons` (vacuous) was already trivial.

## What is blocked: `dfs_finish_unfold` / `dfs_scc_unfold`

Both `unfold` lemmas need to expand `dfs_finish u = Lfix (Kosaraju.DFS_finish_f empty_adj) u` by ONE fixpoint step:

```
Lfix f u  ==  (f (Lfix f)) u          (applied form)
```

i.e. `dfs_finish u == visit1 u ;; repeat_break (...) ∅`. This is structurally identical to the well-known `repeat_break_unfold` / `while_unfold` pattern in `FixpointLib.v`, which work because their goal is the **function-level** form (`repeat_break body == fun a => ...`) and `Lfix_fixpoint' f` proves that by `apply (Lfix_fixpoint' f); unfold f; mono_cont_auto`.

For `dfs_finish_unfold` the goal is the **applied** form `(Lfix f) u == (f (Lfix f)) u`. Two independent gaps block this:

1. **`mono_cont (Kosaraju.DFS_finish_f empty_adj)` cannot be discharged.** `mono_cont_auto` handles the function-level `repeat_break (fun e_set => ...)` body, but `DFS_finish_f W u` contains `repeat_break (...) ∅` — the `Lfix` is **applied to the constant `∅`**. `mono_cont_auto`'s case `mono_cont (fun W => Lfix _)` matches only the *un-applied* `Lfix`; the application `(Lfix (repeat_break_f (BODY W))) ∅` is out of scope and falls through unsolved. Building it by hand requires a `Proper (Sets.included ==> Sets.included)` / `sseq_continuous` argument for the *application* of `repeat_break`, which in turn needs a `repeat_break_proper` lemma (via `Lfix_congr`/`Lfix_mono`) that does **not exist** in the repo.

2. **No `Proper` instance for program-function application under `Sets.equiv`.** Even if the function-level equation `Lfix f == f (Lfix f)` were available, lifting it to the applied form `(Lfix f) u == (f (Lfix f)) u` needs `f == g -> f u == g u` (pointwise/resppectful on the function space `(Z*Z->Prop) -> program`). Probing `rewrite Hfg` on a goal `f u == g u` from `Hfg : f == g` leaves unresolved `pointwise_relation` / `subrelation` instance-search placeholders — there is **no registered `Proper (Sets.equiv ==> Sets.equiv)` morphism for application** of `program`-valued functions. (The `from_unfold` proofs avoid this by `specialize (Hrb arg)`, which produces the already-applied equality directly from `repeat_break_unfold`'s statement — but `repeat_break_unfold` is itself a pre-proved lemma that does not exist for `DFS_finish`.)

This is a **missing-helper / missing-instance** blocker, not a soundness issue and not a dead-continue issue. Both `unfold` lemmas are the same blocker (the `dfs_scc` one is the symmetric mirror).

### Recommended Round 4 path for the 2 unfold lemmas (concrete)

Pick ONE of:

**Option A — add a `repeat_break_proper` + `mono_cont`-for-application helper (in scratch / task_local, then lib).**
1. Prove `repeat_break_proper : forall b1 b2, b1 == b2 -> repeat_break b1 == repeat_break b2` via `Lfix_congr (repeat_break_f b1) (repeat_break_f b2)`; the per-point step needs `common_step_equiv` + a `by_break`/`by_continue` case split. (`Lfix_congr` exists in `SetsFixedpoints.v`.)
2. From it derive `mono_cont_repeat_break_const : mono_cont BODY -> mono_cont (fun W => repeat_break (BODY W) c)` for constant `c`, by unfolding `mono_cont`/`mono`/`continuous` to pointwise `Sets.included` and using `Lfix_mono`.
3. Feed that into `mono_cont (DFS_finish_f empty_adj)` so `mono_cont_auto` (or an explicit `mono_cont_bind'` + the new helper) closes it.
4. `apply (Lfix_fixpoint' (Kosaraju.DFS_finish_f empty_adj))` then gives `Lfix f == f (Lfix f)` (function level); `specialize (Hfn u)` (as done in `from_unfold`) lifts to the applied form; unfold `DFS_finish_f`, then `∅ == (fun e => In e nil)` + the break-collapse closes against `dfs_finish_from u nil`.

**Option B — add a `Proper (Sets.equiv ==> Sets.equiv)` instance for program-function application** (a `Global Instance` over `@StateRelMonad.bind`/the function space), so `rewrite` of a function-level `==` propagates through application. This is broader and would also help any other applied-Lfix reasoning in the case.

Either option touches only the helper-suffix of `task_local_scratch_lib` (after the frozen prefix) — no frozen-prefix change, no new forbidden top-level. **This is exactly the kind of work the orchestrator routes back to `vc-proving-subagent` for Round 4.**

## Files (all absolute, all in scratch — no formal file touched)

- **Scratch lib (6/8 prorefine Qed + 2/8 Admitted, EXIT=0, 2 Admitted)**:
  `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/scratch_lib/kosaraju_rel_lib_scratch.v` (820 lines)
- coqc wrapper: `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/coqc_scratch_lib.sh`
- Round 1 witness-VC scratch (unchanged): `/home/user/src/tarjan-coq/.tmp/kosaraju_proving/kosaraju_rel_proof_manual_scratch.v`

## Integration guidance for main agent

- **Do NOT back-fill yet.** The orchestrator one-shot rule says back-fill `common_case_formal_lib` only after *all* target VC are done. 2/8 prorefine are still Admitted, so the lib is not ready.
- **When Round 4 closes the 2 unfold lemmas**, the back-fill batch is:
  - **6 Qed prorefine** (`adj_fwd_step_iff`, `adj_rev_step_iff`, `dfs_finish_from_cons`, `dfs_scc_from_cons`, `dfs_finish_from_unfold`, `dfs_scc_from_unfold`) — replace each `admit. Admitted.` with the scratch proof + `Qed.` in the frozen prefix (lines ~363/380/523/540 for the R2 four; the two `from_unfold` are at their existing lib positions).
  - **2 unfold prorefine** once Round 4 Qed's them.
  - **Helper-suffix (after frozen prefix line 663)**: the `*_continue_empty`, `*_body_break`, `*_body_only_break`, `bind_break_only` helpers go to the helper-suffix (they are reusable helper lemmas, no forbidden top-level). The `empty_adj_no_step`, `assume_false_empty`, `bind_empty_l`, `bind_empty_r` are likewise helper-suffix candidates. The 2 unfold proofs may additionally need `repeat_break_proper` / `mono_cont_repeat_break_const` as Round-4 helper-suffix additions.
- **No `Admitted` / `Axiom` / forbidden top-level introduced** by the Qed work.

## Round did NOT modify any protected/formal file

- Real `kosaraju_rel_lib.v`, `kosaraju_rel_proof_manual.v`, and all generated files untouched (read-only).
- All work is in `.tmp/kosaraju_proving/scratch_lib/`.

## Why partial (not blocked-on-this-subagent)

The 2 remaining `unfold` lemmas are blocked on a **well-characterised, single missing helper** (`repeat_break_proper` / application-`Proper` morphism), with a concrete Round-4 proof path. They are NOT blocked on the dead-continue reasoning (fully Qed) or on soundness. This is a focused Round-4 task for the same `vc-proving-subagent`, exactly as Round 2 routed `body_only_break` to Round 3.
