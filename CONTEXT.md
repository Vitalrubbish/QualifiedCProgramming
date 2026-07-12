# Tarjan SCC Proof Architecture — Key Context

## 1. The Redundant `if_else` Guard

**Problem**: commit `67f4dd0` added `if_else (fun s => ~ u ∈ visited s)` to `tarjan_scc_f`, causing all fixpoint proofs to handle an unnecessary branch.

**Why redundant**: both call sites already guard against re-visiting:
- Outer: `tarjan_scc_all` uses `If (fun s => ~ v ∈ visited s) (tarjan_scc v)` 
- Inner: `process_edge` uses `if_else (fun s => ~ v ∈ visited s)` before `W v`

**Fix**: removed the guard from `tarjan_scc_f` (and reverted `tarjan_scc_f_mono_cont`). This follows Kosaraju's pattern: guards belong at call sites, not inside the recursive function body.

## 2. The `s0` vs `s0'` Problem in `frame_post`

**Original definition**:
```coq
frame_post v _ s := ∀ anc d s0', <frame at s0'> → <frame at s>
```

**Problem**: the proof decomposes execution `s0 --preloop→ s_pre --forset→ s_forset --If→ s2`. Frame hypotheses are about arbitrary `s0'` (from ∀-intro), but execution relates `s0` to `s_pre`. No connection between `s0'` and `s_pre` → 3 admits unprovable.

**Fix**: `frame_post_nf` makes `s0` an explicit parameter (removing ∀), and `frame_post_wrap` bundles it existentially for `Hoare_fix_mutual_conj` compatibility. In Step 2, `exists s1` (execution start) witnesses the existential.

## 3. Normal Form (Hoare_normal_LFix) Analysis

**When it helps**: postconditions that reference the initial state (`dfn s v = dfn s0 v`). Eliminates explicit "value" parameters like `dfnv`.

**When it doesn't**: 
- Simple preservation (`v ∈ visited s`): `hoare_fix_nolv_auto` is simpler
- Multi-invariant threading (`is_dfn.v`, `is_low.v`): complexity is in invariant structure, not fixpoint mode

**Infrastructure added** to `Tarjan_scc_basics.v`:
- `Hoare_normalize`, `Hoare_normal_assume_bind`
- `Hoare_normal_LFix`, `Hoare_normal_LFix_closed`

## 4. Fixpoint Patterns by File

| File | Pattern | Why |
|------|---------|-----|
| `Tarjan_scc_basics.v` | `hoare_fix_nolv_auto` | Postconditions don't reference `s0`; simplest |
| `Tarjan_scc_is_dfn.v` | `Hoare_fix_logicv_conj` | Multi-invariant threading (visited + fa_visited + dfn_valid) |
| `Tarjan_scc_is_low.v` | `Hoare_fix_mutual_conj` | Mutual induction for low-post + frame post, custom ∃/∀ encoding |

## 5. Remaining Work

| Item | File | Status |
|------|------|--------|
| `frame_IH_to_hw_frame` | `is_low.v` | Admitted — existential wrapper can't guarantee `s0_wrap = s0` |
| Admit A (preloop) | `is_low.v` | Structurally fillable — `s1` now equals frame reference state |
| Admit B (forset) | `is_low.v` | Needs forset frame-threading lemma |
| Admit C (If/pop_scc) | `is_low.v` | Needs pop_scc frame-preservation lemma |
| `tarjan_scc_all_scc_is_low` | `is_low.v` | Not yet stated/proved |
