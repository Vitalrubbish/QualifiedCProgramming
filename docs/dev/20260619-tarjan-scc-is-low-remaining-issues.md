# Tarjan_scc_is_low.v — Remaining Issues

**Author**: Vitalrubbish
**Date**: 2026-06-19
**Last updated**: 2026-06-19 (post Phase 1–3 review)

---

## Current Status

| Metric | Before phases | After Phase 1–3 | Δ |
|--------|--------------|-----------------|---|
| Qed (fully proved) | 29 | **30** | +1 (`tree_child_low_le`) |
| Lemma-level `Admitted.` | 4 | **4** | — (`tree_child_low_le` → Qed; `popped_vertex_low_eq_dfn` new) |
| Internal subgoal `admit.` | 5 | **4** | -1 (B2 `set_low fa=v` fixed) |
| **Effective leaf admits** | **9** | **8** | **net -1** |

The 4 lemma-level `Admitted.` are now:
- `popped_vertex_low_eq_dfn` (**new**, introduced as `tree_child_low_le` dependency)
- `process_edge_keep_low_forset_inv` (contains 3 remaining internal `admit.`)
- `forset_keep_low_forset_inv` (contains 1 remaining internal `admit.`)
- `tarjan_scc_all_scc_low_valid`

The 4 internal `admit.` (L1346 `all: admit.`, L1423, L1645, L1878)
are subgoals within the enclosing lemma proofs. Filling all 4 internal
admits automatically discharges the 2 enclosing lemma-level admits
(`process_edge_keep_low_forset_inv`, `forset_keep_low_forset_inv`).

---

## What Phase 1–3 Actually Changed

### Resolved

| Admit | How | Commit |
|-------|-----|--------|
| B2 `set_low fa=v` (L1314) | Contradiction: `dfn s v < low s u` with `low s u ≤ dfn s u < dfn s v` via `dfn_valid` + `state_to_dfs_tree_step_fa` | `8aed4e6` |
| `tree_child_low_le` (lemma) | `dfn_valid` → `dfn s u < dfn s v`; `popped_vertex_low_eq_dfn` → `low s v = dfn s v`; `low_forset_inv_implies_low_le_dfn` → `low s u ≤ dfn s u`. Transitivity closes. | `409c204` |

### New

| Item | What | Why |
|------|------|-----|
| `popped_vertex_low_eq_dfn` (L1149–1160) | Lemma: `dfn_inv s → v ∈ visited s → ~ In v (stack s) → low s v = dfn s v` | Needed for `tree_child_low_le`; captures push→pop lifecycle invariant |

### Proven but not yet consumed

| Item | Status | Blocked by what |
|------|--------|-----------------|
| `back_edges_done == scc_back_edge` set equivalence | **Proved** (`d5f4351`) | — |
| `tree_child_low_le` | **Qed** (`409c204`) | Depends on `popped_vertex_low_eq_dfn` (Admitted); not applicable to B2 skip (wrong `~In v stack` precondition) |

---

## Admit-by-Admit Breakdown

### Admit A: `popped_vertex_low_eq_dfn` (NEW, L1149–1160)

**Enclosing lemma**: standalone (used by `tree_child_low_le`)

**Statement**:
```coq
Lemma popped_vertex_low_eq_dfn (s: @SCCSt V) (v: V):
  dfn_inv s -> v ∈ visited s -> ~ In v (stack s) ->
  low s v = dfn s v.
```

**What it captures**: Vertices that were visited and later popped from the
stack must have been SCC roots (`low s v = dfn s v`) at pop time, and both
values are stable after popping. Formalizing this requires reasoning about
the DFS lifecycle: vertex gets pushed onto stack when first visited; later
gets popped by `pop_scc` which requires `low = dfn`; after popping, `low`
and `dfn` are unchanged.

**Blocks**: `tree_child_low_le` (already Qed but conditional on this);
transitively blocks B3 cross-edge (which uses `tree_child_low_le`).

**Proof strategy**: Use the Hoare triple of `pop_scc` (postcondition
includes `low s x = dfn s x`) combined with the invariance of `low`/`dfn`
under `update_low`, `set_dfn`, and other operations that don't touch
already-popped vertices. The lemma `pop_scc_keep_scc_low_valid_v` (L465,
Qed) demonstrates similar temporal reasoning about `pop_scc`; analogous
machinery can be reused.

**Location**: `Tarjan_scc_is_low.v`, L1149.

**Estimated**: ~40 lines, moderate-hard.

---

### Admit B: `all: admit` — B1 tree-edge recursive preservation (L1346)

**Enclosing lemma**: `process_edge_keep_low_forset_inv` (L1313)

**Context**: In the tree-edge branch of `process_edge`, after `set_fa v u`,
`tarjan_scc v` is called recursively. Before the call, `low_forset_inv u done`
holds. After the call returns, we need to apply `update_low_tree_edge`
to establish `low_forset_inv u (done ∪ [v])`. But `update_low_tree_edge`
requires `low_forset_inv u done` as a precondition, which must have been
preserved across the recursive `tarjan_scc v` call.

**What's needed**:
```coq
Lemma low_forset_inv_preserved_by_tarjan_scc_child (u v: V) (done: V -> Prop):
  ~ v ∈ done ->
  Hoare (fun s => low_forset_inv u done s /\ low_pre v s)
        (tarjan_scc v)
        (fun _ s => low_forset_inv u done s).
```

**Why it's hard**: `tarjan_scc v` modifies state for v and its descendants.
`low_forset_inv u done` involves u's children (in `children_done`) and u's
back edges (in `back_edges_done`). We must argue that neither set is
affected by operations on v's subtree — vertices in `done` and ancestors
of u are disjoint from v's subtree. Back edges from v's subtree to u might
lower `low s u`, but this only strengthens the min inequality.

**Proof strategy**: Use an "untouched by subtree" invariant. Vertices in
`children_done u done` have `fa s w = u`, meaning they depend on u's
`set_fa` calls, not v's. `tarjan_scc v` only calls `set_fa` for vertices
under v (where `fa` gets set to some descendant-of-v vertex), never to u.
Back edges from v's descendants to u can trigger `update_low u (dfn w)`
which only decreases `low s u` — this preserves `low s u ≤ min_val` since
the min inequality becomes easier.

**Location**: New lemma, likely in `Tarjan_scc_basics.v` or `Tarjan_scc_is_low.v`.

**Estimated**: ~60 lines, hardest remaining admit.

---

### Admit C: B2 skip `fa=v` — back-edge state-unchanged case (L1423)

**Enclosing lemma**: `process_edge_keep_low_forset_inv` (L1313)

**Context**: Back-edge branch, state-unchanged subgoal (`~ dfn s0 v < low s0 u`).
When `fa s0 v = u`, the `children_done` set includes v, and we need
`low s0 u ≤ low s0 v` to show the min condition is preserved.

**Why the original dependency graph was wrong**: The document's original
dependency graph showed `tree_child_low_le → B2 skip fa=v`. But
`tree_child_low_le` requires `~ In v (stack s)` as a precondition, and
in this back-edge context **`In v (stack s)` holds**. So `tree_child_low_le`
is not applicable here, even though it's now Qed.

**Three possible approaches**:

1. **Temporal update_low argument** (simplest): When `fa s v = u` (and
   `fa s v ≠ v`), the tree edge `(u, v)` was processed earlier, calling
   `update_low u (low s v)` which set `low s u := min(old, low s v)`.
   Subsequent `update_low` calls only decrease `low s u`, so
   `low s u ≤ low s v` is preserved. This is a point-in-time inequality
   lemma about `update_low` history, not a full stack-ordering lemma.

2. **`stack_ancestor_dfn_lt`** (from original Phase 1): Prove
   `dfn s v < dfn s u` (since v is an ancestor of u on the stack).
   From `fa s v = u` and `dfn_valid`: `dfn s u < dfn s v`. Contradiction.
   This would prove the `fa = u` case is unreachable in the back-edge
   context, eliminating the need for `low s u ≤ low s v`.

3. **Structural `fa`-set argument** (from code comments): `fa s v = u`
   can only be set by the tree-edge branch of `process_edge`, which
   requires `v ∉ visited` at set time. But in the back-edge branch
   `v ∈ visited s ∧ In v (stack s)`. Since state evolves monotonically
   (visited only grows, fa only changes from unset to set), this can't
   happen — unless `fa` was already set before the current edge iteration.
   This argument requires a lemma about when `fa` can change.

**Recommendation**: Approach 1 (temporal update_low) is the most direct
and reusable; approaches 2–3 provide alternative angles if approach 1
proves too complex.

**Location**: `Tarjan_scc_is_low.v`, L1423.

**Estimated**: ~20–30 lines (approach 1), moderate.

---

### Admit D: B3 cross-edge min transfer (L1645)

**Enclosing lemma**: `process_edge_keep_low_forset_inv` (L1313)

**Context**: Cross-edge branch (v visited, not on stack), `fa s0 v = u`
and `fa s0 v ≠ v` (proper child). The children_done set expands by `[v]`.
`tree_child_low_le` gives `low s0 u ≤ low s0 v` (conditional on
`popped_vertex_low_eq_dfn`). The admit is about proving that adding
`low s0 v` to the min set doesn't change the min value.

**What's needed**: A pure set-theoretic lemma:
```coq
Lemma min_add_element (S: V -> Prop) (f: V -> nat) (a: V) (m: nat):
  min_value_of_subset Nat.le S f m ->
  m <= f a ->
  min_value_of_subset Nat.le (S ∪ [a]) f m.
```

**Blockers**:
1. `tree_child_low_le` → gives `low s0 u ≤ low s0 v` (🟡 conditional on `popped_vertex_low_eq_dfn`)
2. `min_add_element` or equivalent min-set rewriting lemma

Both blockers are independent — `min_add_element` doesn't depend on
`popped_vertex_low_eq_dfn` or any algorithm-specific invariant.

**Location**: `Tarjan_scc_is_low.v`, L1645. The min lemma belongs in
`MaxMinLib` or inline.

**Estimated**: ~15 lines for the min lemma (easy, pure set theory);
B3 admit itself ~10 lines to apply it. Total ~25 lines, moderate
(because of the transitive `popped_vertex_low_eq_dfn` dependency).

---

### Admit E: forset internal conversion — `children_done` set equivalence (L1878)

**Enclosing lemma**: `forset_keep_low_forset_inv` (L1813)

**Context**: Converting the `low_forset_inv u (all_neighbors)` postcondition
(where `all_neighbors = dg_step g u`) into `scc_low_valid_v s u`. The
`back_edges_done` half of this conversion is **already proved** (`Hback_eq`,
commit `d5f4351`). The `children_done` half remains:

```
children_done s u (dg_step g u)  ==  dg_step (state_to_dfs_tree g s root) u
```

**What this expands to**:
- LHS: `{v | dg_step g u v ∧ fa s v = u ∧ fa s v ≠ v}`
- RHS: `{v | tree edge u→v in DFS tree}`

**Proof needs**:
- **Forward** (children_done → tree edge): Given `dg_step g u v`, `fa s v = u`,
  `fa s v ≠ v`, need `dg_step (state_to_dfs_tree ...) u v`. This is exactly
  `state_to_dfs_tree_step_char_backward` (L342 in `Tarjan_scc.v`, Qed),
  plus `v ∈ visited s` which comes from `stack_in_visited s` (available in
  `low_forset_inv`).
- **Backward** (tree edge → children_done): Given `dg_step (state_to_dfs_tree ...) u v`,
  need `dg_step g u v`. This requires a "DFS tree is subgraph of original
  graph" lemma: `dg_step (state_to_dfs_tree g s root) u v → dg_step g u v`.
  Such a lemma is not yet in the codebase, but the tree is built from
  `fa` pointers which are only set for edges in the original graph — this
  is ~10 lines using the construction of `state_to_dfs_tree`.

**The `fa-implies-dg_step` invariant**: The backward direction needs to
know that `fa s v = u` (from `state_to_dfs_tree_step_char`) implies
`dg_step g u v`. The `state_to_dfs_tree_step_char_backward` lemma already
captures the converse direction. A forward version of this invariant may
need to be proved, or may already be derivable from `state_to_dfs_tree_step_char`.

**Location**: `Tarjan_scc_is_low.v`, L1878. Supporting lemmas may go in
`Tarjan_scc_basics.v` or inline.

**Estimated**: ~30 lines, moderate. This is likely the lowest-hanging fruit
because `state_to_dfs_tree_step_char` and `_backward` already provide both
directions of the tree-edge characterization; only the original-graph-edge
direction needs a small bridging lemma.

---

### Admit F: `tarjan_scc_all_scc_low_valid` (L1955–1960)

**Enclosing lemma**: standalone (outer-loop theorem)

**What's needed**: Lift the per-vertex proof `tarjan_scc_keep_low_valid`
(already Qed, L1892) over all vertices via the standard outer-loop
induction pattern established in `Tarjan_scc_is_dfn.v` (see
`tarjan_scc_all_dfn_valid` and `tarjan_scc_all_keep_dfn_inv`).

**Blockers**: Must wait until `process_edge_keep_low_forset_inv` and
`forset_keep_low_forset_inv` are fully proved (i.e., their internal admits
are resolved). The induction pattern itself is routine.

**Location**: `Tarjan_scc_is_low.v`, L1960.

**Estimated**: ~20 lines, easy (once blockers cleared).

---

## Corrected Dependency Graph

```
                           ┌─────────────────────────┐
                           │ popped_vertex_low_eq_dfn │ ← NEW Admitted
                           │ (temporal: push→pop)     │
                           └────────────┬────────────┘
                                        │ depends on
                                        ▼
                           ┌─────────────────────────┐
                           │ tree_child_low_le        │ ← Qed (conditional)
                           │ (dfn ordering argument)  │
                           └────────────┬────────────┘
                                        │ used by
                    ┌───────────────────┼───────────────┐
                    │                   │               │
                    ▼                   ▼               │
   ┌─────────────────────────┐  ┌──────────────────┐   │
   │ B3 cross-edge min trans │  │ B2 skip fa=v     │   │
   │ (L1645)                 │  │ (L1423)          │   │
   │ ALSO needs:             │  │ NEEDS temporal    │   │
   │  min_add_element lemma  │  │  update_low arg   │   │
   └────────────┬────────────┘  │  (NOT tree_child_ │   │
                │                │   low_le — wrong  │   │
                │                │   precondition!)  │   │
                │                └────────┬─────────┘   │
                │                         │             │
                ▼                         ▼             ▼
   ┌──────────────────────────────────────────────────────┐
   │ process_edge_keep_low_forset_inv (enclosing lemma)   │
   │ internal admits: B1(L1346), B2-skip(L1423), B3(L1645)│
   └──────────────────────────┬───────────────────────────┘
                              │
   ┌──────────────────────────┼───────────────────────────┐
   │                          │                           │
   ▼                          │                           │
┌─────────────────────┐        │                           │
│ children_done_set   │        │                           │
│ _equiv (L1878)      │        │                           │
│ NEEDS:              │        │                           │
│  fa→visited         │        │                           │
│  fa→dg_step         │        │                           │
└──────────┬──────────┘        │                           │
           │                    │                           │
           ▼                    │                           │
┌─────────────────────┐        │                           │
│ forset_keep_low     │        │                           │
│ _forset_inv         │        │                           │
│ (enclosing)         │        │                           │
│ Hback_eq is PROVED  │        │                           │
└──────────┬──────────┘        │                           │
           │                    │                           │
           └────────────────────┼───────────────────────────┘
                                │
                                ▼
          ┌──────────────────────────────────────┐
          │ tarjan_scc_all_scc_low_valid         │
          │ (standard outer-loop induction)      │
          └──────────────────────────────────────┘
```

**Key corrections from original document**:

1. **`tree_child_low_le` does NOT unlock B2 skip `fa=v`**: The lemma
   requires `~ In v (stack s)`, but in the back-edge branch `In v (stack s)`
   holds. A different approach (temporal update_low or stack_ancestor_dfn_lt)
   is needed.

2. **`tree_child_low_le` is only ONE of TWO blockers for B3**: The other
   is a pure set-theoretic `min_add_element` lemma.

3. **`popped_vertex_low_eq_dfn` is a new dependency**: It gates
   `tree_child_low_le` and therefore transitively gates B3.

4. **`children_done_set_equiv` is independent**: It doesn't depend on any
   of the other admits, and can be solved in parallel with them.

5. **`back_edges_done` equivalence is done**: `Hback_eq` (L1838–1870) is
   already proved, reducing the forset conversion from two gaps to one.

---

## Recommended Fix Order

Ordered by (dependency satisfaction × cost-effectiveness):

### Step 1: `children_done_set_equiv` (~30 lines, moderate)

**Why first**: Zero dependencies on other admits. Unlocks the forset
conversion admit (L1878). Uses existing lemmas `state_to_dfs_tree_step_char`
and `state_to_dfs_tree_step_char_backward` (both Qed in `Tarjan_scc.v`).

**What to do**:
```coq
Lemma children_done_eq_tree_edges (s: @SCCSt V) (u: V):
  stack_in_visited s -> fa_visited s ->
  children_done s u (dg_step g u) == dg_step (state_to_dfs_tree g s root) u.
```

This closes the forset internal admit → `forset_keep_low_forset_inv` becomes fully proved → 2 admits removed (1 internal + 1 enclosing).

### Step 2: `min_add_element` lemma (~15 lines, easy)

**Why second**: Zero dependencies. Pure set theory, no algorithm knowledge
needed. One of two blockers for B3.

**What to do**:
```coq
Lemma min_value_of_subset_add_element (S: V -> Prop) (f: V -> nat) (a: V) (m: nat):
  min_value_of_subset Nat.le S f m ->
  m <= f a ->
  min_value_of_subset Nat.le (S ∪ [a]) f m.
```

**Location**: `MaxMinLib` or inline in `Tarjan_scc_is_low.v`.

### Step 3: `popped_vertex_low_eq_dfn` (~40 lines, moderate-hard)

**Why third**: Needed to firm up `tree_child_low_le` (currently conditional)
and therefore needed for B3. Has temporal reasoning complexity but the
proof pattern (`pop_scc` postcondition → persistent) is similar to
`pop_scc_keep_scc_low_valid_v` (L465, Qed).

**Proof sketch**: Use `stack_in_visited` to get that v was pushed at some
point. Use `~ In v (stack s)` to get that v was popped by `pop_scc`.
`pop_scc`'s Hoare triple postcondition requires `low = dfn` at pop time.
Since `low` and `dfn` are only modified by `update_low` (which only lowers
low) and `set_dfn` (which only sets for unvisited vertices), they are
unchanged after popping.

### Step 4: B3 cross-edge min transfer (~10 lines, easy)

**Why fourth**: After steps 2 and 3, both blockers (`tree_child_low_le`
now fully grounded, `min_add_element` lemma available) are resolved.
Just apply the min lemma with `m = low s0 u` and `a = v`.

This closes 1 internal admit → `process_edge_keep_low_forset_inv` has
only 2 remaining internal admits (B1, B2-skip).

### Step 5: B2 skip `fa=v` (~20–30 lines, moderate)

**Why fifth**: Only one remaining back-edge admit. Use the temporal
update_low approach: prove that `fa s v = u` and `fa s v ≠ v` (and the
edge was processed) implies `low s u ≤ low s v`.

**Lemma needed**:
```coq
Lemma fa_implies_low_le (s: @SCCSt V) (u v: V):
  dfn_valid g s root -> dfn_inv s ->
  fa s v = u -> fa s v <> v -> v ∈ visited s ->
  low s u <= low s v.
```

Note: this lemma does NOT require `~ In v (stack s)` — the proof uses
the fact that `update_low u (low s v)` was called when the tree edge was
processed, establishing the inequality. This is a temporal argument but
simpler than full stack-ordering.

Alternatively, if the temporal argument proves too complex, use the
structural argument: `fa s v = u` is set by `set_fa` in the tree-edge
branch of `process_edge` which requires `v ∉ visited`; but `stack_in_visited`
gives `v ∈ visited s` in the back-edge context. Show this is contradictory
via monotonicity of visited.

This closes 1 more internal admit → `process_edge` has only B1 remaining.

### Step 6: B1 tree-edge `low_forset_inv_preserved_by_tarjan_scc_child` (~60 lines, hard)

**Why last**: Hardest remaining admit (recursive preservation), but all
other blockers are now resolved. At this point only the B1 `all: admit.`
and `tarjan_scc_all_scc_low_valid` remain.

**Approach**: Frame property — `low_forset_inv u done` is preserved across
`tarjan_scc v` because v's subtree doesn't overlap with u's `children_done`
or `back_edges_done` sets. Back edges from v's subtree to u can only
decrease `low s u`, which preserves the min inequality.

This closes the last internal admit → `process_edge_keep_low_forset_inv`
fully proved → 2 admits removed (1 internal + 1 enclosing).

### Step 7: `tarjan_scc_all_scc_low_valid` (~20 lines, easy)

**Why last**: Trivial once all upstream admits are resolved. Standard
outer-loop induction following the `tarjan_scc_all_dfn_valid` pattern.

---

## Progress Summary

| Step | What | Difficulty | Admits closed | Cumulative |
|------|------|-----------|---------------|------------|
| — | Baseline (after Phase 1–3) | — | — | 8 remaining |
| 1 | `children_done_set_equiv` | Moderate | 2 (forset internal + enclosing) | 6 |
| 2 | `min_add_element` lemma | Easy | 0 (prep for step 4) | 6 |
| 3 | `popped_vertex_low_eq_dfn` | Moderate-hard | 1 (new Admitted → Qed) | 5 |
| 4 | B3 cross-edge min transfer | Easy | 1 (B3 internal) | 4 |
| 5 | B2 skip `fa=v` | Moderate | 1 (B2-skip internal) | 3 |
| 6 | B1 tree-edge recursion | Hard | 2 (B1 internal + process_edge enclosing) | 1 |
| 7 | `tarjan_scc_all_scc_low_valid` | Easy | 1 (outer theorem) | **0** |

Steps 1–3 are independent and can be done in any order (or in parallel).
Steps 4 and 5 depend on steps 2–3 completing. Steps 6 depends on the
process_edge enclosing lemma having only B1 left. Step 7 gates on
everything above.

---

## Related Documents

- `20260619-tarjan-scc-is-low-admit-fix-checklist.md` — original fix checklist
- `20260619-stack-in-visited-lemma.md` — `stack_in_visited` gap analysis (resolved)
- `20260616-tarjan-keep-fa-visited-forset-fix.md` — forset and fa_visited fixes
- `20260618-tarjan-scc-is-low-min-lemma-issue.md` — min lemma issues (possibly solved by `min_add_element`)
- `20260618-tarjan-scc-is-low-open-issues.md` — earlier open issues snapshot
