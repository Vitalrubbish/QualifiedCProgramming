# Tarjan_scc_is_low.v — Remaining Issues

**Author**: Claude Code Agent
**Date**: 2026-06-19

---

## Current Status

| Metric | Count |
|--------|-------|
| Qed (fully proved) | 29 |
| Admitted | 10 |

## Admit Breakdown by Root Cause

### Blocker 1: Stack-DFN Ordering Lemma (blocks 2 admits)

**Affected admits**: B2 set_low `fa=v`, B2 skip `fa=v`

**What's needed**:

```coq
Lemma stack_ancestor_dfn_lt (s: SCCSt) (u v: V):
  dfn_valid g s root -> dfn_inv s -> fa_visited s ->
  dg_step g u v -> In u (stack s) -> In v (stack s) ->
  dfn s v < dfn s u.
```

**Why**: To derive a contradiction when `fa s v = u` in a back-edge context.
If `fa s v = u`, then `state_to_dfs_tree_step_fa` gives a tree edge, and
`dfn_valid` gives `dfn s u < dfn s v`. But if v is on the stack with u,
v is an ancestor, so `dfn s v < dfn s u`. Contradiction.

**Proof strategy**: The stack in Tarjan's algorithm contains the DFS path
from the root to the current vertex. If both u and v are on the stack and
there's an edge u→v, then v must be an ancestor of u, implying `dfn s v < dfn s u`.
This can be proved by induction on the stack structure using `fa` parent
pointers and `dfn_valid`.

**Location**: New lemma, likely in `Tarjan_scc_basics.v`.

**Already available**: `stack_in_visited` (proved in basics), `state_to_dfs_tree_step_fa`,
`dfn_valid`, `dfn_inv`.

---

### Blocker 2: `tree_child_low_le` (blocks 1 admit)

**Affected admits**: B3 cross-edge proper child

**What's needed**: Prove `low s u ≤ low s v` when:
- `fa s v = u`, `fa s v ≠ v` (v is proper tree child of u)
- `v ∈ visited s`, `~ In v (stack s)` (v's SCC was popped)
- `low_forset_inv u done s` holds

**Why**: In the cross-edge proper-child case (`fa s v = u, fa s v ≠ v`),
`children_done` expands by `[v]`. The nested min value must remain `low s u`,
which requires `low s u ≤ low s v`.

**Proof strategy**: Temporal reasoning — when the tree edge (u,v) was processed,
`update_low u (low s v)` was called, setting `low s u := min(old, low s v)`.
Subsequent `update_low` calls can only decrease `low s u`, and `low s v`
does not change after v's SCC is popped. Thus `low s u ≤ low s v` is preserved.

Alternatively: use `dfn_valid` to get `dfn s u < dfn s v`, combined with
`low_forset_inv_implies_low_le_dfn` giving `low s u ≤ dfn s u`, and
`scc_low_valid_v s v` (from pop_scc preservation) giving `low s v ≤ dfn s v`.
Gap: need `dfn s v ≤ low s v` which is generally false.

**Location**: `Tarjan_scc_is_low.v`, line ~1120.

---

### Blocker 3: `low_forset_inv` Under Recursion (blocks 1 admit)

**Affected admits**: B1 tree-edge branch (`all: admit`)

**What's needed**: Prove that `tarjan_scc v` preserves `low_forset_inv u done`
when `u ∈ visited s`. Specifically:

```coq
Lemma low_forset_inv_preserved_by_tarjan_scc_child (u v: V) (done: V -> Prop):
  ~ v ∈ done ->
  Hoare (fun s => low_forset_inv u done s /\ low_pre v s)
        (tarjan_scc v)
        (fun _ s => low_forset_inv u done s).
```

**Why**: In the tree-edge branch of `process_edge`, after `set_fa v u`,
`tarjan_scc v` is called recursively. Before the call, `low_forset_inv u done`
holds. After the call returns, we need it to still hold so that
`update_low_tree_edge` can establish `low_forset_inv u (done ∪ [v])`.

**Proof strategy**: `tarjan_scc v` only modifies the state for v and its
descendants. The invariant `low_forset_inv u done` involves u's children
(in `children_done`) and u's back edges (in `back_edges_done`). Vertices
in these sets are not in v's subtree (they're in `done` or are ancestors).
Back edges from v's subtree to u might update `low s u`, but this only
lowers it, which preserves the min inequality.

**Location**: New lemma, likely in `Tarjan_scc_basics.v`.

---

### Blocker 4: Forset Set Equivalence (blocks 1 admit)

**Affected admits**: `forset_keep_low_forset_inv` internal conversion

**What's needed**: When `done = all neighbors of u`, prove:
- `children_done s u (all_neighbors)` ≈ `dg_step(state_to_dfs_tree g s root) u`
- `back_edges_done s u (all_neighbors) ∪ [u]` ≈ `scc_back_edge s u ∪ [u]`

**Why**: The forset postcondition gives `low_forset_inv u (all_neighbors) s`,
but we need `scc_low_valid_v s u` to return from the lemma. These are the
same nested-min structure but with different inner sets.

**Proof strategy**: Pure set-theoretic equivalence using existing lemmas:
- `state_to_dfs_tree_step_char` / `_backward` for children_done ↔ tree edges
- `scc_back_edge` definition for the back-edge part
- Need `v ∈ visited s` for children_done vertices (now available from `stack_in_visited`)

**Location**: `Tarjan_scc_is_low.v`, line ~1700.

---

## Dependency Graph

```
stack_ancestor_dfn_lt ──→ B2 fa=v (×2) ──┐
                                           ├─→ process_edge_outer ──→ DONE
tree_child_low_le ──→ B3 cross-edge ──────┤
                                           │
low_forset_inv_preserved ──→ B1 tree-edge ─┘

children_done_set_equiv ──→ forset_internal ──→ forset_outer
back_edges_set_equiv    ──→ forset_internal

scc_low_valid_preservation ──→ tarjan_scc_all_scc_low_valid
```

## Recommended Fix Order

1. `stack_ancestor_dfn_lt` — unlocks 2 admits, moderate difficulty (~50 lines)
2. `children_done_set_equiv` + `back_edges_set_equiv` — pure math, moderate (~80 lines)
3. `tree_child_low_le` — hard, temporal reasoning
4. `low_forset_inv_preserved_by_tarjan_scc` — hardest, recursive preservation

## Related Documents

- `20260619-tarjan-scc-is-low-admit-fix-checklist.md` — original fix checklist
- `20260619-stack-in-visited-lemma.md` — stack_in_visited gap analysis (now resolved)
