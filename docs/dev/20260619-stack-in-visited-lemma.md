# Stack-in-visited Lemma Needed

**Author**: Claude Code Agent
**Date**: 2026-06-19

---

## Problem

The `Tarjan_scc_is_low.v` proof has 2 admits (B2 set_low `fa=v`, B2 skip `fa=v`) that
require the lemma:

```coq
Lemma stack_impl_visited (s: SCCSt) (v: V):
  In v (stack s) -> v ∈ visited s.
```

This lemma states that any vertex on the DFS stack has been visited.
It is needed to derive a contradiction when `fa s v = u` in a back-edge
context (see `process_edge_keep_low_forset_inv`).

## Current State

- `stack_in_visited` is **defined** in `Tarjan_scc_basics.v` (line 55) but
  **never proved** for any state.
- It is part of `basics_invariant` (line 64-71) which is also defined but
  never established as an invariant.
- No lemma in the entire codebase connects `In v (stack s)` to `v ∈ visited s`.

## Proof Strategy

The invariant follows from the fact that `push_stack v` is only called in
`preloop v`, which first calls `visit v`. Since visitedness is monotonic
(never removed), any vertex on the stack was visited when pushed.

Needed lemmas (to be added to `Tarjan_scc_basics.v`):

1. `push_stack_preserves_stack_in_visited`:
   ```coq
   Lemma push_stack_preserves_stack_in_visited (v: V):
     Hoare (fun s => stack_in_visited s /\ v ∈ visited s)
           (push_stack v)
           (fun _ s => stack_in_visited s).
   ```

2. `stack_in_visited_init`: `stack_in_visited initSt`.

3. Preservation through `pop_scc`, `preloop`, `update_low`, `set_fa`, etc.

Alternatively, a simpler standalone lemma:

```coq
Lemma stack_in_visited_holds (s: SCCSt) (v: V):
  reachable_state s -> In v (stack s) -> v ∈ visited s.
```

## Impact

Unblocks 2 admits in `Tarjan_scc_is_low.v` (B2 `fa=v` cases).
Combined with `state_to_dfs_tree_step_fa` + `dfn_valid`, these cases
can be eliminated by contradiction.

## Related

- `docs/dev/20260619-tarjan-scc-is-low-admit-fix-checklist.md` — Step 0.3
