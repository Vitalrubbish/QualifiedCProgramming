# Tarjan_scc_is_low.v Open Issues

**Author**: Kimi Code Agent
**Date**: 2026-06-18

---

## Issue #1: Core theorems are still `Admitted`

### Status
Blocking / High Priority

### Description
`SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v` currently leaves the central Hoare theorems and their forset lemmas as `Admitted`. This prevents the file from being considered verified.

### Affected goals

| Line | Theorem / Lemma | Why it matters |
|------|-----------------|----------------|
| 638 | `process_edge_keep_low_forset_inv` | Single-step preservation of the forset low invariant |
| 656 | `forset_keep_low_forset_inv` | Lifts the invariant to the whole neighbour loop |
| 673 | `tarjan_scc_keep_low_valid` | Main recursive Hoare theorem for `tarjan_scc u` |
| 687 | `tarjan_scc_all_scc_low_valid` | Global constructive low correctness |
| 696 | `tarjan_scc_all_scc_is_low` | Final deliverable: declarative low correctness |

### Evidence
```coq
Lemma process_edge_keep_low_forset_inv (u v: V) (done: V -> Prop)
  (W: V -> program (@SCCSt V) unit):
  ...
Proof.
Admitted.
```

### Expected behavior
All five goals should be closed with real proofs, and `grep -n "Admitted" Tarjan_scc_is_low.v` should return nothing.

### Suggested fix order
1. `process_edge_keep_low_forset_inv` (the largest sub-goal)
2. `forset_keep_low_forset_inv`
3. `tarjan_scc_keep_low_valid`
4. `tarjan_scc_all_scc_low_valid`
5. `tarjan_scc_all_scc_is_low`

### Related files
- `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`
- `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_dfn.v` (reference pattern)

---

## Issue #2: `forset_keep_low_forset_inv` callback shape is weaker than `process_edge_keep_low_forset_inv`

### Status
Design / Medium Priority

### Description
The callback hypothesis of `forset_keep_low_forset_inv` is weaker than what `process_edge_keep_low_forset_inv` requires, which will force an extra strengthening step inside the forset proof.

### Current code
```coq
Lemma process_edge_keep_low_forset_inv (u v: V) (done: V -> Prop)
  (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                   (fun _ s => low_post x s /\ u ∈ visited s)) ->
  Hoare (fun s => low_forset_inv u done s)
        (process_edge u W v)
        (fun _ s => low_forset_inv u (done ∪ [v]) s).

Lemma forset_keep_low_forset_inv (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => low_pre x s) (W x) (fun _ s => low_post x s)) ->
  Hoare (fun s => low_forset_inv u ∅ s)
        (forset (fun v => dg_step g u v) (process_edge u W))
        (fun _ s => scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s).
```

### Problem
`process_edge` needs to thread `u ∈ visited s` through the recursive call `W v`, because `set_fa v u` happens before `W v` and the post-state must still know `u` is visited. `forset_keep_low_forset_inv` only assumes `low_pre x -> low_post x`, so its proof will have to manually strengthen the induction hypothesis to `low_pre x /\ u ∈ visited -> low_post x /\ u ∈ visited` (using `tarjan_scc_keep_visited`) before calling `process_edge_keep_low_forset_inv`.

### Expected behavior
Either:
- (A) Align `forset_keep_low_forset_inv`'s callback hypothesis with `process_edge_keep_low_forset_inv`:
  ```coq
  (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                   (fun _ s => low_post x s /\ u ∈ visited s))
  ```
- or (B) Keep the current weaker form but document explicitly that the proof must strengthen the IH, and provide the strengthening lemma.

### Suggested fix
Option (A) is preferred because it matches the proven pattern in `Tarjan_scc_is_dfn.v` (`forset_process_edge_keep_dfn_valid_pre`).

### Related files
- `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v` (lines 630--656)
- `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_dfn.v` (lines 1161--1194)

---

## Issue #3: Missing helper lemmas for back-edge and cross-edge branches

### Status
Proof gap / Medium Priority

### Description
The proof of `process_edge_keep_low_forset_inv` will need two DFS-timing helper lemmas that are currently not present in the file. Without them the back-edge and cross-edge sub-cases cannot be closed.

### Required helper lemmas

#### Lemma A: back-edge implies `fa s v <> u`
```coq
Lemma back_edge_fa_neq (s: @SCCSt V) (u v: V):
  dfn_inv s ->
  fa_visited s ->
  u ∈ visited s ->
  ~ v ∈ visited s ->   (* tree-edge guard *)
  ...                       (* or appropriate guard *)
  fa s v <> u.
```
Actually, the needed form for the back-edge branch is:
```coq
Lemma visited_in_stack_fa_neq_parent (s: @SCCSt V) (u v: V):
  dfn_inv s ->
  fa_visited s ->
  u ∈ visited s ->
  v ∈ visited s ->
  In v (stack s) ->
  dg_step g u v ->
  fa s v <> u.
```
Reason: if `fa s v = u`, then `v` would be a tree child of `u`. But `v` is already visited while `u` is currently being expanded, contradicting the DFS parent-before-child order.

#### Lemma B: cross-edge target is not a child of `u`
```coq
Lemma cross_edge_not_child (s: @SCCSt V) (u v: V):
  dfn_inv s ->
  fa_visited s ->
  u ∈ visited s ->
  v ∈ visited s ->
  ~ In v (stack s) ->
  dg_step g u v ->
  fa s v <> u.
```
This ensures that adding a cross-edge neighbour `v` to `done` does not accidentally enlarge `children_done s u done`.

### Impact
Both lemmas are needed to show that `back_edges_done` and `children_done` correctly partition the processed neighbours, matching the algorithm's tree/back/cross classification.

### Suggested fix
1. Prove the two lemmas above (possibly in `Tarjan_scc_basics.v` if they are generally useful, or locally in `Tarjan_scc_is_low.v`).
2. Use them inside the three branches of `process_edge_keep_low_forset_inv`.

### Related files
- `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v`
- `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_basics.v` (candidate location for reusable lemmas)

---

## Issue #4: Document/proof strategy mismatch for `scc_low_valid_implies_is_low`

### Status
Documentation / Low Priority

### Description
The design document (`docs/dev/20260617-tarjan-scc-is-low-design.md`, Section 3.4 and 4.3) states that `scc_low_valid_implies_is_low` should be proved using `rooted_tree_induction_bottom_up`. The actual implementation uses well-founded induction on `timer s - dfn s u`.

### Current code
```coq
induction n as [n IH] using (well_founded_induction (Nat.lt_wf 0)).
```

### Evaluation
The well-founded induction is logically correct because `dfn_valid` guarantees child dfn values are larger, so `timer - dfn` strictly decreases along tree edges. However, the documentation should be updated to reflect the actual strategy, or the proof should be rewritten to match the documented plan.

### Suggested fix
- Update `docs/dev/20260617-tarjan-scc-is-low-design.md` Section 3.4 / 4.3 to state that `scc_low_valid_implies_is_low` uses `well_founded_induction` on `timer s - dfn s u`.
- Or, if the project prefers the tree-induction style, refactor the proof to use `rooted_tree_induction_bottom_up`.

### Related files
- `SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v` (lines 228--255)
- `docs/dev/20260617-tarjan-scc-is-low-design.md`

---

## Summary of priorities

| Issue | Priority | Blocks final-check? |
|-------|----------|---------------------|
| #1 Core theorems admitted | High | Yes |
| #2 Callback shape mismatch | Medium | Indirectly |
| #3 Missing back/cross helpers | Medium | Yes (for Issue #1) |
| #4 Doc/proof mismatch | Low | No |

---

## How to reproduce the current state

```bash
cd /mnt/d/Rocq/QualifiedCProgramming
grep -n "Admitted" SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v
```

Expected output until fixed:
```
SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v:638:Proof.
SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v:656:Proof.
SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v:673:Proof.
SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v:687:Proof.
SeparationLogic/algorithms/Tarjan_directed/Tarjan_scc_is_low.v:696:Proof.
```

Note: the file compiles because `Admitted` is accepted by Coq, but it is not a completed proof.
