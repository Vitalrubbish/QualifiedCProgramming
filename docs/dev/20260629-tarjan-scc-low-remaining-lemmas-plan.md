# Tarjan-SCC-Low-Remaining-Lemmas-Plan
**Author**: Codex
**Date**: 2026-06-29

## 1. Current proof shape

`Tarjan_scc_is_low.v` now has most of the local low-link pipeline:

- `low_iteration_inv` / `low_iteration_entry` / `low_iteration_done`
- `process_edge_preserves_low_iteration`
- `forset_preserves_low_iteration`
- `tarjan_scc_f_keep_low_valid_from_tree_child_frame`
- `tarjan_scc_f_tree_child_frame_from_parent_pending`
- `low_tree_child_frame_contract`
- `low_tree_child_pending_contract`
- parent-frame helpers based on `active_base`
- a new `no_new_parent_except` lemma family through primitive operations, `process_edge`, `forset`, and `tarjan_scc_f`

The remaining top-level admitted theorems are:

```coq
tarjan_scc_keep_low_valid
tarjan_scc_keep_is_low
```

The proof of `tarjan_scc_keep_low_valid` should not restart from primitive low-link reasoning. The intended route is:

1. close `low_tree_child_pending_contract (tarjan_scc_f g W)`;
2. use `tarjan_scc_f_tree_child_frame_from_parent_pending` to obtain `low_tree_child_frame_contract (tarjan_scc_f g W)`;
3. feed that into `tarjan_scc_f_keep_low_valid_from_tree_child_frame`;
4. close the fixed point for `tarjan_scc`.

## 2. Lemmas still needed for `tarjan_scc_keep_low_valid`

### 2.1 Fixed-point contract combiner

The top-level fixed point needs a theorem of this shape:

```coq
Lemma tarjan_scc_f_low_contracts
      (W: V -> program (@SCCSt V) unit):
  low_tree_child_frame_contract W ->
  low_tree_child_pending_contract (tarjan_scc_f g W) ->
  low_tree_child_frame_contract (tarjan_scc_f g W).
```

This is mostly a wrapper around the existing:

```coq
tarjan_scc_f_tree_child_frame_from_parent_pending
```

Once this combiner exists, `Hoare_fix_logicv` can use:

```coq
P x tt s :=
  low_pre g root x s /\ stack_dfn_order s /\ dfn_injective s

Q x tt _ s :=
  low_valid_post g root x s /\
  x ∈ visited s /\
  stack_dfn_order s /\
  dfn_injective s
```

plus a second recursive contract carrying `low_tree_child_frame_contract`.

### 2.2 Parent-pending contract after recursive child call

The main missing Hoare statement is:

```coq
Lemma tarjan_scc_f_parent_pending_from_after_set_fa
      (W: V -> program (@SCCSt V) unit)
      (u a: V) (done: V -> Prop):
  (* required IH/frame assumptions *)
  Hoare (low_tree_child_after_set_fa u a done)
        (tarjan_scc_f g W a)
        (fun _ s => low_tree_child_parent_pending u a done s).
```

This lemma must assemble the existing parent fields:

- `wf_scc_state g root s`
- `u ∈ visited s`
- `In u (stack s)`
- `done_visited done s`
- `stack_dfn_order s`
- `dfn_injective s`
- `dg_step g u a`
- `~ done a`
- `a ∈ visited s`
- `fa s a = u`
- `fa s a <> a`

Most of these are already covered by existing helpers:

- `tarjan_scc_preserves_parent_stack_fields_from_after_set_fa`
- `tarjan_scc_preserves_done_visited_from_after_set_fa`
- `tarjan_scc_preserves_child_parent_fa_from_after_set_fa`

The remaining hard part is exactly:

```coq
low_tree_child_parent_low_fields u a done s
```

### 2.3 Preservation of parent low fields

The needed theorem should be:

```coq
Lemma tarjan_scc_f_preserves_parent_low_fields_from_after_set_fa
      (W: V -> program (@SCCSt V) unit)
      (u a: V) (done: V -> Prop):
  (* recursive assumptions *)
  Hoare (low_tree_child_after_set_fa u a done)
        (tarjan_scc_f g W a)
        (fun _ s => low_tree_child_parent_low_fields u a done s).
```

It decomposes into five preservation obligations:

```coq
low_frontier g u done s
low_src g u done s
children_low_valid g root u done s
fa_child_of_u g u s
fa_not_done_implies_eq_u u (done ∪ [a]) s
```

Expected support lemmas:

- `tarjan_scc_f_preserves_parent_low_frontier`
- `tarjan_scc_f_preserves_parent_low_src`
- `tarjan_scc_f_preserves_parent_children_low_valid`
- `tarjan_scc_f_preserves_parent_fa_child_of_u`
- `tarjan_scc_f_preserves_parent_fa_not_done`

The first two are mostly `low u` and `dfn/stack` frame facts. The third depends on preserving old done children's `scc_low_valid_v`. The last two are fa-frame obligations and are where `no_new_parent_except` is needed.

### 2.4 Closing `fa_child_of_u`

Current difficulty:

```coq
fa_child_of_u g u s :=
  forall v, fa s v = u /\ fa s v <> v -> dg_step g u v.
```

During `tarjan_scc_f g W a`, new descendants may be visited. Existing `tarjan_scc_keep_fa` only protects old visited vertices and is not enough for new descendants.

Needed lemma:

```coq
Lemma no_new_parent_except_implies_fa_child_of_u
      (u a: V) (snap s: @SCCSt V):
  fa_child_of_u g u snap ->
  dg_step g u a ->
  fa s a = u ->
  no_new_parent_except u a snap s ->
  fa_child_of_u g u s.
```

Proof split:

- if `v = a`, use `dg_step g u a`;
- if `v <> a` and `fa s v = u`, `no_new_parent_except` gives `v ∈ visited snap`;
- for old visited `v`, use a fa-stability lemma from `tarjan_scc_keep_fa` / `tarjan_scc_f` frame to rewrite `fa s v = fa snap v`;
- then apply `fa_child_of_u g u snap`.

This requires an additional old-visited fa stability theorem for `tarjan_scc_f g W a`:

```coq
Lemma tarjan_scc_f_preserves_old_visited_fa
      (W: V -> program (@SCCSt V) unit) (a: V) (snap: @SCCSt V):
  (* recursive fa-stability assumption *)
  Hoare (fun s => s = snap)
        (tarjan_scc_f g W a)
        (fun _ s => forall v, v ∈ visited snap -> fa s v = fa snap v).
```

### 2.5 Closing `fa_not_done_implies_eq_u`

Current target:

```coq
fa_not_done_implies_eq_u u (done ∪ [a]) s
```

For any `v`, assume:

```coq
~ (done ∪ [a]) v
fa s v = u
```

Need to prove `v = u`.

Use `no_new_parent_except u a snap s`:

- `v <> a` follows from `~ (done ∪ [a]) v`;
- if `v = u`, done;
- otherwise `no_new_parent_except` gives `v ∈ visited snap`;
- old-visited fa stability rewrites `fa snap v = u`;
- apply the pre-state `fa_not_done_implies_eq_u u (done ∪ [a]) snap`;
- `~ done v` follows from `~ (done ∪ [a]) v`.

Needed lemma:

```coq
Lemma no_new_parent_except_implies_fa_not_done
      (u a: V) (done: V -> Prop) (snap s: @SCCSt V):
  fa_not_done_implies_eq_u u (done ∪ [a]) snap ->
  (forall v, v ∈ visited snap -> fa s v = fa snap v) ->
  no_new_parent_except u a snap s ->
  fa_not_done_implies_eq_u u (done ∪ [a]) s.
```

### 2.6 Closing `children_low_valid`

For each old done child `v`, need to preserve:

```coq
scc_low_valid_v g root s v
```

Existing update lemmas cover `set_low` when the updated vertex is not that child, but recursive calls can add new DFS-tree descendants and update their lows. The expected statement is:

```coq
Lemma tarjan_scc_f_preserves_done_children_low_valid
      (W: V -> program (@SCCSt V) unit)
      (u a: V) (done: V -> Prop) (snap: @SCCSt V):
  Hoare (fun s =>
           s = snap /\
           children_low_valid g root u done s /\
           (* old-visited fa stability / no-new-parent frame inputs *))
        (tarjan_scc_f g W a)
        (fun _ s => children_low_valid g root u done s).
```

Likely proof strategy:

- show old done children remain old visited;
- show their outgoing tree-child set in `state_to_dfs_tree` is unchanged for children whose parent is not modified;
- use low-field preservation for those child roots, or a direct pure lemma that `scc_low_valid_v` is stable under changes outside that old child subtree.

This is probably the largest remaining proof obligation for `tarjan_scc_keep_low_valid`.

## 3. Lemmas still needed for `tarjan_scc_keep_is_low`

### 3.1 Why `tarjan_scc_keep_low_valid` is not enough

`tarjan_scc_keep_low_valid` returns only:

```coq
scc_low_valid_v g root s u
```

But the existing bridge:

```coq
scc_low_valid_implies_is_low :
  dfn_valid g s root ->
  dfn_inv s ->
  scc_low_valid g root s ->
  scc_is_low g root s
```

requires:

```coq
forall v, v ∈ visited s -> scc_low_valid_v g root s v
```

Therefore `tarjan_scc_keep_is_low` needs either a stronger program theorem or a local pure bridge.

### 3.2 Preferred stronger program theorem

Add an internal theorem that proves low-valid for the DFS subtree visited by the current call:

```coq
Definition scc_low_valid_new_subtree
           (snap s: @SCCSt V) (u: V): Prop := ...

Theorem tarjan_scc_keep_low_valid_subtree (u: V):
  Hoare (fun s => low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
        (tarjan_scc g u)
        (fun _ s =>
           low_valid_post g root u s /\
           scc_low_valid_new_subtree snap s u /\
           u ∈ visited s /\
           stack_dfn_order s /\
           dfn_injective s).
```

The definition should not demand global `scc_low_valid`, because old visited vertices may be outside this call's responsibility. It should cover:

- `u`;
- all DFS-tree descendants newly visited by the call;
- child roots whose `scc_is_low_induction_is_low` facts are needed to prove `u`.

### 3.3 Local pure bridge from subtree validity to `scc_is_low_v`

Alternative to full global `scc_low_valid`:

```coq
Lemma scc_low_valid_subtree_implies_is_low_v
      (s: @SCCSt V) (u: V):
  u ∈ visited s ->
  scc_low_valid_v g root s u ->
  (forall v,
     dg_step (state_to_dfs_tree g s root) u v ->
     scc_is_low_v_val g root s v (low s v)) ->
  scc_is_low_v g root s u.
```

This is essentially the already existing:

```coq
scc_is_low_induction_is_low
```

So the real missing data is child `scc_is_low_v_val` for all DFS-tree children of `u`. That data can be obtained if the strengthened program theorem stores child/subtree closure.

### 3.4 If choosing the global bridge route

A stronger theorem could instead establish:

```coq
forall v, v ∈ visited s -> scc_low_valid_v g root s v
```

after a full top-level traversal from an initially empty visited set. That would make `scc_low_valid_implies_is_low` directly usable. But it is too strong for the current single-call theorem, because its precondition allows arbitrary old visited vertices. This route should be avoided for `tarjan_scc_keep_is_low`.

## 4. Suggested proof order

1. Keep the current `no_new_parent_except` family, but do not try to close the global fixed point with it directly. It is a frame ingredient for parent low fields, not the main theorem.
2. Prove old-visited fa stability for `tarjan_scc_f g W a`.
3. Prove `no_new_parent_except_implies_fa_child_of_u`.
4. Prove `no_new_parent_except_implies_fa_not_done`.
5. Prove preservation of `low_frontier`, `low_src`, and `children_low_valid` for the parent during the child recursive call.
6. Assemble `tarjan_scc_f_preserves_parent_low_fields_from_after_set_fa`.
7. Assemble `tarjan_scc_f_parent_pending_from_after_set_fa`.
8. Close `low_tree_child_pending_contract (tarjan_scc_f g W)`.
9. Close `tarjan_scc_keep_low_valid`.
10. Add the subtree/child closure theorem needed by `tarjan_scc_keep_is_low`.
11. Use `scc_is_low_induction_is_low` to close `tarjan_scc_keep_is_low`.

## 5. Notes on current partial implementation

The current `no_new_parent_except` family is useful but should be used carefully:

```coq
no_new_parent_except parent root_child s0 s :=
  forall v,
    fa s v = parent ->
    v <> parent ->
    v <> root_child ->
    v ∈ visited s0.
```

It proves that a recursive call rooted below `root_child` cannot create a new non-exempt vertex whose parent is the external parent. It does not by itself prove recursive roots are different from `parent`; that proof in tree-edge branches comes from `parent ∈ visited s` and `~ child ∈ visited s`.

This is why the final fixed-point proof should avoid a bare callback:

```coq
forall y, Hoare P (W y) Q
```

when `P` requires `y <> parent`. The `y <> parent` fact is only available inside the tree-edge branch of `process_edge`, after reading `~ y ∈ visited s`.
