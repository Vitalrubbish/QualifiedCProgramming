Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From MaxMinLib Require Import MaxMin Interface.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn.

Import SetsNotation.
Local Open Scope sets.

Section LOW_DEFS.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  (* ================================================================ *)
  (* Public low-link specifications                                  *)
  (* ================================================================ *)

  Definition scc_back_edge (s: @SCCSt V) (x y: V): Prop :=
    dg_step g x y /\
    In y (stack s) /\
    ~ dg_step (state_to_dfs_tree g s root) x y.

  Definition scc_low_reachable (s: @SCCSt V) (x y: V): Prop :=
    exists z,
      dg_reachable (state_to_dfs_tree g s root) x z /\
      (z = y \/ scc_back_edge s z y).

  Definition scc_low_tree (s: @SCCSt V) (x: V): V -> Prop :=
    fun y => scc_low_reachable s x y.

  Definition scc_is_low_v_val (s: @SCCSt V) (u: V) (n: nat): Prop :=
    min_value_of_subset Nat.le (scc_low_tree s u) (dfn s) n.

  Definition scc_is_low_v (s: @SCCSt V) (u: V): Prop :=
    scc_is_low_v_val s u (low s u).

  Definition scc_low_valid_v (s: @SCCSt V) (u: V): Prop :=
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (dg_step (state_to_dfs_tree g s root) u) (low s) ∪
       min_value_of_subset Nat.le (scc_back_edge s u ∪ [u]) (dfn s))
      (fun x => x) (low s u).

  Definition scc_is_low (s: @SCCSt V): Prop :=
    forall v, v ∈ visited s -> scc_is_low_v s v.

  Definition scc_low_valid (s: @SCCSt V): Prop :=
    forall v, v ∈ visited s -> scc_low_valid_v s v.

  Definition low_pre (u: V) (s: @SCCSt V): Prop :=
    wf_scc_state g root s /\ ~ u ∈ visited s.

  Definition low_valid_post (u: V) (s: @SCCSt V): Prop :=
    wf_scc_state g root s /\ scc_low_valid_v s u.

  Definition low_post (u: V) (s: @SCCSt V): Prop :=
    wf_scc_state g root s /\ scc_is_low_v s u.

  (* ================================================================ *)
  (* Local forset specifications                                     *)
  (* ================================================================ *)

  Definition done_visited (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall w, done w -> w ∈ visited s.

  Definition fa_child_of_u (u: V) (s: @SCCSt V): Prop :=
    forall v, fa s v = u /\ fa s v <> v -> dg_step g u v.

  Definition fa_not_done_implies_eq_u
             (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall v, ~ done v -> fa s v = u -> v = u.

  Definition low_frontier (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    low s u <= dfn s u /\
    forall v, done v -> dg_step g u v ->
      (fa s v = u -> low s u <= low s v) /\
      (In v (stack s) -> low s u <= dfn s v).

  Definition low_src (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
       low s u = dfn s u
    \/ (exists v,
          done v /\ dg_step g u v /\
          fa s v = u /\ fa s v <> v /\ low s u = low s v)
    \/ (exists w,
          done w /\ dg_step g u w /\
          In w (stack s) /\ fa s w <> u /\ low s u = dfn s w).

  Definition children_low_valid
             (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall v, done v -> dg_step g u v ->
      fa s v = u -> fa s v <> v -> scc_low_valid_v s v.

  Definition low_iteration_inv
             (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    wf_scc_state g root s /\
    u ∈ visited s /\
    In u (stack s) /\
    done_visited done s /\
    low_frontier u done s /\
    low_src u done s /\
    children_low_valid u done s /\
    fa_child_of_u u s /\
    fa_not_done_implies_eq_u u done s.

  Definition low_iteration_entry (u: V) (s: @SCCSt V): Prop :=
    low_iteration_inv u ∅ s /\
    stack_dfn_order s /\
    dfn_injective s.

  Definition low_iteration_done (u: V) (s: @SCCSt V): Prop :=
    low_iteration_inv u (dg_step g u) s /\
    stack_dfn_order s /\
    dfn_injective s.

End LOW_DEFS.
