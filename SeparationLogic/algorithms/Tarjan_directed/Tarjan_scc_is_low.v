Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From MaxMinLib Require Import MaxMin Interface.
From RecordUpdate Require Import RecordSet.
From Algorithms.Tarjan_directed Require Import SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section IS_LOW.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  (* ================================================================ *)
  (* 1. SCC Low Correctness Definitions                               *)
  (* ================================================================ *)

  Definition scc_back_edge (s: @SCCSt V) (x y: V): Prop :=
    dg_step g x y /\
    In y (stack s) /\
    ~ dg_step (state_to_dfs_tree g s root) x y.

  Definition scc_low_valid_v (s: @SCCSt V) (u: V): Prop :=
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (dg_step (state_to_dfs_tree g s root) u) (low s) ∪
       min_value_of_subset Nat.le (scc_back_edge s u ∪ [u]) (dfn s))
      (fun x => x) (low s u).

  Definition scc_low_valid (s: @SCCSt V): Prop :=
    forall v, v ∈ visited s -> scc_low_valid_v s v.

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

  Definition scc_is_low (s: @SCCSt V): Prop :=
    forall v, v ∈ visited s -> scc_is_low_v s v.

  (* ================================================================ *)
  (* 2. SCC Low Witness / Bound Lemmas                                *)
  (* ================================================================ *)
(** * Framework overview for the low-link correctness proof

    The file is organized into the following layers:

    1. [SCC-low definitions and induction lemmas]
       ([scc_low_witness], [scc_low_bound], [scc_low_valid_induction], ...)
       Define [scc_low_valid_v] and show that it implies the global
       [scc_is_low] property.

    2. [Empty-set and low-equals-dfn facts]
       ([preloop_low_eq_dfn], [children_done_empty], [low_eq_dfn_to_min_empty])
       Small algebraic facts used when a vertex has no processed children
       or back edges.

    3. [Primitive-operation invariants]
       ([preloop_establishes_low_forset_inv], [pop_scc_keep_scc_low_valid_v],
       [children_done_add], ...)
       What each basic state transition does to the components of
       [low_forset_inv].

    4. [set_fa / set_low helpers]
       ([set_fa_preserves_low_pre_rich], [set_low_preserves_low_forset_inv])
       Hoare lemmas for the two assignment primitives.

    5. [update_low concrete cases]
       ([update_low_tree_edge], [update_low_back_edge])
       Reasoning about how [low] is updated on tree edges and back edges.

    6. [low_forset_inv for "other" vertices]
       Lemmas showing that operations on vertex [a] preserve
       [low_forset_inv u done] for [u <> a].

    7. [fa preservation]
       Each transition preserves the [fa] relation for vertices already
       assigned a parent.

    8. [Min-value, visited, and done-visited preservation]
       ([set_fa_preserves_min], [pop_scc_preserves_done_visited], ...)

    9. [Ancestor preservation]
       ([pop_scc_preserves_ancestor_inv], [preloop_preserves_ancestor_inv])
       Preservation of [low_forset_inv] along the parent chain.

    10. [Stack ordering]
        Structural lemmas about [stack_split_at] and dfn ordering on the
        DFS stack.

    11. [W preserves ancestor invariant]
        ([W_preserves_ancestor_inv])
        Combining the above to show a recursive call preserves the
        ancestor invariant.

    12. [Properness]
        ([low_forset_inv_proper], ...)
        Setoid properness needed for the forset fixpoint rule.

    13. [fa_children and full_eq]
        Lemmas connecting [children_done] / [back_edges_done] with their
        unrestricted versions.

    14. [Convergence to scc_low_valid_v]
        ([low_forset_inv_to_scc_low_valid], [forset_keep_low_forset_inv])
        Closing the loop: after the forset over children, [scc_low_valid_v]
        holds.

    15. [Main theorems]
        ([tarjan_scc_keep_low_valid], [tarjan_scc_all_scc_low_valid],
        [tarjan_scc_all_scc_is_low]). *)


  Lemma scc_low_witness (s: @SCCSt V) (w: V) (n: nat):
    scc_is_low_v_val s w n ->
    exists x, scc_low_tree s w x /\ dfn s x = n.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma scc_low_bound (s: @SCCSt V) (w: V) (n: nat) (x: V):
    scc_is_low_v_val s w n ->
    scc_low_tree s w x ->
    n <= dfn s x.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (* ================================================================ *)
  (* 3. Helper Lemma: First Step Decomposition                        *)
  (* ================================================================ *)

  Lemma dg_reachable_first_step (T: OriginalGraphType V E) (u z: V):
    dg_reachable T u z ->
    u = z \/ exists v, dg_step T u v /\ dg_reachable T v z.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (* ================================================================ *)
  (* 4. SCC Low Tree Decomposition                                    *)
  (* ================================================================ *)

  Lemma scc_low_tree_decompose (s: @SCCSt V) (u: V):
    u ∈ visited s ->
    scc_low_tree s u ==
    [u] ∪ scc_back_edge s u ∪
    (fun w => exists v,
      dg_step (state_to_dfs_tree g s root) u v /\
      scc_low_tree s v w).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (* ================================================================ *)
  (* 5. SCC Low Induction Lemmas                                      *)
  (* ================================================================ *)

  Lemma scc_low_valid_induction (s: @SCCSt V) (u: V)
    (IHu: forall v,
      dg_step (state_to_dfs_tree g s root) u v ->
      scc_is_low_v_val s v (low s v)):
    min_value_of_subset Nat.le
      (dg_step (state_to_dfs_tree g s root) u) (low s) ==
    min_value_of_subset Nat.le
      ((fun w => exists v,
        dg_step (state_to_dfs_tree g s root) u v /\
        scc_low_tree s v w))
      (dfn s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma scc_low_valid_induction_is_low (s: @SCCSt V) (u: V)
    (Hu: u ∈ visited s)
    (IHu: forall v,
      dg_step (state_to_dfs_tree g s root) u v ->
      scc_is_low_v_val s v (low s v)):
    scc_low_valid_v s u -> scc_is_low_v s u.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma scc_low_valid_implies_is_low (s: @SCCSt V):
    dfn_valid g s root -> dfn_inv s ->
    scc_low_valid s -> scc_is_low s.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.
  (** * Well-formed SCC state abstraction

      We bundle the four global invariants that are preserved by every
      primitive operation.  This makes later Hoare triples more compact
      and emphasizes that the four predicates are maintained together. *)

  Definition wf_scc_state (s: @SCCSt V): Prop :=
    stack_in_visited s /\ dfn_inv s /\ dfn_valid g s root /\ fa_visited s.

  Lemma pop_scc_preserves_wf_scc_state (u: V):
    Hoare (fun s: @SCCSt V => wf_scc_state s)
          (pop_scc u)
          (fun _ s => wf_scc_state s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.


  (* ================================================================ *)
  (* 6. Invariant Definitions                                         *)
  (* ================================================================ *)

  Ltac unfold_op :=
    unfold visit, set_dfn, set_low, set_fa, incr_timer,
           push_stack, update_low, pop_scc.

  Definition children_done (s: @SCCSt V) (u: V) (done: V -> Prop) (v: V): Prop :=
    v ∈ done /\ fa s v = u /\ fa s v <> v.

  Definition children_done_visited (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall v, children_done s u done v -> v ∈ visited s.

  Definition done_visited (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall w, done w -> w ∈ visited s.

  Definition back_edges_done (s: @SCCSt V) (u: V) (done: V -> Prop) (v: V): Prop :=
    v ∈ done /\ In v (stack s) /\ fa s v <> u.

  Definition low_forset_inv (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    stack_in_visited s /\
    dfn_inv s /\
    dfn_valid g s root /\
    fa_visited s /\
    u ∈ visited s /\
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
       min_value_of_subset Nat.le
         (fun w => back_edges_done s u done w \/ w = u) (dfn s))
      (fun x => x) (low s u).

  Definition low_pre (u: V) (s: @SCCSt V): Prop :=
    stack_in_visited s /\ ~ u ∈ visited s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s.

  Definition low_post (u: V) (s: @SCCSt V): Prop :=
    scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s.

  (* ================================================================ *)
  (* 6.5. Fa Constraint Lemmas (Phase 1)                               *)
  (* ================================================================ *)

  (** [low_pre_fa_eq_u_implies_eq_u]: In the [low_pre u s] state
      (u is not yet visited), no vertex has [fa = u] except possibly u
      itself.  This follows from [fa_visited s]: if [fa s v ≠ v] then
      [fa s v ∈ visited s]; since [~ u ∈ visited s], [fa s v] cannot
      equal [u] when [v ≠ u]. *)
  Lemma low_pre_fa_eq_u_implies_eq_u (u v: V) (s: @SCCSt V):
    low_pre u s -> fa s v = u -> v = u.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma low_pre_no_fa_child_of_u (u v: V) (s: @SCCSt V):
    low_pre u s -> ~ (fa s v = u /\ fa s v <> v).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (* ================================================================ *)
  (* 7. Preloop Establishes Low Forset Invariant                      *)
  (* ================================================================ *)

  Lemma preloop_low_eq_dfn (u: V):
    Hoare (fun s: @SCCSt V => True)
          (preloop u)
          (fun _ s => low s u = dfn s u).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma children_done_empty (s: @SCCSt V) (u: V):
    children_done s u ∅ == ∅.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma back_edges_done_empty_char (s: @SCCSt V) (u: V):
    (fun w => back_edges_done s u ∅ w \/ w = u) == [u].
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma low_eq_dfn_to_min_empty (u: V) (s: @SCCSt V):
    low s u = dfn s u ->
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
       min_value_of_subset Nat.le (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
      (fun x => x) (low s u).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma preloop_establishes_low_forset_inv (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s)
          (preloop u)
          (fun _ s => low_forset_inv u ∅ s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (* ================================================================ *)
  (* 8. pop_scc Preserves Low Valid                                   *)
  (* ================================================================ *)

  (** [stack_split_at_partition]: [stack_split_at stk v] splits the stack
      into [popped] and [rest]; every element of the original stack is in
      exactly one of the two parts, and [rest] is included in the original
      stack.  This merges the previous three separate characterizations. *)
  Lemma stack_split_at_partition (stk: list V) (v: V)
    (popped rest: list V):
    stack_split_at stk v = (popped, rest) ->
    (forall w, In w rest -> In w stk) /\
    (forall w, In w stk -> ~ In w popped -> In w rest) /\
    (forall w, In w stk -> In w popped \/ In w rest).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma scc_low_valid_v_low_eq_dfn_implies_dfn_le_back_edge_dfn (s: @SCCSt V) (u w: V):
    scc_low_valid_v s u ->
    low s u = dfn s u ->
    scc_back_edge s u w ->
    dfn s u <= dfn s w.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma pop_scc_keep_scc_low_valid_v (u: V):
    Hoare (fun s: @SCCSt V =>
      scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s /\
      low s u = dfn s u)
          (pop_scc u)
          (fun _ s => scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (* ================================================================ *)
  (* 9. Set Decomposition Lemmas (needed for process_edge)            *)
  (* ================================================================ *)

  Lemma children_done_add (s: @SCCSt V) (u v: V) (done: V -> Prop):
    fa s v = u -> fa s v <> v ->
    children_done s u (done ∪ [v]) == children_done s u done ∪ [v].
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma children_done_no_add (s: @SCCSt V) (u v: V) (done: V -> Prop):
    fa s v <> u ->
    children_done s u (done ∪ [v]) == children_done s u done.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma back_edges_done_add (s: @SCCSt V) (u v: V) (done: V -> Prop):
    In v (stack s) -> fa s v <> u ->
    back_edges_done s u (done ∪ [v]) == back_edges_done s u done ∪ [v].
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma back_edges_done_no_add (s: @SCCSt V) (u v: V) (done: V -> Prop):
    ~ In v (stack s) \/ fa s v = u ->
    back_edges_done s u (done ∪ [v]) == back_edges_done s u done.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (* ================================================================ *)
  (* 10. process_edge Preserves low_forset_inv                         *)
  (* ================================================================ *)

  Lemma set_fa_preserves_low_pre_rich (v u: V):
    Hoare (fun s: @SCCSt V => low_pre v s /\ u ∈ visited s)
          (set_fa v u)
          (fun _ s => low_pre v s /\ u ∈ visited s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [set_low_keep_low_forset_inv_components]: [set_low u n] only
      modifies [low]; all other fields are unchanged. *)
  Lemma set_low_keep_low_forset_inv_components (u: V) (n: nat):
    Hoare (fun s: @SCCSt V => dfn_inv s /\ dfn_valid g s root /\ fa_visited s /\ u ∈ visited s)
          (set_low u n)
          (fun _ s => dfn_inv s /\ dfn_valid g s root /\ fa_visited s /\ u ∈ visited s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma set_low_preserves_low_forset_inv (u v: V) (done: V -> Prop) (n: nat):
    u <> v -> ~ done v ->
    Hoare (fun s: @SCCSt V => low_forset_inv u done s)
          (set_low v n)
          (fun _ s => low_forset_inv u done s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [update_low_tree_edge]: specialized lemma for the tree-edge case.
      After [get' low v], we call [update_low u (low v)]. This lemma
      proves that [low_forset_inv] is preserved. *)
  Lemma update_low_tree_edge (u v: V) (done: V -> Prop) (s: @SCCSt V):
    fa s v = u -> fa s v <> v ->
    low_forset_inv u done s ->
    low_forset_inv u (done ∪ [v])
      (RecordSet.set low (fun low0 x => if equiv_decb x u then Nat.min (low s u) (low s v) else low0 x) s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma low_forset_inv_implies_low_le_dfn (u: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s -> low s u <= dfn s u.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma update_low_back_edge (u v: V) (done: V -> Prop) (s: @SCCSt V):
    dg_step g u v ->
    In v (stack s) ->
    done ⊆ visited s ->
    v ∈ done \/ fa s v <> u ->
    low_forset_inv u done s ->
    low_forset_inv u (done ∪ [v])
      (RecordSet.set low (fun low0 x => if equiv_decb x u then Nat.min (low s u) (dfn s v) else low0 x) s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.


  Lemma low_forset_inv_children_done_low_le (u v: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s ->
    children_done s u done v ->
    low s u <= low s v.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [low_forset_inv_expand_child_done]: When [v] is a proper child
      of [u] ([fa s v = u], [fa s v ≠ v]) and [low s u ≤ low s v],
      expanding [done] to [done ∪ [v]] preserves [low_forset_inv].
      The proof uses [min_value_of_subset_nested_update_left_nat]
      because [children_done] expands by [v] while [back_edges_done]
      is unchanged (handled separately by the caller). *)
  Lemma low_forset_inv_expand_child_done (u v: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s ->
    fa s v = u -> fa s v <> v ->
    low s u <= low s v ->
    low_forset_inv u (done ∪ [v]) s.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.



  (** [process_edge_preserves_ancestor_inv]: [process_edge v W x]
      processes one neighbor [x] of [v].  The operations on [v]'s
      edges do not modify [fa] for [u]'s done vertices, [low u],
      or [fa v]. *)
  (** [update_low_preserves_low_forset_inv_for_other]: When [~ done v],
      [update_low v n] does not affect [low_forset_inv u done] because [v]
      is not in [children_done s u done] (requires [v ∈ done]) nor in
      [back_edges_done s u done] (requires [fa s v ≠ u], but here
      [fa s v = u]).  The key proof obligation is that changing [low v]
      does not shift the minimum over [children_done] or [back_edges_done]
      since [v] appears in neither set. *)
  Lemma update_low_preserves_low_forset_inv_for_other (u v: V) (n: nat) (done: V -> Prop) (s: @SCCSt V):
    u <> v ->
    ~ done v ->
    low_forset_inv u done s ->
    low_forset_inv u done (RecordSet.set low (fun low0 x => if equiv_decb x v then Nat.min (low s v) n else low0 x) s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.


  (** [set_fa_preserves_low_forset_inv_for_new_child]: When [~ x ∈ visited],
      [u ∈ visited], and [~ done v], setting [fa x := v] does not affect
      [low_forset_inv u done].  The key insight: [x ≠ u] (since x is
      unvisited but u is visited), so [children_done u done] (which requires
      [fa = u]) and [back_edges_done u done] are unchanged. *)
  Lemma set_fa_preserves_low_forset_inv_for_new_child (u v x: V) (done: V -> Prop) (s0: @SCCSt V):
    ~ x ∈ visited s0 -> v ∈ visited s0 -> u ∈ visited s0 -> ~ done v -> ~ done x ->
    low_forset_inv u done s0 ->
    low_forset_inv u done (RecordSet.set fa (fun _ x0 => if equiv_decb x0 x then v else fa s0 x0) s0).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.







  (** [preloop_keeps_low_forset_inv_other]: [preloop a] preserves
      [low_forset_inv u done] when [~a in visited].  Extracted from the
      first branch of [preloop_preserves_ancestor_inv] (Qed, line 1620). *)
  Lemma preloop_keeps_low_forset_inv_other (u a: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\ ~ a ∈ visited s /\ ~ done a)
          (preloop a)
          (fun _ s => low_forset_inv u done s /\ a ∈ visited s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [pop_scc_keeps_low_forset_inv_other]: [pop_scc a] preserves
      [low_forset_inv u done].  Extracted from the first branch of
      [pop_scc_preserves_ancestor_inv] (Qed, line 1514). *)
  Lemma pop_scc_keeps_low_forset_inv_other (u a: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\
                   In a (stack s) /\
                   (forall w, done w -> forall popped' rest',
                     stack_split_at (stack s) a = (popped', rest') -> ~ In w popped'))
          (pop_scc a)
          (fun _ s => low_forset_inv u done s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [preloop_keeps_fa]: [preloop a] does not modify the [fa] field,
      so [fa s a = p] is preserved. *)
  Lemma preloop_keeps_fa (a p: V):
    Hoare (fun s => fa s a = p)
          (preloop a)
          (fun _ s => fa s a = p /\ a ∈ visited s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [forset_keeps_fa]: [forset (process_edge a W)] preserves
      [fa s v = parent] given the fixpoint IH. *)
  (** [process_edge_keeps_fa_simple]: [process_edge a W x] does not
      change [fa s v = parent] when [v] is visited (so [set_fa x a]
      with [x ≠ v] doesn't affect [fa v]). *)
  Lemma process_edge_keeps_fa_simple (a x v parent: V)
    (W: V -> program (@SCCSt V) unit)
    (IH_fa: forall y, Hoare (fun s => fa s v = parent) (W y) (fun _ s => fa s v = parent))
    (IH_vis: forall y, Hoare (fun s => v ∈ visited s) (W y) (fun _ s => v ∈ visited s)):
    Hoare (fun s => fa s v = parent /\ v ∈ visited s)
          (process_edge a W x)
          (fun _ s => fa s v = parent /\ v ∈ visited s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.






  Lemma forset_keeps_fa (a v parent: V)
    (W: V -> program (@SCCSt V) unit)
    (IH_fa: forall y, Hoare (fun s => fa s v = parent) (W y) (fun _ s => fa s v = parent))
    (IH_vis: forall y, Hoare (fun s => v ∈ visited s) (W y) (fun _ s => v ∈ visited s)):
    Hoare (fun s => fa s v = parent /\ a ∈ visited s /\ v ∈ visited s)
          (forset (fun w => dg_step g a w) (process_edge a W))
          (fun _ s => fa s v = parent).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.












  (** [set_fa_W_preserves_low_forset_inv]: key lemma for the tree edge
      branch of [process_edge_keep_low_forset_inv].  After [set_fa v u]
      (which sets [fa v := u]) followed by the recursive call [W v]
      (which is [tarjan_scc g v]), both [low_forset_inv u done] and
      [fa s v = u] are preserved.

      Proof sketch (requires 2 sub-lemmas):
      1. [set_fa_preserves_low_forset_inv]: set_fa v u does not change
         children_done/back_edges_done (v ∉ done), fa_visited preserved
         via u ∈ visited, stack/dfn/low unchanged.
      2. [W_preserves_low_forset_inv_and_fa]: W v (tarjan_scc g v) does
         not modify fa v (only sets fa for v's descendants), does not
         modify low u (only update_low on v/descendants), children_done
         and back_edges_done for done vertices unchanged (done vertices
         are not descendants of v). Proved by fixpoint induction on
         tarjan_scc, adding a new visited_tag constructor. *)
  Lemma set_fa_preserves_min (u v: V) (done: V -> Prop) (s0: @SCCSt V): ~ done v ->
    min_value_of_subset Nat.le (min_value_of_subset Nat.le (children_done s0 u done) (low s0) ∪ min_value_of_subset Nat.le (fun w => back_edges_done s0 u done w \/ w = u) (dfn s0)) (fun x => x) (low s0 u) ->
    min_value_of_subset Nat.le (min_value_of_subset Nat.le (children_done (RecordSet.set fa (fun _ x => if equiv_decb x v then u else fa s0 x) s0) u done) (low s0) ∪ min_value_of_subset Nat.le (fun w => back_edges_done (RecordSet.set fa (fun _ x => if equiv_decb x v then u else fa s0 x) s0) u done w \/ w = u) (dfn s0)) (fun x => x) (low s0 u).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [pop_scc_preserves_done_visited]: [pop_scc a] does not modify
      [visited] (only [stack] and [sccs]), so [done_visited done] is
      trivially preserved.

      Note: [tarjan_scc_keep_visited] is already available in
      [Tarjan_scc_basics]; the local duplicate has been removed. *)
  Lemma pop_scc_preserves_done_visited (a: V) (done: V -> Prop):
    Hoare (fun s => done_visited done s) (pop_scc a) (fun _ s => done_visited done s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (* ================================================================ *)
  (* 10.5. Ancestor Invariant Preservation Lemmas                      *)
  (* ================================================================ *)

  (** Lemmas to prove that operations on vertex [v] preserve
      [low_forset_inv u done] and [fa s v = u] for an ancestor [u].
      These are the building blocks for [W_preserves_ancestor_inv]. *)

  (** [pop_scc_preserves_ancestor_inv]: [pop_scc v] only modifies
      [stack] and [sccs]; [fa], [low], [dfn], [visited] unchanged. *)
  Lemma pop_scc_preserves_ancestor_inv (u v: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ done v /\
                   dg_step g u v /\ In v (stack s) /\
                   forall w, done w -> forall popped' rest',
                     stack_split_at (stack s) v = (popped', rest') ->
                     ~ In w popped')
          (pop_scc v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [preloop_preserves_ancestor_inv]: [preloop v] modifies [dfn v],
      [low v], [timer], [stack], [visited] — all local to [v].
      No effect on [fa], [low] for [u ≠ v], or [done] vertices. *)
  Lemma preloop_preserves_ancestor_inv (u v: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v)
          (preloop v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [done_not_popped_by_subtree_pop_scc]: Under [low_forset_inv u done s]
      with [done_visited done s] and [~ done a], when [pop_scc a] splits
      the stack at [a], no vertex from [done] appears in the popped
      portion.  This holds because [done] vertices are ancestors processed
      before the current DFS subtree, hence are below [a] on the stack
      or already removed.

      Strengthened with [In a (stack s)] (a is on the stack) and
      [forall w, done w -> In w (stack s) -> dfn s w < dfn s a]
      (done vertices that are on the stack have smaller dfn than a,
      hence are below a). *)
  (** [stack_split_at_in_popped_before_a]: If [w] is in [popped] from
      [stack_split_at stk a], and [w ≠ a], then [w] appears strictly
      before [a] in the list [stk].  This is a purely structural lemma
      about [stack_split_at], independent of DFS invariants. *)
  Lemma stack_split_at_in_popped_before_a (stk: list V) (a w: V):
    In a stk ->
    forall popped rest,
      stack_split_at stk a = (popped, rest) ->
      In w popped -> w <> a ->
      exists l1 l2, stk = l1 ++ w :: l2 /\ In a l2.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [in_list_one_above_other]: If two distinct elements [x] and [y] are
      both in a list, then either [x] appears before [y] or [y] appears
      before [x] (i.e., one is above the other). *)
  Lemma in_list_one_above_other {A: Type} (l: list A) (x y: A):
    In x l -> In y l -> x <> y ->
    (exists l1 l2, l = l1 ++ x :: l2 /\ In y l2) \/
    (exists l1 l2, l = l1 ++ y :: l2 /\ In x l2).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [done_vertex_dfn_lt]: For the current vertex [a] (with [~ done a],
      [In a (stack s)]) and any [done] vertex [w] still on the stack,
      [dfn s w < dfn s a].  This holds because [w] was processed before
      [a] (it is already in [done] while [a] is not), so [preloop w]
      executed earlier, assigning a smaller dfn from the monotonically
      increasing timer.  The proof uses [stack_dfn_order] to deduce
      [dfn s w <= dfn s a] (since [a] is above [w]), and [dfn_injective]
      (from [low_forset_inv]'s [dfn_valid] and [dfn_inv] which together
      ensure uniqueness of dfn values on the stack) to rule out equality,
      yielding the strict inequality. *)
  (** [preloop_above_existing]: After [preloop x], [x] is above any
      vertex [y] that was on the stack before (and [x ≠ y]). *)
  Lemma preloop_above_existing (x y: V):
    Hoare (fun s => In y (stack s))
          (preloop x)
          (fun _ s => exists l1 l2, stack s = l1 ++ x :: l2 /\ In y l2).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [current_above_done_vertex]: In the state after preloop and forset
      for vertex [a], all [done] vertices that are still on the stack
      appear BELOW [a] (i.e., [a] is above them).  This holds because
      [a] was preloop'd after all [done] vertices, so [push_stack a]
      put [a] at the front. *)
  (** [done_dfn_lt_not_done]: A done vertex [w] has strictly smaller
      dfn than the current vertex [a] (which is not done).  This holds
      because [w] was processed before [a] (w ∈ done, a ∉ done),
      so [preloop w] executed earlier, setting [dfn w] from a smaller
      timer value than [preloop a] used for [dfn a].  Since dfn values
      are immutable, [dfn w < dfn a] in all subsequent states.
      Formal proof: see comment below. *)
  Lemma done_dfn_lt_not_done (pu a: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv pu done s ->
    done_visited done s ->
    ~ done a ->
    In a (stack s) ->
    dfn_injective s ->
    forall w, done w -> In w (stack s) -> dfn s w < dfn s a.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma current_above_done_vertex (pu a: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv pu done s ->
    done_visited done s ->
    ~ done a ->
    In a (stack s) ->
    stack_dfn_order s ->
    dfn_injective s ->
    forall w, done w -> In w (stack s) ->
    exists l1 l2, stack s = l1 ++ a :: l2 /\ In w l2.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma done_vertex_dfn_lt (pu a: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv pu done s ->
    done_visited done s ->
    ~ done a ->
    In a (stack s) ->
    stack_dfn_order s ->
    dfn_injective s ->
    forall w, done w -> In w (stack s) -> dfn s w < dfn s a.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma done_not_popped_by_subtree_pop_scc (u a: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s ->
    done_visited done s ->
    ~ done a ->
    In a (stack s) ->
    stack_dfn_order s ->
    (forall w, done w -> In w (stack s) -> dfn s w < dfn s a) ->
    forall w, done w -> forall popped' rest',
      stack_split_at (stack s) a = (popped', rest') -> ~ In w popped'.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [W_preserves_ancestor_inv]: Combining the above, [W v]
      ([tarjan_scc g v]) preserves [low_forset_inv u done] and
      [fa s v = u]. *)
  Lemma W_preserves_ancestor_inv (u v: V) (done: V -> Prop):
    u <> v -> ~ done v ->
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v /\ done_visited done s /\ (stack_dfn_order s /\ dfn_injective s))
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u /\ done_visited done s /\ (stack_dfn_order s /\ dfn_injective s)).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.


  Lemma set_fa_W_preserves_low_forset_inv (u v: V) (done: V -> Prop):
    u <> v -> dg_step g u v -> ~ done v ->
    Hoare (fun s => low_forset_inv u done s /\ ~ v ∈ visited s /\ ~ done v /\ done_visited done s /\ (stack_dfn_order s /\ dfn_injective s))
          (set_fa v u;; tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u /\ done_visited done s /\ (stack_dfn_order s /\ dfn_injective s)).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [low_forset_inv_proper]: [low_forset_inv u done s] is a Proper
      morphism w.r.t. set equivalence of [done].  When [done1 == done2],
      the [children_done] and [back_edges_done] sets are equivalent,
      so the nested min condition transfers via [min_eq_forward]. *)
  Lemma low_forset_inv_proper u: Proper (Sets.equiv ==> eq ==> iff) (low_forset_inv u).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma children_done_visited_proper u: Proper (Sets.equiv ==> eq ==> iff) (children_done_visited u).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma done_visited_proper: Proper (Sets.equiv ==> eq ==> iff) done_visited.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Inductive visited_tag :=
    | VSelf | VKeep (w: V) | VKeepAll (done: V -> Prop)
    | VKeepFaChildren (parent: V).

  Definition visited_tag_pre (x: V) (t: visited_tag) (s: @SCCSt V): Prop :=
    match t with
    | VSelf => True | VKeep w => w ∈ visited s
    | VKeepAll done => forall w, done w -> w ∈ visited s
    | VKeepFaChildren parent => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v
    end.

  Definition visited_tag_post (x: V) (t: visited_tag) (_: unit) (s: @SCCSt V): Prop :=
    match t with
    | VSelf => x ∈ visited s | VKeep w => w ∈ visited s
    | VKeepAll done => forall w, done w -> w ∈ visited s
    | VKeepFaChildren parent => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v
    end.

  (** [process_edge_keep_fa_children]: preserves the forall fa-children
      property.  Requires [dg_step g u v] (the edge being processed)
      to justify the new [fa]-child when [set_fa v u] creates one. *)
  Lemma process_edge_keep_fa_children (parent u v: V) (W: V -> program (@SCCSt V) unit):
    dg_step g u v ->
    (forall x, Hoare (fun s: @SCCSt V => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w) (W x)
                     (fun _ s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)) ->
    Hoare (fun s: @SCCSt V => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)
          (process_edge u W v)
          (fun _ s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  Lemma tarjan_scc_keep_fa_children_in_universe (parent a: V):
    Hoare (fun s: @SCCSt V => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g a)
          (fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.


  (** [children_done_full_eq]: When [done = dg_step g u], the
      [children_done] set coincides with the DFS-tree children of [u].
      Requires [done_visited] (neighbors are visited) for the forward
      direction via [state_to_dfs_tree_step_char_backward], and
      [fa_children_in_g] (fa-children of u correspond to g-edges) for
      the backward direction — the tree's [original_step] references
      edge endpoints from [g] but does not itself require [original_step g e]. *)
  Lemma children_done_full_eq (u: V) (s: SCCSt):
    done_visited (fun v => dg_step g u v) s ->
    (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) ->
    children_done s u (fun v => dg_step g u v) == dg_step (state_to_dfs_tree g s root) u.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [back_edges_done_full_eq]: When [done = dg_step g u], the
      [back_edges_done] set coincides with [scc_back_edge s u].
      Both sides require [dg_step g u v], [In v (stack s)]; the
      difference is [fa s v <> u] vs [~ dg_step (state_to_dfs_tree) u v].
      Forward direction uses [state_to_dfs_tree_step_char] (tree edge ⇒
      fa = u); backward requires [stack_fa_neq_self] for
      [state_to_dfs_tree_step_char_backward]. *)
  Lemma back_edges_done_full_eq (u: V) (s: SCCSt):
    done_visited (fun v => dg_step g u v) s ->
    (forall v, In v (stack s) -> fa s v <> v) ->
    back_edges_done s u (fun v => dg_step g u v) == scc_back_edge s u.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [low_forset_inv_to_scc_low_valid]: When [done] is the full set of
      neighbors [dg_step g u], [low_forset_inv u done s] implies
      [scc_low_valid_v s u].  The proof uses [min_eq_forward] with the
      characterizations [state_to_dfs_tree_step_char] and
      [state_to_dfs_tree_step_char_backward]. *)
  (** [low_forset_inv_to_scc_low_valid]: When [done] is the full neighbor
      set [dg_step g u], [low_forset_inv u done] implies [scc_low_valid_v s u].

      Proof plan:
      1. Use [children_done_full_eq] to replace [children_done s u (dg_step g u)]
         with the DFS-tree children [dg_step (state_to_dfs_tree g s root) u].
      2. Use [back_edges_done_full_eq] to replace [back_edges_done s u (dg_step g u)]
         with [scc_back_edge s u].
      3. Apply [min_eq_forward] (or the appropriate min-value equivalence lemma)
         to show the nested min in [low_forset_inv] equals the nested min in
         [scc_low_valid_v].

      Required previous lemmas:
      - [children_done_full_eq]
      - [back_edges_done_full_eq]
      - [min_eq_forward] (from MaxMinLib) *)
  Lemma low_forset_inv_to_scc_low_valid (u: V) (s: SCCSt):
    done_visited (fun v => dg_step g u v) s ->
    (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) ->
    (forall v, In v (stack s) -> fa s v <> v) ->
    low_forset_inv u (fun v => dg_step g u v) s ->
    scc_low_valid_v s u.
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.



  (** [forset_keeps_low_forset_inv]: [forset (process_edge a W)] preserves
      [low_forset_inv u done] given the fixpoint IH.

      Proof plan: apply [Hoare_forset] with invariant
        [P(done) := low_forset_inv u done s /\ a ∈ visited s /\ done_visited done s].
      - Properness of [P] follows from [low_forset_inv_proper] and
        [done_visited_proper].
      - For each neighbor [x] of [a], [process_edge a W x] has two branches:
        * Tree edge ([~ x ∈ visited]): [set_fa x a] preserves [low_forset_inv]
          by [set_fa_preserves_low_forset_inv_for_new_child]; the recursive
          [W x] preserves it by the IH; [update_low a (low x)] preserves it
          by [update_low_tree_edge].
        * Non-tree edge ([x ∈ visited]):
          - If [x] is on the stack, it is a back edge; use [update_low_back_edge].
          - If [x] is not on the stack, it is a cross edge; adding [x] to [done]
            does not change [back_edges_done] (which requires [In x (stack s)]),
            so [low_forset_inv] is preserved by set equivalence.

      Required previous lemmas:
      - [Hoare_forset]
      - [low_forset_inv_proper]
      - [done_visited_proper]
      - [set_fa_preserves_low_forset_inv_for_new_child]
      - [update_low_tree_edge]
      - [update_low_back_edge] *)
  Lemma forset_keeps_low_forset_inv (u a: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit)
    (Hneq: u <> a)
    (Hndone_a: ~ done a)
    (IH: forall x, Hoare (fun s => low_forset_inv u done s /\ ~ x ∈ visited s /\ ~ done x /\ a ∈ visited s /\ done_visited done s) (W x)
                         (fun _ s => low_forset_inv u done s /\ a ∈ visited s /\ done_visited done s)):
    Hoare (fun s => low_forset_inv u done s /\ a ∈ visited s /\ done_visited done s)
          (forset (fun w => dg_step g a w) (process_edge a W))
          (fun _ s => low_forset_inv u done s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [forset_keep_low_forset_inv]: after iterating over all children of [u],
      [low_forset_inv u ∅] is turned into [scc_low_valid_v s u].

      Proof plan: define the forset invariant
        [P(done) := low_forset_inv u done s /\ dfn_valid g s root /\ dfn_inv s
                    /\ fa_visited s /\ done_visited done s
                    /\ (forall v, fa s v = u /\ fa s v <> v -> v ∈ done)].
      - Apply [Hoare_forset]; properness follows from [low_forset_inv_proper]
        and [done_visited_proper].
      - For each neighbor [a0]:
        * Tree edge: after [set_fa a0 u], use [set_fa_W_preserves_low_forset_inv]
          to run the recursive [W a0] while preserving [low_forset_inv u done]
          and establishing [fa a0 = u]. Then [low_forset_inv_expand_child_done]
          moves from [done] to [done ∪ [a0]] (since [a0] is now a proper child
          and [low u ≤ low a0] holds after the recursive call).
        * Non-tree edge: back edge uses [update_low_back_edge]; cross edge uses
          set equivalence as in [forset_keeps_low_forset_inv].
      - After the loop [done = dg_step g u]; the fa-child condition together
        with [done_visited] gives the premises of [low_forset_inv_to_scc_low_valid],
        yielding [scc_low_valid_v s u].

      Required previous lemmas:
      - [Hoare_forset]
      - [low_forset_inv_proper]
      - [done_visited_proper]
      - [set_fa_W_preserves_low_forset_inv]
      - [update_low_tree_edge]
      - [update_low_back_edge]
      - [low_forset_inv_expand_child_done]
      - [low_forset_inv_to_scc_low_valid] *)
  Lemma forset_keep_low_forset_inv (u: V) (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                     (fun _ s => low_post x s /\ u ∈ visited s)) ->
    (forall a, Hoare (fun s => True) (W a) (fun _ s => a ∈ visited s)) ->
    (forall (a: V) (done': V -> Prop), Hoare (fun s => forall w, done' w -> w ∈ visited s) (W a)
                                         (fun _ s => forall w, done' w -> w ∈ visited s)) ->
    (forall a, Hoare (fun s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) (W a)
                    (fun _ s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v)) ->
    Hoare (fun s => low_forset_inv u ∅ s /\ (forall v, fa s v = u -> v = u))
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [tarjan_scc_keep_low_valid]: one-vertex main theorem.
      [tarjan_scc g u] transforms [low_pre u] into [low_post u].

      Proof plan: apply [Hoare_fix_logicv_conj] (fixpoint induction) with
        [P1(a) := low_pre a], [Q1(a) := low_post a],
        [P2(a,w) := w ∈ visited s], [Q2(a,w) := w ∈ visited s].
      1. The auxiliary visitedness goal is discharged by the external lemma
         [tarjan_scc_keep_visited] from [Tarjan_scc_basics].
      2. In the body:
         - [preloop u] establishes [low_forset_inv u ∅] by
           [preloop_establishes_low_forset_inv]. [preloop_keeps_fa] gives
           [fa v = u -> v = u] for all [v].
         - The [forset] over children uses [forset_keep_low_forset_inv].
           Its four W-assumptions come from the induction hypotheses:
           * [HW_pre_post] from the low-link IH;
           * [HW_vis] from the visited IH;
           * [HW_done_vis] by lifting the visited IH to arbitrary [done'];
           * [HW_fa_children] from [process_edge_keep_fa_children] and
             [tarjan_scc_keep_fa_children_in_universe] applied to the IH.
           Result: [scc_low_valid_v s u /\ dfn_valid /\ dfn_inv /\ fa_visited].
         - The final [If (low u = dfn u) (pop_scc u)]:
           * If [low u = dfn u], apply [pop_scc_keep_scc_low_valid_v] to keep
             [scc_low_valid_v u].
           * If not, the state is unchanged and [scc_low_valid_v u] still holds.
      3. The postcondition is exactly [low_post u].

      Required previous lemmas:
      - [Hoare_fix_logicv_conj]
      - [tarjan_scc_keep_visited] (from Tarjan_scc_basics)
      - [preloop_establishes_low_forset_inv]
      - [preloop_keeps_fa]
      - [forset_keep_low_forset_inv]
      - [process_edge_keep_fa_children]
      - [tarjan_scc_keep_fa_children_in_universe]
      - [pop_scc_keep_scc_low_valid_v] *)
  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
          (fun _ s => low_post u s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (* ================================================================ *)
  (* 13. Global scc_low_valid / scc_is_low                             *)
  (* ================================================================ *)

  (** [tarjan_scc_establishes_and_preserves_scc_low_valid]:
      If [a] is unvisited and [scc_low_valid] holds for all currently
      visited vertices, then after [tarjan_scc g a], [scc_low_valid]
      holds for all vertices (including new ones in [a]'s SCC tree).
      Also preserves [dfn_inv], [fa_visited], [dfn_valid].

      Proof plan:
      1. From [tarjan_scc_keep_low_valid], after [tarjan_scc g a] we have
         [low_post a], in particular [scc_low_valid_v s a]. Thus [a] and the
         vertices in its DFS subtree satisfy [scc_low_valid_v].
      2. Cross-tree preservation: for any already-visited vertex [u] that is an
         ancestor of [a] in the DFS tree, [W_preserves_ancestor_inv] (or the
         more specific [set_fa_W_preserves_low_forset_inv] for the tree-edge
         step) preserves [low_forset_inv u done] for the growing [done] set.
         When [a]'s subtree finishes, [done] contains all neighbors of [u];
         apply [low_forset_inv_to_scc_low_valid] to obtain [scc_low_valid_v s u].
      3. Vertices outside [a]'s subtree and not on its ancestor chain are not
         affected by the state changes local to [a]'s subtree (their stack/dfn/
         low/fa values remain unchanged), so their [scc_low_valid_v] is preserved.
      4. [dfn_inv], [fa_visited], [dfn_valid] are preserved by the basic
         primitive-operation invariants.

      Required previous lemmas:
      - [tarjan_scc_keep_low_valid]
      - [W_preserves_ancestor_inv]
      - [set_fa_W_preserves_low_forset_inv]
      - [low_forset_inv_to_scc_low_valid]
      - Basic primitive invariants (e.g. [pop_scc_keep_dfn_inv],
        [pop_scc_keep_fa_visited], [pop_scc_keep_dfn_valid]) *)
  Lemma tarjan_scc_establishes_and_preserves_scc_low_valid (a: V):
    Hoare (fun s => scc_low_valid s /\ dfn_inv s /\ fa_visited s /\ dfn_valid g s root /\ ~ a ∈ visited s)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g a)
          (fun _ s => scc_low_valid s /\ dfn_inv s /\ fa_visited s /\ dfn_valid g s root).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [tarjan_scc_all_scc_low_valid]: global [scc_low_valid] after the full
      Tarjan loop over all vertices.

      Proof plan: [tarjan_scc_all] is a [forset] over all vertices
      [v] of [If (~ v ∈ visited) (tarjan_scc g v)]. Apply [Hoare_forset]
      with invariant
        [P(done) := (forall w, done w -> scc_low_valid_v s w)
                    /\ dfn_inv s /\ fa_visited s /\ dfn_valid g s root].
      - Properness of [P] follows from set-equivalence on [done].
      - For each vertex [a]:
        * If [~ a ∈ visited], use [tarjan_scc_establishes_and_preserves_scc_low_valid]
          to establish [scc_low_valid_v s a] and preserve the invariant for
          all already-done vertices.
        * If [a ∈ visited], the command is a no-op. We need [P done -> P (done ∪ [a])],
          i.e. [scc_low_valid_v s a] already holds. In the standard execution
          (starting with empty visited) this is true because [a] was processed
          in a previous iteration, so [a ∈ done].
      - After the loop, [done] is the full vertex universe [original_vvalid g].
        Since [visited s ⊆ original_vvalid g] is a basic invariant of Tarjan,
        [scc_low_valid] follows.

      Required previous lemmas:
      - [Hoare_forset]
      - [tarjan_scc_establishes_and_preserves_scc_low_valid]
      - Basic invariant [visited s ⊆ original_vvalid g]
        (available from Tarjan_scc / Tarjan_scc_basics) *)
  Theorem tarjan_scc_all_scc_low_valid:
    Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
          (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
          (fun _ s => scc_low_valid s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

  (** [tarjan_scc_all_scc_is_low]: final theorem — the global Tarjan
      algorithm computes the correct low-link values for every visited vertex.

      Proof plan:
      1. Use [Hoare_conseq_post] to strengthen the postcondition from
         [scc_low_valid s] to [scc_is_low s].
      2. Apply [scc_low_valid_implies_is_low], which requires [dfn_valid g s root]
         and [dfn_inv s]. These are already part of the postcondition of
         [tarjan_scc_all_scc_low_valid].
      3. Combine [tarjan_scc_all_scc_low_valid] with the dfn invariants via
         [Hoare_conj]. If needed, [dfn_valid] and [dfn_inv] for the full
         algorithm are given by the external lemmas [tarjan_scc_all_dfn_valid]
         and [tarjan_scc_all_keep_dfn_inv] from [Tarjan_scc_is_dfn].

      Required previous lemmas:
      - [tarjan_scc_all_scc_low_valid]
      - [scc_low_valid_implies_is_low]
      - [tarjan_scc_all_dfn_valid] (from Tarjan_scc_is_dfn)
      - [tarjan_scc_all_keep_dfn_inv] (from Tarjan_scc_is_dfn)
      - [Hoare_conseq_post] / [Hoare_conj] *)
  Theorem tarjan_scc_all_scc_is_low:
    Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
          (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
          (fun _ s => scc_is_low s).
  Proof.
    (* Proof idea: original proof preserved in Tarjan_scc_is_low.v.orig. *)
    Admitted.

End IS_LOW.
