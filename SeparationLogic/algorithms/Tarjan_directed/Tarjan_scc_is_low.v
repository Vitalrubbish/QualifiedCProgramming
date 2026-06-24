Require Import Coq.Logic.FunctionalExtensionality.
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
       ([set_fa_preserves_wf_scc_state_pre], [set_low_preserves_low_forset_inv])
       Hoare lemmas for the two assignment primitives.

    5. [update_low concrete cases / edge classification]
       ([update_low_tree_edge], [update_low_back_edge],
        [cross_edge_preserves_low_forset_inv])
       Reasoning about how [low] is updated on tree edges, back edges, and
       how cross edges preserve the invariant by only extending [done].

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
        ([low_forset_inv_to_scc_low_valid], [tree_edge_preserves_low_forset_inv_lowlink],
         [forset_keep_low_forset_inv])
        Closing the loop: after the forset over children, [scc_low_valid_v]
        holds.

    15. [Main theorems]
        ([tarjan_scc_keep_low_valid], [tarjan_scc_all_scc_low_valid],
        [tarjan_scc_all_scc_is_low]). *)


  Lemma scc_low_witness (s: @SCCSt V) (w: V) (n: nat):
    scc_is_low_v_val s w n ->
    exists x, scc_low_tree s w x /\ dfn s x = n.
  Proof.
    unfold scc_is_low_v_val.
    intros H. destruct H as [x [[Hin Hmin] Heq]].
    exists x; auto.
  Qed.

  Lemma scc_low_bound (s: @SCCSt V) (w: V) (n: nat) (x: V):
    scc_is_low_v_val s w n ->
    scc_low_tree s w x ->
    n <= dfn s x.
  Proof.
    unfold scc_is_low_v_val.
    intros H Hx. destruct H as [y [[Hin Hmin] Heq]].
    subst. apply Hmin. auto.
  Qed.

  (* ================================================================ *)
  (* 3. Helper Lemma: First Step Decomposition                        *)
  (* ================================================================ *)

  Lemma dg_reachable_first_step (T: OriginalGraphType V E) (u z: V):
    dg_reachable T u z ->
    u = z \/ exists v, dg_step T u v /\ dg_reachable T v z.
  Proof.
    induction 1.
    - right. exists y. split; [exact H |].
      apply Coq.Relations.Relation_Operators.rt_refl.
    - left. reflexivity.
    - destruct IHclos_refl_trans1 as [Heq | [v [Hstep_uv Hreach_vy]]].
      + subst y. exact IHclos_refl_trans2.
      + right. exists v. split; [exact Hstep_uv |].
        eapply Coq.Relations.Relation_Operators.rt_trans.
        * exact Hreach_vy.
        * exact H1.
  Qed.

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
    intros Huvis.
    hnf. intro a. hnf. split.
    - intros H. unfold scc_low_tree, scc_low_reachable in H.
      destruct H as [z [Hz_reach Hz_end]].
      apply dg_reachable_first_step in Hz_reach as [Hu_eq_z | [v [Hstep Hreach]]].
      + subst z.
        destruct Hz_end as [Heq | Hback].
        * subst a. left. left. sets_unfold. reflexivity.
        * left. right. exact Hback.
      + right. exists v. split; [exact Hstep |].
        unfold scc_low_tree, scc_low_reachable.
        exists z. split; [exact Hreach | exact Hz_end].
    - intros H. destruct H as [[Hu_case | Hbe_case] | Hchild_case].
      + sets_unfold in Hu_case. subst a.
        unfold scc_low_tree, scc_low_reachable.
        exists u. split.
        * apply Coq.Relations.Relation_Operators.rt_refl.
        * left. reflexivity.
      + unfold scc_low_tree, scc_low_reachable.
        exists u. split.
        * apply Coq.Relations.Relation_Operators.rt_refl.
        * right. exact Hbe_case.
      + destruct Hchild_case as [v [Hstep Hvw]].
        unfold scc_low_tree, scc_low_reachable in Hvw.
        destruct Hvw as [z [Hz_reach Hz_end]].
        unfold scc_low_tree, scc_low_reachable.
        exists z. split.
        * eapply Coq.Relations.Relation_Operators.rt_trans.
          -- apply Coq.Relations.Relation_Operators.rt_step. exact Hstep.
          -- exact Hz_reach.
        * exact Hz_end.
  Qed.

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
    split; intros.
    - apply min_eq_forward with
        (f1 := low s) (P1 := dg_step (state_to_dfs_tree g s root) u);
        auto using NatLe_TotalOrder.
      + intros v Hson.
        pose proof (IHu v Hson) as Hlow_v.
        apply scc_low_witness in Hlow_v as [x [Hx Heq]].
        exists x. split.
        * exists v. split; auto.
        * rewrite Heq. apply Nat.le_refl.
      + intros w [v [Hson Hlow]].
        exists v. split; auto.
        pose proof (IHu v Hson) as Hlow_v.
        apply scc_low_bound with (x := w) in Hlow_v; auto.
    - apply min_eq_forward with
        (f1 := dfn s)
        (P1 := (fun w => exists v,
          dg_step (state_to_dfs_tree g s root) u v /\
          scc_low_tree s v w));
        auto using NatLe_TotalOrder.
      + intros w [v [Hson Hlow]].
        exists v. split; auto.
        pose proof (IHu v Hson) as Hlow_v.
        apply scc_low_bound with (x := w) in Hlow_v; auto.
      + intros v Hson.
        pose proof (IHu v Hson) as Hlow_v.
        apply scc_low_witness in Hlow_v as [x [Hx Heq]].
        exists x. split.
        * exists v. split; auto.
        * rewrite Heq. apply Nat.le_refl.
  Qed.

  Lemma scc_low_valid_induction_is_low (s: @SCCSt V) (u: V)
    (Hu: u ∈ visited s)
    (IHu: forall v,
      dg_step (state_to_dfs_tree g s root) u v ->
      scc_is_low_v_val s v (low s v)):
    scc_low_valid_v s u -> scc_is_low_v s u.
  Proof.
    intros Hvalid.
    unfold scc_low_valid_v in Hvalid.
    rewrite scc_low_valid_induction in Hvalid; auto.
    apply min_union_iff in Hvalid.
    unfold scc_is_low_v, scc_is_low_v_val.
    rewrite scc_low_tree_decompose; auto.
    rewrite (Sets_union_comm [u] (scc_back_edge s u)).
    rewrite Sets_union_comm.
    exact Hvalid.
  Qed.

  Lemma scc_low_valid_implies_is_low (s: @SCCSt V):
    dfn_valid g s root -> dfn_inv s ->
    scc_low_valid s -> scc_is_low s.
  Proof.
    intros Hvalid Hinv Hlow.
    destruct Hinv as [Hdfn_lt [Hdfn_zero Hpos]].
    unfold scc_is_low.
    cut (forall n u, u ∈ visited s -> timer s - dfn s u = n -> scc_is_low_v s u).
    { intros H u Hu. apply H with (n := timer s - dfn s u); auto. }
    induction n as [n IH] using (well_founded_induction (Nat.lt_wf 0)).
    intros u Hu Hn.
    apply (scc_low_valid_induction_is_low s u Hu).
    - intros v Hson_orig.
      pose proof Hson_orig as Hson_for_step.
      apply state_to_dfs_tree_step_char in Hson_for_step.
      destruct Hson_for_step as [_ [_ Hvis_v]].
      apply Hvalid in Hson_orig.
      pose proof (Hdfn_lt u Hu) as Hdfn_u_lt.
      pose proof (Hdfn_lt v Hvis_v) as Hdfn_v_lt.
      apply (IH (timer s - dfn s v)).
      + lia.
      + exact Hvis_v.
      + reflexivity.
    - apply Hlow. exact Hu.
  Qed.
  (** * Well-formed SCC state abstraction

      We bundle the four global invariants that are preserved by every
      primitive operation.  This makes later Hoare triples more compact
      and emphasizes that the four predicates are maintained together. *)

  (** [wf_scc_state]: global well-formedness predicate preserved by every
      primitive operation of the Tarjan algorithm. *)
  Definition wf_scc_state (s: @SCCSt V): Prop :=
    stack_in_visited s /\ dfn_inv s /\ dfn_valid g s root /\ fa_visited s.

  (** [wf_scc_state_pre u s]: "pre-state" for an unvisited vertex [u].
      The global invariants hold, but [u] itself is not yet visited.
      This is the state right before [preloop u] and right after
      [set_fa u p] (when [u] has been assigned a parent [p] but not yet
      visited).  In the latter case [dfn_valid g s root] is still globally
      meaningful because the pending tree edge [p -> u] does not yet need
      to satisfy the dfn order (it will after [preloop u]). *)
  Definition wf_scc_state_pre (u: V) (s: @SCCSt V): Prop :=
    wf_scc_state s /\ ~ u ∈ visited s.

  (** [pop_scc_preserves_wf_scc_state]: [pop_scc] only removes vertices from
      the stack and adds an SCC record; it does not modify [visited], [dfn],
      [fa], or the low/dfn values of remaining vertices. *)
  Lemma pop_scc_preserves_wf_scc_state (u: V):
    Hoare (fun s: @SCCSt V => wf_scc_state s)
          (pop_scc u)
          (fun _ s => wf_scc_state s).
  Proof.
    (* pop_scc only modifies stack and sccs, not visited/dfn/timer/fa.
       wf_scc_state components are all preserved.
       stack_in_visited: use pop_scc_keep_stack_in_visited.
       dfn_inv, dfn_valid, fa_visited: intro_state + hoare_auto_s. *)
    unfold wf_scc_state.
    apply Hoare_conj with (Q1 := fun _ s => stack_in_visited s).
    - apply (Hoare_conseq_pre (fun s => wf_scc_state s) (fun s => stack_in_visited s) (pop_scc u) (fun _ s => stack_in_visited s)).
      intros s [Hsiv _]. exact Hsiv.
      apply (pop_scc_keep_stack_in_visited u).
    - apply Hoare_conj with (Q1 := fun _ s => dfn_inv s).
      apply (Hoare_conseq_pre (fun s => wf_scc_state s) (fun s => dfn_inv s) (pop_scc u) (fun _ s => dfn_inv s)).
      intros s [_ [Hinv _]]. exact Hinv.
      unfold pop_scc. intro_state. hoare_auto_s. subst s. simpl.
      unfold pop_scc_state. destruct (stack_split_at (stack s0) u) as [popped rest]. simpl.
      exact H.
      apply Hoare_conj with (Q1 := fun _ s => dfn_valid g s root).
      * apply (Hoare_conseq_pre (fun s => wf_scc_state s) (fun s => dfn_valid g s root) (pop_scc u) (fun _ s => dfn_valid g s root)).
        intros s [_ [_ [Hvalid _]]]. exact Hvalid.
        unfold pop_scc. intro_state. hoare_auto_s. subst s. simpl.
        unfold pop_scc_state. destruct (stack_split_at (stack s0) u) as [popped rest]. simpl.
        exact H.
      * apply (Hoare_conseq_pre (fun s => wf_scc_state s) (fun s => fa_visited s) (pop_scc u) (fun _ s => fa_visited s)).
        intros s [_ [_ [_ Hfa]]]. exact Hfa.
        unfold pop_scc. intro_state. hoare_auto_s. subst s. simpl.
        unfold pop_scc_state. destruct (stack_split_at (stack s0) u) as [popped rest]. simpl.
        exact H.
  Qed.

  (** [preloop_preserves_wf_scc_state]: [preloop u] assigns [dfn u], [low u],
      pushes [u] onto the stack, and marks [u] visited. Starting from
      [wf_scc_state_pre u], it restores full [wf_scc_state]. *)
  Lemma preloop_preserves_wf_scc_state (u: V):
    Hoare (fun s: @SCCSt V => wf_scc_state_pre u s)
          (preloop u)
          (fun _ s => wf_scc_state s).
  Proof.
    unfold wf_scc_state_pre, wf_scc_state.
    apply Hoare_conj with (Q1 := fun _ s => stack_in_visited s).
    - apply (Hoare_conseq_pre (fun s => wf_scc_state s /\ ~ u ∈ visited s)
        (fun s => stack_in_visited s) (preloop u) (fun _ s => stack_in_visited s)).
      intros s [[Hsiv _] _]. exact Hsiv.
      apply (preloop_keep_stack_in_visited u).
    - apply Hoare_conj with (Q1 := fun _ s => dfn_inv s).
      apply (Hoare_conseq_pre (fun s => wf_scc_state s /\ ~ u ∈ visited s)
        (fun s => dfn_inv s) (preloop u) (fun _ s => dfn_inv s)).
      intros s [[_ [Hinv _]] _]. exact Hinv.
      apply (preloop_keep_dfn_inv u).
      apply Hoare_conj with (Q1 := fun _ s => dfn_valid g s root).
      * apply (Hoare_conseq_pre
          (fun s => wf_scc_state s /\ ~ u ∈ visited s)
          (fun s => ~ u ∈ visited s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s)
          (preloop u) (fun _ s => dfn_valid g s root)).
        intros s [[Hsiv [Hinv [Hvalid Hfa]]] Hnuvis].
        split. exact Hnuvis. split. exact Hvalid. split. exact Hinv. exact Hfa.
        apply (Hoare_conseq_post
          (fun s => ~ u ∈ visited s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s)
          (preloop u)
          (fun _ s => dfn_valid g s root)
          (fun _ s => u ∈ visited s /\ dfn_valid g s root /\ dfn_inv s)).
        intros _ s [Huvis [Hvalid Hinv]]. exact Hvalid.
        apply (preloop_preserves_dfn_valid g root u).
      * apply (Hoare_conseq_pre
          (fun s => wf_scc_state s /\ ~ u ∈ visited s)
          (fun s => fa_visited s) (preloop u) (fun _ s => fa_visited s)).
        intros s [[_ [_ [_ Hfa]]] _]. exact Hfa.
        apply (preloop_keep_fa_visited u).
  Qed.

  (** [set_fa_preserves_wf_scc_state_pre]: [set_fa v u] assigns a parent
      [u] to an unvisited vertex [v]. It does NOT preserve full
      [wf_scc_state] globally, because the new tree edge [u -> v] does not
      yet satisfy the dfn order (v is unvisited). It does preserve the
      "pre-state" [wf_scc_state_pre v] as long as [u] is visited.
      This is the exact analogue of [set_fa_preserves_dfn_pre_child]
      in [Tarjan_scc_is_dfn.v]. *)
  Lemma set_fa_preserves_wf_scc_state_pre (v u: V):
    Hoare (fun s: @SCCSt V => wf_scc_state s /\ u ∈ visited s /\ ~ v ∈ visited s)
          (set_fa v u)
          (fun _ s => wf_scc_state_pre v s /\ u ∈ visited s).
  Proof.
    unfold wf_scc_state_pre, wf_scc_state.
    eapply Hoare_conseq_post.
    2: { apply Hoare_conj with (Q1 := fun _ s => dfn_pre g v s root /\ u ∈ visited s).
      - apply (Hoare_conseq_pre
          (fun s => wf_scc_state s /\ u ∈ visited s /\ ~ v ∈ visited s)
          (fun s => dfn_pre g v s root /\ u ∈ visited s)
          (set_fa v u) (fun _ s => dfn_pre g v s root /\ u ∈ visited s)).
        { intros s [[Hsiv [Hinv [Hvalid Hfa]]] [Huvis Hnv]].
          unfold dfn_pre. split. { split. exact Hnv. split. exact Hvalid.
          split. exact Hinv. exact Hfa. } exact Huvis. }
        apply (set_fa_preserves_dfn_pre_child_rich g root v u).
      - apply (Hoare_conseq_pre
          (fun s => wf_scc_state s /\ u ∈ visited s /\ ~ v ∈ visited s)
          (fun s => stack_in_visited s)
          (set_fa v u) (fun _ s => stack_in_visited s)).
        { intros s [[Hsiv _] _]. exact Hsiv. }
        unfold set_fa. intro_state. hoare_auto_s. subst s. simpl. exact H. }
    intros _ s [[[Hnv [Hvalid [Hinv Hfa]]] Huvis] Hsiv].
    split; [| exact Huvis]. split; [| exact Hnv]. split; [exact Hsiv | split; [exact Hinv | split; [exact Hvalid | exact Hfa]]].
  Qed.

  (** [set_low_preserves_wf_scc_state]: [set_low u n] only changes [low u],
      so all four global invariants are trivially preserved. *)
  Lemma set_low_preserves_wf_scc_state (u: V) (n: nat):
    Hoare (fun s: @SCCSt V => wf_scc_state s)
          (set_low u n)
          (fun _ s => wf_scc_state s).
  Proof.
    unfold set_low.
    apply Hoare_state_intro.
    intros s0 Hwf.
    pose (f := fun (s: SCCSt) => set low (fun low0 x => if x ==b u then n else low0 x) s).
    apply (Hoare_conseq_post (fun s => s = s0) (update' f)
      (fun _ s => wf_scc_state s) (fun _ s1 => s1 = f s0)).
    - intros _ s1 Heq. subst s1.
      unfold f, wf_scc_state.
      destruct s0 as [vis timer fa dfn low stack sccs].
      simpl. unfold wf_scc_state in Hwf. simpl in Hwf. exact Hwf.
    - apply Hoare_update'.
  Qed.

  (** [update_low_preserves_wf_scc_state]: [update_low u n] is a read of
      [low u] followed by [set_low u (min (low u) n)], so it preserves
      [wf_scc_state] (requires [u] visited so that [low u] is defined). *)
  Lemma update_low_preserves_wf_scc_state (u: V) (n: nat):
    Hoare (fun s: @SCCSt V => wf_scc_state s /\ u ∈ visited s)
          (update_low u n)
          (fun _ s => wf_scc_state s).
  Proof.
    unfold update_low. intro_state. hoare_auto_s.
    - (* n < low s0 u: set_low branch *)
      destruct H as [Hwf Huvis].
      pose (f := fun (s: SCCSt) => set low (fun low0 x => if x ==b u then n else low0 x) s).
      apply (Hoare_conseq_post (fun s => s = s0) (update' f)
        (fun _ s => wf_scc_state s) (fun _ s1 => s1 = f s0)).
      intros _ s1 Heq. subst s1. unfold f, wf_scc_state.
      destruct s0 as [vis timer fa dfn low stack sccs]. simpl.
      unfold wf_scc_state in Hwf. simpl in Hwf. exact Hwf.
      apply Hoare_update'.
    - (* ~ n < low s0 u: skip branch *)
      destruct H1 as [Heq _]. subst s. destruct H as [Hwf _]. exact Hwf.
  Qed.


  (* ================================================================ *)
  (* 6. Invariant Definitions                                         *)
  (* ================================================================ *)

  Ltac unfold_op :=
    unfold visit, set_dfn, set_low, set_fa, incr_timer,
           push_stack, update_low, pop_scc.

  Definition children_done (s: @SCCSt V) (u: V) (done: V -> Prop) (v: V): Prop :=
    v ∈ done /\ fa s v = u /\ fa s v <> v.

  Definition done_visited (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall w, done w -> w ∈ visited s.

  Definition back_edges_done (s: @SCCSt V) (u: V) (done: V -> Prop) (v: V): Prop :=
    v ∈ done /\ In v (stack s) /\ fa s v <> u.

  (** [low_forset_inv_core]: the part of [low_forset_inv] that actually
      depends on the processed-child set [done].  It states that [low s u]
      is the minimum of (low values of proper children in [done]) and
      (dfn values of back-edge targets in [done], plus [u] itself). *)
  Definition low_forset_inv_core (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
       min_value_of_subset Nat.le
         (fun w => back_edges_done s u done w \/ w = u) (dfn s))
      (fun x => x) (low s u).

  (** [low_forset_inv]: local low-link invariant for vertex [u] after
      processing the child set [done].  It combines the global well-formedness
      predicate, the fact that [u] is visited, and the core min condition. *)
  Definition low_forset_inv (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    wf_scc_state s /\ u ∈ visited s /\ low_forset_inv_core u done s.

  (** [low_pre]: pre-condition for [tarjan_scc g u].  It is exactly the
      "pre-state" [wf_scc_state_pre u]: global well-formedness plus [u]
      not yet visited. *)
  Definition low_pre (u: V) (s: @SCCSt V): Prop :=
    wf_scc_state_pre u s.

  (** [low_post]: post-condition for [tarjan_scc g u].  Requires global
      well-formedness and that [u]'s low-link value is correct. *)
  Definition low_post (u: V) (s: @SCCSt V): Prop :=
    wf_scc_state s /\ scc_low_valid_v s u.

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
    unfold low_pre, wf_scc_state_pre, wf_scc_state.
    intros [[Hsiv [Hinv [Hvalid Hfa_vis]]] Hnuvis] Hfa_eq.
    destruct (classic (v = u)) as [Heq | Hneq]; [exact Heq |].
    exfalso.
    assert (Htemp: fa s v <> v).
    { rewrite Hfa_eq. intro Heq2. apply Hneq. symmetry; exact Heq2. }
    apply Hfa_vis in Htemp.
    rewrite Hfa_eq in Htemp.
    exact (Hnuvis Htemp).
  Qed.

  (* ================================================================ *)
  (* 7. Preloop Establishes Low Forset Invariant                      *)
  (* ================================================================ *)

  Lemma preloop_low_eq_dfn (u: V):
    Hoare (fun s: @SCCSt V => True)
          (preloop u)
          (fun _ s => low s u = dfn s u).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    unfold equiv_decb. destruct (equiv_dec u u) as [Heq|Hneq]; simpl;
      [reflexivity | exfalso; apply Hneq; reflexivity].
  Qed.

  Lemma children_done_empty (s: @SCCSt V) (u: V):
    children_done s u ∅ == ∅.
  Proof.
    unfold children_done.
    hnf. intro v. hnf. split; intros H; [destruct H as [Hemp _] | destruct H].
    sets_unfold in Hemp. destruct Hemp.
  Qed.

  Lemma back_edges_done_empty_char (s: @SCCSt V) (u: V):
    (fun w => back_edges_done s u ∅ w \/ w = u) == [u].
  Proof.
    hnf. intro w. hnf. split; intros H.
    - destruct H as [Hbed | Heq].
      + unfold back_edges_done in Hbed. destruct Hbed as [Hemp _].
        sets_unfold in Hemp. destruct Hemp.
      + sets_unfold. symmetry. exact Heq.
    - sets_unfold in H. subst w. right. reflexivity.
  Qed.

  Lemma low_eq_dfn_to_min_empty (u: V) (s: @SCCSt V):
    low s u = dfn s u ->
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
       min_value_of_subset Nat.le (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
      (fun x => x) (low s u).
  Proof.
    intros Heq. rewrite Heq.
    exists (dfn s u). split.
    - split.
      + sets_unfold. right.
        exists u. split.
        * split.
          -- unfold back_edges_done. sets_unfold. right. reflexivity.
          -- intros v Hv_back. unfold back_edges_done in Hv_back. compute in Hv_back.
             destruct Hv_back as [[Hfalse_v _] | Heq_v].
             ++ destruct Hfalse_v.
             ++ subst v. apply Nat.le_refl.
        * reflexivity.
      + intros b Hb. sets_unfold in Hb.
        destruct Hb as [Hb_left | Hb_right].
        * destruct Hb_left as [v [[Hv_in _] Heq_v]].
          unfold children_done in Hv_in. sets_unfold in Hv_in.
          destruct Hv_in as [Hfalse_v _]. destruct Hfalse_v.
        * destruct Hb_right as [v [[Hv_in Hv_min] Heq_v]].
          unfold back_edges_done in Hv_in. compute in Hv_in.
          destruct Hv_in as [[Hfalse_in _] | Heq_vin].
          -- destruct Hfalse_in.
          -- subst v. rewrite Heq_v. apply Nat.le_refl.
    - reflexivity.
  Qed.

  (** [preloop_establishes_low_forset_inv]: [preloop u] establishes the
      full precondition required by [forset_keep_low_forset_inv].
      In addition to [low_forset_inv u ∅], it guarantees:
      - no other vertex has been assigned [u] as parent;
      - [u] is on the stack;
      - stack dfn ordering and dfn injectivity are preserved. *)
  Lemma preloop_establishes_low_forset_inv (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s /\ stack_dfn_order s /\ dfn_injective s)
          (preloop u)
          (fun _ s => low_forset_inv u ∅ s /\
                      (forall v, fa s v = u -> v = u) /\
                      In u (stack s) /\ stack_dfn_order s /\ dfn_injective s).
  Proof.
    apply Hoare_conj. (* split low_forset_inv from fa /\ In /\ order /\ inj *)
    - (* low_forset_inv u ∅ *)
      unfold low_forset_inv.
      apply Hoare_conj. (* wf_scc_state *)
      + apply (Hoare_conseq_pre
          (fun s => low_pre u s /\ stack_dfn_order s /\ dfn_injective s)
          (fun s => wf_scc_state_pre u s)
          (preloop u) (fun _ s => wf_scc_state s)).
        { unfold low_pre, wf_scc_state_pre, wf_scc_state.
          intros s [[[Hsiv [Hinv [Hvalid Hfa]]] Hnuvis] _].
          split. { split; [exact Hsiv | split; [exact Hinv | split; [exact Hvalid | exact Hfa]]]. } exact Hnuvis. }
        apply preloop_preserves_wf_scc_state.
      + apply Hoare_conj. (* u ∈ visited *)
        * apply (Hoare_conseq_pre
            (fun s => low_pre u s /\ stack_dfn_order s /\ dfn_injective s)
            (fun _ => True) (preloop u) (fun _ s => u ∈ visited s)).
          { intros s _. exact I. }
          apply preloop_self_visited.
        * (* low_forset_inv_core u ∅ *)
          apply (Hoare_conseq_post
            (fun s => low_pre u s /\ stack_dfn_order s /\ dfn_injective s)
            (preloop u)
            (fun _ s => low_forset_inv_core u ∅ s)
            (fun _ s => low s u = dfn s u)).
          { intros _ s Heq. apply low_eq_dfn_to_min_empty. exact Heq. }
          apply (Hoare_conseq_pre
            (fun s => low_pre u s /\ stack_dfn_order s /\ dfn_injective s)
            (fun _ => True) (preloop u) (fun _ s => low s u = dfn s u)).
          { intros s _. exact I. }
          apply preloop_low_eq_dfn.
    - apply Hoare_conj. (* fa property *)
      + (* fa s v = u -> v = u *)
        unfold low_pre, wf_scc_state_pre.
        unfold preloop, set_dfn, set_low, incr_timer, push_stack, visit.
        intro_state. hoare_auto_s.
        (* After hoare_auto_s, the post-state has fa unchanged from s0.
           The goal is forall v, fa (post_state) v = u -> v = u.
           Since fa is unchanged, this is exactly fa s0 v = u -> v = u. *)
        destruct H as [[[Hsiv [Hinv [Hvalid Hfa_vis]]] Hnuvis] [Horder Hinj]].
        subst s. simpl in H2.
        apply low_pre_fa_eq_u_implies_eq_u with (s := s0) (v := v); auto.
        unfold low_pre, wf_scc_state_pre, wf_scc_state.
        split; [split; [exact Hsiv | split; [exact Hinv | split; [exact Hvalid | exact Hfa_vis]]] | exact Hnuvis].
      + apply Hoare_conj. (* In u (stack s) *)
        * apply (Hoare_conseq_pre
            (fun s => low_pre u s /\ stack_dfn_order s /\ dfn_injective s)
            (fun _ => True) (preloop u) (fun _ s => In u (stack s))).
          { intros s _. exact I. }
          apply preloop_in_stack.
        * apply Hoare_conj. (* stack_dfn_order *)
          { apply (Hoare_conseq_pre
              (fun s => low_pre u s /\ stack_dfn_order s /\ dfn_injective s)
              (fun s => stack_dfn_order s /\ dfn_inv s /\ stack_in_visited s /\ ~ u ∈ visited s)
              (preloop u) (fun _ s => stack_dfn_order s)).
            { unfold low_pre, wf_scc_state_pre.
              intros s [[[Hsiv [Hinv [Hvalid Hfa]]] Hnuvis] [Horder Hinj]].
              split; [exact Horder | split; [exact Hinv | split; [exact Hsiv | exact Hnuvis]]]. }
            apply preloop_preserves_stack_dfn_order. }
          (* dfn_injective s *)
          apply (Hoare_conseq_pre
            (fun s => low_pre u s /\ stack_dfn_order s /\ dfn_injective s)
            (fun s => dfn_injective s /\ dfn_inv s /\ ~ u ∈ visited s)
            (preloop u) (fun _ s => dfn_injective s)).
          { unfold low_pre, wf_scc_state_pre.
            intros s [[[Hsiv [Hinv [Hvalid Hfa]]] Hnuvis] [Horder Hinj]].
            split; [exact Hinj | split; [exact Hinv | exact Hnuvis]]. }
          apply preloop_preserves_dfn_injective.
  Qed.

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
    (* Rename to avoid naming conflicts *)
    rename popped into pp, rest into rr.
    intros Hsplit.
    induction stk as [| x xs IH] in v, pp, rr, Hsplit |- *; simpl in Hsplit.
    - apply pair_equal_spec in Hsplit. destruct Hsplit; subst. simpl. auto.
    - destruct (equiv_decb x v) eqn:Heq_xv.
      + apply pair_equal_spec in Hsplit. destruct Hsplit as [Hpop Hrest]; subst.
        simpl. split; [| split]; intros w Hw; simpl in Hw.
        * right. exact Hw.
        * destruct Hw as [Heq|Hw_xs].
          { subst w. intros Hfalse. simpl in Hfalse. tauto. }
          { auto. }
        * destruct Hw as [Heq|Hw_xs].
          { left. left. auto. }
          { right. exact Hw_xs. }
      + destruct (stack_split_at xs v) as (pxs, rxs) eqn:Hinner.
        apply pair_equal_spec in Hsplit. destruct Hsplit as [Hpop Hrest]; subst.
        destruct (IH v pxs rr Hinner) as [H1 [H2 H3]].
        simpl. split; [| split]; intros w Hw; simpl in Hw.
        * apply H1 in Hw. right; exact Hw.
        * destruct Hw as [Heq|Hw_xs].
          { subst w. intros Hfalse. simpl in Hfalse.
            exfalso. apply Hfalse. left. reflexivity. }
          { intros Hfalse.
            apply H2; [exact Hw_xs | intro Hp; apply Hfalse; right; exact Hp]. }
        * destruct Hw as [Heq|Hw_xs].
          { left. left. auto. }
          { destruct (H3 w Hw_xs) as [Hp|Hr];
            [left; right; exact Hp|right; exact Hr]. }
  Qed.

  Lemma scc_low_valid_v_low_eq_dfn_implies_dfn_le_back_edge_dfn (s: @SCCSt V) (u w: V):
    scc_low_valid_v s u ->
    low s u = dfn s u ->
    scc_back_edge s u w ->
    dfn s u <= dfn s w.
  Proof.
    intros Hvalid Heq_low Hback.
    unfold scc_low_valid_v in Hvalid.
    destruct Hvalid as [a_min [[Ha_in Ha_min] Ha_eq]].
    rewrite Heq_low in Ha_eq.
    subst a_min.
    assert (Hright_nonempty: exists a, (scc_back_edge s u ∪ [u]) a).
    { exists u. sets_unfold. right. reflexivity. }
    pose proof (min_nonempty_exists (dfn s) (scc_back_edge s u ∪ [u]) Hright_nonempty)
      as [m_right Hright].
    assert (Houter_bound: dfn s u <= m_right). {
      apply Ha_min.
      sets_unfold. right. exact Hright.
    }
    destruct Hright as [w_min [[_ Hw_min] Heq_wmin]].
    assert (Hinner_bound: m_right <= dfn s w). {
      rewrite <- Heq_wmin.
      apply Hw_min. left. exact Hback.
    }
    exact (Nat.le_trans _ _ _ Houter_bound Hinner_bound).
  Qed.

  Lemma pop_scc_keep_scc_low_valid_v (u: V):
    Hoare (fun s: @SCCSt V =>
      wf_scc_state s /\ scc_low_valid_v s u /\ low s u = dfn s u)
          (pop_scc u)
          (fun _ s => wf_scc_state s /\ scc_low_valid_v s u).
  Proof.
    unfold pop_scc. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit. simpl.
    destruct H as [Hwf [Hlow_valid Heq_low]].
    destruct (stack_split_at_partition (stack s0) u popped rest Hsplit) as [Hrest_incl [Hfresh Hcover]].
    assert (Hwf_post: wf_scc_state
      {| visited := visited s0; timer := timer s0;
         dfn := dfn s0; low := low s0; fa := fa s0;
         stack := rest; sccs := (fun v => In v popped) :: sccs s0 |}).
    { destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]].
      unfold wf_scc_state. simpl. split; [| split; [| split]]; auto.
      (* stack_in_visited: rest ⊆ original stack ⊆ visited *)
      unfold stack_in_visited. intros w Hw. simpl in Hw.
      apply Hrest_incl in Hw. apply Hsiv. exact Hw. }
    assert (Hlow_valid_post: scc_low_valid_v
      {| visited := visited s0; timer := timer s0;
         dfn := dfn s0; low := low s0; fa := fa s0;
         stack := rest; sccs := (fun v => In v popped) :: sccs s0 |} u).
    { unfold scc_low_valid_v. simpl. rewrite Heq_low.
      exists (dfn s0 u). split.
      - split.
        + sets_unfold. right.
          exists u. split.
          * split.
            -- sets_unfold. right. reflexivity.
            -- intros v Hv. sets_unfold in Hv.
               destruct Hv as [Hback_post | Heq_v].
               ++ destruct Hback_post as [Hstep [Hin_rest Hnot_tree]].
                  assert (Hv_in_stack0: In v (stack s0)). { apply Hrest_incl. exact Hin_rest. }
                  assert (Hback_pre: scc_back_edge s0 u v). {
                    unfold scc_back_edge. split; [exact Hstep | split; [exact Hv_in_stack0 | exact Hnot_tree]]. }
                  eapply scc_low_valid_v_low_eq_dfn_implies_dfn_le_back_edge_dfn;
                    [exact Hlow_valid | exact Heq_low | exact Hback_pre].
               ++ subst v. apply Nat.le_refl.
          * reflexivity.
        + intros n Hn. sets_unfold in Hn.
          destruct Hn as [Hn_left | Hn_right].
          * unfold scc_low_valid_v in Hlow_valid.
            destruct Hlow_valid as [a_pre [[_ Ha_pre_min] Ha_pre_eq]].
            rewrite Heq_low in Ha_pre_eq.
            rewrite <- Ha_pre_eq.
            apply Ha_pre_min. sets_unfold. left. exact Hn_left.
          * destruct Hn_right as [v [[Hv_in Hv_min] Heq_v]].
            rewrite <- Heq_v.
            sets_unfold in Hv_in.
            destruct Hv_in as [Hback_post | Heq_vin].
            -- destruct Hback_post as [Hstep [Hin_rest Hnot_tree]].
               assert (Hv_in_stack0: In v (stack s0)). { apply Hrest_incl. exact Hin_rest. }
               assert (Hback_pre: scc_back_edge s0 u v). {
                 unfold scc_back_edge. split; [exact Hstep | split; [exact Hv_in_stack0 | exact Hnot_tree]]. }
               eapply scc_low_valid_v_low_eq_dfn_implies_dfn_le_back_edge_dfn;
                 [exact Hlow_valid | exact Heq_low | exact Hback_pre].
            -- subst v. apply Nat.le_refl.
      - reflexivity. }
    split; [exact Hwf_post | exact Hlow_valid_post].
  Qed.

  (* ================================================================ *)
  (* 9. Set Decomposition Lemmas (needed for process_edge)            *)
  (* ================================================================ *)

  Lemma children_done_add (s: @SCCSt V) (u v: V) (done: V -> Prop):
    fa s v = u -> fa s v <> v ->
    children_done s u (done ∪ [v]) == children_done s u done ∪ [v].
  Proof.
    intros Hfa_eq Hfa_neq.
    unfold children_done.
    apply Sets_equiv_Sets_included. split.
    - sets_unfold. intros w [[Hw_done | Hw_v] [Hw_fa Hw_neq]].
      + left. split; [exact Hw_done | split; [exact Hw_fa | exact Hw_neq]].
      + subst w. right. reflexivity.
    - sets_unfold. intros w [Hw_child | Hw_v].
      + destruct Hw_child as [Hw_done [Hw_fa Hw_neq]].
        split; [left; exact Hw_done | split; [exact Hw_fa | exact Hw_neq]].
      + subst w. split; [right; reflexivity | split; [exact Hfa_eq | exact Hfa_neq]].
  Qed.

  Lemma children_done_no_add (s: @SCCSt V) (u v: V) (done: V -> Prop):
    fa s v <> u ->
    children_done s u (done ∪ [v]) == children_done s u done.
  Proof.
    intros Hfa_neq.
    unfold children_done.
    apply Sets_equiv_Sets_included. split.
    - sets_unfold. intros w [[Hw_done | Hw_v] [Hw_fa Hw_neq]].
      + split; [exact Hw_done | split; [exact Hw_fa | exact Hw_neq]].
      + subst w. exfalso. apply Hfa_neq. exact Hw_fa.
    - sets_unfold. intros w [Hw_done [Hw_fa Hw_neq]].
      split; [left; exact Hw_done | split; [exact Hw_fa | exact Hw_neq]].
  Qed.

  Lemma back_edges_done_add (s: @SCCSt V) (u v: V) (done: V -> Prop):
    In v (stack s) -> fa s v <> u ->
    back_edges_done s u (done ∪ [v]) == back_edges_done s u done ∪ [v].
  Proof.
    intros Hinstack Hfa_neq.
    unfold back_edges_done.
    apply Sets_equiv_Sets_included. split.
    - sets_unfold. intros w [[Hw_done | Hw_v] [Hw_stack Hw_fa]].
      + left. split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
      + subst w. right. reflexivity.
    - sets_unfold. intros w [Hw_back | Hw_v].
      + destruct Hw_back as [Hw_done [Hw_stack Hw_fa]].
        split; [left; exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
      + subst w. split; [right; reflexivity | split; [exact Hinstack | exact Hfa_neq]].
  Qed.

  Lemma back_edges_done_no_add (s: @SCCSt V) (u v: V) (done: V -> Prop):
    ~ In v (stack s) \/ fa s v = u ->
    back_edges_done s u (done ∪ [v]) == back_edges_done s u done.
  Proof.
    intros Hnot.
    unfold back_edges_done.
    apply Sets_equiv_Sets_included. split.
    - sets_unfold. intros w [[Hw_done | Hw_v] [Hw_stack Hw_fa]].
      + split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
      + subst w. destruct Hnot as [Hnstack | Hfa_eq].
        * exfalso. apply Hnstack. exact Hw_stack.
        * exfalso. apply Hw_fa. exact Hfa_eq.
    - sets_unfold. intros w [Hw_done [Hw_stack Hw_fa]].
      split; [left; exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
  Qed.

  (* ================================================================ *)
  (* 10. process_edge Preserves low_forset_inv                         *)
  (* ================================================================ *)

  (** [set_low_preserves_low_forset_inv]: changing [low v] does not affect
      [low_forset_inv u done] when [u <> v] and [~ done v], because [v] is not
      in [children_done u done] and not in [back_edges_done u done].
      [wf_scc_state] is preserved by [set_low_preserves_wf_scc_state]. *)
  Lemma set_low_preserves_low_forset_inv (u v: V) (done: V -> Prop) (n: nat):
    u <> v -> ~ done v ->
    Hoare (fun s: @SCCSt V => low_forset_inv u done s)
          (set_low v n)
          (fun _ s => low_forset_inv u done s).
  Proof.
    intros Hne Hndone.
    unfold set_low. intro_state. hoare_auto_s. subst s.
    destruct s0 as [vis timer fa dfn low stack sccs].
    simpl.
    unfold low_forset_inv, low_forset_inv_core in *.
    destruct H as [Hwf [Huvis Hmin]].
    simpl in Hwf, Huvis, Hmin.
    split; [exact Hwf |].
    split; [exact Huvis |].
    simpl in Hmin |- *.
    (* The outer low value: u <> v so it's unchanged *)
    unfold equiv_decb. destruct (equiv_dec u v) as [Heq_uv | Hneq_uv].
    { exfalso. apply Hne. exact Heq_uv. }
    (* Key: ~ done v, so v is not in children_done or back_edges_done.
       The changed low function agrees with low on all elements of these sets.
       The sets themselves are identical (they depend on fa, not low). *)
    assert (Hchild_set_eq: children_done {| visited := vis; timer := timer; fa := fa; dfn := dfn; low := (fun x => if equiv_decb x v then n else low x); stack := stack; sccs := sccs |} u done == children_done {| visited := vis; timer := timer; fa := fa; dfn := dfn; low := low; stack := stack; sccs := sccs |} u done). {
      unfold children_done. simpl. reflexivity. }
    assert (Hback_set_eq: back_edges_done {| visited := vis; timer := timer; fa := fa; dfn := dfn; low := (fun x => if equiv_decb x v then n else low x); stack := stack; sccs := sccs |} u done == back_edges_done {| visited := vis; timer := timer; fa := fa; dfn := dfn; low := low; stack := stack; sccs := sccs |} u done). {
      unfold back_edges_done. simpl. reflexivity. }
    assert (Hlow_agree: forall w, done w ->
      (fun x => if equiv_decb x v then n else low x) w = low w). {
      intros w Hw_done.
      unfold equiv_decb. destruct (equiv_dec w v) as [Heq_wv | Hneq_wv]; [| reflexivity].
      assert (w = v). { rewrite Heq_wv. reflexivity. }
      subst w. exfalso. exact (Hndone Hw_done). }
    (* Unfold equiv_decb in Hlow_agree to match the simpl'd goal *)
    unfold equiv_decb in Hlow_agree.
    eapply min_eq_forward; [auto using NatLe_TotalOrder | exact Hmin | | ].
    - intros a1 Ha1. exists a1. split; [| apply Nat.le_refl].
      destruct Ha1 as [Ha1 | Ha2].
      + left. destruct Ha1 as [w [[Hw_in Hw_min] Heq_a1]].
        exists w. split.
        * unfold min_object_of_subset. split.
          -- apply Hchild_set_eq. exact Hw_in.
          -- intros x Hx. apply Hchild_set_eq in Hx.
             destruct Hw_in as [Hw_done _].
             assert (Hx_done: x ∈ done) by (destruct Hx as [Hd _]; exact Hd).
             rewrite (Hlow_agree w Hw_done). rewrite (Hlow_agree x Hx_done).
             apply Hw_min. exact Hx.
        * destruct Hw_in as [Hw_done _]. rewrite (Hlow_agree w Hw_done). exact Heq_a1.
      + right. destruct Ha2 as [w [[Hw_in Hw_min] Heq_a1]].
        exists w. split.
        * unfold min_object_of_subset. split.
          -- destruct Hw_in as [Hw_back | Hw_u].
             ++ left. apply Hback_set_eq. exact Hw_back.
             ++ right. exact Hw_u.
          -- intros x Hx. destruct Hx as [Hx_back | Hx_u].
             ++ apply Hw_min. left. apply Hback_set_eq. exact Hx_back.
             ++ subst x. apply Hw_min. right. reflexivity.
        * exact Heq_a1.
    - intros a2 Ha2. exists a2. split; [| apply Nat.le_refl].
      destruct Ha2 as [Ha2 | Ha2'].
      + left. destruct Ha2 as [w [[Hw_in Hw_min] Heq_a2]].
        exists w. split.
        * unfold min_object_of_subset. split.
          -- apply Hchild_set_eq. exact Hw_in.
          -- intros x Hx.
             destruct Hw_in as [Hw_done _].
             assert (Hx_done: x ∈ done) by (destruct Hx as [Hd _]; exact Hd).
             pose proof (Hw_min x Hx) as Hle.
             rewrite (Hlow_agree w Hw_done) in Hle.
             rewrite (Hlow_agree x Hx_done) in Hle.
             exact Hle.
        * destruct Hw_in as [Hw_done _]. rewrite (Hlow_agree w Hw_done) in Heq_a2. exact Heq_a2.
      + right. destruct Ha2' as [w [[Hw_in Hw_min] Heq_a2]].
        exists w. split.
        * unfold min_object_of_subset. split.
          -- destruct Hw_in as [Hw_back | Hw_u].
             ++ left. apply Hback_set_eq. exact Hw_back.
             ++ right. exact Hw_u.
          -- intros x Hx. destruct Hx as [Hx_back | Hx_u].
             ++ apply Hw_min. left. apply Hback_set_eq. exact Hx_back.
             ++ subst x. apply Hw_min. right. reflexivity.
        * exact Heq_a2.
  Qed.

  (** [update_low_tree_edge]: specialized lemma for the tree-edge case.
      After [get' low v], we call [update_low u (low v)]. This lemma
      proves that [low_forset_inv] is preserved. *)
  Lemma update_low_tree_edge (u v: V) (done: V -> Prop) (s: @SCCSt V):
    fa s v = u -> fa s v <> v ->
    low_forset_inv u done s ->
    low_forset_inv u (done ∪ [v])
      (RecordSet.set low (fun low0 x => if equiv_decb x u then Nat.min (low s u) (low s v) else low0 x) s).
  Proof.
    intros Hfa_v_u Hfa_v_neq_v Hinv_s.
    unfold low_forset_inv in Hinv_s.
    destruct Hinv_s as [Hwf [Huvis Hmin]].
    unfold low_forset_inv. simpl.
    split; [exact Hwf |].
    split; [exact Huvis |].
    unfold low_forset_inv_core. simpl.
    unfold children_done, back_edges_done. simpl.
    change (fun x : V => (x ∈ (done ∪ [v]) /\ fa s x = u /\ fa s x <> x)%sets)
      with (children_done s u (done ∪ [v])).
    change (fun x : V => ((x ∈ (done ∪ [v]) /\ In x (stack s) /\ fa s x <> u) \/ x = u)%sets)
      with (fun x => back_edges_done s u (done ∪ [v]) x \/ x = u).
    pose proof (children_done_add s u v done Hfa_v_u Hfa_v_neq_v) as Hchild_eq.
    pose proof (back_edges_done_no_add s u v done (or_intror Hfa_v_u)) as Hback_eq.
    unfold equiv_decb. destruct (equiv_dec u u) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
    eapply min_eq_forward.
    - typeclasses eauto.
    - eapply (min_value_of_subset_nested_update_left_nat
        (A := V) (B := V)
        (low s) (children_done s u done) v
        (dfn s) (fun w => back_edges_done s u done w \/ w = u)
        (low s u)).
      exact Hmin.
    - (* forward: each a1 in old min has a2 in new min with a2 ≤ a1 *)
      intros a1 Ha1.
      exists a1. split.
      { destruct Ha1 as [Ha1_L | Ha1_R].
        - (* a1 from LEFT = min(children_done(done∪[v]), low s) *)
          left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - apply Hchild_eq. exact Hw_in.
            - intros x Hx. apply Hchild_eq in Hx.
              set (f := fun z => if equiv_decb z u then Nat.min (low s u) (low s v) else low s z).
              assert (Hw_neq_u: w <> u). {
                unfold children_done in Hw_in. sets_unfold in Hw_in.
                destruct Hw_in as [Hw_done | Hw_v].
                - destruct Hw_done as [_ [Hw_fa Hw_neq]]. intro Heq. subst w. apply Hw_neq. exact Hw_fa.
                - subst w. intro Heq. apply Hfa_v_neq_v. rewrite Heq. rewrite Heq in Hfa_v_u. exact Hfa_v_u. }
              assert (Hx_neq_u: x <> u). {
                unfold children_done in Hx. sets_unfold in Hx.
                destruct Hx as [Hx_done | Hx_v].
                - destruct Hx_done as [_ [Hx_fa Hx_neq]]. intro Heq. subst x. apply Hx_neq. exact Hx_fa.
                - subst x. intro Heq. apply Hfa_v_neq_v. rewrite Heq. rewrite Heq in Hfa_v_u. exact Hfa_v_u. }
              unfold f, equiv_decb.
              destruct (equiv_dec w u) as [Hw_eq | _]; [exfalso; apply Hw_neq_u; exact Hw_eq|].
              destruct (equiv_dec x u) as [Hx_eq | _]; [exfalso; apply Hx_neq_u; exact Hx_eq|].
              apply Hw_min. exact Hx. }
          { set (f := fun z => if equiv_decb z u then Nat.min (low s u) (low s v) else low s z).
            assert (Hw_neq_u: w <> u). {
              unfold children_done in Hw_in. sets_unfold in Hw_in.
              destruct Hw_in as [Hw_done | Hw_v].
              - destruct Hw_done as [_ [Hw_fa Hw_neq]]. intro Heq. subst w. apply Hw_neq. exact Hw_fa.
              - subst w. intro Heq. apply Hfa_v_neq_v. rewrite Heq. rewrite Heq in Hfa_v_u. exact Hfa_v_u. }
            unfold f, equiv_decb.
            destruct (equiv_dec w u); [exfalso; apply Hw_neq_u; auto | exact Heq_a1]. }
        - (* a1 from RIGHT = min(back_edges(done)∪[u], dfn s) *)
          right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - destruct Hw_in as [Hw_back | Hw_u].
              + left. apply Hback_eq in Hw_back. exact Hw_back.
              + right. exact Hw_u.
            - intros x Hx. destruct Hx as [Hx_back | Hx_u].
              + apply Hw_min. left. apply Hback_eq. exact Hx_back.
              + subst x. apply Hw_min. right. reflexivity. }
          { exact Heq_a1. } }
      { apply Nat.le_refl. }
    - (* backward: each a2 in new min has a1 in old min with a1 ≤ a2 *)
      intros a2 Ha2.
      exists a2. split.
      { destruct Ha2 as [Ha2_L | Ha2_R].
        - (* children_done backward case *)
          left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - (* w ∈ children_done s u done ∪ [v] *)
              apply Hchild_eq. exact Hw_in.
            - (* minimality for union form using NEW low function *)
              intros x Hx. apply Hchild_eq in Hx.
              pose proof (Hw_min x Hx) as Hineq.
              unfold equiv_decb in Hineq. simpl in Hineq.
              destruct (equiv_dec w u) as [Heq_w | Hneq_w];
                [| destruct (equiv_dec x u) as [Heq_x | Hneq_x]].
              + (* w = u: impossible *)
                exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                destruct Hw_in as [Hw_first [Hw_fa' Hw_neq']].
                destruct Hw_first as [Hw_in_done | Hw_eq_v].
                * apply Hw_neq'. rewrite Heq_w. rewrite Heq_w in Hw_fa'. exact Hw_fa'.
                * subst w. apply Hfa_v_neq_v. rewrite Heq_w. rewrite Heq_w in Hfa_v_u. exact Hfa_v_u.
              + (* x = u: impossible *)
                exfalso. unfold children_done in Hx. sets_unfold in Hx.
                destruct Hx as [Hx_first [Hx_fa' Hx_neq']].
                destruct Hx_first as [Hx_in_done | Hx_eq_v].
                * apply Hx_neq'. rewrite Heq_x. rewrite Heq_x in Hx_fa'. exact Hx_fa'.
                * subst x. apply Hfa_v_neq_v. rewrite Heq_x. rewrite Heq_x in Hfa_v_u. exact Hfa_v_u.
              + (* both w ≠ u and x ≠ u: f_new agrees with low s *)
                exact Hineq. }
          { unfold equiv_decb in Heq_a2. simpl in Heq_a2.
            destruct (equiv_dec w u) as [Heq_w | Hneq_w].
            - (* w = u: impossible *)
              exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
              destruct Hw_in as [Hw_first [Hw_fa' Hw_neq']].
              destruct Hw_first as [Hw_in_done | Hw_eq_v].
              + apply Hw_neq'. rewrite Heq_w. rewrite Heq_w in Hw_fa'. exact Hw_fa'.
              + subst w. apply Hfa_v_neq_v. rewrite Heq_w. rewrite Heq_w in Hfa_v_u. exact Hfa_v_u.
            - (* f_new w = low s w, so Heq_a2 gives low s w = a2 *)
              exact Heq_a2. }
        - right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - destruct Hw_in as [Hw_back | Hw_u].
              + left. apply Hback_eq. exact Hw_back.
              + right. exact Hw_u.
            - intros x Hx. destruct Hx as [Hx_back | Hx_u].
              + apply Hw_min. left. apply Hback_eq. exact Hx_back.
              + subst x. apply Hw_min. right. reflexivity. }
          { exact Heq_a2. } }
      { apply Nat.le_refl. }
  Qed.

  Lemma low_forset_inv_implies_low_le_dfn (u: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s -> low s u <= dfn s u.
  Proof.
    unfold low_forset_inv, low_forset_inv_core.
    intros [[_ [_ [_ Hfa]]] [Huvis Hmin] ].
    destruct Hmin as [m [[Hm_in Hm_min] Heq_m]].
    rewrite <- Heq_m.
    assert (Hright: exists r, min_value_of_subset Nat.le (fun w => back_edges_done s u done w \/ w = u) (dfn s) r). {
      apply min_nonempty_exists. exists u. sets_unfold. right. reflexivity. }
    destruct Hright as [r Hr].
    assert (Hr_le_u: r <= dfn s u). {
      destruct Hr as [w [[Hw_in Hw_min] Hr_eq]].
      rewrite <- Hr_eq.
      apply Hw_min. sets_unfold. right. reflexivity. }
    assert (Hm_le_r: m <= r). {
      apply Hm_min. sets_unfold. right. exact Hr. }
    apply Nat.le_trans with (m := r); auto.
  Qed.

  Lemma update_low_back_edge (u v: V) (done: V -> Prop) (s: @SCCSt V):
    dg_step g u v ->
    In v (stack s) ->
    done ⊆ visited s ->
    v ∈ done \/ fa s v <> u ->
    low_forset_inv u done s ->
    low_forset_inv u (done ∪ [v])
      (RecordSet.set low (fun low0 x => if equiv_decb x u then Nat.min (low s u) (dfn s v) else low0 x) s).
  Proof.
    intros Hstep Hstack Hdone_sub Hv_cases Hinv_s.
    unfold low_forset_inv in Hinv_s.
    destruct Hinv_s as [Hwf [Huvis Hmin]].
    unfold low_forset_inv. simpl.
    split; [exact Hwf |].
    split; [exact Huvis |].
    unfold low_forset_inv_core. simpl.
    unfold children_done, back_edges_done. simpl.
    change (fun x : V => (x ∈ (done ∪ [v]) /\ fa s x = u /\ fa s x <> x)%sets)
      with (children_done s u (done ∪ [v])).
    change (fun x : V => ((x ∈ (done ∪ [v]) /\ In x (stack s) /\ fa s x <> u) \/ x = u)%sets)
      with (fun x => back_edges_done s u (done ∪ [v]) x \/ x = u).
    unfold equiv_decb. destruct (equiv_dec u u) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
    destruct Hv_cases as [Hv_done | Hfa_neq].
    - (* Case 1: v ∈ done — sets unchanged, need low s u ≤ dfn s v for min to stay same *)
      assert (Hdone_eq: done ∪ [v] == done). {
        apply Sets_equiv_Sets_included. split.
        - sets_unfold. intros x [Hx_done | Hx_v]; [exact Hx_done | subst x; exact Hv_done].
        - sets_unfold. intros x Hx. left. exact Hx. }
      assert (Hchild_eq: children_done s u (done ∪ [v]) == children_done s u done). {
        unfold children_done.
        apply Sets_equiv_Sets_included. split.
        - sets_unfold. intros x [Hx_done_or_v [Hx_fa Hx_neq]].
          destruct Hx_done_or_v as [Hx_done | Hx_v].
          + split; [exact Hx_done | split; [exact Hx_fa | exact Hx_neq]].
          + subst x. split; [exact Hv_done | split; [exact Hx_fa | exact Hx_neq]].
        - sets_unfold. intros x [Hx_done [Hx_fa Hx_neq]].
          split; [left; exact Hx_done | split; [exact Hx_fa | exact Hx_neq]]. }
      assert (Hback_eq: back_edges_done s u (done ∪ [v]) == back_edges_done s u done). {
        unfold back_edges_done.
        apply Sets_equiv_Sets_included. split.
        - sets_unfold. intros x [Hx_done_or_v [Hx_stack' Hx_fa]].
          destruct Hx_done_or_v as [Hx_done | Hx_v].
          + split; [exact Hx_done | split; [exact Hx_stack' | exact Hx_fa]].
          + subst x. split; [exact Hv_done | split; [exact Hstack | exact Hx_fa]].
        - sets_unfold. intros x [Hx_done [Hx_stack' Hx_fa]].
          split; [left; exact Hx_done | split; [exact Hx_stack' | exact Hx_fa]]. }
      (* Core: prove low s u ≤ dfn s v *)
      assert (Hlow_le_dfn_v: low s u <= dfn s v). {
        destruct (equiv_dec (fa s v) u) as [Hfa_eq | Hfa_neq_u].
        - (* fa s v = u: v is tree child, dfn_valid gives dfn s u < dfn s v *)
          destruct (equiv_dec u v) as [Heq_uv | Hneq_uv].
          + (* u = v: trivial *)
            pose proof (low_forset_inv_implies_low_le_dfn u done s
              (conj Hwf (conj Huvis Hmin))) as Hle.
            rewrite <- Heq_uv. exact Hle.
          + (* u ≠ v *)
            assert (Hfa_v_neq_v: fa s v <> v). {
              rewrite Hfa_eq. intro Heq. apply Hneq_uv. exact Heq. }
            assert (Hvis_v: v ∈ visited s). {
              apply Hdone_sub. exact Hv_done. }
            assert (Htree_edge: dg_step (state_to_dfs_tree g s root) u v). {
              eapply state_to_dfs_tree_step_char_backward.
              - exact Hstep.
              - apply Hfa_eq.
              - exact Hfa_v_neq_v.
              - exact Hvis_v. }
            unfold wf_scc_state in Hwf. destruct Hwf as [Hsiv [Hinv' [Hvalid Hfa_vis]]].
            apply Hvalid in Htree_edge.
            pose proof (low_forset_inv_implies_low_le_dfn u done s
              (conj (conj Hsiv (conj Hinv' (conj Hvalid Hfa_vis))) (conj Huvis Hmin))) as Hle.
            exact (Nat.le_trans _ _ _ Hle (Nat.lt_le_incl _ _ Htree_edge)).
        - (* fa s v ≠ u: v in back_edges_done, min condition gives low s u ≤ dfn s v *)
          assert (Hv_back: back_edges_done s u done v). {
            unfold back_edges_done. sets_unfold.
            split; [exact Hv_done | split; [exact Hstack | exact Hfa_neq_u]]. }
          assert (Hright: exists r, min_value_of_subset Nat.le
            (fun w => back_edges_done s u done w \/ w = u) (dfn s) r). {
            apply min_nonempty_exists. exists v. sets_unfold. left. exact Hv_back. }
          destruct Hright as [r Hr].
          assert (Hr_le_dfv: r <= dfn s v). {
            destruct Hr as [w [[Hw_in Hw_min] Hr_eq]].
            rewrite <- Hr_eq. apply Hw_min. sets_unfold. left. exact Hv_back. }
          destruct Hmin as [a_min [[Ha_min_in Ha_min_min] Ha_min_eq]].
          assert (Ha_min_le_r: a_min <= r). {
            apply Ha_min_min. sets_unfold. right. exact Hr. }
          rewrite Ha_min_eq in Ha_min_le_r. simpl in Ha_min_le_r.
          exact (Nat.le_trans _ _ _ Ha_min_le_r Hr_le_dfv). }
      (* With low s u ≤ dfn s v, min(low, dfn) = low, so low' = low s everywhere *)
      rewrite (Nat.min_l (low s u) (dfn s v) Hlow_le_dfn_v).
      (* Since low' = low s pointwise and sets are equivalent, target = source *)
      eapply min_eq_forward.
      + typeclasses eauto.
      + exact Hmin.
      + (* forward *)
        intros a1 Ha1. exists a1. split.
        { destruct Ha1 as [Ha1_L | Ha1_R].
          - left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
            exists w. split.
            { unfold min_object_of_subset. split.
              - simpl. apply Hchild_eq. exact Hw_in.
              - intros x Hx. apply Hchild_eq in Hx. simpl.
                destruct (equiv_dec w u) as [Hw_eq | Hw_ne].
                + exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                  destruct Hw_in as [Hw_first [Hw_fa Hw_neq]].
                  rewrite Hw_eq in Hw_fa. apply Hw_neq. rewrite Hw_eq. exact Hw_fa.
                + destruct (equiv_dec x u) as [Hx_eq | Hx_ne].
                  * exfalso. unfold children_done in Hx. sets_unfold in Hx.
                    destruct Hx as [Hx_first [Hx_fa Hx_neq]].
                    rewrite Hx_eq in Hx_fa. apply Hx_neq. rewrite Hx_eq. exact Hx_fa.
                  * apply Hw_min. exact Hx. }
            { simpl. destruct (equiv_dec w u) as [Hw_eq | Hw_ne].
              - exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                destruct Hw_in as [Hw_first [Hw_fa Hw_neq]].
                rewrite Hw_eq in Hw_fa. apply Hw_neq. rewrite Hw_eq. exact Hw_fa.
              - exact Heq_a1. }
          - right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
            exists w. split.
            { unfold min_object_of_subset. split.
              - sets_unfold in Hw_in. simpl in Hw_in.
                destruct Hw_in as [Hw_back | Hw_u].
                + simpl. left. apply Hback_eq. exact Hw_back.
                + subst w. simpl. right. reflexivity.
              - intros x Hx. sets_unfold in Hx. simpl in Hx.
                destruct Hx as [Hx_back | Hx_u].
                + apply Hw_min. sets_unfold. simpl. left. apply Hback_eq. exact Hx_back.
                + subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity. }
            { exact Heq_a1. } }
        { apply Nat.le_refl. }
      + (* backward *)
        intros a2 Ha2. exists a2. split.
        { destruct Ha2 as [Ha2_L | Ha2_R].
          - left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
            assert (Hw_min_src: forall b, b ∈ children_done s u (done ∪ [v]) ->
              Nat.le (low s w) (low s b)). {
              intros b Hb. specialize (Hw_min b Hb). simpl in Hw_min.
              destruct (equiv_dec w u) as [Hw_eq | Hw_ne].
              - exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                destruct Hw_in as [Hw_first [Hw_fa Hw_neq]].
                rewrite Hw_eq in Hw_fa. apply Hw_neq. rewrite Hw_eq. exact Hw_fa.
              - destruct (equiv_dec b u) as [Hb_eq | Hb_ne].
                + exfalso. unfold children_done in Hb. sets_unfold in Hb.
                  destruct Hb as [Hb_first [Hb_fa Hb_neq]].
                  rewrite Hb_eq in Hb_fa. apply Hb_neq. rewrite Hb_eq. exact Hb_fa.
                + exact Hw_min. }
            exists w. split.
            { unfold min_object_of_subset. split.
              - simpl. apply Hchild_eq. exact Hw_in.
              - intros x Hx. apply Hchild_eq in Hx. apply Hw_min_src. exact Hx. }
            { simpl. destruct (equiv_dec w u) as [Hw_eq | Hw_ne].
              - exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                destruct Hw_in as [Hw_first [Hw_fa Hw_neq]].
                rewrite Hw_eq in Hw_fa. apply Hw_neq. rewrite Hw_eq. exact Hw_fa.
              - exact Heq_a2. }
          - right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
            exists w. split.
            { unfold min_object_of_subset. split.
              - sets_unfold in Hw_in. simpl in Hw_in.
                destruct Hw_in as [Hw_back | Hw_u].
                + apply Hback_eq in Hw_back. sets_unfold. simpl. left. exact Hw_back.
                + subst w. sets_unfold. simpl. right. reflexivity.
              - intros x Hx. sets_unfold in Hx. simpl in Hx.
                destruct Hx as [Hx_back | Hx_u].
                + apply Hw_min. sets_unfold. simpl. left. apply Hback_eq. exact Hx_back.
                + subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity. }
            { exact Heq_a2. } }
        { apply Nat.le_refl. }
    - (* Case 2: fa s v ≠ u — normal back edge, back_edges_done expands *)
      pose proof (children_done_no_add s u v done Hfa_neq) as Hchild_eq.
      pose proof (back_edges_done_add s u v done Hstack Hfa_neq) as Hback_eq.
      eapply min_eq_forward.
      + typeclasses eauto.
      + eapply (min_value_of_subset_nested_update_right_nat
          (A := V) (B := V)
          (low s) (children_done s u done)
          (dfn s) (fun w => back_edges_done s u done w \/ w = u) v
          (low s u)).
        exact Hmin.
      + (* forward *)
        intros a1 Ha1. exists a1. split.
        { destruct Ha1 as [Ha1_L | Ha1_R].
          - (* children_done unchanged *)
            left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
            exists w. split.
            { unfold min_object_of_subset. split.
              - apply Hchild_eq. exact Hw_in.
              - intros x Hx. apply Hchild_eq in Hx.
                set (f := fun z => if equiv_decb z u then Nat.min (low s u) (dfn s v) else low s z).
                assert (Hw_neq_u: w <> u). {
                  unfold children_done in Hw_in. sets_unfold in Hw_in.
                  destruct Hw_in as [Hw_first [Hw_fa Hw_neq]]. intro Heq. subst w.
                  apply Hw_neq. exact Hw_fa. }
                assert (Hx_neq_u: x <> u). {
                  unfold children_done in Hx. sets_unfold in Hx.
                  destruct Hx as [Hx_first [Hx_fa Hx_neq]]. intro Heq. subst x.
                  apply Hx_neq. exact Hx_fa. }
                unfold f, equiv_decb.
                destruct (equiv_dec w u) as [Hw_eq | _];
                  [exfalso; apply Hw_neq_u; exact Hw_eq|].
                destruct (equiv_dec x u) as [Hx_eq | _];
                  [exfalso; apply Hx_neq_u; exact Hx_eq|].
                apply Hw_min. exact Hx. }
            { set (f := fun z => if equiv_decb z u then Nat.min (low s u) (dfn s v) else low s z).
              assert (Hw_neq_u: w <> u). {
                unfold children_done in Hw_in. sets_unfold in Hw_in.
                destruct Hw_in as [Hw_first [Hw_fa Hw_neq]]. intro Heq. subst w.
                apply Hw_neq. exact Hw_fa. }
              unfold f, equiv_decb.
              destruct (equiv_dec w u); [exfalso; apply Hw_neq_u; auto | exact Heq_a1]. }
          - (* back_edges expands by v *)
            right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
            exists w. split.
            { unfold min_object_of_subset. split.
              - sets_unfold in Hw_in. simpl in Hw_in.
                destruct Hw_in as [[Hw_back | Hw_u] | Hw_v'].
                + sets_unfold. left. apply Hback_eq. sets_unfold. left. exact Hw_back.
                + subst w. sets_unfold. right. reflexivity.
                + subst w. sets_unfold. left. apply Hback_eq. sets_unfold. right. reflexivity.
              - intros x Hx. unfold back_edges_done in Hx. sets_unfold in Hx. simpl in Hx.
                destruct Hx as [[Hx_done_or_v [Hx_stack' Hx_fa]] | Hx_u].
                + destruct Hx_done_or_v as [Hx_done | Hx_v'].
                  * apply Hw_min. sets_unfold. simpl. left. left.
                    unfold back_edges_done. sets_unfold.
                    split; [exact Hx_done | split; [exact Hx_stack' | exact Hx_fa]].
                  * subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
                + subst x. apply Hw_min. sets_unfold. simpl. left. right. reflexivity. }
            { exact Heq_a1. } }
        { apply Nat.le_refl. }
      + (* backward *)
        intros a2 Ha2. exists a2. split.
        { destruct Ha2 as [Ha2_L | Ha2_R].
          - (* children_done unchanged *)
            left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
            exists w. split.
            { unfold min_object_of_subset. split.
              - apply Hchild_eq. exact Hw_in.
              - intros x Hx. apply Hchild_eq in Hx.
                pose proof (Hw_min x Hx) as Hineq.
                unfold equiv_decb in Hineq. simpl in Hineq.
                destruct (equiv_dec w u) as [Heq_w | Hneq_w];
                  [| destruct (equiv_dec x u) as [Heq_x | Hneq_x]].
                + exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                  destruct Hw_in as [Hw_first [Hw_fa Hw_neq]].
                  apply Hw_neq. rewrite Heq_w. rewrite Heq_w in Hw_fa. exact Hw_fa.
                + exfalso. unfold children_done in Hx. sets_unfold in Hx.
                  destruct Hx as [Hx_first [Hx_fa Hx_neq]].
                  apply Hx_neq. rewrite Heq_x. rewrite Heq_x in Hx_fa. exact Hx_fa.
                + exact Hineq. }
            { unfold equiv_decb in Heq_a2. simpl in Heq_a2.
              destruct (equiv_dec w u) as [Heq_w | Hneq_w].
              - exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                destruct Hw_in as [Hw_first [Hw_fa Hw_neq]].
                apply Hw_neq. rewrite Heq_w. rewrite Heq_w in Hw_fa. exact Hw_fa.
              - exact Heq_a2. }
          - (* back_edges expands by v *)
            right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
            exists w. split.
            { unfold min_object_of_subset. split.
              - unfold back_edges_done in Hw_in. sets_unfold in Hw_in. simpl in Hw_in.
                destruct Hw_in as [[Hw_done_or_v [Hw_stack' Hw_fa]] | Hw_u].
                + destruct Hw_done_or_v as [Hw_done | Hw_v'].
                  * sets_unfold. simpl. left. left.
                    unfold back_edges_done. sets_unfold.
                    split; [exact Hw_done | split; [exact Hw_stack' | exact Hw_fa]].
                  * subst w. sets_unfold. simpl. right. reflexivity.
                + subst w. sets_unfold. simpl. left. right. reflexivity.
              - intros x Hx. unfold back_edges_done in Hx. sets_unfold in Hx. simpl in Hx.
                destruct Hx as [[[Hx_done [Hx_stack' Hx_fa]] | Hx_u] | Hx_v'].
                + apply Hw_min. sets_unfold. simpl. left.
                  unfold back_edges_done. sets_unfold.
                  split; [left; exact Hx_done | split; [exact Hx_stack' | exact Hx_fa]].
                + subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
                + subst x. apply Hw_min. sets_unfold. simpl. left.
                  unfold back_edges_done. sets_unfold.
                  split; [right; reflexivity | split; [exact Hstack | exact Hfa_neq]]. }
            { exact Heq_a2. } }
        { apply Nat.le_refl. }
  Qed.

  (** [cross_edge_preserves_low_forset_inv]: Extending [done] by a cross-edge
      neighbor [v] of [u] preserves [low_forset_inv u done].

      A cross edge is characterized by: [v] is already visited, [v] is not on
      the stack, and [v] is not a DFS-tree child of [u] (i.e. [fa s v <> u]).
      Under these conditions, adding [v] to [done] does not change
      [children_done] (which requires [fa s v = u]) nor [back_edges_done]
      (which requires [In v (stack s)]). Hence the min condition in
      [low_forset_inv_core] is unchanged. *)
  Lemma cross_edge_preserves_low_forset_inv (u v: V) (done: V -> Prop) (s: @SCCSt V):
    dg_step g u v ->
    v ∈ visited s ->
    ~ In v (stack s) ->
    fa s v <> u ->
    low_forset_inv u done s ->
    low_forset_inv u (done ∪ [v]) s.
  Proof.
    unfold low_forset_inv, low_forset_inv_core.
    intros Hdg Hvis Hnstack Hfa_neq Hinv.
    destruct Hinv as [Hwf [Huvis Hmin]].
    split; [exact Hwf | split; [exact Huvis |]].
    assert (Hchild_eq: children_done s u (done ∪ [v]) == children_done s u done).
    { apply children_done_no_add; exact Hfa_neq. }
    assert (Hback_eq: back_edges_done s u (done ∪ [v]) == back_edges_done s u done).
    { apply back_edges_done_no_add; left; exact Hnstack. }
    eapply min_eq_forward; [typeclasses eauto | exact Hmin | | ].
    - intros a1 Ha1. exists a1. split.
      { destruct Ha1 as [Ha1_L | Ha1_R].
        - left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - apply Hchild_eq. exact Hw_in.
            - intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx. }
          { exact Heq_a1. }
        - right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - destruct Hw_in as [Hw_back | Hw_u].
              + left. apply Hback_eq. exact Hw_back.
              + right. exact Hw_u.
            - intros x Hx. destruct Hx as [Hx_back | Hx_u].
              + apply Hw_min. left. apply Hback_eq. exact Hx_back.
              + subst x. apply Hw_min. right. reflexivity. }
          { exact Heq_a1. } }
      { apply Nat.le_refl. }
    - intros a2 Ha2. exists a2. split.
      { destruct Ha2 as [Ha2_L | Ha2_R].
        - left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - apply Hchild_eq. exact Hw_in.
            - intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx. }
          { exact Heq_a2. }
        - right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - destruct Hw_in as [Hw_back | Hw_u].
              + left. apply Hback_eq. exact Hw_back.
              + right. exact Hw_u.
            - intros x Hx. destruct Hx as [Hx_back | Hx_u].
              + apply Hw_min. left. apply Hback_eq. exact Hx_back.
              + subst x. apply Hw_min. right. reflexivity. }
          { exact Heq_a2. } }
      { apply Nat.le_refl. }
  Qed.

  Lemma low_forset_inv_children_done_low_le (u v: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s ->
    children_done s u done v ->
    low s u <= low s v.
  Proof.
    unfold low_forset_inv, low_forset_inv_core.
    intros [_ [Huvis Hmin]] Hchild.
    destruct Hmin as [m [[Hm_in Hm_min] Heq_m]].
    rewrite <- Heq_m.
    assert (Hchild_min_exists: exists cmin,
      min_value_of_subset Nat.le (children_done s u done) (low s) cmin). {
      apply min_nonempty_exists. exists v. exact Hchild. }
    destruct Hchild_min_exists as [cmin Hcmin].
    assert (Hcmin_in_union: cmin ∈ (min_value_of_subset Nat.le (children_done s u done) (low s) ∪
      min_value_of_subset Nat.le (fun w => back_edges_done s u done w \/ w = u) (dfn s))). {
      sets_unfold. left. exact Hcmin. }
    assert (Hm_le_cmin: m <= cmin). {
      apply Hm_min. exact Hcmin_in_union. }
    destruct Hcmin as [w [[Hw_in Hw_min] Heq_cmin]].
    assert (Hcmin_le_lowv: cmin <= low s v). {
      rewrite <- Heq_cmin. apply Hw_min. exact Hchild. }
    eapply Nat.le_trans; eauto.
  Qed.

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
    intros Hinv Hfa_eq Hfa_neq Hlow_le.
    unfold low_forset_inv, low_forset_inv_core in Hinv.
    destruct Hinv as [[Hsiv [Hinv' [Hvalid Hfa_vis]]] [Huvis Hmin]].
    unfold low_forset_inv, low_forset_inv_core.
    split; [| split; [exact Huvis |]].
    split; [exact Hsiv | split; [exact Hinv' | split; [exact Hvalid | exact Hfa_vis]]].
    pose proof (children_done_add s u v done Hfa_eq Hfa_neq) as Hchild_eq.
    pose proof (back_edges_done_no_add s u v done (or_intror Hfa_eq)) as Hback_eq.
    apply Sets_equiv_Sets_included in Hchild_eq. destruct Hchild_eq as [Hchild_new_to_old Hchild_old_to_new].
    apply Sets_equiv_Sets_included in Hback_eq. destruct Hback_eq as [Hback_new_to_old Hback_old_to_new].
    pose proof (min_value_of_subset_nested_update_left_nat
        (A := V) (B := V) (low s) (children_done s u done) v
        (dfn s) (fun w => back_edges_done s u done w \/ w = u) (low s u)
        Hmin) as Hmin_new.
    rewrite (Nat.min_l (low s u) (low s v) Hlow_le) in Hmin_new.
    unfold id in Hmin_new.
    eapply min_eq_forward.
    - typeclasses eauto.
    - exact Hmin_new.
    - intros a1 Ha1. exists a1. split.
      { destruct Ha1 as [Ha1_L | Ha1_R].
        - left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
          exists w. split.
          + unfold min_object_of_subset. split.
            * apply Hchild_old_to_new. exact Hw_in.
            * intros x Hx. apply Hchild_new_to_old in Hx. apply Hw_min. exact Hx.
          + exact Heq_a1.
        - right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
          exists w. split.
          + unfold min_object_of_subset. split.
            * destruct Hw_in as [Hw_back | Hw_u].
              -- left. apply Hback_old_to_new. exact Hw_back.
              -- right. exact Hw_u.
            * intros x Hx. destruct Hx as [Hx_back | Hx_u].
              -- apply Hw_min. left. apply Hback_new_to_old. exact Hx_back.
              -- subst x. apply Hw_min. right. reflexivity.
          + exact Heq_a1. }
      { apply Nat.le_refl. }
    - intros a2 Ha2. exists a2. split.
      { destruct Ha2 as [Ha2_L | Ha2_R].
        - left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
          exists w. split.
          + unfold min_object_of_subset. split.
            * apply Hchild_new_to_old. exact Hw_in.
            * intros x Hx. apply Hchild_old_to_new in Hx. apply Hw_min. exact Hx.
          + exact Heq_a2.
        - right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
          exists w. split.
          + unfold min_object_of_subset. split.
            * destruct Hw_in as [Hw_back | Hw_u].
              -- left. apply Hback_new_to_old. exact Hw_back.
              -- right. exact Hw_u.
            * intros x Hx. destruct Hx as [Hx_back | Hx_u].
              -- apply Hw_min. left. apply Hback_old_to_new. exact Hx_back.
              -- subst x. apply Hw_min. right. reflexivity.
          + exact Heq_a2. }
      { apply Nat.le_refl. }
  Qed.



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
    intros Hneq_uv Hndone Hinv.
    unfold low_forset_inv, low_forset_inv_core in *.
    destruct Hinv as [Hwf [Huvis Hmin]].
    unfold low_forset_inv, low_forset_inv_core.
    split; [| split; [|]].
    - (* wf_scc_state: set_low doesn't affect stack_in_visited, dfn_inv, dfn_valid, fa_visited *)
      unfold wf_scc_state in *. destruct Hwf as [Hsiv [Hinv' [Hvalid Hfa_vis]]].
      unfold wf_scc_state. simpl. split; [exact Hsiv | split; [exact Hinv' | split; [exact Hvalid | exact Hfa_vis]]].
    - (* u ∈ visited: set_low doesn't change visited *)
      simpl. exact Huvis.
    - (* low_forset_inv_core: min condition preserved *)
      unfold children_done, back_edges_done in *. simpl.
      unfold equiv_decb. destruct (equiv_dec u v) as [Heq | Hneq]; [exfalso; apply Hneq_uv; exact Heq |].
      set (f_new := fun (x: V) => if if equiv_dec x v then true else false then Nat.min (low s v) n else low s x).
      assert (Hlow_eq_done: forall x, x ∈ done -> f_new x = low s x).
      { intros x0 Hx0_done. unfold f_new.
        destruct (equiv_dec x0 v) as [Heq_x0v | Hneq_x0v].
        - rewrite Heq_x0v in Hx0_done. exfalso. apply Hndone. exact Hx0_done.
        - reflexivity. }
      eapply min_eq_forward; [typeclasses eauto | exact Hmin | | ].
      + (* forward direction *)
        simpl. intros a1 [Ha1_L | Ha1_R].
        * (* children: low s → f_new *)
          exists a1. split.
          -- left. eapply min_eq_forward; [typeclasses eauto | exact Ha1_L | | ].
             ++ intros x (Hx_done & Hx_fa & Hx_neq). exists x. split.
                ** exact (conj Hx_done (conj Hx_fa Hx_neq)).
                ** rewrite (Hlow_eq_done x Hx_done). apply Nat.le_refl.
             ++ intros y (Hy_done & Hy_fa & Hy_neq). exists y. split.
                ** exact (conj Hy_done (conj Hy_fa Hy_neq)).
                ** rewrite (Hlow_eq_done y Hy_done). apply Nat.le_refl.
          -- apply Nat.le_refl.
        * (* back_edges: unchanged *)
          exists a1. split; [right; exact Ha1_R | apply Nat.le_refl].
      + (* backward direction *)
        simpl. intros a2 [Ha2_L | Ha2_R].
        * (* children: f_new → low s *)
          exists a2. split.
          -- left. eapply min_eq_forward; [typeclasses eauto | exact Ha2_L | | ].
             ++ intros x (Hx_done & Hx_fa & Hx_neq). exists x. split.
                ** exact (conj Hx_done (conj Hx_fa Hx_neq)).
                ** rewrite (Hlow_eq_done x Hx_done). apply Nat.le_refl.
             ++ intros y (Hy_done & Hy_fa & Hy_neq). exists y. split.
                ** exact (conj Hy_done (conj Hy_fa Hy_neq)).
                ** rewrite (Hlow_eq_done y Hy_done). apply Nat.le_refl.
          -- apply Nat.le_refl.
        * (* back_edges: unchanged *)
          exists a2. split; [right; exact Ha2_R | apply Nat.le_refl].
  Qed.


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
    intros Hnv_x Hv_vis Hu_vis Hndone_v Hndone_x Hinv.
    unfold low_forset_inv, low_forset_inv_core in *.
    destruct Hinv as [Hwf [Hu_vis' Hmin]].
    unfold wf_scc_state in Hwf. destruct Hwf as [Hsiv [Hinv' [Hvalid Hfa_vis]]].
    unfold low_forset_inv, low_forset_inv_core. simpl.
    split; [| split; [simpl; exact Hu_vis' |]].
    - (* wf_scc_state: set_fa only changes fa x, which is unvisited *)
      unfold wf_scc_state. simpl. split; [exact Hsiv | split; [exact Hinv' |]].
      split.
      + (* dfn_valid: tree edges unchanged since x is unvisited *)
        unfold dfn_valid. intros p q Htree. apply Hvalid.
        unfold dg_step in Htree. destruct Htree as [e [Htree' [Hfst Hsnd]]].
        unfold original_step in Htree'. simpl in Htree'.
        destruct Htree' as [w [Hwvis [Hwfa [Hwfst Hwsnd]]]].
        unfold equiv_decb in Hwfa, Hwfst.
        destruct (equiv_dec w x) as [Heq_wx | Hneq_wx].
        { exfalso. rewrite Heq_wx in Hwvis. exact (Hnv_x Hwvis). }
        { unfold dg_step. exists e. split; [| split]; auto.
          unfold original_step. exists w. repeat split; auto. }
      + (* fa_visited: new child x has parent v which is visited *)
        unfold fa_visited. intros w Hfa_neq_w.
        unfold equiv_decb. destruct (equiv_dec w x) as [Heq_wx | Hneq_wx].
        { rewrite Heq_wx in *. simpl. unfold equiv_decb.
          destruct (equiv_dec x x) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
          exact Hv_vis. }
        { simpl in Hfa_neq_w. unfold equiv_decb in Hfa_neq_w.
          destruct (equiv_dec w x) as [Heq' | Hneq'] in Hfa_neq_w.
          { exfalso. apply Hneq_wx. exact Heq'. }
          { simpl. unfold equiv_decb. destruct (equiv_dec w x) as [Heqw | Hneqw];
              [exfalso; apply Hneq_wx; exact Heqw |]. apply Hfa_vis. exact Hfa_neq_w. } }
    - (* low_forset_inv_core: children_done/back_edges_done unchanged because x ∉ done *)
      set (new_s := RecordSet.set fa (fun (_ : V -> V) (x0 : V) => if equiv_decb x0 x then v else fa s0 x0) s0).
      assert (Hchild_eq: children_done new_s u done == children_done s0 u done). {
        unfold children_done. simpl. apply Sets_equiv_Sets_included. split; sets_unfold.
        - intros w [Hw_done [Hw_fa Hw_neq]]. unfold equiv_decb in Hw_fa, Hw_neq.
          destruct (equiv_dec w x) as [Heqw | Hneqw].
          + rewrite Heqw in Hw_done. exfalso. exact (Hndone_x Hw_done).
          + split; [exact Hw_done | split; [exact Hw_fa | exact Hw_neq]].
        - intros w [Hw_done [Hw_fa Hw_neq]]. unfold equiv_decb.
          destruct (equiv_dec w x) as [Heqw | Hneqw].
          + rewrite Heqw in Hw_done. exfalso. exact (Hndone_x Hw_done).
          + split; [exact Hw_done | split; [exact Hw_fa | exact Hw_neq]]. }
      assert (Hback_eq: back_edges_done new_s u done == back_edges_done s0 u done). {
        unfold back_edges_done. simpl. apply Sets_equiv_Sets_included. split; sets_unfold.
        - intros w [Hw_done [Hw_stack Hw_fa]]. unfold equiv_decb in Hw_fa.
          destruct (equiv_dec w x) as [Heqw | Hneqw].
          + rewrite Heqw in Hw_done. exfalso. exact (Hndone_x Hw_done).
          + split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
        - intros w [Hw_done [Hw_stack Hw_fa]]. unfold equiv_decb.
          destruct (equiv_dec w x) as [Heqw | Hneqw].
          + rewrite Heqw in Hw_done. exfalso. exact (Hndone_x Hw_done).
          + split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]]. }
      subst new_s.
      apply min_eq_forward with (f1 := fun x0 : nat => x0) (f2 := fun x0 : nat => x0) (P1 := fun n : nat => min_value_of_subset Nat.le (children_done s0 u done) (low s0) n \/ min_value_of_subset Nat.le (fun w => back_edges_done s0 u done w \/ w = u) (dfn s0) n) (P2 := fun n : nat => min_value_of_subset Nat.le (children_done (RecordSet.set fa (fun (_ : V -> V) (x0 : V) => if equiv_decb x0 x then v else fa s0 x0) s0) u done) (low s0) n \/ min_value_of_subset Nat.le (fun w => back_edges_done (RecordSet.set fa (fun (_ : V -> V) (x0 : V) => if equiv_decb x0 x then v else fa s0 x0) s0) u done w \/ w = u) (dfn s0) n) (n := low s0 u); [typeclasses eauto|exact Hmin| |].
      { intros a1 Ha1; destruct Ha1 as [Ha1|Ha1].
        - destruct Ha1 as [w' [[Hw_in Hw_min] Heq_a1]]; exists a1; split; [left; exists w'; split; [unfold min_object_of_subset; split; [apply Hchild_eq; exact Hw_in|intros w0 Hw0; apply Hchild_eq in Hw0; apply Hw_min; exact Hw0]|exact Heq_a1]|apply Nat.le_refl].
        - destruct Ha1 as [w' [[Hw_in Hw_min] Heq_a1]]; exists a1; split; [right; exists w'; split; [unfold min_object_of_subset; split; [destruct Hw_in as [Hw_back|Hw_u]; [left; apply Hback_eq; exact Hw_back|right; exact Hw_u]|intros w0 Hw0; destruct Hw0 as [Hw0_back|Hw0_u]; [apply Hw_min; left; apply Hback_eq; exact Hw0_back|subst w0; apply Hw_min; right; reflexivity]]|exact Heq_a1]|apply Nat.le_refl]. }
      { intros a2 Ha2; destruct Ha2 as [Ha2|Ha2].
        - destruct Ha2 as [w' [[Hw_in Hw_min] Heq_a2]]; exists a2; split; [left; exists w'; split; [unfold min_object_of_subset; split; [apply Hchild_eq; exact Hw_in|intros w0 Hw0; apply Hchild_eq in Hw0; apply Hw_min; exact Hw0]|exact Heq_a2]|apply Nat.le_refl].
        - destruct Ha2 as [w' [[Hw_in Hw_min] Heq_a2]]; exists a2; split; [right; exists w'; split; [unfold min_object_of_subset; split; [destruct Hw_in as [Hw_back|Hw_u]; [left; apply Hback_eq; exact Hw_back|right; exact Hw_u]|intros w0 Hw0; destruct Hw0 as [Hw0_back|Hw0_u]; [apply Hw_min; left; apply Hback_eq; exact Hw0_back|subst w0; apply Hw_min; right; reflexivity]]|exact Heq_a2]|apply Nat.le_refl]. }
  Qed.

  (** [preloop_keeps_low_forset_inv_other]: [preloop a] preserves
      [low_forset_inv u done] when [~a in visited].  Helper for
      [preloop_preserves_ancestor_inv]. *)
  Lemma preloop_keeps_low_forset_inv_other (u a: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\ ~ a ∈ visited s /\ ~ done a)
          (preloop a)
          (fun _ s => low_forset_inv u done s /\ a ∈ visited s).
  Proof.
    intro_state. destruct H as [Hinv [Hnv Hndone]].
    unfold low_forset_inv in Hinv.
    destruct Hinv as [Hwf [Huvis Hmin]].
    apply Hoare_conj.
    - (* low_forset_inv u done *)
      unfold low_forset_inv. apply Hoare_conj.
      + (* wf_scc_state *)
        eapply Hoare_conseq_pre. 2: apply (preloop_preserves_wf_scc_state a).
        intros s1 Hs1. subst s1. unfold wf_scc_state_pre. split; [exact Hwf | exact Hnv].
      + apply Hoare_conj.
        * (* u ∈ visited *)
          eapply Hoare_conseq_pre. 2: apply (preloop_keep_visited a u).
          intros s1 Hs1. subst s1. exact Huvis.
        * (* low_forset_inv_core *)
          unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s.
          set (s' := {| visited := visited s0 ∪ [a]; timer := S (timer s0); fa := fa s0;
                        dfn := fun x => if x ==b a then timer s0 else dfn s0 x;
                        low := fun x => if x ==b a then timer s0 else low s0 x;
                        stack := a :: stack s0; sccs := sccs s0 |}).
          assert (Hchild_eq: children_done s' u done == children_done s0 u done). {
            unfold children_done. subst s'. simpl.
            apply Sets_equiv_Sets_included. split; sets_unfold;
              intros x [Hx_done [Hx_fa Hx_neq]]; repeat split; auto. }
          assert (Hback_eq: back_edges_done s' u done == back_edges_done s0 u done). {
            unfold back_edges_done. subst s'. simpl.
            apply Sets_equiv_Sets_included. split; sets_unfold;
              intros x [Hx_done [Hx_stack Hx_fa_neq]]; repeat split; auto;
              try (simpl; right; exact Hx_stack);
              try (destruct Hx_stack as [Heq | Hin]; [subst x; exfalso; apply Hndone; exact Hx_done | exact Hin]). }
          assert (Hlow_child: forall w, children_done s0 u done w -> low s' w = low s0 w). {
            intros w Hw. unfold children_done in Hw. sets_unfold in Hw.
            destruct Hw as [Hw_done _]. subst s'. simpl.
            unfold equiv_decb. destruct (equiv_dec w a) as [Heq | Hneq];
              [exfalso; apply Hndone; rewrite <- Heq; exact Hw_done | reflexivity]. }
          assert (Hlow_back: forall w, back_edges_done s0 u done w -> low s' w = low s0 w). {
            intros w Hw. unfold back_edges_done in Hw. sets_unfold in Hw.
            destruct Hw as [Hw_done _]. subst s'. simpl.
            unfold equiv_decb. destruct (equiv_dec w a) as [Heq | Hneq];
              [exfalso; apply Hndone; rewrite <- Heq; exact Hw_done | reflexivity]. }
          assert (Hdfn_back: forall w, back_edges_done s0 u done w -> dfn s' w = dfn s0 w). {
            intros w Hw. unfold back_edges_done in Hw. sets_unfold in Hw.
            destruct Hw as [Hw_done _]. subst s'. simpl.
            unfold equiv_decb. destruct (equiv_dec w a) as [Heq | Hneq];
              [exfalso; apply Hndone; rewrite <- Heq; exact Hw_done | reflexivity]. }
          assert (Hdfn_u: dfn s' u = dfn s0 u). {
            subst s'. simpl. unfold equiv_decb. destruct (equiv_dec u a) as [Heq | Hneq];
              [exfalso; apply Hnv; rewrite <- Heq; exact Huvis | reflexivity]. }
          assert (Hlow_u: low s' u = low s0 u). {
            subst s'. simpl. unfold equiv_decb. destruct (equiv_dec u a) as [Heq | Hneq];
              [exfalso; apply Hnv; rewrite <- Heq; exact Huvis | reflexivity]. }
          assert (Hlow_all: forall w, children_done s0 u done w \/
            back_edges_done s0 u done w \/ w = u ->
            low s' w = low s0 w). {
            intros w [Hw | [Hw | Heq]].
            - apply Hlow_child. exact Hw.
            - apply Hlow_back. exact Hw.
            - subst w. exact Hlow_u. }
          unfold low_forset_inv_core.
          rewrite Hlow_u. eapply min_eq_forward.
          -- typeclasses eauto.
          -- exact Hmin.
          -- (* forward: old -> new *)
            intros a1 Ha1. exists a1. split; [| apply Nat.le_refl].
            destruct Ha1 as [Ha1_L | Ha1_R].
            ++ (* children_done *)
              left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
              exists w. split; [| rewrite (Hlow_all w (or_introl Hw_in)); exact Heq_a1].
              unfold min_object_of_subset. split.
              ** apply Hchild_eq. exact Hw_in.
              ** intros x Hx. apply Hchild_eq in Hx.
                rewrite (Hlow_all w (or_introl Hw_in)).
                rewrite (Hlow_all x (or_introl Hx)).
                apply Hw_min. exact Hx.
            ++ (* back_edges *)
              right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
              pose proof Hw_in as Hw_in_save.
              assert (Hdfn_w: dfn s' w = dfn s0 w). {
                destruct Hw_in as [Hw_back | Hw_u].
                ** apply Hdfn_back. exact Hw_back.
                ** subst w. exact Hdfn_u. }
              exists w. split; [| rewrite Hdfn_w; exact Heq_a1].
              unfold min_object_of_subset. split.
              ** destruct Hw_in_save as [Hw_back | Hw_u].
                 --- left. apply Hback_eq. exact Hw_back.
                 --- right. exact Hw_u.
              ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                 --- rewrite Hdfn_w. apply Hback_eq in Hx_back.
                     assert (Hdfn_x: dfn s' x = dfn s0 x). { apply Hdfn_back. exact Hx_back. }
                     rewrite Hdfn_x. apply Hw_min. left. exact Hx_back.
                 --- subst x. rewrite Hdfn_w, Hdfn_u. apply Hw_min. right. reflexivity.
          -- (* backward: new -> old *)
            intros a2 Ha2. exists a2. split; [| apply Nat.le_refl].
            destruct Ha2 as [Ha2_L | Ha2_R].
            ++ (* children_done *)
              left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
              exists w. split; [| rewrite (Hlow_all w (or_introl Hw_in)) in Heq_a2; exact Heq_a2].
              unfold min_object_of_subset. split.
              ** apply Hchild_eq. exact Hw_in.
              ** intros x Hx. apply Hchild_eq in Hx.
                pose proof (Hw_min x Hx) as Hle.
                rewrite (Hlow_all w (or_introl Hw_in)) in Hle.
                rewrite (Hlow_all x (or_introl Hx)) in Hle.
                exact Hle.
            ++ (* back_edges *)
              right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
              pose proof Hw_in as Hw_in_save.
              assert (Hdfn_w: dfn s' w = dfn s0 w). {
                destruct Hw_in as [Hw_back | Hw_u].
                ** apply Hback_eq in Hw_back. apply Hdfn_back. exact Hw_back.
                ** subst w. exact Hdfn_u. }
              exists w. split; [| rewrite <- Hdfn_w; exact Heq_a2].
              unfold min_object_of_subset. split.
              ** destruct Hw_in_save as [Hw_back | Hw_u].
                 --- left. apply Hback_eq. exact Hw_back.
                 --- right. exact Hw_u.
              ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                 --- assert (Hx_new: back_edges_done s' u done x). { apply Hback_eq. exact Hx_back. }
                     assert (Hdfn_x: dfn s' x = dfn s0 x). { apply Hdfn_back. exact Hx_back. }
                     pose proof (Hw_min x (or_introl Hx_new)) as Hle.
                     rewrite Hdfn_w, Hdfn_x in Hle. exact Hle.
                 --- subst x. pose proof (Hw_min u (or_intror eq_refl)) as Hle.
                     rewrite Hdfn_w, Hdfn_u in Hle. exact Hle.
    - (* a ∈ visited *)
      eapply Hoare_conseq_pre. 2: apply (preloop_self_visited a).
      intros s1 Hs1. exact I.
  Qed.

  (** [pop_scc_keeps_low_forset_inv_other]: [pop_scc a] preserves
      [low_forset_inv u done].  Helper for [pop_scc_preserves_ancestor_inv]. *)
  Lemma pop_scc_keeps_low_forset_inv_other (u a: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\
                   In a (stack s) /\
                   (forall w, done w -> forall popped' rest',
                     stack_split_at (stack s) a = (popped', rest') -> ~ In w popped'))
          (pop_scc a)
          (fun _ s => low_forset_inv u done s).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s. subst s.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s0) a) as [popped rest] eqn:Hsplit. simpl.
    destruct H as [Hinv [Hin_stack Hdone_not_popped]].
    unfold low_forset_inv, low_forset_inv_core in *.
    destruct Hinv as [Hwf [Huvis Hmin]].
    destruct (stack_split_at_partition (stack s0) a popped rest Hsplit) as [Hrest_incl [Hfresh Hcover]].
    unfold low_forset_inv, low_forset_inv_core. simpl.
    split; [| split; [simpl; exact Huvis |]].
    - (* wf_scc_state *)
      destruct Hwf as [Hsiv [Hinv' [Hvalid Hfa_vis]]].
      unfold wf_scc_state. simpl. split; [| split; [exact Hinv' | split; [exact Hvalid | exact Hfa_vis]]].
      unfold stack_in_visited. intros w Hw. apply Hrest_incl in Hw. apply Hsiv. exact Hw.
    - (* min condition: children_done unchanged (depends on fa), back_edges_done unchanged
         because all done vertices are NOT in popped, hence remain on rest ⊆ stack *)
      unfold children_done, back_edges_done in *. simpl.
      assert (Hback_eq: (fun w => (w ∈ done /\ In w rest /\ fa s0 w <> u) \/ w = u) ==
                        (fun w => (w ∈ done /\ In w (stack s0) /\ fa s0 w <> u) \/ w = u)).
      { apply Sets_equiv_Sets_included. split; sets_unfold.
        - intros w [[Hdone [Hin_rest Hfa_neq]] | Heq_w].
          + left. split; [exact Hdone | split; [apply Hrest_incl; exact Hin_rest | exact Hfa_neq]].
          + right. exact Heq_w.
        - intros w [[Hdone [Hin_stk Hfa_neq]] | Heq_w].
          + left. split; [exact Hdone |].
            split; [| exact Hfa_neq].
            assert (Hin_rest_or_popped: In w rest \/ In w popped).
            { apply Hcover in Hin_stk. destruct Hin_stk as [Hp | Hr]; [right; exact Hp | left; exact Hr]. }
            destruct Hin_rest_or_popped as [Hr | Hp]; [exact Hr |].
            exfalso. exact (Hdone_not_popped w Hdone popped rest eq_refl Hp).
          + right. exact Heq_w. }
      eapply min_eq_forward; [auto using NatLe_TotalOrder | exact Hmin | | ].
      + intros a1 Ha1. exists a1. split; [| apply Nat.le_refl].
        destruct Ha1 as [Ha1_L | Ha1_R].
        * left. exact Ha1_L.
        * right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
          exists w. split.
          -- unfold min_object_of_subset. split.
             ++ apply Hback_eq. exact Hw_in.
             ++ intros x Hx. apply Hback_eq in Hx. apply Hw_min. exact Hx.
          -- exact Heq_a1.
      + intros a2 Ha2. exists a2. split; [| apply Nat.le_refl].
        destruct Ha2 as [Ha2_L | Ha2_R].
        * left. exact Ha2_L.
        * right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
          exists w. split.
          -- unfold min_object_of_subset. split.
             ++ apply Hback_eq. exact Hw_in.
             ++ intros x Hx. apply Hback_eq in Hx. apply Hw_min. exact Hx.
          -- exact Heq_a2.
  Qed.

  (** [preloop_keeps_fa]: [preloop a] does not modify the [fa] field,
      so [fa s a = p] is preserved. *)
  Lemma preloop_keeps_fa (a p: V):
    Hoare (fun s => fa s a = p)
          (preloop a)
          (fun _ s => fa s a = p /\ a ∈ visited s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
    split. { reflexivity. } { sets_unfold. right. reflexivity. }
  Qed.

  (** Helper lemmas for the tree-edge step.  The actual tree-edge lemmas
      used in the main proof are:
      - [set_fa_W_preserves_low_forset_inv]: a convenience lemma for the
        direct-parent case, assuming [W v] already satisfies the ancestor
        invariant;
      - [tree_edge_preserves_low_forset_inv_lowlink]: the tree-edge lemma
        used by [forset_keep_low_forset_inv], which only assumes the
        low-link induction hypothesis.

      Both rely on the following facts:
      1. [set_fa_preserves_wf_scc_state_pre]: after [set_fa v u] the state
         satisfies [low_pre v] as long as [u] is visited and [v] is unvisited.
      2. [set_fa_preserves_low_forset_inv_for_new_child]: [set_fa v u] does
         not change [children_done]/[back_edges_done] for [u] (v ∉ done), and
         preserves [low_forset_inv u done].
      3. [set_fa_preserves_min]: the min-value in [low_forset_inv_core] is
         preserved by [set_fa v u] when [v] is not in [done]. *)
  Lemma set_fa_preserves_min (u v: V) (done: V -> Prop) (s0: @SCCSt V): ~ done v ->
    min_value_of_subset Nat.le (min_value_of_subset Nat.le (children_done s0 u done) (low s0) ∪ min_value_of_subset Nat.le (fun w => back_edges_done s0 u done w \/ w = u) (dfn s0)) (fun x => x) (low s0 u) ->
    min_value_of_subset Nat.le (min_value_of_subset Nat.le (children_done (RecordSet.set fa (fun _ x => if equiv_decb x v then u else fa s0 x) s0) u done) (low s0) ∪ min_value_of_subset Nat.le (fun w => back_edges_done (RecordSet.set fa (fun _ x => if equiv_decb x v then u else fa s0 x) s0) u done w \/ w = u) (dfn s0)) (fun x => x) (low s0 u).
  Proof.
    intros Hndone Hmin_s0. set (f := fun (fa0 : V -> V) (x : V) => if equiv_decb x v then u else fa0 x).
    assert (Hchild_eq: children_done (set fa f s0) u done == children_done s0 u done). {
      unfold children_done. simpl. apply Sets_equiv_Sets_included. split; sets_unfold.
      - intros w [Hw_done [Hw_fa Hw_neq]]. unfold f in Hw_fa, Hw_neq; simpl in Hw_fa, Hw_neq.
        unfold equiv_decb in Hw_fa, Hw_neq. destruct (equiv_dec w v) as [Heqw | Hneqw].
        + rewrite Heqw in Hw_done. exfalso. exact (Hndone Hw_done).
        + split; [exact Hw_done | split; [exact Hw_fa | exact Hw_neq]].
      - intros w [Hw_done [Hw_fa Hw_neq]]. unfold f; simpl; unfold equiv_decb.
        destruct (equiv_dec w v) as [Heqw | Hneqw].
        + rewrite Heqw in Hw_done. exfalso. exact (Hndone Hw_done).
        + split; [exact Hw_done | split; [exact Hw_fa | exact Hw_neq]]. }
    assert (Hback_eq: back_edges_done (set fa f s0) u done == back_edges_done s0 u done). {
      unfold back_edges_done. simpl. apply Sets_equiv_Sets_included. split; sets_unfold.
      - intros w [Hw_done [Hw_stack Hw_fa]]. unfold f in Hw_fa; simpl in Hw_fa; unfold equiv_decb in Hw_fa.
        destruct (equiv_dec w v) as [Heqw | Hneqw].
        + rewrite Heqw in Hw_done. exfalso. exact (Hndone Hw_done).
        + split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
      - intros w [Hw_done [Hw_stack Hw_fa]]. unfold f; simpl; unfold equiv_decb.
        destruct (equiv_dec w v) as [Heqw | Hneqw].
        + rewrite Heqw in Hw_done. exfalso. exact (Hndone Hw_done).
        + split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]]. }
    unfold f.
    apply min_eq_forward with (f1 := fun x : nat => x) (f2 := fun x : nat => x)
      (P1 := fun n => min_value_of_subset Nat.le (children_done s0 u done) (low s0) n \/ min_value_of_subset Nat.le (fun w => back_edges_done s0 u done w \/ w = u) (dfn s0) n)
      (P2 := fun n => min_value_of_subset Nat.le (children_done (RecordSet.set fa (fun _ x => if equiv_decb x v then u else fa s0 x) s0) u done) (low s0) n \/ min_value_of_subset Nat.le (fun w => back_edges_done (RecordSet.set fa (fun _ x => if equiv_decb x v then u else fa s0 x) s0) u done w \/ w = u) (dfn s0) n) (n := low s0 u);
      [typeclasses eauto|exact Hmin_s0| |].
    { intros a1 Ha1; destruct Ha1 as [Ha1|Ha1].
      - destruct Ha1 as [w' [[Hw_in Hw_min] Heq_a1]]; exists a1; split; [left; exists w'; split; [unfold min_object_of_subset; split; [apply Hchild_eq; exact Hw_in|intros x Hx; apply Hchild_eq in Hx; apply Hw_min; exact Hx]|exact Heq_a1]|apply Nat.le_refl].
      - destruct Ha1 as [w' [[Hw_in Hw_min] Heq_a1]]; exists a1; split; [right; exists w'; split; [unfold min_object_of_subset; split; [destruct Hw_in as [Hw_back|Hw_u]; [left; apply Hback_eq; exact Hw_back|right; exact Hw_u]|intros x Hx; destruct Hx as [Hx_back|Hx_u]; [apply Hw_min; left; apply Hback_eq; exact Hx_back|subst x; apply Hw_min; right; reflexivity]]|exact Heq_a1]|apply Nat.le_refl]. }
    { intros a2 Ha2; destruct Ha2 as [Ha2|Ha2].
      - destruct Ha2 as [w' [[Hw_in Hw_min] Heq_a2]]; exists a2; split; [left; exists w'; split; [unfold min_object_of_subset; split; [apply Hchild_eq; exact Hw_in|intros x Hx; apply Hchild_eq in Hx; apply Hw_min; exact Hx]|exact Heq_a2]|apply Nat.le_refl].
      - destruct Ha2 as [w' [[Hw_in Hw_min] Heq_a2]]; exists a2; split; [right; exists w'; split; [unfold min_object_of_subset; split; [destruct Hw_in as [Hw_back|Hw_u]; [left; apply Hback_eq; exact Hw_back|right; exact Hw_u]|intros x Hx; destruct Hx as [Hx_back|Hx_u]; [apply Hw_min; left; apply Hback_eq; exact Hx_back|subst x; apply Hw_min; right; reflexivity]]|exact Heq_a2]|apply Nat.le_refl]. }
  Qed.

  (** [pop_scc_preserves_done_visited]: [pop_scc a] does not modify
      [visited] (only [stack] and [sccs]), so [done_visited done] is
      trivially preserved.

      Note: [tarjan_scc_keep_visited] is already available in
      [Tarjan_scc_basics]; the local duplicate has been removed. *)
  Lemma pop_scc_preserves_done_visited (a: V) (done: V -> Prop):
    Hoare (fun s => done_visited done s) (pop_scc a) (fun _ s => done_visited done s).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s. subst s. simpl.
    unfold pop_scc_state. destruct (stack_split_at (stack s0) a) as [popped rest]. simpl.
    exact H.
  Qed.

  (** [pop_scc_preserves_dfn_injective]: [pop_scc u] does not modify
      [dfn] or [visited] (only [stack] and [sccs]), so [dfn_injective]
      is trivially preserved. *)
  Lemma pop_scc_preserves_dfn_injective (u: V):
    Hoare (fun s: @SCCSt V => dfn_injective s)
          (pop_scc u)
          (fun _ s => dfn_injective s).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s. subst s. simpl.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s0) u) as [popped rest]. simpl.
    exact H.
  Qed.

  (* ================================================================ *)
  (* 10.5. Ancestor Invariant Preservation Lemmas                      *)
  (* ================================================================ *)

  (** Lemmas to prove that operations on vertex [cur] preserve
      [low_forset_inv ancestor done] and [fa s cur = parent] for an
      ancestor [ancestor] with direct parent [parent].
      These are the building blocks for the generalized
      [W_preserves_ancestor_inv]. *)

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
    induction stk as [| x xs IH] in a, w |- *;
      intros Ha_in popped rest Hsplit Hw_in Hw_ne_a.
    { destruct Ha_in. }
    { simpl in Hsplit.
      destruct (equiv_decb x a) eqn:Heq_xa.
      { apply pair_equal_spec in Hsplit. destruct Hsplit as [Hpop Hrest]; subst popped rest.
        simpl in Hw_in. destruct Hw_in as [Heq_wx | []].
        exfalso. apply Hw_ne_a. rewrite <- Heq_wx.
        unfold equiv_decb in Heq_xa. destruct (equiv_dec x a) as [Heq' | Hneq];
          [exact Heq' | discriminate Heq_xa]. }
      { destruct (stack_split_at xs a) as (popped_inner, rest_inner) eqn:Hsplit_inner.
        apply pair_equal_spec in Hsplit. destruct Hsplit as [Hpop Hrest]; subst popped rest.
        simpl in Hw_in. destruct Hw_in as [Heq_wx | Hw_in_inner].
        { subst w. destruct Ha_in as [Heq_ax | Ha_in_xs].
          { exfalso. unfold equiv_decb in Heq_xa.
            rewrite Heq_ax in Heq_xa. destruct (equiv_dec a a) as [_ | Hc];
              [discriminate Heq_xa | exfalso; apply Hc; reflexivity]. }
          { exists (@nil V). exists xs. split; [reflexivity | exact Ha_in_xs]. } }
        { destruct Ha_in as [Heq_ax | Ha_in_xs].
          { exfalso. unfold equiv_decb in Heq_xa.
            rewrite Heq_ax in Heq_xa. destruct (equiv_dec a a) as [_ | Hc];
              [discriminate Heq_xa | exfalso; apply Hc; reflexivity]. }
          { destruct (IH a w Ha_in_xs popped_inner rest_inner Hsplit_inner Hw_in_inner Hw_ne_a)
              as (l1 & l2 & Heq & Ha_in_l2).
            exists (x :: l1). exists l2. split.
            { rewrite Heq. reflexivity. }
            { exact Ha_in_l2. } } } } }
  Qed.

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
    intros Hlow Hdv Hndone Ha_in_stack Hdfn_order Hdfn_lt w Hdone popped' rest' Hsplit.
    intro Hw_in_popped.
    destruct (equiv_dec w a) as [Heq_wa | Hneq_wa].
    { exfalso. apply Hndone. rewrite <- Heq_wa. exact Hdone. }
    destruct (stack_split_at_in_popped_before_a (stack s) a w
      Ha_in_stack popped' rest' Hsplit Hw_in_popped Hneq_wa)
      as [l1 [l2 [Heq_stk Ha_in_l2]]].
    assert (Hw_in_stk: In w (stack s)). {
      rewrite Heq_stk. rewrite List.in_app_iff. right. simpl. left. reflexivity. }
    assert (Ha_in_stk: In a (stack s)). {
      rewrite Heq_stk. rewrite List.in_app_iff. right. simpl. right. exact Ha_in_l2. }
    unfold stack_dfn_order in Hdfn_order.
    assert (Hdfn_le: dfn s a <= dfn s w). {
      apply (Hdfn_order w a Hw_in_stk Ha_in_stk).
      exists l1. exists l2. split; [exact Heq_stk | exact Ha_in_l2]. }
    assert (Hdfn_lt': dfn s w < dfn s a). {
      apply (Hdfn_lt w Hdone Hw_in_stk). }
    lia.
  Qed.

  (** [pop_scc_preserves_ancestor_inv]: [pop_scc v] only modifies
      [stack] and [sccs]; [fa], [low], [dfn], [visited] are unchanged.
      For an ancestor [u] of [v] that stays on the stack, the ancestor
      invariant is preserved, including the new stack-ordering conjuncts.

      The precondition additionally requires:
      - [~ done v]: [v] has not yet been moved into [done] (it is the
        currently active vertex whose SCC is being popped).
      - [forall w, done w -> In w (stack s) -> dfn s w < dfn s v]: any
        already-done neighbor of [u] that is still on the stack lies below
        [v], so it is not removed by [pop_scc v].  This is needed to apply
        [pop_scc_keeps_low_forset_inv_other] / [done_not_popped_by_subtree_pop_scc]. *)
    (** [pop_scc_preserves_ancestor_inv]: [pop_scc cur] only modifies
      [stack] and [sccs]; [fa], [low], [dfn], [visited] are unchanged.
      For an ancestor [ancestor] of [cur] that stays on the stack, the
      ancestor invariant is preserved.

      The precondition additionally requires:
      - [~ done cur]: [cur] has not yet been moved into [done];
      - [forall w, done w -> In w (stack s) -> dfn s w < dfn s cur]: any
        already-done neighbor of [ancestor] that is still on the stack lies
        below [cur], so it is not removed by [pop_scc cur];
      - [dfn s ancestor < dfn s cur]: [ancestor] is below [cur] on the stack.
        This is the missing piece identified in
        docs/dev/20260623-tarjan-scc-is-low-proof-gaps.md: the old
        [(ancestor = parent \\ dg_step g ancestor parent)] premise was too
        weak to derive [In ancestor (stack s)] in the postcondition. *)
  Lemma pop_scc_preserves_ancestor_inv (ancestor parent cur: V) (done: V -> Prop):
    ancestor <> cur -> parent <> cur -> dg_step g parent cur ->
    Hoare (fun s => low_forset_inv ancestor done s /\ fa s cur = parent /\ ~ done cur /\
                   In cur (stack s) /\ In ancestor (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ done_visited done s /\
                   (forall w, done w -> In w (stack s) -> dfn s w < dfn s cur) /\
                   dfn s ancestor < dfn s cur)
          (pop_scc cur)
          (fun _ s => low_forset_inv ancestor done s /\ fa s cur = parent /\ In ancestor (stack s) /\
                      stack_dfn_order s /\ dfn_injective s /\ done_visited done s).
  Proof.
    intros Hanc_ne Hpar_ne Hdg.
    apply Hoare_conj. (* low_forset_inv ancestor done *)
    - apply (Hoare_conseq_pre _
        (fun s => low_forset_inv ancestor done s /\ In cur (stack s) /\
                  (forall w, done w -> forall popped' rest',
                    stack_split_at (stack s) cur = (popped', rest') -> ~ In w popped'))
        (pop_scc cur) (fun _ s => low_forset_inv ancestor done s)).
      { intros s [Hlow [Hfa [Hnd [Hinc [Hina [Horder [Hinj [Hdv [Hdfn_lt Hdfn_anc]]]]]]]]].
        split; [exact Hlow | split; [exact Hinc |]].
        eapply done_not_popped_by_subtree_pop_scc; eauto. }
      apply pop_scc_keeps_low_forset_inv_other.
    - apply Hoare_conj.
      + (* fa s cur = parent *)
        unfold pop_scc. intro_state. hoare_auto_s. subst. simpl.
        unfold pop_scc_state.
        destruct (stack_split_at (stack s0) cur) as [popped rest]. simpl.
        destruct H as [_ [Hfa _]]. exact Hfa.
      + apply Hoare_conj.
        * (* In ancestor (stack s) *)
          unfold pop_scc. intro_state. hoare_auto_s. subst. simpl.
          unfold pop_scc_state.
          destruct (stack_split_at (stack s0) cur) as [popped rest] eqn:Hsplit. simpl.
          destruct H as [_ [_ [_ [Hinc [Hina [Horder [Hinj [Hdv [Hdfn_lt Hdfn_anc]]]]]]]]].
          destruct (stack_split_at_partition (stack s0) cur popped rest Hsplit)
            as [_ [_ Hcover]].
          destruct (Hcover ancestor Hina) as [Hpop | Hrest].
          { (* ancestor ∈ popped: contradiction via dfn ordering *)
            destruct (stack_split_at_in_popped_before_a (stack s0) cur ancestor
              Hinc popped rest Hsplit Hpop Hanc_ne)
              as [l1 [l2 [Hstk_eq Hcur_in_l2]]].
            assert (Hanc_in_stk: In ancestor (stack s0)). {
              rewrite Hstk_eq. apply List.in_or_app. right. simpl. left. reflexivity. }
            assert (Hcur_in_stk: In cur (stack s0)). {
              rewrite Hstk_eq. apply List.in_or_app. right. simpl. right. exact Hcur_in_l2. }
            assert (Horder_res: exists l1' l2', stack s0 = l1' ++ ancestor :: l2' /\ In cur l2').
            { exists l1. exists l2. split; [exact Hstk_eq | exact Hcur_in_l2]. }
            pose proof (Horder ancestor cur Hanc_in_stk Hcur_in_stk Horder_res) as Hle.
            lia. }
          { exact Hrest. }
        * apply Hoare_conj.
          { apply (Hoare_conseq_pre _ (fun s => stack_dfn_order s /\ In cur (stack s))
              (pop_scc cur) (fun _ s => stack_dfn_order s)).
            { intros s [_ [_ [_ [Hinc [Hina [Horder _]]]]]]. split; [exact Horder | exact Hinc]. }
            apply pop_scc_preserves_stack_dfn_order. }
          apply Hoare_conj.
          { apply (Hoare_conseq_pre _ (fun s => dfn_injective s)
              (pop_scc cur) (fun _ s => dfn_injective s)).
            { intros s [_ [_ [_ [_ [_ [_ [Hinj _]]]]]]]. exact Hinj. }
            apply pop_scc_preserves_dfn_injective. }
          apply (Hoare_conseq_pre _ (fun s => done_visited done s)
            (pop_scc cur) (fun _ s => done_visited done s)).
          { intros s [_ [_ [_ [_ [_ [_ [_ [Hdv _]]]]]]]]. exact Hdv. }
          apply pop_scc_preserves_done_visited.
  Qed.

  (** [preloop_preserves_ancestor_inv]: Generalized to an arbitrary
      ancestor [ancestor] of [cur].  [preloop cur] only modifies fields
      local to [cur], so it preserves [low_forset_inv ancestor done],
      [fa s cur = parent], and the stack-ordering conjuncts.

      It also preserves [dfn s ancestor < dfn s cur]: [preloop cur] assigns
      [dfn cur] to the current timer (which is strictly larger than
      [dfn ancestor], since [ancestor] was already visited and assigned a
      dfn earlier) and does not modify [dfn ancestor]. *)
  Lemma preloop_preserves_ancestor_inv (ancestor parent cur: V) (done: V -> Prop):
    ancestor <> cur -> parent <> cur ->
    Hoare (fun s => low_forset_inv ancestor done s /\ fa s cur = parent /\ ~ cur ∈ visited s /\ ~ done cur /\
                   In ancestor (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ done_visited done s)
          (preloop cur)
          (fun _ s => low_forset_inv ancestor done s /\ fa s cur = parent /\ In ancestor (stack s) /\
                      stack_dfn_order s /\ dfn_injective s /\ done_visited done s /\
                      dfn s ancestor < dfn s cur).
  Proof.
    intros Hanc_ne Hpar_ne.
    apply Hoare_conj. (* low_forset_inv ancestor done *)
    - apply (Hoare_conseq_pre _
        (fun s => low_forset_inv ancestor done s /\ ~ cur ∈ visited s /\ ~ done cur)
        (preloop cur) (fun _ s => low_forset_inv ancestor done s)).
      { intros s [Hlow [Hfa [Hnv [Hnd [Hina [Horder [Hinj Hdv]]]]]]].
        split; [exact Hlow | split; [exact Hnv | exact Hnd]]. }
      apply (Hoare_conseq_post
        (fun s => _) (preloop cur)
        (fun _ s => low_forset_inv ancestor done s)
        (fun _ s => low_forset_inv ancestor done s /\ cur ∈ visited s)).
      { intros _ s [Hlow _]. exact Hlow. }
      apply preloop_keeps_low_forset_inv_other.
    - apply Hoare_conj.
      + (* fa s cur = parent *)
        apply (Hoare_conseq_pre _ (fun s => fa s cur = parent)
          (preloop cur) (fun _ s => fa s cur = parent)).
        { intros s [_ [Hfa _]]. exact Hfa. }
        apply (Hoare_conseq_post
          (fun s => fa s cur = parent) (preloop cur)
          (fun _ s => fa s cur = parent)
          (fun _ s => fa s cur = parent /\ cur ∈ visited s)).
        { intros _ s [Hfa _]. exact Hfa. }
        apply (preloop_keeps_fa cur parent).
      + apply Hoare_conj.
        * (* In ancestor (stack s) *)
          apply (Hoare_conseq_pre _ (fun s => In ancestor (stack s))
            (preloop cur) (fun _ s => In ancestor (stack s))).
          { intros s [_ [_ [_ [_ [Hina _]]]]]. exact Hina. }
          unfold preloop, set_dfn, set_low, incr_timer, push_stack, visit.
          intro_state. hoare_auto_s. subst. simpl. auto.
        * apply Hoare_conj.
          { (* stack_dfn_order *)
            apply (Hoare_conseq_pre _
              (fun s => stack_dfn_order s /\ dfn_inv s /\ stack_in_visited s /\ ~ cur ∈ visited s)
              (preloop cur) (fun _ s => stack_dfn_order s)).
            { intros s [Hlow [Hfa [Hnv [Hnd [Hina [Horder [Hinj Hdv]]]]]]].
              destruct Hlow as [[Hsiv [Hinv' _]] _].
              split; [exact Horder | split; [exact Hinv' | split; [exact Hsiv | exact Hnv]]]. }
            apply preloop_preserves_stack_dfn_order. }
          apply Hoare_conj.
          { (* dfn_injective *)
            apply (Hoare_conseq_pre _
              (fun s => dfn_injective s /\ dfn_inv s /\ ~ cur ∈ visited s)
              (preloop cur) (fun _ s => dfn_injective s)).
            { intros s [Hlow [Hfa [Hnv [Hnd [Hina [Horder [Hinj Hdv]]]]]]].
              destruct Hlow as [[_ [Hinv' _]] _].
              split; [exact Hinj | split; [exact Hinv' | exact Hnv]]. }
            apply preloop_preserves_dfn_injective. }
          apply Hoare_conj.
          { (* done_visited done s *)
            apply (Hoare_conseq_pre _ (fun s => done_visited done s)
              (preloop cur) (fun _ s => done_visited done s)).
            { intros s [Hlow [Hfa [Hnv [Hnd [Hina [Horder [Hinj Hdv]]]]]]]. exact Hdv. }
            unfold preloop, set_dfn, set_low, incr_timer, push_stack, visit.
            intro_state. hoare_auto_s. subst. simpl.
            unfold done_visited. intros w Hw. simpl. sets_unfold. left. apply H. exact Hw. }
          (* dfn s ancestor < dfn s cur *)
          apply (Hoare_conseq_pre _
            (fun s => low_forset_inv ancestor done s /\ ~ cur ∈ visited s)
            (preloop cur) (fun _ s => dfn s ancestor < dfn s cur)).
          { intros s [Hlow [Hfa [Hnv [Hnd [Hina [Horder [Hinj Hdv]]]]]]].
            split; [exact Hlow | exact Hnv]. }
          unfold preloop, set_dfn, set_low, incr_timer, push_stack, visit.
          intro_state. hoare_auto_s. subst. simpl.
          destruct H as [Hlow Hnv].
          destruct Hlow as [[_ [Hinv' _]] [Hanc_vis _]].
          unfold dfn_inv in Hinv'. destruct Hinv' as [Hdfn_lt _].
          unfold equiv_decb.
          destruct (equiv_dec ancestor cur) as [Heq | Hneq].
          { exfalso. apply Hanc_ne. exact Heq. }
          destruct (equiv_dec cur cur) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
          apply Hdfn_lt. exact Hanc_vis.
  Qed.

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
  (** [preloop_above_existing]: After [preloop x], [x] is above any
      vertex [y] that was on the stack before (and [x ≠ y]). *)
  Lemma preloop_above_existing (x y: V):
    Hoare (fun s => In y (stack s))
          (preloop x)
          (fun _ s => exists l1 l2, stack s = l1 ++ x :: l2 /\ In y l2).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
    exists (@nil V). exists (stack s0). split; [reflexivity | exact H].
  Qed.

  (** [W_preserves_ancestor_inv]: During [W cur] (= [tarjan_scc g cur]),
      the ancestor invariant for an arbitrary ancestor [ancestor] of [cur]
      is preserved.

      The parameters are:
      - [ancestor]: the vertex whose [low_forset_inv] we preserve;
      - [parent]: the direct DFS parent of [cur] (so [fa s cur = parent]);
      - [cur]: the vertex being recursively processed.

      The invariant is:
        - [low_forset_inv ancestor done s]
        - [fa s cur = parent]
        - [~ cur ∈ visited s], [~ done cur], [done_visited done s]
        - [In ancestor (stack s)]
        - [stack_dfn_order s]
        - [dfn_injective s]
      and the postcondition additionally records
        - [dfn s ancestor < dfn s cur]  (needed for [pop_scc_preserves_ancestor_inv])
        - every [done] vertex still on the stack has dfn strictly smaller than [cur].

      Importantly, the precondition does *not* require
      [dfn s ancestor < dfn s cur]; that ordering is established by the
      [preloop cur] step inside [W cur] (which assigns [dfn cur] a fresh
      value larger than [dfn ancestor]).  Requiring it in the precondition
      would make the lemma unusable at the entry of [W cur], because [cur]
      is then unvisited and [dfn s cur = 0] by [dfn_inv]. *)

  (** [preloop_establishes_ancestor_inv]: Like [preloop_preserves_ancestor_inv]
      but does *not* require [dfn s ancestor < dfn s cur] in the precondition.
      [preloop cur] assigns [dfn cur] the current timer, which is strictly
      larger than [dfn ancestor] (since [ancestor] is already visited). *)
  Lemma preloop_establishes_ancestor_inv (ancestor parent cur: V) (done: V -> Prop):
    ancestor <> cur -> parent <> cur ->
    Hoare (fun s => low_forset_inv ancestor done s /\ fa s cur = parent /\ ~ cur ∈ visited s /\ ~ done cur /\
                   In ancestor (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ done_visited done s)
          (preloop cur)
          (fun _ s => low_forset_inv ancestor done s /\ fa s cur = parent /\ In ancestor (stack s) /\
                      stack_dfn_order s /\ dfn_injective s /\ done_visited done s /\
                      dfn s ancestor < dfn s cur).
  Proof.
    intros Hanc_ne Hpar_ne.
    apply Hoare_conj. (* low_forset_inv ancestor done *)
    - apply (Hoare_conseq_pre _ (fun s => low_forset_inv ancestor done s /\ ~ cur ∈ visited s /\ ~ done cur)
        (preloop cur) (fun _ s => low_forset_inv ancestor done s)).
      { intros s [Hlow [Hfa [Hnv [Hnd _]]]]. split; [exact Hlow | split; [exact Hnv | exact Hnd]]. }
      apply (Hoare_conseq_post _ (preloop cur) (fun _ s => low_forset_inv ancestor done s)
        (fun _ s => low_forset_inv ancestor done s /\ cur ∈ visited s)).
      { intros _ s [Hlow _]. exact Hlow. }
      apply preloop_keeps_low_forset_inv_other.
    - apply Hoare_conj.
      + apply (Hoare_conseq_pre _ (fun s => fa s cur = parent)
          (preloop cur) (fun _ s => fa s cur = parent)).
        { intros s [_ [Hfa _]]. exact Hfa. }
        apply (Hoare_conseq_post _ (preloop cur) (fun _ s => fa s cur = parent)
          (fun _ s => fa s cur = parent /\ cur ∈ visited s)).
        { intros _ s [Hfa _]. exact Hfa. }
        apply (preloop_keeps_fa cur parent).
      + apply Hoare_conj.
        * apply (Hoare_conseq_pre _ (fun s => In ancestor (stack s))
            (preloop cur) (fun _ s => In ancestor (stack s))).
          { intros s [_ [_ [_ [_ [Hina _]]]]]. exact Hina. }
          unfold preloop, set_dfn, set_low, incr_timer, push_stack, visit.
          intro_state. hoare_auto_s. subst. simpl. auto.
        * apply Hoare_conj.
          { apply (Hoare_conseq_pre _
              (fun s => stack_dfn_order s /\ dfn_inv s /\ stack_in_visited s /\ ~ cur ∈ visited s)
              (preloop cur) (fun _ s => stack_dfn_order s)).
            { intros s [Hlow [Hfa [Hnv [Hnd [Hina [Horder [Hinj Hdv]]]]]]].
              destruct Hlow as [[Hsiv [Hinv' _]] _].
              split; [exact Horder | split; [exact Hinv' | split; [exact Hsiv | exact Hnv]]]. }
            apply preloop_preserves_stack_dfn_order. }
          apply Hoare_conj.
          { apply (Hoare_conseq_pre _
              (fun s => dfn_injective s /\ dfn_inv s /\ ~ cur ∈ visited s)
              (preloop cur) (fun _ s => dfn_injective s)).
            { intros s [Hlow [Hfa [Hnv [Hnd [Hina [Horder [Hinj Hdv]]]]]]].
              destruct Hlow as [[_ [Hinv' _]] _].
              split; [exact Hinj | split; [exact Hinv' | exact Hnv]]. }
            apply preloop_preserves_dfn_injective. }
          apply Hoare_conj.
          { apply (Hoare_conseq_pre _ (fun s => done_visited done s)
              (preloop cur) (fun _ s => done_visited done s)).
            { intros s [Hlow [Hfa [Hnv [Hnd [Hina [Horder [Hinj Hdv]]]]]]]. exact Hdv. }
            unfold preloop, set_dfn, set_low, incr_timer, push_stack, visit.
            intro_state. hoare_auto_s. subst. simpl.
            unfold done_visited. intros w Hw. simpl. sets_unfold. left. apply H. exact Hw. }
          (* dfn s ancestor < dfn s cur *)
          apply (Hoare_conseq_pre _
            (fun s => low_forset_inv ancestor done s /\ ~ cur ∈ visited s)
            (preloop cur) (fun _ s => dfn s ancestor < dfn s cur)).
          { intros s [Hlow [Hfa [Hnv [Hnd [Hina [Horder [Hinj Hdv]]]]]]].
            split; [exact Hlow | exact Hnv]. }
          unfold preloop, set_dfn, set_low, incr_timer, push_stack, visit.
          intro_state. hoare_auto_s. subst. simpl.
          destruct H as [Hlow Hnv].
          destruct Hlow as [[_ [Hinv' _]] [Hanc_vis _]].
          unfold dfn_inv in Hinv'. destruct Hinv' as [Hdfn_lt _].
          unfold equiv_decb. destruct (equiv_dec ancestor cur) as [Heq | Hneq].
          { exfalso. apply Hanc_ne. exact Heq. }
          destruct (equiv_dec cur cur) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
          apply Hdfn_lt. exact Hanc_vis.
  Qed.

  (** [tarjan_scc_keep_dfn_forall]: preserves [dfn] values for a set [S]
      of visited vertices through [tarjan_scc g u0], provided [u0 ≠ w]
      for all [w ∈ S].  The inequality is embedded in the Hoare
      precondition so the fixpoint induction can carry it. *)

  Lemma preloop_keep_dfn_forall (u: V) (S: V -> Prop) (dfn_vals: V -> nat):
    (forall w, S w -> u <> w) ->
    Hoare (fun s: @SCCSt V => (forall w, S w -> w ∈ visited s) /\
                               (forall w, S w -> dfn s w = dfn_vals w))
          (preloop u)
          (fun _ s => (forall w, S w -> w ∈ visited s) /\
                      (forall w, S w -> dfn s w = dfn_vals w)).
  Proof.
    intros Hneq. unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [Hvis Hdfn_vals]. split.
    - intros w Hw. sets_unfold. left. apply Hvis. exact Hw.
    - intros w Hw. unfold equiv_decb. destruct (equiv_dec w u) as [Heq | Hneq'].
      + exfalso. apply (Hneq w Hw). symmetry. exact Heq.
      + apply Hdfn_vals. exact Hw.
  Qed.

  Lemma pop_scc_keep_dfn_forall (u: V) (S: V -> Prop) (dfn_vals: V -> nat):
    Hoare (fun s: @SCCSt V => (forall w, S w -> w ∈ visited s) /\
                               (forall w, S w -> dfn s w = dfn_vals w))
          (pop_scc u)
          (fun _ s => (forall w, S w -> w ∈ visited s) /\
                      (forall w, S w -> dfn s w = dfn_vals w)).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s. subst s. simpl.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
    simpl. exact H.
  Qed.

  Lemma update_low_keep_dfn_forall (u: V) (n: nat) (S: V -> Prop) (dfn_vals: V -> nat):
    Hoare (fun s: @SCCSt V => (forall w, S w -> w ∈ visited s) /\
                               (forall w, S w -> dfn s w = dfn_vals w))
          (update_low u n)
          (fun _ s => (forall w, S w -> w ∈ visited s) /\
                      (forall w, S w -> dfn s w = dfn_vals w)).
  Proof.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    { subst s. simpl. destruct H as [Hvis Hdfn]. split; intros w Hw; [apply Hvis | apply Hdfn]; exact Hw. }
    { destruct H1. subst s. exact H. }
  Qed.

  Lemma set_fa_keep_dfn_forall (v p: V) (S: V -> Prop) (dfn_vals: V -> nat):
    Hoare (fun s: @SCCSt V => (forall w, S w -> w ∈ visited s) /\
                               (forall w, S w -> dfn s w = dfn_vals w))
          (set_fa v p)
          (fun _ s => (forall w, S w -> w ∈ visited s) /\
                      (forall w, S w -> dfn s w = dfn_vals w)).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl. destruct H as [Hvis Hdfn]. split; intros w Hw; [apply Hvis | apply Hdfn]; exact Hw.
  Qed.

  Lemma get_low_update_low_keep_dfn_forall (u v: V) (S: V -> Prop) (dfn_vals: V -> nat):
    Hoare (fun s: @SCCSt V => (forall w, S w -> w ∈ visited s) /\
                               (forall w, S w -> dfn s w = dfn_vals w))
          (lv <- get' (fun s => low s v);; update_low u lv)
          (fun _ s => (forall w, S w -> w ∈ visited s) /\
                      (forall w, S w -> dfn s w = dfn_vals w)).
  Proof.
    intro_state. eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    apply Hoare_conseq_pre with (P2 := fun s => (forall w, S w -> w ∈ visited s) /\
                                                (forall w, S w -> dfn s w = dfn_vals w)).
    { intros s1 Hs1. destruct Hs1. subst s1. simpl. auto. }
    apply (update_low_keep_dfn_forall u lv S dfn_vals).
  Qed.

  Lemma process_edge_keep_dfn_forall (u v: V) (W: V -> program (@SCCSt V) unit)
        (S: V -> Prop) (dfn_vals: V -> nat):
    (forall w, S w -> u <> w) ->
    (forall x, Hoare (fun s: @SCCSt V => (forall w, S w -> x <> w) /\
                                         (forall w, S w -> w ∈ visited s) /\
                                         (forall w, S w -> dfn s w = dfn_vals w))
                     (W x)
                     (fun _ s => (forall w, S w -> w ∈ visited s) /\
                                 (forall w, S w -> dfn s w = dfn_vals w))) ->
    Hoare (fun s: @SCCSt V => (forall w, S w -> w ∈ visited s) /\
                               (forall w, S w -> dfn s w = dfn_vals w))
          (process_edge u W v)
          (fun _ s => (forall w, S w -> w ∈ visited s) /\
                      (forall w, S w -> dfn s w = dfn_vals w)).
  Proof.
    intros Hneq_u HW.
    unfold process_edge, if_else. intro_state. destruct H as [Hvis Hdfn].
    apply Hoare_choice.
    - (* Tree edge *)
      apply Hoare_assume_bind. simpl. intro_state.
      destruct H as [Hnv Heq_s]. subst s1.
      assert (Hneq_child: forall w, S w -> v <> w).
      { intros w Hw. intro Heq. subst w. apply Hnv. apply Hvis. exact Hw. }
      apply Hoare_conseq_pre with (P2 := fun s => (forall w, S w -> w ∈ visited s) /\ (forall w, S w -> dfn s w = dfn_vals w)).
      { intros s1 Hs1. subst s1. split. exact Hvis. exact Hdfn. }
      apply (Hoare_bind (fun s => (forall w, S w -> w ∈ visited s) /\ (forall w, S w -> dfn s w = dfn_vals w))
               (set_fa v u)
               (fun (_: unit) s => (forall w, S w -> w ∈ visited s) /\ (forall w, S w -> dfn s w = dfn_vals w))
               (fun _ => W v ;; lv <- get' (fun s => low s v) ;; update_low u lv)
               (fun (_: unit) s => (forall w, S w -> w ∈ visited s) /\ (forall w, S w -> dfn s w = dfn_vals w))).
      { unfold set_fa. intro_state. hoare_auto_s.
        subst s. simpl. destruct H as [Hvis' Hdfn']. split; intros w Hw; [apply Hvis' | apply Hdfn']; exact Hw. }
      simpl. intros _.
      eapply Hoare_bind.
      { apply (Hoare_conseq_pre _ (fun s => (forall w, S w -> v <> w) /\
                                            (forall w, S w -> w ∈ visited s) /\
                                            (forall w, S w -> dfn s w = dfn_vals w))
               (W v) (fun _ s => (forall w, S w -> w ∈ visited s) /\
                                 (forall w, S w -> dfn s w = dfn_vals w))).
        { intros s [Hvis_post Hdfn_post]. split. exact Hneq_child. split. exact Hvis_post. exact Hdfn_post. }
        apply HW. }
      simpl. intros _. apply get_low_update_low_keep_dfn_forall.
    - (* Non-tree edge *)
      intro_state. hoare_auto_s.
      + apply Hoare_conseq_pre with (P2 := fun s => (forall w, S w -> w ∈ visited s) /\
                                                    (forall w, S w -> dfn s w = dfn_vals w)).
        { intros s1 Hs1. subst s1. split; auto. }
        apply (update_low_keep_dfn_forall u (dfn s0 v) S dfn_vals).
      + destruct H2 as [Heq Hnin]. subst s. subst s1. split. exact Hvis. exact Hdfn.
  Qed.

  Lemma forset_process_edge_keep_dfn_forall (u: V) (W: V -> program (@SCCSt V) unit)
        (S: V -> Prop) (dfn_vals: V -> nat):
    (forall w, S w -> u <> w) ->
    (forall x, Hoare (fun s: @SCCSt V => (forall w, S w -> x <> w) /\
                                         (forall w, S w -> w ∈ visited s) /\
                                         (forall w, S w -> dfn s w = dfn_vals w))
                     (W x)
                     (fun _ s => (forall w, S w -> w ∈ visited s) /\
                                 (forall w, S w -> dfn s w = dfn_vals w))) ->
    Hoare (fun s: @SCCSt V => (forall w, S w -> w ∈ visited s) /\
                               (forall w, S w -> dfn s w = dfn_vals w))
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => (forall w, S w -> w ∈ visited s) /\
                      (forall w, S w -> dfn s w = dfn_vals w)).
  Proof.
    intros Hneq_u HW. unfold forset. hoare_fix_nolv_auto (V -> Prop).
    simpl; intros W0 IH0 todo. unfold forset_f.
    hoare_auto_s. intro_state. destruct H as [Hvis Hdfn].
    hoare_auto_s.
    - eapply Hoare_bind with (R := fun _ s => (forall w, S w -> w ∈ visited s) /\
                                               (forall w, S w -> dfn s w = dfn_vals w)).
      { apply Hoare_conseq_pre with (P2 := fun s => (forall w, S w -> w ∈ visited s) /\
                                                    (forall w, S w -> dfn s w = dfn_vals w)).
        - intros s1 Hs1. subst s1. split. exact Hvis. exact Hdfn.
        - apply (process_edge_keep_dfn_forall u a W S dfn_vals Hneq_u). intros x. apply HW. }
      simpl. intros _. apply IH0.
  Qed.

  Lemma tarjan_scc_keep_dfn_forall (S: V -> Prop) (dfn_vals: V -> nat) (u0: V):
    (forall w, S w -> u0 <> w) ->
    Hoare (fun s: @SCCSt V => (forall w, S w -> w ∈ visited s) /\
                               (forall w, S w -> dfn s w = dfn_vals w))
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u0)
          (fun _ s => (forall w, S w -> w ∈ visited s) /\
                      (forall w, S w -> dfn s w = dfn_vals w)).
  Proof.
    intros Hneq_u0.
    set (P := fun (u: V) (s: SCCSt) =>
      (forall w, S w -> u <> w) /\
      (forall w, S w -> w ∈ visited s) /\
      (forall w, S w -> dfn s w = dfn_vals w)).
    set (Q := fun (u: V) (_: unit) (s: SCCSt) =>
      (forall w, S w -> w ∈ visited s) /\
      (forall w, S w -> dfn s w = dfn_vals w)).
    apply Hoare_conseq_pre with (P2 := P u0).
    { intros s [Hvis' Hdfn']. unfold P. split. exact Hneq_u0. split. exact Hvis'. exact Hdfn'. }
    apply (Hoare_fix P Q (tarjan_scc_f (V:=V) (E:=E) g) u0).
    intros W IH u. unfold tarjan_scc_f, P, Q.
    intro_state. destruct H as [Hneq_u [Hvis Hdfn_vals]].
    eapply Hoare_bind.
    { apply Hoare_conseq_pre with (P2 := fun s => (forall w, S w -> w ∈ visited s) /\ (forall w, S w -> dfn s w = dfn_vals w)).
      { intros s' Hs'. subst s'. split. exact Hvis. exact Hdfn_vals. }
      apply (preloop_keep_dfn_forall u S dfn_vals Hneq_u). }
    simpl. intro a.
    eapply Hoare_bind.
    - apply (forset_process_edge_keep_dfn_forall u W S dfn_vals Hneq_u). intros x. apply IH.
    - simpl. intro a0. intro_state. hoare_auto_s.
      + apply Hoare_conseq_pre with (P2 := fun s => (forall w, S w -> w ∈ visited s) /\
                                                    (forall w, S w -> dfn s w = dfn_vals w)).
        { intros s' Hs'. subst s'. exact H. }
        apply pop_scc_keep_dfn_forall.
      + destruct H1 as [Heq Hneq']. subst s. destruct H. split; auto.
  Qed.

  (** Wrapper with inequalities baked into the Hoare precondition.
      The precondition format matches the induction property P exactly:
      (anc <> cur /\ par <> cur /\ dg_step g par cur /\ ~ done cur) /\
      low_forset_inv anc done s /\ fa s cur = par /\ ... *)
  Lemma preloop_establishes_ancestor_inv_hoare (ancestor parent cur: V) (done: V -> Prop):
    Hoare (fun s => (ancestor <> cur /\ parent <> cur /\ dg_step g parent cur /\ ~ done cur) /\
                    low_forset_inv ancestor done s /\ fa s cur = parent /\ ~ cur ∈ visited s /\ ~ done cur /\
                    done_visited done s /\ In ancestor (stack s) /\ stack_dfn_order s /\ dfn_injective s)
          (preloop cur)
          (fun _ s => low_forset_inv ancestor done s /\ fa s cur = parent /\ In ancestor (stack s) /\
                      stack_dfn_order s /\ dfn_injective s /\ done_visited done s /\
                      dfn s ancestor < dfn s cur).
  Proof.
    apply Hoare_state_intro. intros s0 H.
    destruct H as [[Hanc_ne [Hpar_ne [Hdg' Hnd']]] Hpre].
    destruct Hpre as [Hlow_inv [Hfa [Hnv [Hnd [Hdv [Hina [Horder Hinj]]]]]]].
    apply (Hoare_conseq_pre (fun s => s = s0) (fun s => low_forset_inv ancestor done s /\
      fa s cur = parent /\ ~ cur ∈ visited s /\ ~ done cur /\
      In ancestor (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ done_visited done s)
      (preloop cur) (fun _ s => low_forset_inv ancestor done s /\ fa s cur = parent /\
      In ancestor (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ done_visited done s /\
      dfn s ancestor < dfn s cur)).
    { intros s1 Heq. subst s1.
      split. exact Hlow_inv. split. exact Hfa. split. exact Hnv. split. exact Hnd.
      split. exact Hina. split. exact Horder. split. exact Hinj. exact Hdv. }
    apply (preloop_establishes_ancestor_inv ancestor parent cur done Hanc_ne Hpar_ne).
  Qed.

  Lemma W_preserves_ancestor_inv (ancestor parent cur: V) (done: V -> Prop):
    ancestor <> cur -> parent <> cur -> dg_step g parent cur -> ~ done cur ->
    Hoare (fun s => low_forset_inv ancestor done s /\ fa s cur = parent /\ ~ cur ∈ visited s /\ ~ done cur /\ done_visited done s /\
                    In ancestor (stack s) /\ In parent (stack s) /\ dfn s ancestor < dfn s parent /\
                    stack_dfn_order s /\ dfn_injective s)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g cur)
          (fun _ s => low_forset_inv ancestor done s /\ fa s cur = parent /\ done_visited done s /\ In ancestor (stack s) /\
                      stack_dfn_order s /\ dfn_injective s /\
                      (forall w, done w -> In w (stack s) -> dfn s w < dfn s cur) /\
                      dfn s ancestor < dfn s cur).
  Proof.
    intros Hanc_ne Hpar_ne Hdg Hndone.
    (* Step 0: strengthen the precondition with the inequalities so the
       fixpoint induction has them available at every step. *)
    apply (Hoare_conseq_pre _
      (fun s => (ancestor <> cur /\ parent <> cur /\ dg_step g parent cur /\ ~ done cur) /\
                low_forset_inv ancestor done s /\ fa s cur = parent /\
                ~ cur ∈ visited s /\ ~ done cur /\ done_visited done s /\
                In ancestor (stack s) /\ In parent (stack s) /\
                dfn s ancestor < dfn s parent /\
                stack_dfn_order s /\ dfn_injective s)
      (tarjan_scc g cur)
      (fun _ s => low_forset_inv ancestor done s /\ fa s cur = parent /\ done_visited done s /\
                  In ancestor (stack s) /\ stack_dfn_order s /\ dfn_injective s /\
                  (forall w, done w -> In w (stack s) -> dfn s w < dfn s cur) /\
                  dfn s ancestor < dfn s cur)).
    { intros s [Hlow_inv [Hfa [Hnv [Hnd [Hdv [Hina [Hipar [Hdfn_anc_lt_par [Horder Hinj]]]]]]]]].
      split. split. exact Hanc_ne. split. exact Hpar_ne. split. exact Hdg. exact Hndone.
      split. exact Hlow_inv. split. exact Hfa. split. exact Hnv. split. exact Hnd.
      split. exact Hdv. split. exact Hina. split. exact Hipar. split. exact Hdfn_anc_lt_par.
      split. exact Horder. exact Hinj. }
    (* Strengthened fixpoint with 5-tuple (anc, par, d, tv, tp).
       The extra (tv, tp) preserves fa tv = tp through all recursive calls,
       solving the fa a = par preservation problem in the forset body. *)
    unfold tarjan_scc.
    match goal with |- Hoare ?P ?f ?Q =>
      refine (Hoare_conseq_pre P (fun s =>
        (cur = cur \/ cur ∈ visited s) /\ fa s cur = parent /\
        (ancestor <> cur /\ parent <> cur /\ dg_step g parent cur /\ ~ done cur) /\
        low_forset_inv ancestor done s /\ fa s cur = parent /\
        ~ cur ∈ visited s /\ ~ done cur /\ done_visited done s /\
        In ancestor (stack s) /\ In parent (stack s) /\
        dfn s ancestor < dfn s parent /\
        stack_dfn_order s /\ dfn_injective s) f Q _ _)
    end.
    { intros s [Hineqs [Hlow [Hfa [Hnv [Hnd [Hdv [Hina [Hipar [Hdfn_anc_lt_par [Horder Hinj]]]]]]]]]].
      split. left. reflexivity. split. exact Hfa.
      split. exact Hineqs. split. exact Hlow. split. exact Hfa.
      split. exact Hnv. split. exact Hnd. split. exact Hdv.
      split. exact Hina. split. exact Hipar. split. exact Hdfn_anc_lt_par.
      split. exact Horder. exact Hinj. }
    match goal with |- Hoare ?P ?f ?Q =>
      refine (Hoare_conseq_post P f Q
        (fun _ s => low_forset_inv ancestor done s /\ fa s cur = parent /\
          done_visited done s /\ In ancestor (stack s) /\
          stack_dfn_order s /\ dfn_injective s /\
          (forall w, done w -> In w (stack s) -> dfn s w < dfn s cur) /\
          dfn s ancestor < dfn s cur /\
          fa s cur = parent /\ cur ∈ visited s /\
          ~ done cur /\ In parent (stack s) /\
          ancestor <> cur /\ parent <> cur /\ dg_step g parent cur /\
          dfn s ancestor < dfn s parent) _ _)
    end.
    { intros _ s [Hlow [Hfa [Hdv [Hina [Horder [Hinj [Hdfn_d_lt [Hdfn_anc _]]]]]]]].
      split. exact Hlow. split. exact Hfa. split. exact Hdv. split. exact Hina.
      split. exact Horder. split. exact Hinj. split. exact Hdfn_d_lt. exact Hdfn_anc. }
    apply (Hoare_fix_logicv (tarjan_scc_f (V:=V) (E:=E) g)
      (fun (x : V) '(anc, par, d, tv, tp) (s : SCCSt) =>
        (tv = x \/ tv ∈ visited s) /\
        fa s tv = tp /\
        (anc <> x /\ par <> x /\ dg_step g par x /\ ~ d x) /\
        low_forset_inv anc d s /\ fa s x = par /\ ~ x ∈ visited s /\ ~ d x /\
        done_visited d s /\ In anc (stack s) /\ In par (stack s) /\
        dfn s anc < dfn s par /\
        stack_dfn_order s /\ dfn_injective s)
      (fun (x : V) '(anc, par, d, tv, tp) (_ : unit) (s : SCCSt) =>
        low_forset_inv anc d s /\ fa s x = par /\ done_visited d s /\ In anc (stack s) /\
        stack_dfn_order s /\ dfn_injective s /\
        (forall w, d w -> In w (stack s) -> dfn s w < dfn s x) /\
        dfn s anc < dfn s x /\
        fa s tv = tp /\ tv ∈ visited s /\
        ~ d x /\ In par (stack s) /\
        anc <> x /\ par <> x /\ dg_step g par x /\
        dfn s anc < dfn s par)
      cur (ancestor, parent, done, cur, parent)).
    intros W IH a [[[[anc par] d] tv] tp].
    unfold tarjan_scc_f.
    eapply Hoare_bind.
    - (* preloop a: prove the intermediate postcondition *)
      apply Hoare_conj.
      + (* ancestor invariant *)
        apply (Hoare_conseq_pre _ (fun s => (anc <> a /\ par <> a /\ dg_step g par a /\ ~ d a) /\
          low_forset_inv anc d s /\ fa s a = par /\ ~ a ∈ visited s /\ ~ d a /\
          done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\ dfn_injective s)
          (preloop a)
          (fun _ s => low_forset_inv anc d s /\ fa s a = par /\ In anc (stack s) /\
                      stack_dfn_order s /\ dfn_injective s /\ done_visited d s /\
                      dfn s anc < dfn s a)).
        { intros s [Htv_or [Hfa_tv [Hineqs [Hlow [Hfa [Hnv [Hnd [Hdv [Hina [Hipar [Hdfn_anc_lt_par [Horder Hinj]]]]]]]]]]]].
          split. exact Hineqs. split. exact Hlow. split. exact Hfa. split. exact Hnv.
          split. exact Hnd. split. exact Hdv. split. exact Hina. split. exact Horder. exact Hinj. }
        apply preloop_establishes_ancestor_inv_hoare.
      + apply Hoare_conj.
        * (* tv/tp preservation *)
          apply (Hoare_conseq_pre _ (fun s => (tv = a \/ tv ∈ visited s) /\ fa s tv = tp)
            (preloop a) (fun _ s => fa s tv = tp /\ tv ∈ visited s)).
          { intros s [Htv_or [Hfa_tv [Hineqs [Hlow [Hfa [Hnv [Hnd [Hdv [Hina [Hipar [Hdfn_anc_lt_par [Horder Hinj]]]]]]]]]]]].
            split. exact Htv_or. exact Hfa_tv. }
          unfold preloop. unfold_op. intro_state. hoare_auto_s.
          destruct H as [Htv_or' Hfa_tv']. subst s. simpl.
          split. { exact Hfa_tv'. }
          { destruct Htv_or' as [Heq | Htv_vis'].
            - subst tv. sets_unfold. right. reflexivity.
            - sets_unfold. left. exact Htv_vis'. }
        * apply Hoare_conj.
          { (* static inequalities preserved by preloop *)
            apply (Hoare_conseq_pre _ (fun s => anc <> a /\ par <> a /\ dg_step g par a)
              (preloop a) (fun _ s => anc <> a /\ par <> a /\ dg_step g par a)).
            { intros s [Htv_or [Hfa_tv [Hineqs [Hlow [Hfa [Hnv [Hnd [Hdv [Hina [Hipar [Hdfn_anc_lt_par [Horder Hinj]]]]]]]]]]]].
              destruct Hineqs as [Ha1 [Ha2 [Ha3 Ha4]]].
              split. exact Ha1. split. exact Ha2. exact Ha3. }
            unfold preloop. unfold_op. intro_state. hoare_auto_s. }
          apply Hoare_conj.
          { (* ~ d a preserved *)
            apply (Hoare_conseq_pre _ (fun s => ~ d a)
              (preloop a) (fun _ s => ~ d a)).
            { intros s [Htv_or [Hfa_tv [Hineqs [Hlow [Hfa [Hnv [Hnd [Hdv [Hina [Hipar [Hdfn_anc_lt_par [Horder Hinj]]]]]]]]]]]].
              destruct Hineqs as [Ha1 [Ha2 [Ha3 Hnda]]]. exact Hnda. }
            unfold preloop. unfold_op. intro_state. hoare_auto_s. }
          apply Hoare_conj.
          { (* In a (stack s) *)
            apply (Hoare_conseq_pre _ (fun s => True) (preloop a) (fun _ s => In a (stack s))).
            { intros s _. exact I. }
            apply preloop_in_stack. }
          apply Hoare_conj.
          { (* static dfn-ordering: forall w, d w -> In w stack -> dfn w < dfn a.
               After preloop a, dfn a = old_timer (the timer value before incr_timer).
               All w ∈ d are visited before preloop, so dfn w < old_timer = dfn a. *)
            apply (Hoare_conseq_pre _ (fun s => ~ a ∈ visited s /\ dfn_inv s /\ done_visited d s /\ ~ d a)
              (preloop a) (fun _ s => forall dw, d dw -> In dw (stack s) -> dfn s dw < dfn s a)).
            { intros s [Htv_or [Hfa_tv [Hineqs [Hlow [Hfa [Hnv [Hnd [Hdv [Hina [Hipar [Hdfn_anc_lt_par [Horder Hinj]]]]]]]]]]]].
              destruct Hlow as [Hwf _]. destruct Hwf as [Hsiv [Hinv' [Hvalid Hfa_vis]]].
              split. exact Hnv. split. exact Hinv'. split. exact Hdv. exact Hnd. }
            unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
            destruct H as [Hnv [Hinv' [Hdv' Hnd_a]]].
            (* dw, H2: d dw, H3: In dw (a::stack s0) are already introduced by hoare_auto_s *)
            assert (Hdwvis: dw ∈ visited s0). { apply Hdv'. exact H2. }
            unfold dfn_inv in Hinv'. destruct Hinv' as [Hdfn_lt [Hdfn_zero Hdfn_pos]].
            apply Hdfn_lt in Hdwvis.
            destruct (equiv_dec dw a) as [Heq_dwa | Hneq_dwa].
            { assert (Hda: d a). { rewrite <- Heq_dwa. exact H2. } exfalso. exact (Hnd_a Hda). }
            { unfold equiv_decb. destruct (equiv_dec dw a) as [Heq' | Hneq']; [exfalso; apply Hneq_dwa; exact Heq' |].
              destruct (equiv_dec a a) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
              exact Hdwvis. } }
          apply Hoare_conj.
          { (* In par (stack s) preserved by preloop *)
            apply (Hoare_conseq_pre _ (fun s => In par (stack s)) (preloop a) (fun _ s => In par (stack s))).
            { intros s [Htv_or [Hfa_tv [Hineqs [Hlow [Hfa [Hnv [Hnd [Hdv [Hina [Hipar [Hdfn_anc_lt_par [Horder Hinj]]]]]]]]]]]].
              exact Hipar. }
            unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
            right. exact H. }
          { (* dfn s anc < dfn s par preserved by preloop *)
            apply (Hoare_conseq_pre _ (fun s => anc <> a /\ par <> a /\ dfn s anc < dfn s par) (preloop a) (fun _ s => dfn s anc < dfn s par)).
            { intros s [Htv_or [Hfa_tv [Hineqs [Hlow [Hfa [Hnv [Hnd [Hdv [Hina [Hipar [Hdfn_anc_lt_par [Horder Hinj]]]]]]]]]]]].
              destruct Hineqs as [Hanc_ne_a [Hpar_ne_a [Hdg_par_a Hnda]]].
              split. exact Hanc_ne_a. split. exact Hpar_ne_a. exact Hdfn_anc_lt_par. }
            unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
            destruct H as [Hanc_ne_a [Hpar_ne_a Hdfn_lt]].
            unfold equiv_decb.
            destruct (equiv_dec anc a) as [Heq | Hneq]; [exfalso; apply Hanc_ne_a; exact Heq |].
            destruct (equiv_dec par a) as [Heq2 | Hneq2]; [exfalso; apply Hpar_ne_a; exact Heq2 |].
            exact Hdfn_lt. }
    - (* forset + If continuation *)
      intro a'. destruct a'.
      eapply Hoare_bind.
      + (* forset over dg_step g a *)
        set (P_forset := fun (_: V -> Prop) (s: SCCSt) =>
          low_forset_inv anc d s /\ fa s a = par /\ done_visited d s /\
          In anc (stack s) /\ stack_dfn_order s /\ dfn_injective s /\
          dfn s anc < dfn s a /\ fa s tv = tp /\ tv ∈ visited s /\
          ~ d a /\ In a (stack s) /\
          anc <> a /\ par <> a /\ dg_step g par a /\
          (forall w, d w -> In w (stack s) -> dfn s w < dfn s a) /\
          In par (stack s) /\ dfn s anc < dfn s par).
        assert (ProperP: Proper (Sets.equiv ==> eq ==> iff) P_forset).
        { unfold P_forset. intros da1 da2 Heq s1 s2 Heqs. subst s2. unfold iff; tauto. }
        assert (Hbody: forall todo v,
          todo ⊆ dg_step g a -> dg_step g a v -> ~ todo v ->
          Hoare (fun s => P_forset todo s) (process_edge a W v) (fun _ s => P_forset (todo ∪ [v]) s)).
        { intros todo v Hsub Huniv Hnotin.
          unfold P_forset, process_edge, if_else. intro_state.
          rename H into HP_forset. apply Hoare_choice.
          - (* Tree edge: ~ v ∈ visited *)
            apply Hoare_assume_bind. simpl. intro_state. destruct H as [Hnv Heq_s]. subst s1.
            unfold P_forset in HP_forset.
            destruct HP_forset as [Hlow_inv [Hfa_a [Hdv' [Hina' [Horder' [Hinj' [Hdfn_anc' [Hfa_tv' [Htv_vis' [Hnd_a [Hina_stack [Hanc_ne_a [Hpar_ne_a [Hdg_par_a [Hdfn_d_lt_a [Hin_par Hdf_anc_par]]]]]]]]]]]]]]]].
            assert (Hneq_av: a <> v).
            { intro Heq. subst v. destruct Hlow_inv as [Hwf _]. destruct Hwf as [Hsiv _].
              apply Hsiv in Hina_stack. exact (Hnv Hina_stack). }
            assert (Hnv_d: ~ d v). { intro Hdv_v. apply Hdv' in Hdv_v. exact (Hnv Hdv_v). }
            set (Qmid := fun (_: unit) (s: SCCSt) => low_forset_inv anc d s /\ fa s v = a /\
                fa s a = par /\ fa s tv = tp /\ tv ∈ visited s /\
                ~ d a /\ In a (stack s) /\ anc <> a /\ par <> a /\ dg_step g par a /\
                done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                dfn_injective s /\ dfn s anc < dfn s a /\ ~ v ∈ visited s).
            set (Qfinal := fun (_: unit) (s: SCCSt) => low_forset_inv anc d s /\ fa s a = par /\
                done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                dfn_injective s /\ dfn s anc < dfn s a /\ fa s tv = tp /\
                tv ∈ visited s /\ ~ d a /\ In a (stack s) /\
                anc <> a /\ par <> a /\ dg_step g par a /\
                (forall w, d w -> In w (stack s) -> dfn s w < dfn s a) /\
                In par (stack s) /\ dfn s anc < dfn s par).
            apply (Hoare_bind (fun s => s = s0) (set_fa v a) Qmid
              (fun _ => W v ;; lv <- get' (fun s => low s v) ;; update_low a lv) Qfinal).
            * (* set_fa v a *)
              unfold set_fa. intro_state. hoare_auto_s. subst s1. simpl. subst s. simpl.
              assert (Hlow_post: low_forset_inv anc d
                {| visited := visited s0; timer := timer s0;
                   fa := fun x : V => if equiv_decb x v then a else fa s0 x;
                   dfn := dfn s0; low := low s0; stack := stack s0; sccs := sccs s0 |}).
              { assert (Ha_vis_s0: a ∈ visited s0).
                { destruct Hlow_inv as [Hwf _]. destruct Hwf as [Hsiv _]. apply Hsiv. exact Hina_stack. }
                assert (Hanc_vis_s0: anc ∈ visited s0).
                { destruct Hlow_inv as [_ [Hanc_vis_s0 _]]. exact Hanc_vis_s0. }
                eapply (set_fa_preserves_low_forset_inv_for_new_child anc a v d s0); eauto. }
              assert (Hfa_v_post: (fun x : V => if equiv_decb x v then a else fa s0 x) v = a).
              { unfold equiv_decb. destruct (equiv_dec v v) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity]. }
              assert (Htv_neq_v: tv <> v).
              { intro Heq. subst tv. exact (Hnv Htv_vis'). }
              assert (Hfa_tv_post: (fun x : V => if equiv_decb x v then a else fa s0 x) tv = tp).
              { unfold equiv_decb. destruct (equiv_dec tv v) as [Heq_tv_v | Hneq_tv_v].
                - exfalso. apply Htv_neq_v. rewrite Heq_tv_v. reflexivity.
                - exact Hfa_tv'. }
              assert (Hfa_a_post: (RecordSet.set fa (fun (_:V->V) (x:V) => if equiv_decb x v then a else fa s0 x) s0).(fa) a = par).
              { simpl. unfold equiv_decb. destruct (equiv_dec a v) as [Heq_av | Hneq_av'].
                - exfalso. apply Hneq_av. exact Heq_av.
                - exact Hfa_a. }
              assert (Hfa_tv_post2: (RecordSet.set fa (fun (_:V->V) (x:V) => if equiv_decb x v then a else fa s0 x) s0).(fa) tv = tp).
              { simpl. unfold equiv_decb. destruct (equiv_dec tv v) as [Heq_tv_v | Hneq_tv_v'].
                - exfalso. apply Htv_neq_v. exact Heq_tv_v.
                - exact Hfa_tv'. }
              assert (Hfa_v_post2: (RecordSet.set fa (fun (_:V->V) (x:V) => if equiv_decb x v then a else fa s0 x) s0).(fa) v = a).
              { simpl. unfold equiv_decb. destruct (equiv_dec v v) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity]. }
              simpl. split. exact Hlow_post. split. exact Hfa_v_post2. split. exact Hfa_a_post.
              split. exact Hfa_tv_post2. split. exact Htv_vis'.
              split. exact Hnd_a. split. exact Hina_stack. split. exact Hanc_ne_a.
              split. exact Hpar_ne_a. split. exact Hdg_par_a.
              split. exact Hdv'. split. exact Hina'. split. exact Horder'.
              split. exact Hinj'. split. exact Hdfn_anc'. simpl. exact Hnv.
            * (* W v ;; get' low v ;; update_low a lv *)
              intros a0. simpl.
              eapply Hoare_bind.
              -- (* W v via two IH instances combined with static properties *)
                apply Hoare_conj.
                ++ (* Frame + tv/tp via IH(v, (anc, a, d, tv, tp)) *)
                  specialize (IH v (anc, a, d, tv, tp)).
                  (* IH now gives extra properties: ~d v, In a(stack), anc<>v, a<>v, dg_step g a v *)
                  apply (Hoare_conseq_pre (fun s => low_forset_inv anc d s /\ fa s v = a /\
                    fa s a = par /\ fa s tv = tp /\ tv ∈ visited s /\
                    ~ d a /\ In a (stack s) /\ anc <> a /\ par <> a /\ dg_step g par a /\
                    done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                    dfn_injective s /\ dfn s anc < dfn s a /\ ~ v ∈ visited s)
                    (fun s => (tv = v \/ tv ∈ visited s) /\ fa s tv = tp /\
                      (anc <> v /\ a <> v /\ dg_step g a v /\ ~ d v) /\
                      low_forset_inv anc d s /\ fa s v = a /\ ~ v ∈ visited s /\ ~ d v /\
                      done_visited d s /\ In anc (stack s) /\ In a (stack s) /\
                      dfn s anc < dfn s a /\
                      stack_dfn_order s /\ dfn_injective s) (W v)
                    (fun _ s => low_forset_inv anc d s /\ fa s v = a /\
                      done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                      dfn_injective s /\ (forall w, d w -> In w (stack s) -> dfn s w < dfn s v) /\
                      dfn s anc < dfn s v /\ fa s tv = tp /\ tv ∈ visited s /\
                      ~ d v /\ In a (stack s) /\ anc <> v /\ a <> v /\ dg_step g a v /\
                      dfn s anc < dfn s a)).
                  { intros s [Hlow' [Hfa_v' [Hfa_a' [Hfa_tv'' [Htv_vis'' [Hnd_a' [Hina_stack' [Hanc_ne_a' [Hpar_ne_a' [Hdg_par_a' [Hdv'' [Hina'' [Horder'' [Hinj'' [Hdfn_anc'' Hnv_s]]]]]]]]]]]]]]].
                    assert (Hanc_ne_v: anc <> v).
                    { intro Heq. subst v. destruct Hlow_inv as [_ [Hanc_vis_s0 _]]. exact (Hnv Hanc_vis_s0). }
                    split. { right. exact Htv_vis''. } split. { exact Hfa_tv''. }
                    split. split. exact Hanc_ne_v. split. exact Hneq_av. split. exact Huniv. exact Hnv_d.
                    split. exact Hlow'. split. exact Hfa_v'. split. exact Hnv_s. split. exact Hnv_d.
                    split. exact Hdv''. split. exact Hina''. split. exact Hina_stack'.
                    split. exact Hdfn_anc''. split. exact Horder''. exact Hinj''. }
                  (* The IH now gives our exact target — use it directly *)
                  exact IH.
                ++ (* fa a = par via IH(v, (anc, a, d, a, par)) *)
                  specialize (IH v (anc, a, d, a, par)).
                     (* The IH postcondition now includes fa s a = par /\ a ∈ visited s *)
                     apply (Hoare_conseq_pre (fun s => low_forset_inv anc d s /\ fa s v = a /\
                       fa s a = par /\ fa s tv = tp /\ tv ∈ visited s /\
                       ~ d a /\ In a (stack s) /\ anc <> a /\ par <> a /\ dg_step g par a /\
                       done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                       dfn_injective s /\ dfn s anc < dfn s a /\ ~ v ∈ visited s)
                       (fun s => (a = v \/ a ∈ visited s) /\ fa s a = par /\
                         (anc <> v /\ a <> v /\ dg_step g a v /\ ~ d v) /\
                         low_forset_inv anc d s /\ fa s v = a /\ ~ v ∈ visited s /\ ~ d v /\
                         done_visited d s /\ In anc (stack s) /\ In a (stack s) /\
                         dfn s anc < dfn s a /\
                         stack_dfn_order s /\ dfn_injective s) (W v) (fun _ s => fa s a = par)).
                     { intros s [Hlow' [Hfa_v' [Hfa_a' [Hfa_tv'' [Htv_vis'' [Hnd_a' [Hina_stack' [Hanc_ne_a' [Hpar_ne_a' [Hdg_par_a' [Hdv'' [Hina'' [Horder'' [Hinj'' [Hdfn_anc'' Hnv_s]]]]]]]]]]]]]]].
                       assert (Hanc_ne_v: anc <> v).
                       { intro Heq. subst v. destruct Hlow_inv as [_ [Hanc_vis_s0 _]]. exact (Hnv Hanc_vis_s0). }
                       split. { right. destruct Hlow' as [Hwf _]. destruct Hwf as [Hsiv _]. apply Hsiv. exact Hina_stack'. } split. { exact Hfa_a'. }
                       split. split. exact Hanc_ne_v. split. exact Hneq_av. split. exact Huniv. exact Hnv_d.
                       split. exact Hlow'. split. exact Hfa_v'. split. exact Hnv_s. split. exact Hnv_d.
                       split. exact Hdv''. split. exact Hina''. split. exact Hina_stack'.
                       split. exact Hdfn_anc''. split. exact Horder''. exact Hinj''. }
                     (* The IH postcondition now includes fa s a = par; weaken it *)
                     eapply Hoare_conseq_post; [| exact IH].
                     intros b s2 Hpost.
                     destruct Hpost as [Hlow_s [Hfa_v_s [Hdv_s [Hina_s [Horder_s [Hinj_s [Hdfn_lt_v [Hdfn_anc_v [Hfa_tv_s Hrest]]]]]]]]].
                     exact Hfa_tv_s.
              -- (* get' low v ;; update_low a lv *)
                intros a1. simpl.
                (* The Hoare_conj gives: (IH1_post) /\ (fa s a = par).
                   We also carry In par (stack s) and dfn s anc < dfn s par from the outer context. *)
                apply (Hoare_conseq_pre _ (fun s => low_forset_inv anc d s /\ fa s a = par /\
                  done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                  dfn_injective s /\ dfn s anc < dfn s a /\ fa s tv = tp /\
                  tv ∈ visited s /\ ~ d a /\ In a (stack s) /\
                  anc <> a /\ par <> a /\ dg_step g par a /\
                  In par (stack s) /\ dfn s anc < dfn s par) _ _).
                { intros s [[Hlow_s [Hfa_v_s [Hdv_s [Hina_s [Horder_s [Hinj_s [Hdfn_lt_v_s [Hdfn_anc_v_s [Hfa_tv_s Htv_vis_s]]]]]]]]] Hfa_a_s].
                  destruct Htv_vis_s as [Htv_vis_s' [Hnd_v [Hina_stack_s [Hanc_ne_v_s [Hneq_av_s Hdg_av_s]]]]].
                  destruct Hdg_av_s as [Hdg_av_s' Hdfn_anc_a_s].
                  split. exact Hlow_s. split. exact Hfa_a_s. split. exact Hdv_s. split. exact Hina_s.
                  split. exact Horder_s. split. exact Hinj_s. split. exact Hdfn_anc_a_s.
                  split. exact Hfa_tv_s. split. exact Htv_vis_s'.
                  split. exact Hnd_a. split. exact Hina_stack_s.
                  split. exact Hanc_ne_a. split. exact Hpar_ne_a. split. exact Hdg_par_a.
                  (* In par and dfn: carried from outer context, preserved through set_fa and W v *)
                  split. admit. admit. } (* TODO: In par (stack s) /\ dfn s anc < dfn s par *)
                apply (Hoare_bind (fun s => low_forset_inv anc d s /\ fa s a = par /\
                  done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                  dfn_injective s /\ dfn s anc < dfn s a /\ fa s tv = tp /\
                  tv ∈ visited s /\ ~ d a /\ In a (stack s) /\
                  anc <> a /\ par <> a /\ dg_step g par a /\
                  In par (stack s) /\ dfn s anc < dfn s par)
                  (get' (fun s => low s v))
                  (fun lv s => low_forset_inv anc d s /\ fa s a = par /\
                    done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                    dfn_injective s /\ dfn s anc < dfn s a /\ fa s tv = tp /\
                    tv ∈ visited s /\ ~ d a /\ In a (stack s) /\
                    anc <> a /\ par <> a /\ dg_step g par a /\
                    In par (stack s) /\ dfn s anc < dfn s par)
                  (fun lv => update_low a lv)
                  Qfinal).
                ++ unfold get'. intro_state. hoare_auto_s.
                   destruct H1 as [Heq _]. subst s. exact H.
                ++ intros lv. unfold update_low. intro_state. hoare_auto_s.
                   { unfold set_low. intro_state. hoare_auto_s. subst s2. subst s.
                     destruct H as (Hlow' & Hfa_a' & Hdv'' & Hina'' & Horder'' & Hinj'' & Hdfn_anc'' & Hfa_tv'' & Htv_vis'' & Hnd_a' & Hina_stack' & Hanc_ne_a' & Hpar_ne_a' & Hdg_par_a' & Hin_par' & Hdfn_par').
                     assert (Hlow_post: low_forset_inv anc d
                       (RecordSet.set low (fun (low0: V->nat) (x:V) => if equiv_decb x a then Nat.min (low s1 a) lv else low0 x) s1)).
                     { eapply (update_low_preserves_low_forset_inv_for_other anc a lv d s1); eauto. }
                     assert (Hle: lv <= low s1 a). { lia. }
                     assert (Hlow_fun_eq: (fun (low0: V->nat) (x:V) => if equiv_decb x a then Nat.min (low s1 a) lv else low0 x)
                                        = (fun (low0: V->nat) (x:V) => if equiv_decb x a then lv else low0 x)).
                     { apply functional_extensionality; intro low0.
                       apply functional_extensionality; intro x.
                       unfold equiv_decb.
                       destruct (equiv_dec x a) as [Heq | Hneq].
                       - rewrite Nat.min_r; [reflexivity | exact Hle].
                       - reflexivity. }
                     rewrite Hlow_fun_eq in Hlow_post.
                     simpl. split. exact Hlow_post. split. exact Hfa_a'. split. exact Hdv''.
                     split. exact Hina''. split. exact Horder''. split. exact Hinj''.
                     split. exact Hdfn_anc''. split. exact Hfa_tv''.
                     split. exact Htv_vis''. split. exact Hnd_a'.
                     split. exact Hina_stack'. split. exact Hanc_ne_a'.
                     split. exact Hpar_ne_a'. split. exact Hdg_par_a'.
                     split. { admit. } (* TODO: dfn_d_lt *)
                     split. exact Hin_par'. simpl. exact Hdfn_par'. }
                   { destruct H1 as [Heq _]. subst s. destruct H as (Hlow' & Hfa_a' & Hdv'' & Hina'' & Horder'' & Hinj'' & Hdfn_anc'' & Hfa_tv'' & Htv_vis'' & Hnd_a' & Hina_stack' & Hanc_ne_a' & Hpar_ne_a' & Hdg_par_a' & Hin_par' & Hdfn_par').
                     split. exact Hlow'. split. exact Hfa_a'. split. exact Hdv''. split. exact Hina''.
                     split. exact Horder''. split. exact Hinj''. split. exact Hdfn_anc''.
                     split. exact Hfa_tv''. split. exact Htv_vis''.
                     split. exact Hnd_a'. split. exact Hina_stack'. split. exact Hanc_ne_a'.
                     split. exact Hpar_ne_a'. split. exact Hdg_par_a'.
                     split. { admit. } (* TODO: dfn_d_lt *)
                     split. exact Hin_par'. simpl. exact Hdfn_par'. }
          - (* Non-tree edge: v ∈ visited *)
            apply Hoare_assume_bind. simpl. intro_state. destruct H as [Hvis Heq_s]. subst s1.
            unfold P_forset in HP_forset.
            destruct HP_forset as [Hlow_inv [Hfa_a [Hdv' [Hina' [Horder' [Hinj' [Hdfn_anc' [Hfa_tv' [Htv_vis' [Hnd_a [Hina_stack [Hanc_ne_a [Hpar_ne_a [Hdg_par_a [Hdfn_d_lt_a [Hin_par Hdf_anc_par]]]]]]]]]]]]]]]].
            apply Hoare_choice.
            + (* Back edge: In v (stack s) *)
              apply Hoare_assume_bind. simpl. intro_state. destruct H as [Hin_stack Heq_s']. subst s1.
              apply (Hoare_bind (fun s => s = s0)
                (get' (fun s0 => dfn s0 v))
                (fun dv s => s = s0 /\
                  low_forset_inv anc d s /\ fa s a = par /\
                  done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                  dfn_injective s /\ dfn s anc < dfn s a /\ fa s tv = tp /\
                  tv ∈ visited s /\ ~ d a /\ In a (stack s) /\
                  anc <> a /\ par <> a /\ dg_step g par a /\
                  In par (stack s) /\ dfn s anc < dfn s par)
                (fun dv => update_low a dv)
                (fun _ s => low_forset_inv anc d s /\ fa s a = par /\
                  done_visited d s /\ In anc (stack s) /\ stack_dfn_order s /\
                  dfn_injective s /\ dfn s anc < dfn s a /\ fa s tv = tp /\
                  tv ∈ visited s /\ ~ d a /\ In a (stack s) /\
                  anc <> a /\ par <> a /\ dg_step g par a /\
                  (forall w, d w -> In w (stack s) -> dfn s w < dfn s a) /\
                  In par (stack s) /\ dfn s anc < dfn s par)).
              ++ unfold get'. intro_state. hoare_auto_s.
                 destruct H1 as [Heq_s _]. subst s. subst s1.
                 split. reflexivity.
                 split. exact Hlow_inv. split. exact Hfa_a. split. exact Hdv'. split. exact Hina'.
                 split. exact Horder'. split. exact Hinj'. split. exact Hdfn_anc'. split. exact Hfa_tv'.
                 split. exact Htv_vis'. split. exact Hnd_a. split. exact Hina_stack.
                 split. exact Hanc_ne_a. split. exact Hpar_ne_a. split. exact Hdg_par_a.
                 split. exact Hin_par. exact Hdf_anc_par.
              ++ intros dv. unfold update_low. intro_state. hoare_auto_s.
                { unfold set_low. intro_state. hoare_auto_s. subst s2. subst s.
                  destruct H as [Heq_s1 Hrest]. subst s1. clear Hrest.
                  assert (Hlow_post: low_forset_inv anc d
                    (RecordSet.set low (fun (low0: V->nat) (x:V) => if equiv_decb x a then Nat.min (low s0 a) dv else low0 x) s0)).
                  { eapply (update_low_preserves_low_forset_inv_for_other anc a dv d s0); eauto. }
                  assert (Hle: dv <= low s0 a). { lia. }
                  assert (Hlow_fun_eq2: (fun (low0: V->nat) (x:V) => if equiv_decb x a then Nat.min (low s0 a) dv else low0 x)
                                     = (fun (low0: V->nat) (x:V) => if equiv_decb x a then dv else low0 x)).
                  { apply functional_extensionality; intro low0.
                    apply functional_extensionality; intro x.
                    unfold equiv_decb.
                    destruct (equiv_dec x a) as [Heq | Hneq].
                    - rewrite Nat.min_r; [reflexivity | auto].
                    - reflexivity. }
                  rewrite Hlow_fun_eq2 in Hlow_post.
                  simpl. split. exact Hlow_post. split. reflexivity. split. exact Hdv'.
                  split. exact Hina'. split. exact Horder'. split. exact Hinj'.
                  split. exact Hdfn_anc'. split. reflexivity.
                  split. exact Htv_vis'. split. exact Hnd_a.
                  split. exact Hina_stack. split. exact Hanc_ne_a.
                  split. exact Hpar_ne_a. split. exact Hdg_par_a.
                  split. exact Hdfn_d_lt_a.
                  split. exact Hin_par. exact Hdf_anc_par. }
                { destruct H1 as [Heq _]. subst s.
                  destruct H as [Heq_s1 Hrest]. subst s1. clear Hrest.
                  split. exact Hlow_inv. split. reflexivity. split. exact Hdv'. split. exact Hina'.
                  split. exact Horder'. split. exact Hinj'. split. exact Hdfn_anc'.
                  split. reflexivity.
                  split. exact Htv_vis'. split. exact Hnd_a. split. exact Hina_stack.
                  split. exact Hanc_ne_a. split. exact Hpar_ne_a. split. exact Hdg_par_a.
                  split. exact Hdfn_d_lt_a.
                  split. exact Hin_par. exact Hdf_anc_par. }
            + (* Cross edge: ~ In v (stack s): skip *)
              intro_state. hoare_auto_s.
              destruct H1 as [Heq_s Hnstack]. subst s. subst s1.
              split. exact Hlow_inv. split. exact Hfa_a. split. exact Hdv'. split. exact Hina'.
              split. exact Horder'. split. exact Hinj'. split. exact Hdfn_anc'.
              split. exact Hfa_tv'. split. exact Htv_vis'.
              split. exact Hnd_a. split. exact Hina_stack. split. exact Hanc_ne_a.
              split. exact Hpar_ne_a. split. exact Hdg_par_a.
              split. exact Hdfn_d_lt_a.
              split. exact Hin_par. exact Hdf_anc_par. }
        (* Apply Hoare_forset: P_forset already includes In par and dfn anc < dfn s par *)
        assert (Hforset_full: Hoare (fun s => P_forset (fun _ => False) s)
          (forset (fun v => dg_step g a v) (process_edge a W))
          (fun _ s => P_forset (fun v => dg_step g a v) s)).
        { refine (@Hoare_forset SCCSt V P_forset (fun v => dg_step g a v) (process_edge a W) ProperP Hbody). }
        apply (Hoare_conseq_pre _ (fun s => P_forset (fun _ => False) s) _ _).
        { intros s [HP_anc [HP_tvtp [HP_ineqs [HP_nda [HP_instack [HP_dfnd [HP_par HP_dfnd_par]]]]]]].
          destruct HP_anc as [Hlow_inv [Hfa_a [Hina' [Horder' [Hinj' [Hdv' Hdfn_anc']]]]]].
          destruct HP_tvtp as [Hfa_tv' Htv_vis'].
          destruct HP_ineqs as [Hanc_ne_a [Hpar_ne_a Hdg_par_a]].
          unfold P_forset. split. exact Hlow_inv. split. exact Hfa_a. split. exact Hdv'.
          split. exact Hina'. split. exact Horder'. split. exact Hinj'. split. exact Hdfn_anc'.
          split. exact Hfa_tv'. split. exact Htv_vis'.
          split. exact HP_nda. split. exact HP_instack. split. exact Hanc_ne_a.
          split. exact Hpar_ne_a. split. exact Hdg_par_a.
          split. exact HP_dfnd. split. exact HP_par. exact HP_dfnd_par. }
        exact Hforset_full.
      + (* If (low a = dfn a) (pop_scc a) *)
        intro a''. destruct a''.
        intro_state. hoare_auto_s.
        * (* pop_scc a branch *)
          destruct H as [Hlow_inv Heq_low_dfn].
          destruct Heq_low_dfn as (Hfa_a & Hdv' & Hina' & Horder' & Hinj' & Hdfn_anc' & Hfa_tv' & Htv_vis' & Hnd_a & Hina_stack & Hanc_ne_a & Hpar_ne_a & Hdg_par_a & Hdfn_d_lt_a & Hin_par & Hdf_anc_par).
          apply Hoare_conseq_pre with (P2 := fun s => low_forset_inv anc d s /\ fa s a = par /\ ~ d a /\
            In a (stack s) /\ In anc (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ done_visited d s /\
            (forall w, d w -> In w (stack s) -> dfn s w < dfn s a) /\ dfn s anc < dfn s a).
          { intros s' Hs'. subst s'. split. exact Hlow_inv. split. exact Hfa_a. split. exact Hnd_a.
            split. exact Hina_stack. split. exact Hina'. split. exact Horder'.
            split. exact Hinj'. split. exact Hdv'.
            split. exact Hdfn_d_lt_a. exact Hdfn_anc'. }
          eapply Hoare_conseq_post.
          2: { eapply (pop_scc_preserves_ancestor_inv anc par a d Hanc_ne_a Hpar_ne_a Hdg_par_a). }
          intros _ s [Hlow_inv' [Hfa_a' [Hina'' [Horder'' [Hinj'' Hdv'']]]]].
          (* Remaining conjuncts: all properties preserved through pop_scc since it only modifies stack/sccs *)
          admit.
        * (* skip branch: ~ low a = dfn a *)
          destruct H as [Hlow_inv Hrest]. destruct H1 as [Heq _]. subst s.
          destruct Hrest as (Hfa_a & Hdv' & Hina' & Horder' & Hinj' & Hdfn_anc' & Hfa_tv' & Htv_vis' & Hnd_a & Hina_stack & Hanc_ne_a & Hpar_ne_a & Hdg_par_a & Hdfn_d_lt_a & Hin_par & Hdf_anc_par).
          split. exact Hlow_inv. split. exact Hfa_a. split. exact Hdv'. split. exact Hina'.
          split. exact Horder'. split. exact Hinj'. split. exact Hdfn_d_lt_a.
          split. exact Hdfn_anc'. split. exact Hfa_tv'. split. exact Htv_vis'.
          split. exact Hnd_a. split. exact Hin_par.
          split. exact Hanc_ne_a. split. exact Hpar_ne_a. split. exact Hdg_par_a.
          exact Hdf_anc_par.
  Admitted.



  (** [set_fa_state_preserves_dg_step]: Setting [fa v] does not create new
      DFS-tree edges when [v] is not visited, because DFS tree edges only
      exist for visited vertices. *)
  Lemma set_fa_state_preserves_dg_step (v u rt: V) (s: SCCSt):
    ~ v ∈ visited s ->
    forall x y, dg_step (state_to_dfs_tree g (set_fa_state s v u) rt) x y ->
           dg_step (state_to_dfs_tree g s rt) x y.
  Proof.
    intros Hnv x y Hstep.
    unfold dg_step, original_step in *.
    destruct Hstep as [e [[w [Hw_vis [Hw_fa [Hwfst Hwsnd]]]] [Hfst Hsnd]]].
    unfold set_fa_state in *. simpl in *.
    simpl in Hw_fa, Hwfst. unfold equiv_decb in Hw_fa, Hwfst.
    destruct (equiv_dec w v) as [Heqw0 | Hneqw0] in Hwfst, Hw_fa |- *.
    - (* w = v: contradicts Hnv *)
      rewrite Heqw0 in Hw_vis. exfalso. exact (Hnv Hw_vis).
    - (* w ≠ v *)
      exists e. split; [| split]; auto.
      exists w. split; [exact Hw_vis |]. split; [exact Hw_fa |]. split; [exact Hwfst | exact Hwsnd].
  Qed.

  (** [set_fa_W_preserves_low_forset_inv]: convenience lemma for the
      direct-parent tree-edge step.  It assumes [W v] already satisfies
      the ancestor invariant (the postcondition of
      [W_preserves_ancestor_inv u u v done]).  After [set_fa v u] and
      [W v], the parent [u] keeps [low_forset_inv u done], [fa s v = u],
      and the stack-ordering conjuncts.

      Note: [forset_keep_low_forset_inv] uses a different tree-edge lemma
      ([tree_edge_preserves_low_forset_inv_lowlink]) because its induction
      hypothesis is the low-link specification, not the ancestor invariant. *)
  Lemma set_fa_W_preserves_low_forset_inv (u v: V) (done: V -> Prop) (W: V -> program (@SCCSt V) unit):
    u <> v -> dg_step g u v -> ~ done v ->
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v /\
                    done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s)
          (W v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u /\ done_visited done s /\
                      In u (stack s) /\ stack_dfn_order s /\ dfn_injective s /\
                      (forall w, done w -> In w (stack s) -> dfn s w < dfn s v)) ->
    Hoare (fun s => low_forset_inv u done s /\ ~ v ∈ visited s /\ ~ done v /\
                    done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s)
          (set_fa v u;; W v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u /\ done_visited done s /\
                      In u (stack s) /\ stack_dfn_order s /\ dfn_injective s /\
                      (forall w, done w -> In w (stack s) -> dfn s w < dfn s v)).
  Proof.
    intros Hneq Hdg Hndone HW.
    pose (P := fun s => low_forset_inv u done s /\ ~ v ∈ visited s /\ ~ done v /\
                        done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s).
    pose (Qmid := fun (_: unit) (s: SCCSt) =>
      low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v /\
      done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s).
    pose (R := fun (_: unit) (s: SCCSt) =>
      low_forset_inv u done s /\ fa s v = u /\ done_visited done s /\
      In u (stack s) /\ stack_dfn_order s /\ dfn_injective s /\
      (forall w, done w -> In w (stack s) -> dfn s w < dfn s v)).
    apply (@Hoare_bind SCCSt unit unit P (set_fa v u) Qmid (fun _ => W v) R).
    - (* first part: set_fa v u *)
      unfold P, Qmid, set_fa. intro_state. hoare_auto_s.
      destruct H as [Hlow [Hnv [Hndone' [Hdv [Hinu [Horder Hinj]]]]]].
      unfold low_forset_inv, low_forset_inv_core.
      destruct Hlow as [Hwf [Huvis Hmin]].
      subst s. simpl.
      (* Goal: Qmid tt (post_state) = (low_forset_inv /\ fa = u /\ ...) *)
      split.  (* low_forset_inv *)
      { unfold low_forset_inv, low_forset_inv_core. simpl. split.
        - (* wf_scc_state *)
          unfold wf_scc_state in *. destruct Hwf as [Hsiv [Hinv' [Hvalid Hfa_vis]]].
          unfold wf_scc_state. simpl. split; [exact Hsiv | split; [exact Hinv' |]].
          split.
          { (* dfn_valid: use set_fa_state_preserves_dg_step *)
            unfold dfn_valid. intros x y Htree.
            eapply Hvalid. eapply (set_fa_state_preserves_dg_step v u root s0 Hnv); eauto. }
          (* fa_visited *)
          unfold fa_visited. simpl. intros w Hfa_w.
          unfold equiv_decb. unfold equiv_decb in Hfa_w.
          destruct (equiv_dec w v) as [Heq_wv | Hneq_wv].
          + simpl. exact Huvis.
          + simpl in Hfa_w. simpl. apply Hfa_vis. exact Hfa_w.
        - split; [exact Huvis |].
          eapply (set_fa_preserves_min u v done s0 Hndone' Hmin). }
      (* fa s v = u *)
      split. { unfold equiv_decb. destruct (equiv_dec v v) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity]. }
      (* ~ v ∈ visited *)
      split; [exact Hnv |].
      (* ~ done v *)
      split; [exact Hndone' |].
      (* done_visited done *)
      split; [unfold done_visited; simpl; exact Hdv |].
      (* In u (stack s) *)
      split; [exact Hinu |].
      (* stack_dfn_order *)
      split; [exact Horder |].
      (* dfn_injective *)
      exact Hinj.
    - (* second part: W v *)
      intros a. destruct a. apply HW.
  Qed.

  (** [tree_edge_preserves_low_forset_inv_lowlink]: Tree-edge step for
      [forset_keep_low_forset_inv].  It uses the low-link induction
      hypothesis (low_pre x -> low_post x) rather than the ancestor
      invariant, because [forset_keep_low_forset_inv] is proved by
      fixpoint induction over [tarjan_scc] with that single IH.

      After [set_fa a0 u] and [W a0], the parent [u] keeps
      [low_forset_inv u done], [fa s a0 = u], the stack-ordering
      conjuncts, and additionally [low_post a0] (needed for the
      subsequent [update_low u (low a0)]). *)
    (** [tree_edge_preserves_low_forset_inv_lowlink]: Tree-edge step for
      [forset_keep_low_forset_inv].  It uses the low-link induction
      hypothesis (low_pre x -> low_post x) rather than the ancestor
      invariant, because [forset_keep_low_forset_inv] is proved by
      fixpoint induction over [tarjan_scc] with that single IH.

      After [set_fa a0 u] and [W a0], the parent [u] keeps
      [low_forset_inv u done], [fa s a0 = u], the stack-ordering
      conjuncts, and additionally [low_post a0] (needed for the
      subsequent [update_low u (low a0)]).

      The induction hypothesis on [W x] is strengthened with
      [x ∈ visited s] in its postcondition.  This is necessary because
      [low_post x] alone only gives [wf_scc_state s] and
      [scc_low_valid_v s x], and [dfn_inv] does not forbid
      [dfn s x = 0] for unvisited vertices; thus [a0 ∈ visited] cannot
      be derived from [low_post a0] alone, yet it is required to show
      [done_visited (done ∪ [a0])] and to invoke later lemmas.
      Strengthening the IH is sound: [W x] begins with [preloop x],
      which marks [x] visited.

      The additional precondition
        [forall w, done w -> In w (stack s) -> dfn s w < dfn s a0]
      is the frame condition identified in
      docs/dev/20260623-tarjan-scc-is-low-proof-gaps.md: it guarantees
      that [W a0] does not pop any [done] vertex that is still on the
      stack, so [back_edges_done] does not shrink unexpectedly.  It is
      available at the call site because every [w ∈ done] was processed
      before the current child [a0].

      To close the Hoare triple for [W a0], we also need a separate
      *frame* hypothesis saying that [W x] preserves the ancestor
      invariant for [u] (i.e. [low_forset_inv u done], [fa s x = u],
      stack ordering, etc.).  This cannot be derived from the low-link
      IH, which only talks about [low_pre/post x].  The frame hypothesis
      is proved for the real recursive function by
      [W_preserves_ancestor_inv]. *)
  Lemma tree_edge_preserves_low_forset_inv_lowlink (u a0: V) (done: V -> Prop) (W: V -> program (@SCCSt V) unit):
    u <> a0 -> dg_step g u a0 -> ~ done a0 ->
    (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s)
                     (W x)
                     (fun _ s => low_post x s /\ x ∈ visited s /\ u ∈ visited s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s)) ->
    (forall x, Hoare (fun s => low_forset_inv u done s /\ fa s x = u /\ low_pre x s /\ ~ done x /\ done_visited done s /\
                            In u (stack s) /\ stack_dfn_order s /\ dfn_injective s)
                     (W x)
                     (fun _ s => low_forset_inv u done s /\ fa s x = u /\ done_visited done s /\
                                 In u (stack s) /\ stack_dfn_order s /\ dfn_injective s /\
                                 (forall w, done w -> In w (stack s) -> dfn s w < dfn s x) /\
                                 dfn s u < dfn s x)) ->
    Hoare (fun s => low_forset_inv u done s /\ ~ a0 ∈ visited s /\ ~ done a0 /\ done_visited done s /\ In u (stack s) /\
                    stack_dfn_order s /\ dfn_injective s /\
                    (forall w, done w -> In w (stack s) -> dfn s w < dfn s a0))
          (set_fa a0 u;; W a0)
          (fun _ s => low_forset_inv u done s /\ fa s a0 = u /\ a0 ∈ visited s /\ done_visited done s /\ In u (stack s) /\
                      stack_dfn_order s /\ dfn_injective s /\ low_post a0 s).
  Proof.
    intros Hneq Hdg Hndone HW Hframe.
    pose (Qmid := fun (_: unit) (s: SCCSt) =>
      low_forset_inv u done s /\ fa s a0 = u /\ low_pre a0 s /\ ~ done a0 /\
      done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s).
    apply (@Hoare_bind SCCSt unit unit
      (fun s => low_forset_inv u done s /\ ~ a0 ∈ visited s /\ ~ done a0 /\
                done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s /\
                (forall w, done w -> In w (stack s) -> dfn s w < dfn s a0))
      (set_fa a0 u) Qmid (fun _ => W a0)
      (fun _ s => low_forset_inv u done s /\ fa s a0 = u /\ a0 ∈ visited s /\
                  done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ low_post a0 s)).
    - (* set_fa a0 u *)
      unfold Qmid, low_pre, wf_scc_state_pre, set_fa. intro_state. hoare_auto_s.
      destruct H as [Hlow [Hnv [Hnd [Hdv [Hinu [Horder [Hinj Hdfn_lt]]]]]]].
      unfold low_forset_inv, low_forset_inv_core.
      destruct Hlow as [Hwf [Huvis Hmin]].
      unfold wf_scc_state in Hwf. destruct Hwf as [Hsiv [Hinv' [Hvalid Hfa_vis]]].
      subst s. simpl.
      split.  (* low_forset_inv *)
      { unfold low_forset_inv, low_forset_inv_core. simpl. split.
        - (* wf_scc_state *)
          unfold wf_scc_state. simpl. split; [exact Hsiv | split; [exact Hinv' |]].
          split.
          * unfold dfn_valid. intros x y Htree.
            eapply Hvalid. eapply (set_fa_state_preserves_dg_step a0 u root s0 Hnv); eauto.
          * unfold fa_visited. simpl. intros w Hfa_w.
            unfold equiv_decb. unfold equiv_decb in Hfa_w.
            destruct (equiv_dec w a0) as [Heq_wa0 | Hneq_wa0].
            + simpl. exact Huvis.
            + simpl in Hfa_w. simpl. apply Hfa_vis. exact Hfa_w.
        - split; [exact Huvis |].
          eapply (set_fa_preserves_min u a0 done s0 Hnd Hmin). }
      split.  (* fa s a0 = u *)
      { unfold equiv_decb. destruct (equiv_dec a0 a0) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity]. }
      split.  (* low_pre a0 *)
      { unfold wf_scc_state. simpl. split.
        * split; [exact Hsiv |].
          split; [exact Hinv' |].
          split.
          { unfold dfn_valid. intros x y Htree.
            eapply Hvalid. eapply (set_fa_state_preserves_dg_step a0 u root s0 Hnv); eauto. }
          { unfold fa_visited. simpl. intros w Hfa_w.
            unfold equiv_decb. unfold equiv_decb in Hfa_w.
            destruct (equiv_dec w a0) as [Heq_wa0 | Hneq_wa0].
            + simpl. exact Huvis.
            + simpl in Hfa_w. simpl. apply Hfa_vis. exact Hfa_w. }
        * exact Hnv. }
      split; [exact Hnd |].
      split; [unfold done_visited; simpl; exact Hdv |].
      split; [exact Hinu |].
      split; [exact Horder |].
      exact Hinj.
    - (* W a0: combine low-link IH and frame lemma *)
      intro a'. destruct a'. specialize (HW a0) as Hlowlink. specialize (Hframe a0) as Hframe_a0.
      (* Step 3: first reshape to the two-group combined postcondition,
         then use Hoare_conj to combine the two IHs. *)
      apply (Hoare_conseq_post (Qmid tt) (W a0)
        (fun (_: unit) (s: SCCSt) => low_forset_inv u done s /\ fa s a0 = u /\ a0 ∈ visited s /\ done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s /\ low_post a0 s)
        (fun (_: unit) (s: SCCSt) =>
          (low_post a0 s /\ a0 ∈ visited s /\ u ∈ visited s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s) /\
          (low_forset_inv u done s /\ fa s a0 = u /\ done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s /\
           (forall w, done w -> In w (stack s) -> dfn s w < dfn s a0) /\ dfn s u < dfn s a0))).
      { intros _ s [[Hpost [Hvis [Huvis' [Hinu' [Horder' Hinj']]]]]
                    [Hlow_inv [Hfa [Hdv' [Hinu0 [Horder0 [Hinj0 [Hdfn_lt Hdfn_u]]]]]]]].
        split. exact Hlow_inv. split. exact Hfa. split. exact Hvis.
        split. exact Hdv'. split. exact Hinu'. split. exact Horder'.
        split. exact Hinj'. exact Hpost. }
      (* Step 1+2: align both IHs to Qmid and combine with Hoare_conj *)
      apply Hoare_conj.
      + (* low-link IH *)
        apply (Hoare_conseq_pre (Qmid tt)
          (fun s => low_pre a0 s /\ u ∈ visited s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s)
          (W a0)
          (fun (_: unit) (s: SCCSt) => low_post a0 s /\ a0 ∈ visited s /\ u ∈ visited s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s)).
        { intros s [Hlow_inv [Hfa [Hpre [Hnd' [Hdv' [Hinu0 [Horder0 Hinj0]]]]]]].
          split. exact Hpre. split.
          destruct Hlow_inv as [_ [Huvis' _]]. exact Huvis'.
          split. exact Hinu0. split. exact Horder0. exact Hinj0. }
        exact Hlowlink.
      + (* frame lemma *)
        apply (Hoare_conseq_pre (Qmid tt)
          (fun s => low_forset_inv u done s /\ fa s a0 = u /\ low_pre a0 s /\ ~ done a0 /\ done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s)
          (W a0)
          (fun (_: unit) (s: SCCSt) => low_forset_inv u done s /\ fa s a0 = u /\ done_visited done s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s /\
           (forall w, done w -> In w (stack s) -> dfn s w < dfn s a0) /\ dfn s u < dfn s a0)).
        { intros s [Hlow_inv [Hfa [Hpre [Hnd' [Hdv' [Hinu0 [Horder0 Hinj0]]]]]]].
          split. exact Hlow_inv. split. exact Hfa. split. exact Hpre.
          split. exact Hnd'. split. exact Hdv'. split. exact Hinu0.
          split. exact Horder0. exact Hinj0. }
        exact Hframe_a0.
  Qed.

  (** [low_forset_inv_proper]: [low_forset_inv u done s] is a Proper
      morphism w.r.t. set equivalence of [done].  When [done1 == done2],
      the [children_done] and [back_edges_done] sets are equivalent,
      so the nested min condition transfers via [min_eq_forward]. *)
  Lemma low_forset_inv_proper u: Proper (Sets.equiv ==> eq ==> iff) (low_forset_inv u).
  Proof.
    intros done1 done2 Hequiv s1 s2 Heq. subst s2.
    assert (Hincl12: done1 ⊆ done2). {
      apply Sets_equiv_Sets_included in Hequiv. tauto. }
    assert (Hincl21: done2 ⊆ done1). {
      apply Sets_equiv_Sets_included in Hequiv. tauto. }
    assert (Hchild_eq: children_done s1 u done1 == children_done s1 u done2). {
      unfold children_done.
      apply Sets_equiv_Sets_included. split.
      - sets_unfold. intros x [Hx_d1 [Hfa_x Hneq]]. split; [apply Hincl12; exact Hx_d1 | auto].
      - sets_unfold. intros x [Hx_d2 [Hfa_x Hneq]]. split; [apply Hincl21; exact Hx_d2 | auto]. }
    assert (Hback_eq: back_edges_done s1 u done1 == back_edges_done s1 u done2). {
      unfold back_edges_done.
      apply Sets_equiv_Sets_included. split.
      - sets_unfold. intros x [Hx_d1 [Hst Hfa]]. split; [apply Hincl12; exact Hx_d1 | auto].
      - sets_unfold. intros x [Hx_d2 [Hst Hfa]]. split; [apply Hincl21; exact Hx_d2 | auto]. }
    split; intro Hlow; unfold low_forset_inv, low_forset_inv_core in *;
      destruct Hlow as [Hwf [Hvis Hmin]].
    - (* forward: done1 → done2 *)
      split; [exact Hwf | split; [exact Hvis |]].
      eapply min_eq_forward; [auto using NatLe_TotalOrder | exact Hmin | | ].
      + intros a1 Ha1. exists a1. split.
        * destruct Ha1 as [Ha1_L | Ha1_R].
          -- left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** apply Hchild_eq. exact Hw_in.
                ** intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx.
             ++ exact Heq_a1.
          -- right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** destruct Hw_in as [Hw_back | Hw_u].
                   --- left. apply Hback_eq. exact Hw_back.
                   --- right. exact Hw_u.
                ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                   --- apply Hw_min. left. apply Hback_eq. exact Hx_back.
                   --- subst x. apply Hw_min. right. reflexivity.
             ++ exact Heq_a1.
        * apply Nat.le_refl.
      + intros a2 Ha2. exists a2. split.
        * destruct Ha2 as [Ha2_L | Ha2_R].
          -- left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** apply Hchild_eq. exact Hw_in.
                ** intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx.
             ++ exact Heq_a2.
          -- right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** destruct Hw_in as [Hw_back | Hw_u].
                   --- left. apply Hback_eq. exact Hw_back.
                   --- right. exact Hw_u.
                ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                   --- apply Hw_min. left. apply Hback_eq. exact Hx_back.
                   --- subst x. apply Hw_min. right. reflexivity.
             ++ exact Heq_a2.
        * apply Nat.le_refl.
    - (* backward: done2 → done1 *)
      split; [exact Hwf | split; [exact Hvis |]].
      eapply min_eq_forward; [auto using NatLe_TotalOrder | exact Hmin | | ].
      + intros a1 Ha1. exists a1. split.
        * destruct Ha1 as [Ha1_L | Ha1_R].
          -- left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** apply Hchild_eq. exact Hw_in.
                ** intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx.
             ++ exact Heq_a1.
          -- right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** destruct Hw_in as [Hw_back | Hw_u].
                   --- left. apply Hback_eq. exact Hw_back.
                   --- right. exact Hw_u.
                ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                   --- apply Hw_min. left. apply Hback_eq. exact Hx_back.
                   --- subst x. apply Hw_min. right. reflexivity.
             ++ exact Heq_a1.
        * apply Nat.le_refl.
      + intros a2 Ha2. exists a2. split.
        * destruct Ha2 as [Ha2_L | Ha2_R].
          -- left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** apply Hchild_eq. exact Hw_in.
                ** intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx.
             ++ exact Heq_a2.
          -- right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** destruct Hw_in as [Hw_back | Hw_u].
                   --- left. apply Hback_eq. exact Hw_back.
                   --- right. exact Hw_u.
                ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                   --- apply Hw_min. left. apply Hback_eq. exact Hx_back.
                   --- subst x. apply Hw_min. right. reflexivity.
             ++ exact Heq_a2.
        * apply Nat.le_refl.
  Qed.

  Lemma done_visited_proper: Proper (Sets.equiv ==> eq ==> iff) done_visited.
  Proof.
    intros done1 done2 Hequiv s1 s2 Heq. subst s2.
    unfold done_visited.
    split; intros H w Hw.
    - apply H. apply Hequiv. exact Hw.
    - apply H. apply Hequiv. exact Hw.
  Qed.

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
    intros Hstep IH.
    unfold process_edge, if_else. intro_state. apply Hoare_choice.
    - (* Tree edge *) apply Hoare_assume_bind. simpl.
      rename H into Hfa_all.
      apply (Hoare_bind (fun s => ~ v ∈ visited s /\ s = s0) (set_fa v u)
               (fun _ s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)
               (fun _ => W v ;; lv <- get' (fun s => low s v) ;; update_low u lv)
               (fun _ s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)).
      + (* set_fa v u *) unfold set_fa. intro_state. hoare_auto_s.
        destruct H as [Hnv' Hs1_eq]. subst s1. subst s. simpl.
        unfold equiv_decb. destruct (equiv_dec w v) as [Heq | Hneq].
        * (* w = v, fa_new w = u *) rewrite Heq in H2 |- *. simpl in H2.
          unfold equiv_decb in H2. destruct (equiv_dec v v) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
          destruct H2 as [Hfa_eq _]. rewrite Hfa_eq in Hstep. exact Hstep.
        * (* w ≠ v, fa_new w unchanged *) simpl in H2.
          unfold equiv_decb in H2. destruct (equiv_dec w v) as [Heq' | Hneq']; [exfalso; apply Hneq; exact Heq'|].
          destruct H2 as [Hfa_eq Hfa_neq]. apply Hfa_all. exact (conj Hfa_eq Hfa_neq).
      + intros _. simpl.
        apply (Hoare_bind (fun s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)
                 (W v) (fun _ s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)
                 (fun _ => lv <- get' (fun s => low s v) ;; update_low u lv)
                 (fun _ s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)).
        * apply IH.
        * intros _. simpl.
          apply (Hoare_bind (fun s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)
                   (get' (fun s => low s v))
                   (fun lv s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)
                   (fun lv => update_low u lv)
                   (fun _ s => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w)).
          -- unfold get'. intro_state. hoare_auto_s.
             apply H. destruct H1 as [Hs1 _]. rewrite <- Hs1. assumption.
          -- intros lv. simpl. unfold update_low. intro_state. hoare_auto_s.
             ++ unfold set_low. intro_state. hoare_auto_s. subst s. subst s2. simpl.
                apply H. destruct H4 as [Hfa Hneq]. split.
                ** exact Hfa.
                ** exact Hneq.
             ++ apply H. destruct H1 as [Hs1 _]. rewrite <- Hs1. exact H2.
    - (* Non-tree edge *) apply Hoare_assume_bind. simpl.
      rename H into Hfa_all. intro_state. hoare_auto_s.
      + (* In stack *) destruct H as [Hx_vis Hs1_eq]. subst s1.
        unfold update_low. intro_state. hoare_auto_s.
        * unfold set_low. intro_state. hoare_auto_s. subst s. simpl.
          apply Hfa_all. destruct H4 as [Hfa Hneq]. split.
          ** rewrite H2 in Hfa. exact Hfa.
          ** rewrite H2 in Hneq. exact Hneq.
        * destruct H. subst s. apply Hfa_all. exact H2.
      + (* Not in stack *) destruct H1 as [Heq _]. subst s.
        destruct H as [Hx_vis Hs1_eq]. subst s1. apply Hfa_all. exact H2.
  Qed.

  Lemma tarjan_scc_keep_fa_children_in_universe (parent a: V):
    Hoare (fun s: @SCCSt V => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g a)
          (fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
  Proof.
    unfold tarjan_scc. hoare_fix_nolv_auto V. clear a. intros W IH a. unfold tarjan_scc_f.
    eapply Hoare_bind with (R := fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
    { unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
      instantiate (1 := fun (_:unit) (s:SCCSt) => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
      exact H. }
    { simpl. intros _. eapply Hoare_bind with (R := fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
      { apply (@Hoare_forset SCCSt V
          (fun done s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)
          (fun v => dg_step g a v) (process_edge a W)).
        { unfold Proper, respectful. intros. subst. reflexivity. }
        { intros todo a0 Hsub Huniv Hnotdone.
          apply process_edge_keep_fa_children.
          { exact Huniv. }
          { intros x. apply IH. } } }
      { simpl. intros _. intro_state. hoare_auto_s.
        { (* pop_scc a branch: low a = dfn a *)
          unfold pop_scc.
          pose (f := fun st : SCCSt => pop_scc_state st a).
          assert (Hpop_scc: Hoare (fun st => st = s0) (update' f) (fun _ st => st = f s0)).
          { apply Hoare_update'. }
          eapply Hoare_conseq_post; [| exact Hpop_scc].
          unfold f. intros _ st Heq. subst st. intros v Hfa_v.
          apply H. unfold pop_scc_state in Hfa_v.
          destruct (stack_split_at (stack s0) a) as [popped rest]. simpl in Hfa_v.
          exact Hfa_v. }
        { (* skip branch: low a <> dfn a *)
          destruct H1 as [Heq _]. subst s. destruct H2 as [Hfa_eq Hfa_neq].
          eapply H. split; eauto. } } }
  Qed.


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
    intros Hdv Hfa_g v. unfold children_done, done_visited in *.
    split.
    - intros [Hdg [Hfa_eq Hfa_neq]].
      apply Hdv in Hdg as Hvis.
      eapply state_to_dfs_tree_step_char_backward; eauto.
    - intros Htree.
      apply state_to_dfs_tree_step_char in Htree as [Hfa_eq [Hfa_neq Hvis]].
      split; [| split; [exact Hfa_eq | exact Hfa_neq]].
      apply Hfa_g. split; assumption.
  Qed.

  (** [back_edges_done_full_eq]: When [done = dg_step g u], the
      [back_edges_done] set coincides with [scc_back_edge s u] except
      possibly at [u] itself: if [fa s u = u] (e.g. a DFS root) and there
      is a self-loop [dg_step g u u], then [u] belongs to
      [scc_back_edge] but not to [back_edges_done] (the latter requires
      [fa s u <> u]).  Adding the singleton [[u]] to both sides restores
      equivalence without the unsatisfiable [stack_fa_neq_self] premise.

      Forward direction uses [state_to_dfs_tree_step_char] (tree edge ⇒
      fa = u).  Backward direction only needs [state_to_dfs_tree_step_char_backward]
      for [v <> u]; the case [v = u] is absorbed by the added [[u]]. *)
  Lemma back_edges_done_full_eq (u: V) (s: SCCSt):
    done_visited (fun v => dg_step g u v) s ->
    back_edges_done s u (fun v => dg_step g u v) ∪ [u] == scc_back_edge s u ∪ [u].
  Proof.
    intros Hdv v. unfold done_visited in Hdv.
    unfold back_edges_done, scc_back_edge.
    split.
    - (* forward: back_edges_done ∪ [u] ⊆ scc_back_edge ∪ [u] *)
      intros H. sets_unfold in H. destruct H as [[Hv_dg [Hv_stack Hfa_neq]] | Heq_vu].
      + (* v ∈ back_edges_done *)
        sets_unfold. left. split; [exact Hv_dg | split; [exact Hv_stack |]].
        intro Htree.
        apply state_to_dfs_tree_step_char in Htree as [Hfa_eq _].
        exact (Hfa_neq Hfa_eq).
      + (* v = u *)
        sets_unfold. subst v. right. reflexivity.
    - (* backward: scc_back_edge ∪ [u] ⊆ back_edges_done ∪ [u] *)
      intros H. sets_unfold in H. destruct H as [[Hv_dg [Hv_stack Hnot_tree]] | Heq_vu].
      + (* v ∈ scc_back_edge *)
        apply Hdv in Hv_dg as Hv_vis.
        destruct (classic (v = u)) as [Heq_uv | Hneq_uv].
        * (* v = u: use [u] singleton *)
          sets_unfold. subst v. right. reflexivity.
        * (* v ≠ u: prove fa s v ≠ u via contrapositive *)
          sets_unfold. left. split; [exact Hv_dg | split; [exact Hv_stack |]].
          intro Hfa_eq.
          assert (Hfa_neq_self: fa s v <> v). {
            rewrite Hfa_eq. intro Heq. apply Hneq_uv. symmetry. exact Heq. }
          apply Hnot_tree.
          eapply state_to_dfs_tree_step_char_backward;
            [exact Hv_dg | exact Hfa_eq | exact Hfa_neq_self | exact Hv_vis].
      + (* v = u *)
        sets_unfold. subst v. right. reflexivity.
  Qed.

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
  Lemma back_edges_done_union_beta (u: V) (s: SCCSt) (w: V):
    (back_edges_done s u (fun v => dg_step g u v) ∪ [u]) w <->
    (w ∈ (fun w0 => back_edges_done s u (fun v => dg_step g u v) w0 \/ w0 = u)).
  Proof.
    sets_unfold. split.
    - intros [H|H]; [left; exact H | right; symmetry; exact H].
    - intros [H|H]; [left; exact H | right; symmetry; exact H].
  Qed.

  Lemma low_forset_inv_to_scc_low_valid (u: V) (s: SCCSt):
    done_visited (fun v => dg_step g u v) s ->
    (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) ->
    low_forset_inv u (fun v => dg_step g u v) s ->
    scc_low_valid_v s u.
  Proof.
    intros Hdv Hfa_g Hlow.
    unfold low_forset_inv, low_forset_inv_core in Hlow.
    destruct Hlow as [Hwf [Huvis Hmin]].
    unfold scc_low_valid_v.
    pose proof (children_done_full_eq u s Hdv Hfa_g) as Hchild_eq.
    pose proof (back_edges_done_full_eq u s Hdv) as Hback_eq.
    eapply min_eq_forward; [typeclasses eauto | exact Hmin | | ].
    - (* forward *)
      intros a1 Ha1. exists a1. split.
      { destruct Ha1 as [Ha1_L | Ha1_R].
        - left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - apply Hchild_eq. exact Hw_in.
            - intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx. }
          { exact Heq_a1. }
        - right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - (* w ∈ scc_back_edge ∪ [u] from w ∈ (fun ... ) *)
              destruct (Hback_eq w) as [Hfwd _]. apply Hfwd.
              apply (proj2 (back_edges_done_union_beta u s w)). exact Hw_in.
            - (* minimality: x ∈ scc_back_edge ∪ [u] -> dfn s w <= dfn s x *)
              intros x Hx.
              destruct (Hback_eq x) as [_ Hbwd].
              apply Hw_min.
              apply (proj1 (back_edges_done_union_beta u s x)).
              apply Hbwd. exact Hx. }
          { exact Heq_a1. } }
      { apply Nat.le_refl. }
    - (* backward *)
      intros a2 Ha2. exists a2. split.
      { destruct Ha2 as [Ha2_L | Ha2_R].
        - left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - apply Hchild_eq. exact Hw_in.
            - intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx. }
          { exact Heq_a2. }
        - right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
          exists w. split.
          { unfold min_object_of_subset. split.
            - (* w ∈ (fun ... ) from w ∈ scc_back_edge ∪ [u] *)
              apply (proj1 (back_edges_done_union_beta u s w)).
              destruct (Hback_eq w) as [_ Hbwd]. apply Hbwd. exact Hw_in.
            - (* minimality: x ∈ (fun ... ) -> dfn s w <= dfn s x *)
              intros x Hx.
              apply Hw_min.
              destruct (Hback_eq x) as [Hfwd _]. apply Hfwd.
              apply (proj2 (back_edges_done_union_beta u s x)). exact Hx. }
          { exact Heq_a2. } }
      { apply Nat.le_refl. }
  Qed.

  (** [forset_end_implies_scc_low_valid_v]: explicit two-stage closing lemma.
      When [u]'s forset over all children has finished, [done = dg_step g u]
      and the global/fa conditions needed by [low_forset_inv_to_scc_low_valid]
      are available, so [scc_low_valid_v s u] holds.

      The previously required [stack_fa_neq_self] premise has been removed:
      [back_edges_done_full_eq] now proves equivalence of the back-edge sets
      after adding the singleton [[u]] to both sides, which absorbs the
      special case [v = u] when [fa s u = u] (e.g. a DFS root).

      This lemma makes the transition from the forset invariant to the target
      property explicit, which is especially useful for cross-tree preservation:
      an ancestor [u] only obtains [scc_low_valid_v s u] after its own forset
      ends, not immediately when a child subtree returns. *)
  Lemma forset_end_implies_scc_low_valid_v (u: V) (s: SCCSt):
    low_forset_inv u (fun v => dg_step g u v) s ->
    done_visited (fun v => dg_step g u v) s ->
    (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) ->
    scc_low_valid_v s u.
  Proof.
    intros Hlow Hdv Hfa_g.
    apply (low_forset_inv_to_scc_low_valid u s Hdv Hfa_g Hlow).
  Qed.



  (** [forset_keep_low_forset_inv]: after iterating over all children of [u],
      the corrected forset invariant [P(done)] from
      docs/dev/20260623-tarjan-scc-program-phases.md is preserved and
      implies [low_post u] at the end.

      The forset invariant is
        [P(done, s) := low_forset_inv u done s
                      /\ done_visited done s
                      /\ done ⊆ dg_step g u
                      /\ (forall v, fa s v = u /\ fa s v <> v -> v ∈ done)
                      /\ In u (stack s)
                      /\ stack_dfn_order s
                      /\ dfn_injective s].

      Proof plan:
      - Apply [Hoare_forset] with [P(done)]; properness follows from
        [low_forset_inv_proper] and [done_visited_proper].
      - For each neighbor [a0]:
        * Tree edge ([~ a0 ∈ visited]):
          [set_fa a0 u;; W a0] preserves [P(done)] and establishes
          [fa a0 = u] by [tree_edge_preserves_low_forset_inv_lowlink]; then
          [update_low u (low a0)] extends the invariant to
          [P(done ∪ [a0])] by [update_low_tree_edge] and
          [low_forset_inv_expand_child_done].
        * Non-tree edge ([a0 ∈ visited]):
          - If [a0] is on the stack, it is a back edge; use
            [update_low_back_edge] to get [P(done ∪ [a0])].
          - If [a0] is not on the stack, it is a cross edge; use
            [cross_edge_preserves_low_forset_inv] to extend [done] to
            [done ∪ [a0]] while preserving [low_forset_inv u done].
      - After the loop [done = dg_step g u]; apply
        [forset_end_implies_scc_low_valid_v] to obtain [scc_low_valid_v s u].
        Together with [wf_scc_state s] (inside [low_forset_inv]) this gives
        [low_post u s]. The additional conjuncts [In u (stack s)],
        [stack_dfn_order], and [dfn_injective] are retained explicitly for
        the following [If (low u = dfn u) (pop_scc u)] step.

      Required previous lemmas:
      - [Hoare_forset]
      - [low_forset_inv_proper]
      - [done_visited_proper]
      - [tree_edge_preserves_low_forset_inv_lowlink]
      - [update_low_tree_edge]
      - [update_low_back_edge]
      - [cross_edge_preserves_low_forset_inv]
      - [low_forset_inv_expand_child_done]
      - [forset_end_implies_scc_low_valid_v] *)
  Lemma forset_keep_low_forset_inv (u: V) (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s /\ In u (stack s) /\
                            stack_dfn_order s /\ dfn_injective s)
                     (W x)
                     (fun _ s => low_post x s /\ u ∈ visited s /\ In u (stack s) /\
                                 stack_dfn_order s /\ dfn_injective s)) ->
    Hoare (fun s => low_forset_inv u ∅ s /\ (forall v, fa s v = u -> v = u) /\
                    In u (stack s) /\ stack_dfn_order s /\ dfn_injective s)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => low_post u s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s).
  Proof.
    (* Proof plan: apply [Hoare_forset] with the corrected [P(done)].
       - Tree-edge branch: use [tree_edge_preserves_low_forset_inv_lowlink]
         (which only needs the low-link IH) to keep [low_forset_inv u done]
         and the stack-ordering conjuncts, then [update_low_tree_edge] moves
         the child [a0] into [done].
       - Non-tree-edge branches: back edge uses [update_low_back_edge];
         cross edge uses [cross_edge_preserves_low_forset_inv].
       - After the loop [done = dg_step g u]; apply
         [forset_end_implies_scc_low_valid_v] to get [scc_low_valid_v s u],
         which together with [wf_scc_state] gives [low_post u s].
       - [In u (stack s)], [stack_dfn_order], [dfn_injective] are preserved
         by all branches. *)
  Admitted.

  (** [tarjan_scc_keep_low_valid]: one-vertex main theorem.
      [tarjan_scc g u] transforms [low_pre u] into [low_post u].

      Proof plan: apply [Hoare_fix_logicv] (fixpoint induction) with
        [P(a) := low_pre a] and [Q(a) := low_post a].
      1. In the body:
         - [preloop u] takes the initial [low_pre u] (= [wf_scc_state_pre u])
           to full [wf_scc_state] by [preloop_preserves_wf_scc_state], and
           establishes [low_forset_inv u ∅] by
           [preloop_establishes_low_forset_inv]. [preloop_in_stack] gives
           [In u (stack s)]; [preloop_preserves_stack_dfn_order] and
           [preloop_preserves_dfn_injective] give the two ordering conjuncts.
           [preloop_keeps_fa] gives [fa v = u -> v = u] for all [v].
         - The [forset] over children uses [forset_keep_low_forset_inv] with
           the single induction hypothesis
           [low_pre x /\ u ∈ visited /\ In u (stack) /\ stack_dfn_order /\ dfn_injective
            -> low_post x /\ ...].
           Result: [low_post u s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s].
         - The final [If (low u = dfn u) (pop_scc u)]:
           * If [low u = dfn u], [pop_scc_preserves_wf_scc_state] preserves
             [wf_scc_state]; [pop_scc_keep_scc_low_valid_v] keeps
             [scc_low_valid_v u]. [pop_scc_preserves_stack_dfn_order] and
             [pop_scc_preserves_dfn_injective] keep the ordering conjuncts.
           * If not, the state is unchanged and [low_post u] still holds.
      2. The postcondition is exactly [low_post u].

      Required previous lemmas:
      - [Hoare_fix_logicv]
      - [preloop_preserves_wf_scc_state]
      - [preloop_establishes_low_forset_inv]
      - [preloop_keeps_fa]
      - [preloop_in_stack]
      - [preloop_preserves_stack_dfn_order]
      - [preloop_preserves_dfn_injective]
      - [forset_keep_low_forset_inv]
      - [pop_scc_preserves_wf_scc_state]
      - [pop_scc_keep_scc_low_valid_v]
      - [pop_scc_preserves_stack_dfn_order]
      - [pop_scc_preserves_dfn_injective] *)
  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s /\ original_vvalid g u)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
          (fun _ s => low_post u s).
  Proof.
    (* 证明思路：对 tarjan_scc g u 用 Hoare_fix_logicv 做不动点归纳，
       规格为 low_pre u → low_post u。preloop u 建立 low_forset_inv u ∅、
       In u (stack s)、stack_dfn_order、dfn_injective 与 fa v = u → v = u；
       forset 阶段用新版 forset_keep_low_forset_inv，其单条 W IH 来自不动点归纳假设；
       最后 If (low u = dfn u) (pop_scc u) 保持 low_post。
       关键引理：Hoare_fix_logicv, preloop_establishes_low_forset_inv,
       preloop_keeps_fa, preloop_in_stack, preloop_preserves_stack_dfn_order,
       preloop_preserves_dfn_injective, forset_keep_low_forset_inv,
       pop_scc_preserves_wf_scc_state, pop_scc_keep_scc_low_valid_v,
       pop_scc_preserves_stack_dfn_order, pop_scc_preserves_dfn_injective。 *)
    Admitted.

  (* ================================================================ *)
  (* 13. Global scc_low_valid / scc_is_low                             *)
  (* ================================================================ *)

  (** [tarjan_scc_establishes_and_preserves_scc_low_valid]:
      If [a] is an original vertex, unvisited, and [scc_low_valid] holds for
      all currently visited vertices, then after [tarjan_scc g a],
      [scc_low_valid] holds for all vertices (including new ones in [a]'s
      SCC tree). Also preserves [wf_scc_state].

      Proof plan (two-stage cross-tree argument):
      1. From [tarjan_scc_keep_low_valid] (using [original_vvalid g a]), after
         [tarjan_scc g a] we have [low_post a], in particular
         [scc_low_valid_v s a]. Thus [a] and the vertices in its DFS subtree
         satisfy [scc_low_valid_v].
      2. Stage one — ancestors keep the corrected forset invariant:
         For any already-visited vertex [u] that is an ancestor of [a] in the
         DFS tree, let [parent] be the direct DFS parent of [a] on the path
         from [u] to [a] (so [fa s a = parent]).  The generalized
         [W_preserves_ancestor_inv u parent a done] preserves
         [low_forset_inv u done] together with [In u (stack s)],
         [stack_dfn_order s], and [dfn_injective s] as [a]'s subtree executes.
         At the moment [a]'s subtree returns, [done] has been expanded to
         include [a] (and possibly other processed children of [u]), but it
         need not yet be all of [dg_step g u].
      3. Stage two — ancestors obtain [scc_low_valid_v] only after their own
         forset ends: when [u]'s forset over all children eventually finishes,
         [done = dg_step g u]. The fa-child condition and [done_visited] then
         satisfy the premises of [forset_end_implies_scc_low_valid_v], yielding
         [scc_low_valid_v s u].
      4. Vertices outside [a]'s subtree and not on its ancestor chain are not
         affected by the state changes local to [a]'s subtree, so their
         [scc_low_valid_v] is preserved.
      5. [wf_scc_state] is preserved by the [wf_scc_state] preservation lemmas
         for every primitive operation.

      Required previous lemmas:
      - [tarjan_scc_keep_low_valid]
      - [W_preserves_ancestor_inv]
      - [forset_end_implies_scc_low_valid_v]
      - [wf_scc_state] preservation lemmas *)
  Lemma tarjan_scc_establishes_and_preserves_scc_low_valid (a: V):
    Hoare (fun s => scc_low_valid s /\ wf_scc_state s /\ ~ a ∈ visited s /\ original_vvalid g a)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g a)
          (fun _ s => scc_low_valid s /\ wf_scc_state s).
  Proof.
    (* Proof plan: lift the single-vertex [low_post] property to a global
       [scc_low_valid] preservation property.
       Stage 1: from [tarjan_scc_keep_low_valid] (with [original_vvalid g a])
       we get that [a] and its DFS subtree satisfy [scc_low_valid_v].
       Stage 2: for every ancestor [u] of [a], the generalized
       [W_preserves_ancestor_inv u parent a done] (where [parent] is the
       direct DFS parent of [a]) preserves [low_forset_inv u done],
       [In u (stack s)], [stack_dfn_order s], and [dfn_injective s] while
       [a]'s subtree executes.  When [u]'s own forset eventually finishes,
       [done = dg_step g u], so [forset_end_implies_scc_low_valid_v] yields
       [scc_low_valid_v s u].
       Vertices outside [a]'s subtree and ancestor chain are unchanged.
       [wf_scc_state] is preserved by the primitive preservation lemmas.
       Key lemmas: [tarjan_scc_keep_low_valid], [W_preserves_ancestor_inv],
       [forset_end_implies_scc_low_valid_v], [low_forset_inv_to_scc_low_valid]. *)
    Admitted.

  (** [tarjan_scc_all_scc_low_valid]: global [scc_low_valid] after the full
      Tarjan loop over all vertices.

      Proof plan: [tarjan_scc_all] is a [forset] over all original vertices
      [v] of [If (~ v ∈ visited) (tarjan_scc g v)]. Apply [Hoare_forset]
      with the invariant
        [P(done) := scc_low_valid s /\ wf_scc_state s /\
                    (forall v, original_vvalid g v -> done v -> v ∈ visited s)].
      - Properness follows from the fact that [done] occurs only positively
        in the third conjunct.
      - For each original vertex [a]:
        * If [~ a ∈ visited], use
          [tarjan_scc_establishes_and_preserves_scc_low_valid] to establish
          [scc_low_valid] for the enlarged [visited] set and preserve
          [wf_scc_state]. The third conjunct is extended with [a].
        * If [a ∈ visited], the command is a no-op. All three conjuncts are
          unchanged; in particular the invariant already guarantees
          [scc_low_valid_v s a].
      - After the loop, [done] is the full [original_vvalid g] set, so the
        third conjunct gives [forall v, original_vvalid g v -> v ∈ visited s].
        Together with [scc_low_valid s] this yields [scc_low_valid] for every
        original vertex.

      Required previous lemmas:
      - [Hoare_forset]
      - [tarjan_scc_establishes_and_preserves_scc_low_valid]
      - [wf_scc_state] preservation lemmas *)
  Theorem tarjan_scc_all_scc_low_valid:
    Hoare (fun s: @SCCSt V => wf_scc_state s)
          (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
          (fun _ s => scc_low_valid s /\ (forall v, original_vvalid g v -> v ∈ visited s) /\ wf_scc_state s).
  Proof.
    (* 证明思路：tarjan_scc_all 对 original_vvalid g 中所有顶点做 forset。
       用 Hoare_forset 配合不变式
       P(done) := scc_low_valid s /\ wf_scc_state s /\
                  (forall v, original_vvalid g v -> done v -> v ∈ visited s)。
       对每个顶点 a：若未访问，调用 tarjan_scc_establishes_and_preserves_scc_low_valid；
       若已访问，命令为 skip，不变式不变。循环结束后 done = original_vvalid g，
       故所有原图顶点均已访问，从而 scc_low_valid 对所有原图顶点成立。
       关键引理：Hoare_forset, tarjan_scc_establishes_and_preserves_scc_low_valid。
       原始 .orig 证明含 admit，尚未完全闭合。 *)
    Admitted.

  (** [tarjan_scc_all_scc_is_low]: final theorem — the global Tarjan
      algorithm computes the correct low-link values for every original
      vertex of [g].

      Proof plan:
      1. From [tarjan_scc_all_scc_low_valid] we obtain
         [scc_low_valid s /\ (forall v, original_vvalid g v -> v ∈ visited s) /\ wf_scc_state s].
      2. Since every original vertex is visited, [scc_low_valid s] yields
         [forall v, original_vvalid g v -> scc_low_valid_v s v].
      3. Apply [scc_low_valid_implies_is_low] (or directly
         [scc_low_valid_induction_is_low]) to turn [scc_low_valid_v] into
         [scc_is_low_v] for each original vertex. [dfn_valid g s root] and
         [dfn_inv s] come from [wf_scc_state s].

      Required previous lemmas:
      - [tarjan_scc_all_scc_low_valid]
      - [scc_low_valid_implies_is_low]
      - [tarjan_scc_all_dfn_valid] (from Tarjan_scc_is_dfn)
      - [tarjan_scc_all_keep_dfn_inv] (from Tarjan_scc_is_dfn)
      - [Hoare_conseq_post] / [Hoare_conj] *)
  Theorem tarjan_scc_all_scc_is_low:
    Hoare (fun s: @SCCSt V => wf_scc_state s)
          (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
          (fun _ s => forall v, original_vvalid g v -> scc_is_low_v s v).
  Proof.
    (* 证明思路：最终结论。由 tarjan_scc_all_scc_low_valid 得
       scc_low_valid s /\ (forall v, original_vvalid g v -> v ∈ visited s) /\ wf_scc_state s。
       因所有原图顶点均已访问，scc_low_valid 给出每个原图顶点满足 scc_low_valid_v；
       再由 scc_low_valid_implies_is_low（或直接 scc_low_valid_induction_is_low）
       得到 scc_is_low_v。dfn_valid 与 dfn_inv 由 wf_scc_state 提供。
       关键引理：tarjan_scc_all_scc_low_valid, scc_low_valid_implies_is_low,
       scc_low_valid_induction_is_low, wf_scc_state。 *)
    Admitted.

End IS_LOW.