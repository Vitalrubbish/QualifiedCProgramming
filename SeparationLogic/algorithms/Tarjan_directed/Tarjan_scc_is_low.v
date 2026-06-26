Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.PropExtensionality.
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

  Definition scc_low_reachable (s: @SCCSt V) (x y: V): Prop :=
    exists z,
      dg_reachable (state_to_dfs_tree g s root) x z /\
      (z = y \/ scc_back_edge s z y).

  Definition scc_low_tree (s: @SCCSt V) (x: V): V -> Prop :=
    fun y => scc_low_reachable s x y.

  Definition scc_is_low_v_val (s: @SCCSt V) (u: V) (n: nat): Prop :=
    min_value_of_subset Nat.le (scc_low_tree s u) (dfn s) n.

  (** [scc_is_low_v]: the public specification — [low s u] is exactly
      the minimum of [dfn] over [scc_low_tree s u]. *)
  Definition scc_is_low_v (s: @SCCSt V) (u: V): Prop :=
    scc_is_low_v_val s u (low s u).

  (** [scc_low_valid_v]: equivalent formulation using a nested
      [min_value_of_subset] over tree-children and back-edges.
      Used as an internal stepping-stone in proofs about [pop_scc].
      Connected to [scc_is_low_v] via [scc_low_valid_implies_is_low]. *)
  Definition scc_low_valid_v (s: @SCCSt V) (u: V): Prop :=
    min_value_of_subset Nat.le
      (min_value_of_subset Nat.le (dg_step (state_to_dfs_tree g s root) u) (low s) ∪
       min_value_of_subset Nat.le (scc_back_edge s u ∪ [u]) (dfn s))
      (fun x => x) (low s u).

  Definition scc_is_low (s: @SCCSt V): Prop :=
    forall v, v ∈ visited s -> scc_is_low_v s v.

  (* ================================================================ *)
  (* 2. SCC Low Witness / Bound Lemmas                                *)
  (* ================================================================ *)
(** * Framework overview for the low-link correctness proof

    The file is organized into the following layers:

    1. [SCC-low definitions and induction lemmas]
       ([scc_low_witness], [scc_low_bound], [scc_is_low_induction], ...)
       Define [scc_is_low_v] and show that it implies the global
       [scc_is_low] property.

    2. [Empty-set and low-equals-dfn facts]
       ([preloop_low_eq_dfn], [children_done_empty], [low_eq_dfn_to_min_empty])
       Small algebraic facts used when a vertex has no processed children
       or back edges.

    3. [Primitive-operation invariants]
       ([preloop_establishes_low_forset_inv], [pop_scc_keep_scc_is_low_v],
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

    14. [Convergence to scc_is_low_v]
        ([low_forset_inv_to_scc_is_low], [tree_edge_preserves_low_forset_inv_lowlink],
         [forset_keep_low_forset_inv])
        Closing the loop: after the forset over children, [scc_is_low_v]
        holds.

    15. [Main theorems]
        ([tarjan_scc_keep_low_valid], [tarjan_scc_all_scc_is_low],
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

  Lemma scc_is_low_induction (s: @SCCSt V) (u: V)
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

  Lemma scc_is_low_induction_is_low (s: @SCCSt V) (u: V)
    (Hu: u ∈ visited s)
    (IHu: forall v,
      dg_step (state_to_dfs_tree g s root) u v ->
      scc_is_low_v_val s v (low s v)):
    scc_low_valid_v s u -> scc_is_low_v s u.
  Proof.
    intros Hvalid.
    unfold scc_low_valid_v in Hvalid.
    rewrite scc_is_low_induction in Hvalid; auto.
    apply min_union_iff in Hvalid.
    unfold scc_is_low_v, scc_is_low_v_val.
    rewrite scc_low_tree_decompose; auto.
    rewrite (Sets_union_comm [u] (scc_back_edge s u)).
    rewrite Sets_union_comm.
    exact Hvalid.
  Qed.

  Lemma scc_low_valid_implies_is_low (s: @SCCSt V):
    dfn_valid g s root -> dfn_inv s ->
    (forall v, v ∈ visited s -> scc_low_valid_v s v) -> scc_is_low s.
  Proof.
    intros Hvalid Hinv Hlow.
    destruct Hinv as [Hdfn_lt [Hdfn_zero Hpos]].
    unfold scc_is_low.
    cut (forall n u, u ∈ visited s -> timer s - dfn s u = n -> scc_is_low_v s u).
    { intros H u Hu. apply H with (n := timer s - dfn s u); auto. }
    induction n as [n IH] using (well_founded_induction (Nat.lt_wf 0)).
    intros u Hu Hn.
    apply (scc_is_low_induction_is_low s u Hu).
    - intros v Hson_orig.
      pose proof Hson_orig as Hson_for_step.
      apply tree_step_char in Hson_for_step.
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

  Definition done_visited (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall w, done w -> w ∈ visited s.

  (** [forset_inv]: inequality-based iteration invariant for the forset
      over [u]'s neighbours.  It uses only inequalities, making it
      monotonic under [low u] decreases and stack changes — no frame
      condition needed for recursive calls.
      At the end of forset ([done = dg_step g u]), a bridging lemma
      recovers the exact [scc_is_low_v] property. *)
  Definition forset_inv (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    wf_scc_state s /\
    u ∈ visited s /\
    In u (stack s) /\
    low s u <= dfn s u /\
    (forall v, done v -> dg_step g u v ->
      (fa s v = u -> low s u <= low s v) /\
      (In v (stack s) -> low s u <= dfn s v)).

  (** [low_pre]: pre-condition for [tarjan_scc g u].  It is exactly the
      "pre-state" [wf_scc_state_pre u]: global well-formedness plus [u]
      not yet visited. *)
  Definition low_pre (u: V) (s: @SCCSt V): Prop :=
    wf_scc_state_pre u s.

  (** [low_post]: post-condition for [tarjan_scc g u].  Requires global
      well-formedness and that [u]'s low-link value is correct. *)
  Definition low_post (u: V) (s: @SCCSt V): Prop :=
    wf_scc_state s /\ scc_is_low_v s u.

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

  (** [fa_child_of_u s u]: if [fa s v = u] and [fa s v <> v] then [dg_step g u v]. *)
  Definition fa_child_of_u (u: V) (s: SCCSt): Prop :=
    forall v, fa s v = u /\ fa s v <> v -> dg_step g u v.

  (** [fa_not_done_implies_eq_u u done s]: if [~ done v] and [fa s v = u] then [v = u]. *)
  Definition fa_not_done_implies_eq_u (u: V) (done: V -> Prop) (s: SCCSt): Prop :=
    forall v, ~ done v -> fa s v = u -> v = u.

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

  Lemma pop_scc_keep_scc_is_low_v (u: V):
    Hoare (fun s: @SCCSt V => wf_scc_state s /\ scc_low_valid_v s u /\ low s u = dfn s u)
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
  Lemma pop_scc_preserves_stack_below (a x: V):
    Hoare (fun s => In a (stack s) /\ In x (stack s) /\ dfn s x < dfn s a /\ stack_dfn_order s)
          (pop_scc a)
          (fun _ s => In x (stack s)).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s. subst. simpl.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s0) a) as [popped rest] eqn:Hsplit. simpl.
    destruct H as [Hina [Hinx [Hdfn_lt Horder]]].
    destruct (stack_split_at_partition (stack s0) a popped rest Hsplit)
      as [Hrest_in [Hnot_popped Hcover]].
    destruct (Hcover x Hinx) as [Hx_pop | Hx_rest].
    - (* x ∈ popped: contradiction via stack_dfn_order *)
      destruct (equiv_dec x a) as [Heq | Hneq].
      + (* x = a: contradicts dfn s x < dfn s a *)
        exfalso. rewrite Heq in Hdfn_lt. lia.
      + (* x ≠ a: x appears before a on the stack, so dfn a <= dfn x *)
        destruct (stack_split_at_in_popped_before_a (stack s0) a x
          Hina popped rest Hsplit Hx_pop Hneq) as [l1 [l2 [Heq_stk Ha_in_l2]]].
        assert (Hx_in_stk: In x (stack s0)). {
          rewrite Heq_stk. apply List.in_or_app. right. simpl. left. reflexivity. }
        assert (Ha_in_stk: In a (stack s0)). {
          rewrite Heq_stk. apply List.in_or_app. right. simpl. right. exact Ha_in_l2. }
        pose proof (Horder x a Hx_in_stk Ha_in_stk (ex_intro _ l1 (ex_intro _ l2 (conj Heq_stk Ha_in_l2)))) as Hle.
        lia.
    - exact Hx_rest.
  Qed.

  (** [tarjan_scc_preserves_stack_element]: [tarjan_scc g u] keeps any
      already-visited vertex [x] that is on the stack below [u].  The
      precondition [~ u ∈ visited s] ensures [u] is still unvisited, so
      after [preloop u] we have [dfn s x < dfn s u] and can apply
      [pop_scc_preserves_stack_below] at the end. *)
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

  (* ================================================================ *)
  (* 5.5. Misc helper lemmas (fa_child_of_u, preloop preserves fa etc.) *)
  (* ================================================================ *)

  Lemma low_pre_implies_fa_child_of_u (a: V) (s: @SCCSt V):
    low_pre a s -> fa_child_of_u a s.
  Proof.
    unfold low_pre, wf_scc_state_pre, fa_child_of_u.
    intros [[_ [_ [_ Hfa_vis]]] Hnu_vis] v [Hfa_eq Hfa_ne].
    exfalso. apply Hnu_vis. apply Hfa_vis in Hfa_ne. rewrite Hfa_eq in Hfa_ne. exact Hfa_ne.
  Qed.

  Lemma low_pre_implies_fa_not_done (a: V) (s: @SCCSt V):
    low_pre a s -> fa_not_done_implies_eq_u a ∅ s.
  Proof.
    unfold fa_not_done_implies_eq_u. intros Hpre v Hnv Hfa_eq.
    apply (low_pre_fa_eq_u_implies_eq_u a v s Hpre Hfa_eq).
  Qed.

  Lemma preloop_keep_fa_child_of_u (u: V):
    Hoare (fun s: @SCCSt V => fa_child_of_u u s)
          (preloop u)
          (fun _ s => fa_child_of_u u s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
    unfold fa_child_of_u in H. unfold fa_child_of_u.
    intros v [Hfa_eq Hfa_ne]. apply H. exact (conj Hfa_eq Hfa_ne).
  Qed.

  Lemma preloop_keep_fa_not_done (u: V):
    Hoare (fun s: @SCCSt V => fa_not_done_implies_eq_u u ∅ s)
          (preloop u)
          (fun _ s => fa_not_done_implies_eq_u u ∅ s).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
    unfold fa_not_done_implies_eq_u in H. unfold fa_not_done_implies_eq_u.
    intros v Hnv Hfa_eq. apply H; [exact Hnv | exact Hfa_eq].
  Qed.

  (** Bundled lemma: from [wf_scc_state_pre a], [preloop a] establishes all
      7 conjuncts needed as preconditions for [forset_keep_forset_inv]. *)
  (* ================================================================ *)
  (* 6. Forset Invariant — Inequality-based Iteration Invariant        *)
  (* ================================================================ *)

  (** [preloop_establishes_forset_inv]: after [preloop u], [forset_inv u ∅]
      holds: [wf_scc_state] restored, [u ∈ visited], [In u (stack)],
      [low u = dfn u] (so [low u <= dfn u]), and the [forall] over empty
      [done] is vacuously true. *)
  Lemma preloop_establishes_forset_inv (u: V):
    Hoare (fun s: @SCCSt V => wf_scc_state_pre u s)
          (preloop u)
          (fun _ s => forset_inv u ∅ s).
  Proof.
    unfold forset_inv.
    apply Hoare_conj with
      (Q1 := fun _ s => wf_scc_state s)
      (Q2 := fun _ s => u ∈ visited s /\ In u (stack s) /\ low s u <= dfn s u /\
             (forall v, ∅ v -> dg_step g u v -> (fa s v = u -> low s u <= low s v) /\ (In v (stack s) -> low s u <= dfn s v))).
    { apply (Hoare_conseq_pre _ (fun s => wf_scc_state_pre u s) (preloop u) (fun _ s => wf_scc_state s)).
      intros s H. exact H. apply preloop_preserves_wf_scc_state. }
    apply Hoare_conj with
      (Q1 := fun _ s => u ∈ visited s)
      (Q2 := fun _ s => In u (stack s) /\ low s u <= dfn s u /\
             (forall v, ∅ v -> dg_step g u v -> (fa s v = u -> low s u <= low s v) /\ (In v (stack s) -> low s u <= dfn s v))).
    { apply (Hoare_conseq_pre _ (fun s => True) (preloop u) (fun _ s => u ∈ visited s)).
      intros s _. exact I. apply preloop_self_visited. }
    apply Hoare_conj with
      (Q1 := fun _ s => In u (stack s))
      (Q2 := fun _ s => low s u <= dfn s u /\
             (forall v, ∅ v -> dg_step g u v -> (fa s v = u -> low s u <= low s v) /\ (In v (stack s) -> low s u <= dfn s v))).
    { apply (Hoare_conseq_pre _ (fun s => True) (preloop u) (fun _ s => In u (stack s))).
      intros s _. exact I. apply preloop_in_stack. }
    apply Hoare_conj with
      (Q1 := fun _ s => low s u <= dfn s u)
      (Q2 := fun _ s => forall v, ∅ v -> dg_step g u v -> (fa s v = u -> low s u <= low s v) /\ (In v (stack s) -> low s u <= dfn s v)).
    { apply (Hoare_conseq_post (fun s => wf_scc_state_pre u s) (preloop u) (fun _ s => low s u <= dfn s u) (fun _ s => low s u = dfn s u)).
      intros _ s' Heq. rewrite Heq. apply Nat.le_refl.
      apply (Hoare_conseq_pre _ (fun s => True) (preloop u) (fun _ s => low s u = dfn s u)).
      intros s _. exact I. apply preloop_low_eq_dfn. }
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl. cbn in H2. destruct H2.
  Qed.

  (** Bundled lemma: from [wf_scc_state_pre a] plus global invariants
      [stack_dfn_order] and [dfn_injective], [preloop a] establishes all
      7 conjuncts needed as preconditions for [forset_keep_forset_inv]. *)
  Lemma preloop_establishes_forset_precond (a: V):
    Hoare (fun s: @SCCSt V => wf_scc_state_pre a s /\ stack_dfn_order s /\ dfn_injective s)
          (preloop a)
          (fun _ s => forset_inv a ∅ s /\ In a (stack s) /\
                     stack_dfn_order s /\ dfn_injective s /\
                     low s a = dfn s a /\ fa_child_of_u a s /\
                     fa_not_done_implies_eq_u a ∅ s).
  Proof.
    unfold Hoare. sets_unfold.
    intros s1 ret s2 [Hpre [Horder Inj]] Hprog.
    destruct Hpre as [Hwf Hnv].
    destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]].
    destruct Hinv as [Hlt [Hiff Hpos]].
    (* Use each individual preloop lemma via its unfolded Hoare *)
    assert (Hfinv: forset_inv a ∅ s2). {
      pose proof (preloop_establishes_forset_inv a) as HL.
      unfold Hoare in HL. sets_unfold in HL.
      eapply HL; [exact (conj (conj Hsiv (conj (conj Hlt (conj Hiff Hpos)) (conj Hvalid Hfa_vis))) Hnv) | exact Hprog]. }
    assert (Hinstk: In a (stack s2)). {
      pose proof (preloop_in_stack a) as HL.
      unfold Hoare in HL. sets_unfold in HL.
      eapply HL; [exact I | exact Hprog]. }
    assert (Hlow_eq: low s2 a = dfn s2 a). {
      pose proof (preloop_low_eq_dfn a) as HL.
      unfold Hoare in HL. sets_unfold in HL.
      eapply HL; [exact I | exact Hprog]. }
    assert (Hfa_child: fa_child_of_u a s2). {
      pose proof (preloop_keep_fa_child_of_u a) as HL.
      unfold Hoare in HL. sets_unfold in HL.
      eapply HL; [|exact Hprog].
      apply low_pre_implies_fa_child_of_u.
      exact (conj (conj Hsiv (conj (conj Hlt (conj Hiff Hpos)) (conj Hvalid Hfa_vis))) Hnv). }
    assert (Hfa_not_done: fa_not_done_implies_eq_u a ∅ s2). {
      pose proof (preloop_keep_fa_not_done a) as HL.
      unfold Hoare in HL. sets_unfold in HL.
      eapply HL; [|exact Hprog].
      apply low_pre_implies_fa_not_done.
      exact (conj (conj Hsiv (conj (conj Hlt (conj Hiff Hpos)) (conj Hvalid Hfa_vis))) Hnv). }
    (* stack_dfn_order and dfn_injective from Tarjan_scc_is_dfn lemmas *)
    assert (Horder2: stack_dfn_order s2). {
      pose proof (preloop_preserves_stack_dfn_order a) as HL.
      unfold Hoare in HL. sets_unfold in HL.
      eapply HL; [split; [exact Horder | split; [exact (conj Hlt (conj Hiff Hpos)) | split; [exact Hsiv | exact Hnv]]] | exact Hprog]. }
    assert (Hinj2: dfn_injective s2). {
      pose proof (preloop_preserves_dfn_injective a) as HL.
      unfold Hoare in HL. sets_unfold in HL.
      eapply HL; [split; [exact Inj | split; [exact (conj Hlt (conj Hiff Hpos)) | exact Hnv]] | exact Hprog]. }
    split; [exact Hfinv | split; [exact Hinstk | split; [exact Horder2 | split;
      [exact Hinj2 | split; [exact Hlow_eq | split; [exact Hfa_child | exact Hfa_not_done]]]]]].
  Qed.

  (** [set_fa_preserves_forset_inv]: [set_fa v p] only changes [fa],
      which does not affect the inequalities in [forset_inv].
      Requires [~ v ∈ visited s] (so that [state_to_dfs_tree] is unchanged,
      preserving [dfn_valid]) and [~ done v] (so that the new [fa v = p]
      doesn't create an unprovable obligation when [p = u]).
      In the intended use (tree-edge branch of [process_edge]), [v] is the
      unvisited neighbour being processed, hence both conditions hold. *)
  Lemma set_fa_preserves_forset_inv (u v p: V) (done: V -> Prop):
    Hoare (fun s: @SCCSt V => forset_inv u done s /\ p ∈ visited s /\ ~ v ∈ visited s /\ ~ done v)
          (set_fa v p)
          (fun _ s => forset_inv u done s).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s. subst s. simpl.
    destruct H as [[Hwf [Huvis [Hinu [Hlow_le Hforall]]]] [Hpvis [Hnv_vis Hnv_done]]].
    unfold forset_inv. simpl.
    split; [| split; [| split; [| split]]].
    - (* wf_scc_state: fa changes but all components preserved *)
      destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]].
      unfold wf_scc_state. simpl. split; [| split; [| split]].
      + (* stack_in_visited *) exact Hsiv.
      + (* dfn_inv *) exact Hinv.
      + (* dfn_valid: since v ∉ visited, no tree edge changes *)
        unfold dfn_valid. intros x y Hstep.
        unfold dg_step, original_step in *.
        destruct Hstep as [e [[w [Hw_vis [Hw_fa [Hwfst Hwsnd]]]] [Hfst Hsnd]]].
        simpl in Hw_vis, Hw_fa, Hwfst.
        unfold equiv_decb in Hw_fa, Hwfst.
        destruct (equiv_dec w v) as [Heq_wv | Hneq_wv].
        { rewrite Heq_wv in Hw_vis. exfalso. exact (Hnv_vis Hw_vis). }
        { assert (Hstep_old: dg_step (state_to_dfs_tree g s0 root) x y). {
            unfold dg_step, original_step.
            exists e. split; [| split]; auto.
            exists w. split; [exact Hw_vis |]. split; [exact Hw_fa |]. split; [exact Hwfst | exact Hwsnd]. }
          simpl. apply (Hvalid x y Hstep_old). }
      + (* fa_visited *) intros w Hfa_ne. simpl in *. unfold equiv_decb in *.
        destruct (equiv_dec w v) as [Heq_wv | Hneq_wv].
        { rewrite Heq_wv in *. simpl. exact Hpvis. }
        { simpl. apply Hfa_vis. exact Hfa_ne. }
    - (* u ∈ visited *) exact Huvis.
    - (* In u (stack) *) exact Hinu.
    - (* low s u <= dfn s u *) exact Hlow_le.
    - (* forall: for w ≠ v, fa unchanged; for w = v, done v is false *)
      intros w Hw_done Hdg_w. simpl. unfold equiv_decb.
      destruct (equiv_dec w v) as [Heq_wv | Hneq_wv].
      + assert (Heq_wv' : w = v) by (apply Heq_wv).
        subst w. exfalso. exact (Hnv_done Hw_done).
      + destruct (Hforall w Hw_done Hdg_w) as [Hfa_part Hstack_part]. split; auto.
  Qed.

  (** [get_low_update_low_preserves_forset_inv]: after [update_low u (low v)]
      (tree edge), [forset_inv u done] is preserved and the new inequality
      [low u <= low v] is established for [v]. *)
  Lemma update_low_tree_preserves_forset_inv (u v: V) (done: V -> Prop):
    Hoare (fun s: @SCCSt V => forset_inv u done s /\ In v (stack s) /\
            fa s v = u /\ wf_scc_state s /\ scc_is_low_v s v /\ dfn s u < dfn s v)
          (lv <- get' (fun s => low s v);; update_low u lv)
          (fun _ s => forset_inv u (done ∪ [v]) s).
  Proof.
    intro_state. destruct H as [Hfinv [Hinstk [Hfa_eq [Hwf [His_low Hdfn_lt]]]]].
    eapply Hoare_bind. { eapply Hoare_get'. }
    simpl. intros lv. apply Hoare_conseq_pre with
      (P2 := fun s => forset_inv u done s /\ In v (stack s) /\ wf_scc_state s /\
             scc_is_low_v s v /\ dfn s u < dfn s v /\ low s v = lv).
    { intros s' [Hs'_eq Hlv_eq]. subst s'. split. exact Hfinv. split. exact Hinstk. split. exact Hwf.
      split. exact His_low. split. exact Hdfn_lt. symmetry. exact Hlv_eq. }
    clear Hfinv Hinstk Hwf His_low Hdfn_lt Hfa_eq.
    intro_state. destruct H as [Hfinv' [Hinstk' [Hwf' [His_low' [Hdfn_lt' Hlv_eq]]]]].
    destruct Hfinv' as [Hwf_inv [Huvis [Hinu [Hlow_le Hforall]]]].
    unfold update_low. (* Don't unfold_op! Keep set_low as a sub-program *)
    intro_state. hoare_auto_s.
    { (* n < low s0 u: set_low branch *)
      pose (f := fun (st: SCCSt) => set low (fun low0 x => if x ==b u then low s1 v else low0 x) st).
      apply (Hoare_conseq_post (fun st' => st' = s1) (update' f)
        (fun _ st' => forset_inv u (done ∪ [v]) st') (fun _ st' => st' = f s1)).
      { intros _ st' Heq. subst st'.
        unfold f, forset_inv. simpl.
        split. { exact Hwf_inv. } split. { exact Huvis. } split. { exact Hinu. } split.
        { simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
          apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ H) Hlow_le). }
        { intros w Hor Hdg_w. simpl. unfold equiv_decb. destruct Hor as [Hw_done|Hw_eq].
          { destruct (Hforall w Hw_done Hdg_w) as [Hfa_w Hstk_w].
            destruct (equiv_dec w u) as [Heq_wu|Hneq_wu].
            { rewrite Heq_wu. split.
              { intros _. simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
                apply Nat.le_refl. }
              { intros _. simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
                apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ H) Hlow_le). } }
            { simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity]. split.
              { intro Hfa_w'. apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ H) (Hfa_w Hfa_w')). }
              { intro Hstk_w'. apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ H) (Hstk_w Hstk_w')). } } }
          { sets_unfold in Hw_eq. subst w. split.
            { intro Hfa_vu. simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
              destruct (equiv_dec v u) as [_|_]; simpl; apply Nat.le_refl. }
            { intro Hv_stk. simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
              unfold scc_is_low_v, scc_is_low_v_val in His_low'.
              destruct His_low' as [x [[Hxin Hxmin] Heqx]].
              assert (Hv_tree: scc_low_tree s1 v v). {
                unfold scc_low_tree, scc_low_reachable.
                exists v. split; [apply rt_refl|left;reflexivity]. }
              rewrite <- Heqx. apply Hxmin. exact Hv_tree. } } } } 
           apply Hoare_update'. }
    { (* ~ n < low s0 u: skip branch *)
      destruct H as [Heq_skip Hnlt]. subst s.
      unfold forset_inv.
      refine (conj Hwf_inv (conj Huvis (conj Hinu (conj Hlow_le _)))).
      intros w Hor Hdg_w. destruct Hor as [Hw_done|Hw_eq].
      { apply Hforall; auto. }
      { sets_unfold in Hw_eq. subst w. split.
        { intro Hfa_vu. apply Nat.nlt_ge. exact Hnlt. }
        { intro Hv_stk.
          apply (Nat.le_trans _ _ _ Hlow_le (Nat.lt_le_incl _ _ Hdfn_lt')). } } }
  Qed.

  (** [update_low_back_preserves_forset_inv]: after [update_low u (dfn v)]
      (back edge), [forset_inv u done] is preserved and the new inequality
      [low u <= dfn v] is established. *)
  Lemma update_low_back_preserves_forset_inv (u v: V) (done: V -> Prop):
    Hoare (fun s: @SCCSt V => forset_inv u done s /\ In v (stack s) /\
            dg_step g u v /\ fa s v <> u /\ dfn s v < dfn s u)
          (dv <- get' (fun s => dfn s v);; update_low u dv)
          (fun _ s => forset_inv u (done ∪ [v]) s).
  Proof.
    intro_state. destruct H as [Hfinv [Hinstk [Hdg [Hfa_ne Hdfn_lt]]]].
    eapply Hoare_bind. { eapply Hoare_get'. }
    simpl. intros dv. apply Hoare_conseq_pre with
      (P2 := fun s => forset_inv u done s /\ In v (stack s) /\ dg_step g u v /\
             fa s v <> u /\ dfn s v < dfn s u /\ dfn s v = dv).
    { intros s' [Hs'_eq Hdv_eq]. subst s'. split. exact Hfinv. split. exact Hinstk. split. exact Hdg.
      split. exact Hfa_ne. split. exact Hdfn_lt. symmetry. exact Hdv_eq. }
    clear Hfinv Hinstk Hdg Hfa_ne Hdfn_lt.
    intro_state. destruct H as [Hfinv' [Hinstk' [Hdg' [Hfa_ne' [Hdfn_lt' Hdv_eq]]]]].
    destruct Hfinv' as [Hwf_inv [Huvis [Hinu [Hlow_le Hforall]]]].
    unfold update_low. (* Don't unfold_op! *)
    intro_state. hoare_auto_s.
    {
     (* n < low s0 u: set_low branch — new low u = dfn s1 v *)
      pose (f := fun (st: SCCSt) => set low (fun low0 x => if x ==b u then dfn s1 v else low0 x) st).
      apply (Hoare_conseq_post (fun st' => st' = s1) (update' f)
        (fun _ st' => forset_inv u (done ∪ [v]) st') (fun _ st' => st' = f s1)).
      { intros _ st' Heq. subst st'.
        unfold f, forset_inv. simpl.
        split. { exact Hwf_inv. } split. { exact Huvis. } split. { exact Hinu. } split.
        { simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
          apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ H) Hlow_le). }
        { intros w Hor Hdg_w. simpl. unfold equiv_decb. destruct Hor as [Hw_done|Hw_eq].
          { destruct (Hforall w Hw_done Hdg_w) as [Hfa_w Hstk_w].
            destruct (equiv_dec w u) as [Heq_wu|Hneq_wu].
            { rewrite Heq_wu. split.
              { intros _. simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
                apply Nat.le_refl. }
              { intros _. simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
                apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ H) Hlow_le). } }
            { simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity]. split.
              { intro Hfa_w'. apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ H) (Hfa_w Hfa_w')). }
              { intro Hstk_w'. apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ H) (Hstk_w Hstk_w')). } } }
          { sets_unfold in Hw_eq. subst w. split.
            { intro Hfa_vu. exfalso. apply Hfa_ne'. exact Hfa_vu. }
            { intro Hv_stk. simpl. unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity]. apply Nat.le_refl. } } } }
      apply Hoare_update'. }
    { (* ~ n < low s0 u: skip branch *)
      destruct H as [Heq_skip Hnlt]. subst s.
      unfold forset_inv.
      refine (conj Hwf_inv (conj Huvis (conj Hinu (conj Hlow_le _)))).
      intros w Hor Hdg_w. destruct Hor as [Hw_done|Hw_eq].
      { apply Hforall; auto. }
      { sets_unfold in Hw_eq. subst w. split.
        { intro Hfa_vu. exfalso. apply Hfa_ne'. exact Hfa_vu. }
        { intro Hv_stk. apply Nat.nlt_ge in Hnlt. exact Hnlt. } } }
  Qed.

  (** [cross_edge_preserves_forset_inv]: for a cross edge (visited, not on stack),
      skip preserves [forset_inv] and adds [v] to [done] vacuously. *)
  Lemma cross_edge_preserves_forset_inv (u v: V) (done: V -> Prop):
    Hoare (fun s: @SCCSt V => forset_inv u done s /\ ~ In v (stack s) /\ fa s v <> u)
          (ret tt)
          (fun _ s => forset_inv u (done ∪ [v]) s).
  Proof.
    intro_state. destruct H as [Hfinv [Hnv_stk Hfa_ne]].
    hoare_auto_s. subst s.
    unfold forset_inv.
    destruct Hfinv as [Hwf [Huvis [Hinu [Hlow_le Hforall]]]].
    refine (conj Hwf (conj Huvis (conj Hinu (conj Hlow_le _)))).
    intros w Hor Hdg_w. destruct Hor as [Hw_done | Hw_eq].
    - apply Hforall; auto.
    - split.
      + intro Hfa_v. rewrite <- Hw_eq in Hfa_v. exfalso. apply Hfa_ne. exact Hfa_v.
      + intro Hinstk_v. rewrite <- Hw_eq in Hinstk_v. exfalso. apply Hnv_stk. exact Hinstk_v.
  Qed.

  (** [W_preserves_forset_inv]: recursive call [W x] preserves [forset_inv u done]
      because [low[u]] is unchanged during [W x] (it only modifies [low[x]]
      and descendants). *)
  Lemma W_preserves_forset_inv (u x: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit):
    (forall y, Hoare (fun s => forset_inv u done s /\ u ∈ visited s /\ In u (stack s) /\
                            stack_dfn_order s /\ dfn_injective s)
                     (W y)
                     (fun _ s => forset_inv u done s /\ u ∈ visited s /\ In u (stack s) /\
                                 stack_dfn_order s /\ dfn_injective s)) ->
    Hoare (fun s => forset_inv u done s /\ u ∈ visited s /\ In u (stack s) /\
                    stack_dfn_order s /\ dfn_injective s)
          (W x)
          (fun _ s => forset_inv u done s).
  Proof.
    intros HW. unfold Hoare. sets_unfold.
    intros s1 b s2 Hpre Hprog. destruct Hpre as [Hfinv [Huvis [Hinu [Horder Hinj]]]].
    unfold Hoare in HW. sets_unfold in HW.
    destruct b.
    apply (HW x s1 tt s2); auto.
  Qed.

  (** [forset_inv_proper]: Proper morphism for [forset_inv] w.r.t. set
      equivalence of [done]. *)
  Lemma forset_inv_proper u: Proper (Sets.equiv ==> eq ==> iff) (forset_inv u).
  Proof.
    intros d1 d2 Heq s1 s2 Heqs. subst s2.
    apply Sets_equiv_Sets_included in Heq. destruct Heq as [Hinc12 Hinc21].
    unfold forset_inv.
    split.
    - intros [Hwf [Huvis [Hinu [Hle Hforall]]]].
      refine (conj Hwf (conj Huvis (conj Hinu (conj Hle _)))).
      intros v Hv Hdg. apply Hforall; [apply Hinc21 |]; auto.
    - intros [Hwf [Huvis [Hinu [Hle Hforall]]]].
      refine (conj Hwf (conj Huvis (conj Hinu (conj Hle _)))).
      intros v Hv Hdg. apply Hforall; [apply Hinc12 |]; auto.
  Qed.

  (* ================================================================ *)
  (* 7. Bridging Lemma: forset_inv → scc_is_low_v                   *)
  (* ================================================================ *)

  (** Helper lemma: low[u] ≤ dfn[w] for every w in scc_low_tree s u,
      using the forset_inv inequalities and the children's low-link correctness. *)
  Lemma low_u_le_dfn_scc_low_tree (u: V) (s: SCCSt):
    u ∈ visited s ->
    low s u <= dfn s u ->
    (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) ->
    (forall v, dg_step g u v -> (fa s v = u -> low s u <= low s v) /\ (In v (stack s) -> low s u <= dfn s v)) ->
    (forall v, dg_step (state_to_dfs_tree g s root) u v -> scc_is_low_v s v) ->
    forall w, scc_low_tree s u w -> low s u <= dfn s w.
  Proof.
    intros Huvis Hle_dfnu Hfa_child Hforall IH_child w Hw.
    apply (scc_low_tree_decompose s u Huvis) in Hw.
    sets_unfold in Hw. destruct Hw as [[Heq_wu | Hback] | Hchild].
    - (* w = u *) subst w. exact Hle_dfnu.
    - (* w is a back-edge target of u *)
      destruct Hback as [Hstep [Hinstk Hnotree]].
      destruct (Hforall w Hstep) as [_ Hstk_part].
      apply Hstk_part. exact Hinstk.
    - (* w reachable through tree child v *)
      destruct Hchild as [v [Htree Hvw]].
      apply tree_step_char in Htree as [Hfa_eq [Hfa_ne Hvis_v]].
      assert (Hdg_v: dg_step g u v). {
        apply (Hfa_child v). split; [exact Hfa_eq | exact Hfa_ne]. }
      destruct (Hforall v Hdg_v) as [Hfa_part _].
      specialize (Hfa_part Hfa_eq).
      assert (Htree_uv: dg_step (state_to_dfs_tree g s root) u v).
      { apply tree_step_char_backward; auto. }
      pose proof (IH_child v Htree_uv) as Hchild_low.
      unfold scc_is_low_v, scc_is_low_v_val in Hchild_low.
      destruct Hchild_low as [x [[Hx_in Hx_min] Heqx]].
      assert (Hlow_v_le_dfn_w: low s v <= dfn s w). {
        rewrite <- Heqx. apply Hx_min. unfold scc_low_tree. exact Hvw. }
      exact (Nat.le_trans _ _ _ Hfa_part Hlow_v_le_dfn_w).
  Qed.

  (** [forset_inv_implies_scc_is_low_v]: When [done = dg_step g u]
      (all neighbours processed), the inequality invariant plus the
      child low-link induction hypothesis plus a source-tracking
      disjunction yields [scc_is_low_v s u].
      The source tracking says [low s u] comes from [dfn s u],
      a tree-child's [low], or a back-edge target's [dfn]. *)
  Lemma forset_inv_implies_scc_is_low_v (u: V) (s: SCCSt):
    forset_inv u (dg_step g u) s ->
    done_visited (dg_step g u) s ->
    (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) ->
    (forall v, dg_step (state_to_dfs_tree g s root) u v -> scc_is_low_v s v) ->
    (low s u = dfn s u \/
     (exists v, dg_step g u v /\ fa s v = u /\ fa s v <> v /\ low s u = low s v) \/
     (exists w, dg_step g u w /\ In w (stack s) /\ fa s w <> u /\ low s u = dfn s w)) ->
    scc_is_low_v s u.
  Proof.
    intros Hfinv Hdone_vis Hfa_child IH_child Hsrc.
    destruct Hfinv as [Hwf [Huvis [Hinu [Hlow_le Hforall]]]].
    unfold scc_is_low_v, scc_is_low_v_val.
    (* Use min_nonempty_exists to find the min dfn in scc_low_tree *)
    assert (Htree_nonempty: exists w, scc_low_tree s u w). {
      exists u. unfold scc_low_tree, scc_low_reachable.
      exists u. split; [apply rt_refl | left; reflexivity]. }
    pose proof (min_nonempty_exists (dfn s) (scc_low_tree s u) Htree_nonempty)
      as [m Hmin].
    unfold min_value_of_subset in Hmin.
    destruct Hmin as [w [[Hw_in Hw_min] Heq_m]].
    (* Prove low s u <= dfn s w via the helper lemma *)
    assert (Hlow_le_min: low s u <= dfn s w). {
      apply (low_u_le_dfn_scc_low_tree u s Huvis Hlow_le Hfa_child); auto. }
    (* Prove dfn s w <= low s u using the source tracking *)
    assert (Hmin_le_low: dfn s w <= low s u). {
      destruct Hsrc as [Heq_dfnu | [[v [Hdg_v [Hfa_v [Hfa_ne Heq_lowv]]]] | [v [Hdg_v [Hinstk_v [Hfa_ne Heq_dfnv]]]]]].
      - (* low s u = dfn s u *)
        assert (Hu_in: scc_low_tree s u u). {
          unfold scc_low_tree, scc_low_reachable.
          exists u. split; [apply rt_refl | left; reflexivity]. }
        apply Hw_min in Hu_in. rewrite Heq_dfnu. exact Hu_in.
      - (* low s u = low s v for tree child v *)
        assert (Hvis_v: v ∈ visited s). { apply Hdone_vis. exact Hdg_v. }
        assert (Htree: dg_step (state_to_dfs_tree g s root) u v). {
          apply tree_step_char_backward; auto. }
        pose proof (IH_child v Htree) as Hchild.
        unfold scc_is_low_v, scc_is_low_v_val in Hchild.
        destruct Hchild as [x [[Hx_in Hx_min'] Heqx]].
        assert (Hx_in_u: scc_low_tree s u x). {
          unfold scc_low_tree, scc_low_reachable.
          destruct Hx_in as [z' [Hz_reach Hz_end]].
          exists z'. split; [eapply dg_reachable_trans; [apply dg_reachable_step; exact Htree | exact Hz_reach] | exact Hz_end]. }
        apply Hw_min in Hx_in_u. rewrite Heqx in Hx_in_u. rewrite <- Heq_lowv in Hx_in_u. exact Hx_in_u.
      - (* low s u = dfn s v for back-edge target v *)
        assert (Hv_in: scc_low_tree s u v). {
          unfold scc_low_tree, scc_low_reachable; exists u; split; [apply rt_refl | right];
          unfold scc_back_edge; split; [exact Hdg_v | split; [exact Hinstk_v |
          intro Htree_uv; apply tree_step_char in Htree_uv as [Hfa_uv _];
          exfalso; apply Hfa_ne; exact Hfa_uv]]. }
        apply Hw_min in Hv_in. rewrite Heq_dfnv. exact Hv_in. }
    apply Nat.le_antisymm in Hlow_le_min; [| exact Hmin_le_low].
    rewrite <- Hlow_le_min. rewrite Heq_m.
    unfold min_value_of_subset. exists w. split. split. exact Hw_in. exact Hw_min. exact Heq_m.
  Qed.

  (* ================================================================ *)
  (* 8. Forset Iteration Lemma                                         *)
  (* ================================================================ *)

  Definition low_src (u: V) (done: V -> Prop) (s: SCCSt): Prop :=
    low s u = dfn s u \/
    (exists v, done v /\ dg_step g u v /\ fa s v = u /\ fa s v <> v /\ low s u = low s v) \/
    (exists w, done w /\ dg_step g u w /\ In w (stack s) /\ fa s w <> u /\ low s u = dfn s w).

  Lemma low_src_proper u s: Proper (Sets.equiv ==> iff) (fun done => low_src u done s).
  Proof.
    intros done1 done2 Hequiv. split; intros [Hdfn | [[v [Hv [Hdg [Hfa [Hne Hlow]]]]] | [w [Hw [Hdg [Hinstk [Hne Hlow]]]]]]].
    - left; exact Hdfn.
    - right; left; exists v; split; [apply Hequiv; exact Hv | auto].
    - right; right; exists w; split; [apply Hequiv; exact Hw | auto].
    - left; exact Hdfn.
    - right; left; exists v; split; [apply Hequiv; exact Hv | auto].
    - right; right; exists w; split; [apply Hequiv; exact Hw | auto].
  Qed.

  Lemma set_low_back_preserves_I (u a: V) (done: V -> Prop) (s: SCCSt):
    wf_scc_state s -> u ∈ visited s -> In u (stack s) ->
    (forall v, done v -> dg_step g u v -> (fa s v = u -> low s u <= low s v) /\ (In v (stack s) -> low s u <= dfn s v)) ->
    done_visited done s -> stack_dfn_order s -> dfn_injective s ->
    low_src u done s ->
    (forall v, done v -> dg_step g u v -> fa s v = u -> fa s v <> v -> scc_is_low_v s v) ->
    fa_child_of_u u s -> fa_not_done_implies_eq_u u done s ->
    In a (stack s) -> a ∈ visited s -> dg_step g u a -> fa s a <> u ->
    dfn s a < low s u -> dfn s a < dfn s u ->
    Hoare (fun s' => s' = s) (set_low u (dfn s a)) (fun _ s' =>
      forset_inv u (done ∪ [a]) s' /\
      done_visited (done ∪ [a]) s' /\
      In u (stack s') /\
      stack_dfn_order s' /\
      dfn_injective s' /\
      low_src u (done ∪ [a]) s' /\
      (forall v, (done ∪ [a]) v -> dg_step g u v -> fa s' v = u -> fa s' v <> v -> scc_is_low_v s' v) /\
      fa_child_of_u u s' /\
      fa_not_done_implies_eq_u u (done ∪ [a]) s').
  Proof.
    intros Hwf Huvis Hinu Hforall Hdone_vis Horder Hinj Hsrc Hchild Hfa_child Hfa_not_done
           Hinstk_a Hvis_a Hdg Ha_ne_u Hlt_low Hdfn_lt.
    unfold set_low; intro_state; hoare_auto_s.
    rewrite H in H1. subst s0. rewrite H1; clear H1 s1.
    repeat (unfold forset_inv, done_visited, low_src, fa_child_of_u, fa_not_done_implies_eq_u,
            wf_scc_state, stack_in_visited, dfn_inv, dfn_valid, fa_visited,
            done_visited, stack_dfn_order, dfn_injective, scc_is_low_v, scc_is_low_v_val,
            min_value_of_subset, min_object_of_subset); simpl.
    repeat split.
    (* Goals 1-5: from Hwf *)
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]].
      exact Hsiv. (* 1: stack_in_visited *)
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]].
      exact Hlt. (* 2: dfn s v < timer s for visited v *)
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]].
      apply Hiff. (* 3: dfn s v = 0 <-> ~ v ∈ visited s *)
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]].
      apply Hiff. (* 4: the reverse direction *)
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]].
      exact Hpos. (* 5: 0 < timer s *)
    (* Goal 6: dfn_valid for set_low state. state_to_dfs_tree unchanged by set_low *)
    - intros x y Hstep.
      destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]].
      apply Hvalid.
      (* state_to_dfs_tree(set_low s) = state_to_dfs_tree(s) since set_low only changes low *)
      unfold state_to_dfs_tree in Hstep |- *. simpl in Hstep |- *.
      exact Hstep.
    (* Goal 7: fa_visited *)
    - destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]]. exact Hfa_vis.
    (* Goals 8-9: from hypotheses *)
    - exact Huvis. (* 8: u ∈ visited s *)
    - exact Hinu. (* 9: In u (stack s) *)
    (* Goal 10: (if u==b u then dfn s a else low s u) <= dfn s u = dfn s a <= dfn s u *)
    - unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
      apply (Nat.lt_le_incl _ _ Hdfn_lt).
    (* Goal 11: forall for forset_inv *)
    (* 11a: fa s v = u -> low'[u] <= low'[v] *)
    - rename H into Hor. rename H1 into Hdg_v. destruct Hor as [Hv_done | Hv_eq_a].
      + intros Hfa_eq1.
        unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
        destruct (equiv_dec v u) as [Heq_vu | Hneq_vu].
        * assert (Heq_vu_eq: v = u) by apply Heq_vu. subst v.
          destruct (equiv_dec u u) as [_|_]; apply Nat.le_refl.
        * destruct (Hforall v Hv_done Hdg_v) as [Hfa_part _].
          apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ Hlt_low) (Hfa_part Hfa_eq1)).
      + sets_unfold in Hv_eq_a; subst v.
        unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
        destruct (equiv_dec a u) as [Heq_au | Hneq_au].
        * assert (Heq_au_eq: a = u) by apply Heq_au. subst a.
          intros _; apply Nat.le_refl.
        * intros Hfa_a_u. exfalso. apply Ha_ne_u. exact Hfa_a_u.
    (* 11b: In v (stack s) -> low'[u] <= dfn s v *)
    - rename H into Hor. rename H1 into Hdg_v. destruct Hor as [Hv_done | Hv_eq_a].
      + intros Hinstk1.
        unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
        destruct (equiv_dec v u) as [Heq_vu | Hneq_vu].
        * assert (Heq_vu_eq: v = u) by apply Heq_vu. subst v.
          destruct (equiv_dec u u) as [_|_]; apply (Nat.lt_le_incl _ _ Hdfn_lt).
        * destruct (Hforall v Hv_done Hdg_v) as [_ Hstk_part].
          apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ Hlt_low) (Hstk_part Hinstk1)).
      + sets_unfold in Hv_eq_a; subst v.
        unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
        intros _. apply Nat.le_refl.
    (* Goal 12: done_visited *)
    - intros w Hor. destruct Hor as [Hw_done | Hw_eq_a].
      + apply Hdone_vis. exact Hw_done.
      + sets_unfold in Hw_eq_a; subst w; exact Hvis_a.
    (* Goal 13: In u (stack s) again *)
    - exact Hinu.
    (* Goal 14: stack_dfn_order *)
    - exact Horder.
    (* Goal 15: dfn_injective *)
    - exact Hinj.
    (* Goal 16: low_src with new low[u] = dfn[a] *)
    - right. right. exists a.
      split; [right; reflexivity | split; [exact Hdg | split; [exact Hinstk_a | split; [exact Ha_ne_u |]]]].
      unfold equiv_decb; destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity]; reflexivity.
    (* Goal 17: child IH for scc_is_low_v — unchanged by set_low *)
    - intros v Hor Hdg_v Hfa_v Hfa_ne_v. destruct Hor as [Hv_done | Hv_eq_a].
      + (* v ∈ done, so v ≠ u (since ~ u ∈ done). low and scc_low_tree unchanged *)
        assert (Hv_ne_u: v <> u). { intro Heq; subst v; exfalso; apply Hfa_ne_v; exact Hfa_v. }
        (* low(set_low s) v = low s v since v ≠ u *)
        assert (Hlow_eq: (if v ==b u then dfn s a else low s v) = low s v). {
          unfold equiv_decb; destruct (equiv_dec v u) as [Heq_vu | Hneq_vu]; [exfalso; apply Hv_ne_u; apply Heq_vu | reflexivity]. }
        rewrite Hlow_eq.
        (* scc_low_tree(set_low s) v = scc_low_tree s v: set_low only changes low *)
        unfold scc_low_tree, scc_low_reachable, scc_back_edge; simpl.
        apply Hchild; [exact Hv_done | exact Hdg_v | exact Hfa_v | exact Hfa_ne_v].
      + sets_unfold in Hv_eq_a; subst v; exfalso; apply Ha_ne_u; exact Hfa_v.
    (* Goal 18: fa_child_of_u *)
    - exact Hfa_child.
    (* Goal 19: fa_not_done_implies_eq_u *)
    - intros v Hnv Hfa_v. apply Hfa_not_done; [intro Hv; apply Hnv; left; exact Hv | exact Hfa_v].
  Qed.

  (** [set_low_tree_preserves_I]: tree-edge version of set_low preservation.
      When [low a < low u] after processing tree child [a] (where [fa a = u]),
      [set_low u (low a)] establishes [I (done ∪ [a])].
      Analogous to [set_low_back_preserves_I] but uses the tree-edge witness
      ([fa a = u]) instead of the back-edge witness ([In a (stack)]). *)
  Lemma set_low_tree_preserves_I (u a: V) (done: V -> Prop) (s: SCCSt):
    wf_scc_state s -> u ∈ visited s -> In u (stack s) -> low s u <= dfn s u ->
    (forall v, done v -> dg_step g u v -> (fa s v = u -> low s u <= low s v) /\ (In v (stack s) -> low s u <= dfn s v)) ->
    done_visited done s -> stack_dfn_order s -> dfn_injective s ->
    low_src u done s ->
    (forall v, done v -> dg_step g u v -> fa s v = u -> fa s v <> v -> scc_is_low_v s v) ->
    fa_child_of_u u s -> fa_not_done_implies_eq_u u (done ∪ [a]) s ->
    a ∈ visited s -> dg_step g u a -> fa s a = u -> fa s a <> a ->
    scc_is_low_v s a -> low s a < low s u ->
    Hoare (fun s' => s' = s) (set_low u (low s a)) (fun _ s' =>
      forset_inv u (done ∪ [a]) s' /\
      done_visited (done ∪ [a]) s' /\
      In u (stack s') /\
      stack_dfn_order s' /\
      dfn_injective s' /\
      low_src u (done ∪ [a]) s' /\
      (forall v, (done ∪ [a]) v -> dg_step g u v -> fa s' v = u -> fa s' v <> v -> scc_is_low_v s' v) /\
      fa_child_of_u u s' /\
      fa_not_done_implies_eq_u u (done ∪ [a]) s').
  Proof.
    intros Hwf Huvis Hinu Hlow_le Hforall Hdone_vis Horder Hinj Hsrc Hchild Hfa_child Hfa_not_done
           Hvis_a Hdg Hfa_a Hfa_ne_a Hscc_a Hlt_low.
    unfold set_low; intro_state; hoare_auto_s.
    rewrite H in H1. subst s0. rewrite H1; clear H1 s1.
    repeat (unfold forset_inv, done_visited, low_src, fa_child_of_u, fa_not_done_implies_eq_u,
            wf_scc_state, stack_in_visited, dfn_inv, dfn_valid, fa_visited,
            done_visited, stack_dfn_order, dfn_injective, scc_is_low_v, scc_is_low_v_val,
            min_value_of_subset, min_object_of_subset); simpl.
    repeat split.
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]]. exact Hsiv.
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]]. exact Hlt.
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]]. apply Hiff.
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]]. apply Hiff.
    - destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]]. exact Hpos.
    - intros x y Hstep.
      destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]]. apply Hvalid.
      unfold state_to_dfs_tree in Hstep |- *. simpl in Hstep |- *. exact Hstep.
    - destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]]. exact Hfa_vis.
    - exact Huvis.
    - exact Hinu.
    - unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
      apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ Hlt_low) Hlow_le).
    - rename H into Hor. rename H1 into Hdg_v. destruct Hor as [Hv_done | Hv_eq_a].
      + intros Hfa_eq1.
        unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
        destruct (equiv_dec v u) as [Heq_vu | Hneq_vu].
        * assert (Heq_vu_eq: v = u) by apply Heq_vu. subst v.
          destruct (equiv_dec u u) as [_|_]; apply Nat.le_refl.
        * destruct (Hforall v Hv_done Hdg_v) as [Hfa_part _].
          apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ Hlt_low) (Hfa_part Hfa_eq1)).
      + sets_unfold in Hv_eq_a; subst v.
        unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
        destruct (equiv_dec a u) as [Heq_au | Hneq_au]; intros _; apply Nat.le_refl.
    - rename H into Hor. rename H1 into Hdg_v. destruct Hor as [Hv_done | Hv_eq_a].
      + intros Hinstk1.
        unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
        destruct (equiv_dec v u) as [Heq_vu | Hneq_vu].
        * assert (Heq_vu_eq: v = u) by apply Heq_vu. subst v.
          unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
          apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ Hlt_low) Hlow_le).
        * destruct (Hforall v Hv_done Hdg_v) as [_ Hstk_part].
          apply (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ Hlt_low) (Hstk_part Hinstk1)).
      + sets_unfold in Hv_eq_a; subst v.
        unfold equiv_decb. destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
        intros _.
        unfold scc_is_low_v, scc_is_low_v_val, min_value_of_subset in Hscc_a.
        destruct Hscc_a as [a0 [Hmo_a0 Heq_a0]].
        unfold min_object_of_subset in Hmo_a0.
        destruct Hmo_a0 as [_ Hmo_forall].
        assert (Hineq: dfn s a0 <= dfn s a) by
          (apply Hmo_forall;
           unfold scc_low_tree, scc_low_reachable;
           exists a; split; [apply rt_refl | left; reflexivity]).
        rewrite <- Heq_a0. exact Hineq.
    - intros w Hor. destruct Hor as [Hw_done | Hw_eq_a].
      + apply Hdone_vis. exact Hw_done.
      + sets_unfold in Hw_eq_a; subst w; exact Hvis_a.
    - exact Hinu.
    - exact Horder.
    - exact Hinj.
    - right. left. exists a.
      split; [right; reflexivity | split; [exact Hdg | split; [exact Hfa_a | split; [exact Hfa_ne_a |]]]].
      unfold equiv_decb.
      destruct (equiv_dec u u) as [_|Hc]; [|exfalso;apply Hc;reflexivity].
      destruct (equiv_dec a u) as [Heq_au | Hneq_au]; reflexivity.
    - intros v Hor Hdg_v Hfa_v Hfa_ne_v. destruct Hor as [Hv_done | Hv_eq_a].
      + assert (Hv_ne_u: v <> u). { intro Heq; subst v; exfalso; apply Hfa_ne_v; exact Hfa_v. }
        assert (Hlow_eq: (if v ==b u then low s a else low s v) = low s v). {
          unfold equiv_decb; destruct (equiv_dec v u) as [Heq_vu | Hneq_vu]; [exfalso; apply Hv_ne_u; apply Heq_vu | reflexivity]. }
        rewrite Hlow_eq.
        unfold scc_low_tree, scc_low_reachable, scc_back_edge; simpl.
        apply Hchild; [exact Hv_done | exact Hdg_v | exact Hfa_v | exact Hfa_ne_v].
      + sets_unfold in Hv_eq_a; subst v.
        (* a ≠ u since fa a = u and fa a ≠ a, so set_low doesn't change low a.
           The scc_is_low_v is unchanged by set_low for a. *)
        unfold scc_is_low_v, scc_is_low_v_val, scc_low_tree, scc_low_reachable, scc_back_edge.
        simpl. unfold equiv_decb.
        destruct (equiv_dec a u) as [Heq_au | Hneq_au]; [exfalso; apply Hfa_ne_a; rewrite <- Heq_au in Hfa_a; exact Hfa_a |].
        simpl.
        exact Hscc_a.
    - exact Hfa_child.
    - exact Hfa_not_done.
  Qed.

  (** [W_preserves_ancestor_I]: The recursive call [W a] (tarjan_scc a)
      preserves all components of [I done] that concern the ancestor [u].
      Structural justification (Design Doc §8.4, lines 480-484):
      1. [dfn s u < dfn s a] — tree edge dfn monotonicity
      2. [stack_dfn_order] ensures u is below a on the stack
      3. [pop_scc] within [W a] only pops vertices with dfn ≥ dfn[a] > dfn[u]
      4. Thus [u] stays on the stack, [low[u]] unchanged, [fa_child_of_u u] preserved.
      TODO: formal proof via fixpoint induction on [W]. *)

  Lemma set_fa_preserves_scc_is_low_v (v a u: V) (s: SCCSt):
    v <> a -> ~ a ∈ visited s ->
    scc_is_low_v (set_fa_state s a u) v <-> scc_is_low_v s v.
  Proof.
    intros Hneq Hnv.
    assert (Htree_eq: state_to_dfs_tree g (set_fa_state s a u) root
                    = state_to_dfs_tree g s root). {
      unfold state_to_dfs_tree; simpl.
      f_equal.
      extensionality e. apply propositional_extensionality.
      split.
      - intros [v0 [Hvis [Hfa_ne [Hfst Hsnd]]]].
        exists v0. split; [exact Hvis | ].
        unfold equiv_decb in Hfa_ne, Hfst |- *.
        destruct (equiv_dec v0 a) as [Heq|Hneq'].
        { assert (Heq_eq: v0 = a) by apply Heq.
          rewrite Heq_eq in Hvis.
          exfalso. apply Hnv. exact Hvis. }
        { split; [exact Hfa_ne | split; [exact Hfst | exact Hsnd]]. }
      - intros [v0 [Hvis [Hfa_ne [Hfst Hsnd]]]].
        exists v0. split; [exact Hvis | ].
        unfold equiv_decb in Hfa_ne, Hfst |- *.
        destruct (equiv_dec v0 a) as [Heq|Hneq'].
        { assert (Heq_eq: v0 = a) by apply Heq.
          rewrite Heq_eq in Hvis.
          exfalso. apply Hnv. exact Hvis. }
        { split; [exact Hfa_ne | split; [exact Hfst | exact Hsnd]]. }
    }
    unfold scc_is_low_v, scc_is_low_v_val, scc_low_tree, scc_low_reachable, scc_back_edge.
    simpl.
    rewrite Htree_eq.
    reflexivity.
  Qed.
  
  Lemma set_fa_preserves_I (u a: V) (done: V -> Prop) (s: SCCSt):
    wf_scc_state s -> u ∈ visited s -> In u (stack s) -> low s u <= dfn s u ->
    (forall v, done v -> dg_step g u v -> (fa s v = u -> low s u <= low s v) /\ (In v (stack s) -> low s u <= dfn s v)) ->
    done_visited done s -> stack_dfn_order s -> dfn_injective s ->
    low_src u done s ->
    (forall v, done v -> dg_step g u v -> fa s v = u -> fa s v <> v -> scc_is_low_v s v) ->
    fa_child_of_u u s -> fa_not_done_implies_eq_u u done s ->
    ~ a ∈ visited s -> ~ a ∈ done -> dg_step g u a -> dfn s u < dfn s a ->
    Hoare (fun s' => s' = s) (set_fa a u) (fun _ s' =>
      forset_inv u done s' /\
      done_visited done s' /\
      In u (stack s') /\
      stack_dfn_order s' /\
      dfn_injective s' /\
      low_src u done s' /\
      (forall v, done v -> dg_step g u v -> fa s' v = u -> fa s' v <> v -> scc_is_low_v s' v) /\
      fa_child_of_u u s' /\
      fa_not_done_implies_eq_u u (done ∪ [a]) s').
  Proof.
    intros Hwf Huvis Hinu Hlow_le Hforall Hdone_vis Horder Hinj Hsrc Hchild Hfa_child Hfa_not_done Hnv_vis Hnv_done Hdg Hdfn_lt.
    unfold set_fa; intro_state; hoare_auto_s.
    rewrite H in H1; subst s0; rewrite H1; clear H1 s1.
    repeat (unfold forset_inv, done_visited, low_src, fa_child_of_u, fa_not_done_implies_eq_u,
            wf_scc_state, stack_in_visited, dfn_inv, dfn_valid, fa_visited,
            stack_dfn_order, dfn_injective, scc_is_low_v, scc_is_low_v_val,
            scc_low_tree, scc_low_reachable, scc_back_edge, state_to_dfs_tree,
            min_value_of_subset, min_object_of_subset); simpl.
    repeat split.
    all: try (destruct Hwf as [Hsiv [[Hlt [Hiff Hpos]] [Hvalid Hfa_vis]]]).
    (* stack_in_visited *) exact Hsiv.
    (* dfn < timer *) exact Hlt.
    (* dfn=0 <-> ~visited, dir1 *) apply Hiff.
    (* dfn=0 <-> ~visited, dir2 *) apply Hiff.
    (* 0 < timer *) exact Hpos.
    all: try (exact Huvis || exact Hinu || exact Hlow_le || exact Hdone_vis || exact Horder || exact Hinj || (destruct Hforall with (v := v) as [? ?]; eauto; fail) || (rename H into Hv_done; rename H1 into Hdg_v; unfold equiv_decb; destruct (equiv_dec v a) as [Heq|Hneq]; [assert (Heq_eq: v = a) by apply Heq; subst v; exfalso; apply Hnv_done; exact Hv_done | destruct (Hforall v Hv_done Hdg_v); eauto])).
    (* dfn_valid *) { intros x y Hstep; unfold state_to_dfs_tree in Hstep; simpl in Hstep; destruct Hstep as [e [[v [Hvis [Hfa_ne [Hfst_e Hsnd_e]]]] [Hfst Hsnd]]]; unfold equiv_decb in Hfa_ne; destruct (equiv_dec v a) as [Heq_va | Hneq_va]; [assert (Heq_va_eq: v = a) by apply Heq_va; rewrite Heq_va_eq in Hvis; exfalso; apply Hnv_vis; exact Hvis | apply Hvalid; unfold state_to_dfs_tree; exists e; split; [exists v; split; [exact Hvis | split; [unfold equiv_decb; destruct (equiv_dec v a) as [Heq'|Hneq']; [exfalso; apply Hneq_va; apply Heq' | exact Hfa_ne] | split; [unfold equiv_decb in Hfst_e; destruct (equiv_dec v a) as [Heq''|Hneq'']; [exfalso; apply Hneq_va; apply Heq'' | exact Hfst_e] | exact Hsnd_e]]] | split; [exact Hfst | exact Hsnd]]]. }
    (* fa_visited *) { intros v0 Hfa_ne; unfold equiv_decb in Hfa_ne; destruct (equiv_dec v0 a) as [Heq|Hneq]; [assert (Heq_eq: v0 = a) by apply Heq; subst v0; unfold equiv_decb; destruct (equiv_dec a a) as [_|Hc]; [|exfalso;apply Hc;reflexivity]; exact Huvis | unfold equiv_decb; destruct (equiv_dec v0 a) as [Heq'|Hneq']; [exfalso; apply Hneq; apply Heq' | apply Hfa_vis; exact Hfa_ne]]. }
    (* low_src *) { unfold low_src; unfold low_src in Hsrc; destruct Hsrc as [Heq_dfnu | [[v0 [Hv0 [Hdg_v0 [Hfa_v0 [Hfa_ne_v0 Heq_low]]]]] | [w0 [Hw0 [Hdg_w0 [Hinstk_w0 [Hfa_ne_w0 Heq_dfn]]]]]]]; [left; exact Heq_dfnu | right; left; exists v0; split; [exact Hv0 | split; [exact Hdg_v0 | unfold equiv_decb; destruct (equiv_dec v0 a) as [Heq_va | Hneq_va]; [exfalso; apply Hnv_done; rewrite <- Heq_va; exact Hv0 | split; [exact Hfa_v0 | split; [exact Hfa_ne_v0 | exact Heq_low]]]]] | right; right; exists w0; split; [exact Hw0 | split; [exact Hdg_w0 | split; [exact Hinstk_w0 | unfold equiv_decb; destruct (equiv_dec w0 a) as [Heq_wa | Hneq_wa]; [exfalso; apply Hnv_done; rewrite <- Heq_wa; exact Hw0 | split; [exact Hfa_ne_w0 | exact Heq_dfn]]]]]]. }
    (* child IH *)
    { intros v0 Hv_done Hdg_v0 Hfa_v0 Hfa_ne_v0;
      unfold equiv_decb in Hfa_v0, Hfa_ne_v0;
      destruct (equiv_dec v0 a) as [Heq|Hneq];
      [ assert (Heq_eq: v0 = a) by apply Heq; subst v0; exfalso; apply Hnv_done; exact Hv_done
      | apply (proj2 (set_fa_preserves_scc_is_low_v v0 a u s Hneq Hnv_vis));
        apply Hchild; [exact Hv_done | exact Hdg_v0 | exact Hfa_v0 | exact Hfa_ne_v0] ]. }
    (* fa_child_of_u *) { intros v0 [Hfa_eq Hfa_ne]; unfold equiv_decb; destruct (equiv_dec v0 a) as [Heq|Hneq]; [assert (Heq_eq: v0 = a) by apply Heq; subst v0; exact Hdg | unfold equiv_decb in Hfa_eq, Hfa_ne; destruct (equiv_dec v0 a) as [Heq'|Hneq']; [exfalso; apply Hneq; apply Heq' | apply Hfa_child; split; [exact Hfa_eq | exact Hfa_ne]]]. }
    (* fa_not_done *) { intros v0 Hnv Hfa_v0; unfold equiv_decb in Hfa_v0; destruct (equiv_dec v0 a) as [Heq|Hneq]; [assert (Heq_eq: v0 = a) by apply Heq; subst v0; exfalso; apply Hnv; right; reflexivity | apply Hfa_not_done; [intro Hv_done; apply Hnv; left; exact Hv_done | exact Hfa_v0]]. }
  Qed.

  (** [set_fa_preserves_scc_is_low_v]: For [v ≠ a] with [a ∉ visited],
      [scc_is_low_v] unchanged by [set_fa a u]. Uses [set_fa_preserves_tree_edges]
      and induction on [dg_reachable]. *)

  (** [W_preserves_ancestor_I]: The recursive call [W a] (tarjan_scc a)
      preserves the invariants about the ancestor [u] and [done] set.
      The proof is trivial given a strong enough induction hypothesis
      [HW_frame] — which is the "ancestor-frame preservation" property
      itself, parameterized over ancestor and done-set.
      [HW_frame] is discharged by [Hoare_fix_logicv_conj] in the main
      theorem [tarjan_scc_keep_low_valid], which proves simultaneously
      [low_pre → low_post] and the frame-preservation property. *)
  Lemma W_preserves_ancestor_I (u a: V) (done: V -> Prop) (s: SCCSt)
        (W: V -> program SCCSt unit):
    (forall v (anc: V) (d: V -> Prop) (s0: SCCSt),
       forset_inv anc d s0 -> In anc (stack s0) -> stack_dfn_order s0 ->
       dfn_injective s0 -> low_src anc d s0 ->
       (forall w, d w -> dg_step g anc w -> fa s0 w = anc -> fa s0 w <> w ->
        scc_is_low_v s0 w) ->
       fa_child_of_u anc s0 -> fa_not_done_implies_eq_u anc (d ∪ [v]) s0 ->
       done_visited d s0 -> dfn s0 anc < timer s0 -> ~ v ∈ visited s0 ->
       Hoare (fun s' => s' = s0) (W v) (fun _ s' =>
         forset_inv anc d s' /\ In anc (stack s') /\ stack_dfn_order s' /\
         dfn_injective s' /\ low_src anc d s' /\
         (forall w, d w -> dg_step g anc w -> fa s' w = anc -> fa s' w <> w ->
          scc_is_low_v s' w) /\
         fa_child_of_u anc s' /\ fa_not_done_implies_eq_u anc (d ∪ [v]) s' /\
         done_visited d s' /\ low_post v s' /\ v ∈ visited s' /\
         (fa s0 v = anc -> fa s' v = anc))) ->
    forset_inv u done s -> In u (stack s) -> stack_dfn_order s -> dfn_injective s ->
    low_src u done s ->
    (forall v, done v -> dg_step g u v -> fa s v = u -> fa s v <> v -> scc_is_low_v s v) ->
    fa_child_of_u u s -> fa_not_done_implies_eq_u u (done ∪ [a]) s ->
    done_visited done s -> dfn s u < timer s ->
    ~ a ∈ visited s -> dg_step g u a ->
    Hoare (fun s' => s' = s) (W a) (fun _ s' =>
      forset_inv u done s' /\ In u (stack s') /\ stack_dfn_order s' /\
      dfn_injective s' /\ low_src u done s' /\
      (forall v, done v -> dg_step g u v -> fa s' v = u -> fa s' v <> v -> scc_is_low_v s' v) /\
      fa_child_of_u u s' /\ fa_not_done_implies_eq_u u (done ∪ [a]) s' /\ done_visited done s' /\
      low_post a s' /\ a ∈ visited s' /\ (fa s a = u -> fa s' a = u)).
  Proof.
    intros HW_frame Hfinv Hinstk Horder Hinj Hsrc Hchild
           Hfa_child Hfa_not_done Hdone_vis Hdfn_lt Hnv_vis Hdg.
    eapply HW_frame; eauto.
  Qed.

  (** [tree_edge_preserves_I]: tree-edge branch composes [set_fa],
      [W a] (via [W_preserves_ancestor_I]), and [update_low]
      to establish [I (done ∪ [a])]. *)
  Lemma tree_edge_preserves_I (u a: V) (done: V -> Prop) (s: SCCSt)
        (W: V -> program SCCSt unit):
    (forall v (anc: V) (d: V -> Prop) (s0: SCCSt),
       forset_inv anc d s0 -> In anc (stack s0) -> stack_dfn_order s0 ->
       dfn_injective s0 -> low_src anc d s0 ->
       (forall w, d w -> dg_step g anc w -> fa s0 w = anc -> fa s0 w <> w ->
        scc_is_low_v s0 w) ->
       fa_child_of_u anc s0 -> fa_not_done_implies_eq_u anc (d ∪ [v]) s0 ->
       done_visited d s0 -> dfn s0 anc < timer s0 -> ~ v ∈ visited s0 ->
       Hoare (fun s' => s' = s0) (W v) (fun _ s' =>
         forset_inv anc d s' /\ In anc (stack s') /\ stack_dfn_order s' /\
         dfn_injective s' /\ low_src anc d s' /\
         (forall w, d w -> dg_step g anc w -> fa s' w = anc -> fa s' w <> w ->
          scc_is_low_v s' w) /\
         fa_child_of_u anc s' /\ fa_not_done_implies_eq_u anc (d ∪ [v]) s' /\
         done_visited d s' /\ low_post v s' /\ v ∈ visited s' /\
         (fa s0 v = anc -> fa s' v = anc))) ->
    wf_scc_state s -> u ∈ visited s -> In u (stack s) -> low s u <= dfn s u ->
    (forall v, done v -> dg_step g u v -> (fa s v = u -> low s u <= low s v) /\ (In v (stack s) -> low s u <= dfn s v)) ->
    done_visited done s -> stack_dfn_order s -> dfn_injective s ->
    low_src u done s ->
    (forall v, done v -> dg_step g u v -> fa s v = u -> fa s v <> v -> scc_is_low_v s v) ->
    fa_child_of_u u s -> fa_not_done_implies_eq_u u done s ->
    ~ a ∈ visited s -> ~ a ∈ done ->
    dg_step g u a -> dfn s u < timer s ->
    Hoare (fun s' => s' = s) (set_fa a u;; W a;; lv <- get' (fun s' => low s' a);; update_low u lv)
          (fun _ s' => forset_inv u (done ∪ [a]) s' /\
                      done_visited (done ∪ [a]) s' /\
                      In u (stack s') /\
                      stack_dfn_order s' /\
                      dfn_injective s' /\
                      low_src u (done ∪ [a]) s' /\
                      (forall v, (done ∪ [a]) v -> dg_step g u v -> fa s' v = u -> fa s' v <> v -> scc_is_low_v s' v) /\
                      fa_child_of_u u s' /\
                      fa_not_done_implies_eq_u u (done ∪ [a]) s').
  Proof.
    intros HW_frame Hwf Huvis Hinu Hlow_le Hforall Hdone_vis Horder Hinj
           Hsrc Hchild Hfa_child Hfa_not_done Hnv_vis Hnv_done Hdg Hdfn_lt_timer.
    unfold set_fa. intro_state. hoare_auto_s. subst s0.
    assert (Hfa_pre: fa (set_fa_state s a u) a = u).
    { unfold set_fa_state. simpl. unfold equiv_decb. destruct (equiv_dec a a); [reflexivity|congruence]. }
    eapply Hoare_bind.
    { apply (W_preserves_ancestor_I u a done (set_fa_state s a u) W HW_frame).
      - (* forset_inv *) destruct Hwf as [Hsiv [Hdfn [Hvalid Hfa]]].
        assert (Hwf_set_fa: wf_scc_state (set_fa_state s a u)). {
          unfold wf_scc_state. simpl. split. exact Hsiv. split. exact Hdfn. split.
          { intros x y Hstep. unfold state_to_dfs_tree in Hstep |- *. simpl in Hstep |- *.
            destruct Hstep as [e [[v' [Hvis' [Hfa_ne' [Hfst_e' Hsnd_e']]]] [Hfst' Hsnd']]].
            unfold equiv_decb in Hfa_ne', Hfst_e'.
            destruct (equiv_dec v' a) as [Heq_va|Hneq_va].
            { assert (Heq_va_eq: v' = a) by apply Heq_va. rewrite Heq_va_eq in Hvis'. exfalso. apply Hnv_vis. exact Hvis'. }
            { apply Hvalid. unfold state_to_dfs_tree. exists e. split.
              - exists v'. split; [exact Hvis'|split;[unfold equiv_decb;destruct (equiv_dec v' a) as [Heq'|Hneq'];[exfalso;apply Hneq_va;exact Heq'|exact Hfa_ne']|split;
                [destruct (equiv_dec v' a) as [Heq''|Hneq''];[exfalso;apply Hneq_va;exact Heq''|exact Hfst_e']|exact Hsnd_e']]].
              - split; [exact Hfst'|exact Hsnd']. } }
          { unfold fa_visited. simpl. intros v0. unfold equiv_decb. destruct (equiv_dec v0 a) as [Heq|Hneq].
            { assert (Heq_eq: v0 = a) by apply Heq. subst v0. destruct (equiv_dec a a) as [_|c];[|congruence]. intros _. exact Huvis. }
            { destruct (equiv_dec v0 a) as [Heq'|Hneq'];[exfalso;apply Hneq;exact Heq'|]. intros Hfa_ne. apply (Hfa v0). exact Hfa_ne. } } }
        unfold forset_inv.
        split; [exact Hwf_set_fa|split; [exact Huvis|split; [exact Hinu|split; [exact Hlow_le|]]]].
        simpl. intros v2 Hv2_done Hdg_v2. unfold equiv_decb. destruct (equiv_dec v2 a) as [Heq|Hneq].
        { assert (Heq_eq: v2 = a) by apply Heq. subst v2. exfalso. apply Hnv_done. exact Hv2_done. }
        apply Hforall; auto.
      - simpl. exact Hinu.
      - simpl. exact Horder.
      - simpl. exact Hinj.
      - (* low_src *) unfold low_src. simpl. unfold low_src in Hsrc.
        destruct Hsrc as [Heq_dfnu|[[v [Hv [Hdg_v [Hfa_v [Hfa_ne_v Heq_low]]]]]|[w [Hw [Hdg_w [Hinstk_w [Hfa_ne_w Heq_dfn]]]]]]].
        left. exact Heq_dfnu.
        right. left. exists v. simpl. unfold equiv_decb. destruct (equiv_dec v a) as [Heq_va|Hneq_va];[exfalso;apply Hnv_done;rewrite<-Heq_va;exact Hv|]. split;[exact Hv|split;[exact Hdg_v|split;[exact Hfa_v|split;[exact Hfa_ne_v|exact Heq_low]]]].
        right. right. exists w. simpl. unfold equiv_decb. destruct (equiv_dec w a) as [Heq_wa|Hneq_wa];[exfalso;apply Hnv_done;rewrite<-Heq_wa;exact Hw|]. split;[exact Hw|split;[exact Hdg_w|split;[exact Hinstk_w|split;[exact Hfa_ne_w|exact Heq_dfn]]]].
      - (* child IH *) intros v Hv_done Hdg_v Hfa_v Hfa_ne_v. simpl in Hfa_v, Hfa_ne_v. unfold equiv_decb in Hfa_v, Hfa_ne_v.
        destruct (equiv_dec v a) as [Heq|Hneq];[assert (Heq_eq: v = a) by apply Heq; subst v; exfalso; apply Hnv_done; exact Hv_done|].
        apply (proj2 (set_fa_preserves_scc_is_low_v v a u s Hneq Hnv_vis)). apply Hchild; auto.
      - (* fa_child_of_u *) unfold fa_child_of_u. simpl. intros v0 [Hfa_eq Hfa_ne]. unfold equiv_decb in Hfa_eq, Hfa_ne.
        destruct (equiv_dec v0 a) as [Heq|Hneq];[assert (Heq_eq: v0 = a) by apply Heq; subst v0; simpl in Hfa_eq; unfold equiv_decb in Hfa_eq;
          destruct (equiv_dec a a) as [_|c];[|congruence]; exact Hdg|].
        simpl in Hfa_eq. unfold equiv_decb in Hfa_eq. destruct (equiv_dec v0 a) as [Heq'|Hneq'];[exfalso;apply Hneq;exact Heq'|].
        apply Hfa_child. exact (conj Hfa_eq Hfa_ne).
      - (* fa_not_done *) unfold fa_not_done_implies_eq_u. simpl. intros v0 Hnv Hfa_v0. unfold equiv_decb in Hfa_v0.
        destruct (equiv_dec v0 a) as [Heq|Hneq];[assert (Heq_eq: v0 = a) by apply Heq; subst v0; exfalso; apply Hnv; right; reflexivity|].
        simpl. unfold equiv_decb. destruct (equiv_dec v0 a) as [Heq'|Hneq'];[exfalso;apply Hneq;exact Heq'|].
        apply Hfa_not_done;[intro Hv_done;apply Hnv;left;exact Hv_done|exact Hfa_v0].
      - unfold done_visited. simpl. exact Hdone_vis.
      - simpl. exact Hdfn_lt_timer.
      - simpl. exact Hnv_vis.
      - exact Hdg. }
    intros []. intro_state.
    destruct H as (Hfinv'' & Hinstk'' & Horder'' & Hinj'' & Hsrc'' & Hchild'' & Hfa_child'' & Hfa_not_done'' & Hdone_vis'' & Hlow_post_a & Hvis_a & Hfa_a_post).
    destruct Hlow_post_a as (Hwf'' & Hscc_a).
    eapply Hoare_bind. { eapply Hoare_get'. }
    simpl. intro lv.
    unfold update_low. intro_state. hoare_auto_s.
    - rename H into Hlt_low. destruct Hlt_low as [Heq_s1 Hlv_eq]. subst s1.
      rewrite Hlv_eq in H1. rewrite Hlv_eq.
      assert (Hfa_eq: fa s0 a = u). { apply Hfa_a_post. exact Hfa_pre. }
      apply (set_low_tree_preserves_I u a done s0).
      + exact Hwf''.
      + destruct Hfinv'' as [_ [Huvis'' _]]. exact Huvis''.
      + exact Hinstk''.
      + destruct Hfinv'' as [_ [_ [_ [Hlow'' _]]]]. exact Hlow''.
      + destruct Hfinv'' as [_ [_ [_ [_ Hforall'']]]]. exact Hforall''.
      + exact Hdone_vis''.
      + exact Horder''.
      + exact Hinj''.
      + exact Hsrc''.
      + exact Hchild''.
      + exact Hfa_child''.
      + exact Hfa_not_done''.
      + exact Hvis_a.
      + exact Hdg.
      + exact Hfa_eq.
      + (* fa s0 a <> a *) rewrite Hfa_eq. intro Heq. apply Hnv_vis. rewrite <- Heq. exact Huvis.
      + exact Hscc_a.
      + exact H1.
    - destruct H as [Heq_s1 Hlv_eq]. destruct H1 as [Heq_s2b Hnlt']. subst s1. subst s2.
      split. { unfold forset_inv. split. exact Hwf''. split. { destruct Hfinv'' as [_ [Huvis'' _]]. exact Huvis''. }
        split. exact Hinstk''. split. { destruct Hfinv'' as [_ [_ [_ [Hlow_le'' _]]]]. exact Hlow_le''. }
        { intros w Hor Hdg_w. destruct Hor as [Hw_done|Hw_eq_a].
          { destruct Hfinv'' as [_ [_ [_ [_ Hforall'']]]]. apply Hforall''; auto. }
          sets_unfold in Hw_eq_a. subst w. split.
          { intro Hfa_au. apply Nat.nlt_ge. rewrite <- Hlv_eq. exact Hnlt'. }
          { intro Hinstk_a. apply Nat.nlt_ge in Hnlt'. rewrite Hlv_eq in Hnlt'.
            apply (Nat.le_trans _ _ _ Hnlt').
            unfold scc_is_low_v, scc_is_low_v_val, min_value_of_subset in Hscc_a.
            destruct Hscc_a as [x [[Hxin Hxmin] Heqx]].
            assert (Ha_tree: scc_low_tree s0 a a). {
              unfold scc_low_tree, scc_low_reachable. exists a. split; [apply rt_refl|left;reflexivity]. }
            rewrite <- Heqx. apply (Hxmin _ Ha_tree). } } }
      split. { intros w Hor. destruct Hor as [Hw_done|Hw_eq_a]. apply Hdone_vis''; exact Hw_done.
        sets_unfold in Hw_eq_a. subst w. exact Hvis_a. }
      split. exact Hinstk''. split. exact Horder''. split. exact Hinj''.
      split. { unfold low_src. unfold low_src in Hsrc''.
        destruct Hsrc'' as [Heq_dfnu|[[v [Hv [Hdg_v [Hfa_v [Hfa_ne_v Heq_low]]]]]|[w [Hw [Hdg_w [Hinstk_w [Hfa_ne_w Heq_dfn]]]]]]].
        left. exact Heq_dfnu. right. left. exists v. split;[left;exact Hv|auto].
        right. right. exists w. split;[left;exact Hw|auto]. }
      split. { intros v Hor Hdg_v Hfa_v Hfa_ne_v. destruct Hor as [Hv_done|Hv_eq_a].
        apply Hchild''; [exact Hv_done|exact Hdg_v|exact Hfa_v|exact Hfa_ne_v].
        sets_unfold in Hv_eq_a. subst v. exact Hscc_a. }
      split. exact Hfa_child''. exact Hfa_not_done''.
  Qed.

  Lemma forset_keep_forset_inv (u: V) (W: V -> program (@SCCSt V) unit):
    (forall v (anc: V) (d: V -> Prop) (s0: SCCSt),
       forset_inv anc d s0 -> In anc (stack s0) -> stack_dfn_order s0 ->
       dfn_injective s0 -> low_src anc d s0 ->
       (forall w, d w -> dg_step g anc w -> fa s0 w = anc -> fa s0 w <> w ->
        scc_is_low_v s0 w) ->
       fa_child_of_u anc s0 -> fa_not_done_implies_eq_u anc (d ∪ [v]) s0 ->
       done_visited d s0 -> dfn s0 anc < timer s0 -> ~ v ∈ visited s0 ->
       Hoare (fun s' => s' = s0) (W v) (fun _ s' =>
         forset_inv anc d s' /\ In anc (stack s') /\ stack_dfn_order s' /\
         dfn_injective s' /\ low_src anc d s' /\
         (forall w, d w -> dg_step g anc w -> fa s' w = anc -> fa s' w <> w ->
          scc_is_low_v s' w) /\
         fa_child_of_u anc s' /\ fa_not_done_implies_eq_u anc (d ∪ [v]) s' /\
         done_visited d s' /\ low_post v s' /\ v ∈ visited s' /\
         (fa s0 v = anc -> fa s' v = anc))) ->
    Hoare (fun s => forset_inv u ∅ s /\ In u (stack s) /\
                    stack_dfn_order s /\ dfn_injective s /\
                    low s u = dfn s u /\ fa_child_of_u u s /\
                    fa_not_done_implies_eq_u u ∅ s)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => low_post u s /\ In u (stack s) /\ stack_dfn_order s /\ dfn_injective s).
  Proof.
    intros HW_frame.
    set (S := fun v => dg_step g u v).
    set (I := fun (done: V -> Prop) (s: SCCSt) =>
      forset_inv u done s /\
      done_visited done s /\
      In u (stack s) /\
      stack_dfn_order s /\
      dfn_injective s /\
      low_src u done s /\
      (forall v, done v -> dg_step g u v -> fa s v = u -> fa s v <> v -> scc_is_low_v s v) /\
      fa_child_of_u u s /\
      fa_not_done_implies_eq_u u done s).
    assert (ProperI: Proper (Sets.equiv ==> eq ==> iff) I). {
      unfold I. intros done1 done2 Hequiv s1 s2 Heqs. subst s2.
      pose proof (forset_inv_proper u done1 done2 Hequiv s1 s1 eq_refl) as Hfinv_equiv.
      destruct Hfinv_equiv as [Hfinv12 Hfinv21].
      pose proof (low_src_proper u s1 done1 done2 Hequiv) as Hsrc_equiv.
      destruct Hsrc_equiv as [Hsrc12 Hsrc21].
      split; intros [Hfinv [Hdonevis [Hinstk [Horder [Hinj [Hsrc [Hchild [Hfa_child Hfa_not_done]]]]]]]].
      - split; [apply Hfinv12; exact Hfinv | split; [intros v Hv; apply Hdonevis; apply Hequiv; exact Hv | split; [exact Hinstk | split; [exact Horder | split; [exact Hinj | split; [apply Hsrc12; exact Hsrc | split; [| split]]]]]]].
        + intros v Hv Hdg Hfa Hfa_ne. apply Hchild; [apply Hequiv; exact Hv | exact Hdg | exact Hfa | exact Hfa_ne].
        + exact Hfa_child.
        + unfold fa_not_done_implies_eq_u. intros v Hnv Hfa_eq.
          apply Hfa_not_done; [intro Hv; apply Hnv; apply Hequiv; exact Hv | exact Hfa_eq].
      - split; [apply Hfinv21; exact Hfinv | split; [intros v Hv; apply Hdonevis; apply Hequiv; exact Hv | split; [exact Hinstk | split; [exact Horder | split; [exact Hinj | split; [apply Hsrc21; exact Hsrc | split; [| split]]]]]]].
        + intros v Hv Hdg Hfa Hfa_ne. apply Hchild; [apply Hequiv; exact Hv | exact Hdg | exact Hfa | exact Hfa_ne].
        + exact Hfa_child.
        + unfold fa_not_done_implies_eq_u. intros v Hnv Hfa_eq.
          apply Hfa_not_done; [intro Hv; apply Hnv; apply Hequiv; exact Hv | exact Hfa_eq]. }
    (* Bridge: Hoare_forset gives Hoare (I ∅) ... (I S); we need lemma's pre/post *)
    apply Hoare_conseq with (P2 := I ∅) (Q2 := fun _ s => I S s).
    - (* lemma_pre ⊆ I ∅ *)
      intros s [Hfinv [Hinstk [Horder [Hinj [Hlow_eq [Hfa_child Hfa_not_done]]]]]].
      unfold I. split. exact Hfinv. split. { intros v Hv. destruct Hv. }
      split. exact Hinstk. split. exact Horder. split. exact Hinj.
      split. { unfold low_src. left. exact Hlow_eq. }
      split. { intros v Hv. destruct Hv. }
      split. exact Hfa_child.
      exact Hfa_not_done.
    - (* I S ⊆ lemma_post: S = dg_step g u *)
      intros _ s [Hfinv [Hdone_vis [Hinstk [Horder [Hinj [Hsrc [Hchild [Hfa_child Hfa_not_done]]]]]]]].
      split. { unfold low_post.
        destruct Hfinv as [Hwf [Huvis [Hinu_stk [Hlow_le Hforall]]]].
        split. exact Hwf.
        apply (forset_inv_implies_scc_is_low_v u s
          (conj Hwf (conj Huvis (conj Hinu_stk (conj Hlow_le Hforall))))).
        - exact Hdone_vis.
        - exact Hfa_child.
        - (* child IH *) intros v Htree.
          apply tree_step_char in Htree as [Hfa_eq [Hfa_ne Hvis_v]].
          apply Hchild.
          { apply Hfa_child. exact (conj Hfa_eq Hfa_ne). }
          { apply Hfa_child. exact (conj Hfa_eq Hfa_ne). }
          { exact Hfa_eq. }
          { exact Hfa_ne. }
        - unfold low_src in Hsrc. destruct Hsrc as [Hdfn | [[v [Hv [Hdg [Hfa [Hne Hlow]]]]] | [w [Hw [Hdg [Hinstk_w [Hne Hlow]]]]]]].
          + left; exact Hdfn.
          + right; left; exists v; auto.
          + right; right; exists w; auto. }
      split. exact Hinstk. split. exact Horder. exact Hinj.
    - apply (Hoare_forset I S (process_edge u W) ProperI).
      intros done a Hdone_sub Ha_S Ha_not_done.
      unfold process_edge, if_else.
      intro_state.
      destruct H as [Hfinv [Hdone_vis [Hinstk [Horder [Hinj [Hsrc [Hchild [Hfa_child Hfa_not_done]]]]]]]].
      destruct Hfinv as [Hwf [Huvis [Hinu_stk [Hlow_le Hforall]]]].
      apply Hoare_choice.
      (* Tree edge: a unvisited *)
      + (* Derive dfn s0 u < timer s0 from wf_scc_state *)
        assert (Hdfn_timer: dfn s0 u < timer s0). {
          destruct Hwf as [_ [Hinv _]].
          destruct Hinv as [Hdfn_inv _]. apply Hdfn_inv. exact Huvis. }
        intro_state. subst s1.
        apply (Hoare_assume_bind (fun s => s = s0) (fun s => ~ a ∈ visited s)
                 (set_fa a u ;; W a ;; lv <- get' (fun s => low s a) ;; update_low u lv)
                 (fun _ s => I (done ∪ [a]) s)).
        intro_state. destruct H as [Hnv_vis_s1 Heq_s1]. subst s1.
        exact (tree_edge_preserves_I u a done s0 W HW_frame Hwf Huvis Hinu_stk Hlow_le Hforall Hdone_vis Horder Hinj Hsrc Hchild Hfa_child Hfa_not_done Hnv_vis_s1 Ha_not_done Ha_S Hdfn_timer).
      (* Non-tree edge: a visited *)
      + intro_state. hoare_auto_s.
      * (* Back edge: In a (stack s0) — H2 holds this *)
        rename H2 into Hinstk_a.
        assert (Hvis_a: a ∈ visited s0). { apply NNPP. exact H1. }
        (* Case split: self-loop vs proper back edge *)
        destruct (classic (a = u)) as [Heq_au | Hneq_au]; [ subst a | ].
        (* === Self-loop case: a = u === *)
        unfold update_low; intro_state; hoare_auto_s;
          [ exfalso; apply (Nat.lt_irrefl (dfn s0 u));
            apply (Nat.lt_le_trans _ _ _ H); exact Hlow_le
          | destruct H as [Heq_s' Hnlt]; subst s ].
        refine (conj (conj Hwf (conj Huvis (conj Hinu_stk (conj Hlow_le _))))
          (conj _ (conj Hinstk (conj Horder (conj Hinj (conj _ (conj _ (conj Hfa_child _)))))))).
        (* 1: forall for forset_inv *)
        { intros v1 Hor1 Hdg1; destruct Hor1 as [Hv_done1 | Hv_eq_u1];
          [ apply Hforall; auto
          | sets_unfold in Hv_eq_u1; subst v1; split; [intros _; apply Nat.le_refl | intros _; exact Hlow_le] ]. }
        (* 2: done_visited *)
        { intros v2 Hor2; destruct Hor2 as [Hv_done2 | Hv_eq_u2];
          [ apply Hdone_vis; auto | sets_unfold in Hv_eq_u2; subst v2; exact Hvis_a ]. }
        (* 3: low_src *)
        { unfold low_src; unfold low_src in Hsrc;
          destruct Hsrc as [Heq_dfnu | [[v3 [Hv3 [Hdg3 [Hfa3 [Hfa_ne3 Heq_low3]]]]] | [w3 [Hw3 [Hdg3' [Hinstk3 [Hfa_ne3' Heq_dfn3]]]]]]];
          [ left; exact Heq_dfnu
          | right; left; exists v3; split; [left; exact Hv3 | auto]
          | right; right; exists w3; split; [left; exact Hw3 | auto] ]. }
        (* 4: child IH *)
        { intros v4 Hor4 Hdg4 Hfa4 Hfa4_ne; destruct Hor4 as [Hv_done4 | Hv_eq_u4];
          [ apply Hchild; [exact Hv_done4 | exact Hdg4 | exact Hfa4 | exact Hfa4_ne]
          | sets_unfold in Hv_eq_u4; subst v4; exfalso; apply Hfa4_ne; exact Hfa4 ]. }
        (* 5: fa_not_done *)
        { unfold fa_not_done_implies_eq_u; intros v5 Hnv5 Hfa5;
          apply Hfa_not_done; [intro Hv5; apply Hnv5; left; exact Hv5 | exact Hfa5]. }
        (* === a <> u case === *)
        assert (Hfa_ne_a: fa s0 a <> u). {
          intro Hfa_eq_a; apply Hfa_not_done in Hfa_eq_a; [| exact Ha_not_done];
          apply Hneq_au; exact Hfa_eq_a. }
        destruct (PeanoNat.Nat.lt_ge_cases (dfn s0 a) (dfn s0 u)) as [Hdfn_lt | Hdfn_ge].
        (* --- Subcase 1: dfn a < dfn u — proper back edge --- *)
        unfold update_low; intro_state; hoare_auto_s.
        (* set_low branch: use helper lemma *)
        rename H into Hlt_low.
        eapply set_low_back_preserves_I; eauto.
        (* skip branch: ~ dfn a < low u, state unchanged *)
        destruct H as [Heq_s' Hnlt]; subst s.
        refine (conj (conj Hwf (conj Huvis (conj Hinu_stk (conj Hlow_le _))))
          (conj _ (conj Hinstk (conj Horder (conj Hinj (conj _ (conj _ (conj Hfa_child _)))))))).
        { intros v1 Hor1 Hdg1; destruct Hor1 as [Hv_done1 | Hv_eq_a1];
          [ apply Hforall; auto
          | sets_unfold in Hv_eq_a1; subst v1; split;
            [ intro Hfa_a_u; exfalso; apply Hfa_ne_a; exact Hfa_a_u
            | intros _; apply Nat.nlt_ge; exact Hnlt ] ]. }
        { intros v2 Hor2; destruct Hor2 as [Hv_done2 | Hv_eq_a2];
          [ apply Hdone_vis; auto | sets_unfold in Hv_eq_a2; subst v2; exact Hvis_a ]. }
        { unfold low_src; unfold low_src in Hsrc;
          destruct Hsrc as [Heq_dfnu | [[v3 [Hv3 [Hdg3 [Hfa3 [Hfa_ne3 Heq_low3]]]]] | [w3 [Hw3 [Hdg3' [Hinstk3 [Hfa_ne3' Heq_dfn3]]]]]]];
          [ left; exact Heq_dfnu
          | right; left; exists v3; split; [left; exact Hv3 | auto]
          | right; right; exists w3; split; [left; exact Hw3 | auto] ]. }
        { intros v4 Hor4 Hdg4 Hfa4 Hfa4_ne; destruct Hor4 as [Hv_done4 | Hv_eq_a4];
          [ apply Hchild; [exact Hv_done4 | exact Hdg4 | exact Hfa4 | exact Hfa4_ne]
          | sets_unfold in Hv_eq_a4; subst v4; exfalso; apply Hfa_ne_a; exact Hfa4 ]. }
        { unfold fa_not_done_implies_eq_u; intros v5 Hnv5 Hfa5;
          apply Hfa_not_done; [intro Hv5; apply Hnv5; left; exact Hv5 | exact Hfa5]. }
        (* --- Subcase 2: dfn u <= dfn a — update_low no-op --- *)
        unfold update_low; intro_state; hoare_auto_s;
          [ exfalso; apply (Nat.lt_irrefl (dfn s0 a));
            apply (Nat.lt_le_trans _ _ _ H);
            apply (Nat.le_trans _ _ _ Hlow_le Hdfn_ge)
          | destruct H as [Heq_s' Hnlt]; subst s ].
        refine (conj (conj Hwf (conj Huvis (conj Hinu_stk (conj Hlow_le _))))
          (conj _ (conj Hinstk (conj Horder (conj Hinj (conj _ (conj _ (conj Hfa_child _)))))))).
        { intros v1 Hor1 Hdg1; destruct Hor1 as [Hv_done1 | Hv_eq_a1];
          [ apply Hforall; auto
          | sets_unfold in Hv_eq_a1; subst v1; split;
            [ intro Hfa_a_u; exfalso; apply Hfa_ne_a; exact Hfa_a_u
            | intros _; apply (Nat.le_trans _ _ _ Hlow_le Hdfn_ge) ] ]. }
        { intros v2 Hor2; destruct Hor2 as [Hv_done2 | Hv_eq_a2];
          [ apply Hdone_vis; auto | sets_unfold in Hv_eq_a2; subst v2; exact Hvis_a ]. }
        { unfold low_src; unfold low_src in Hsrc;
          destruct Hsrc as [Heq_dfnu | [[v3 [Hv3 [Hdg3 [Hfa3 [Hfa_ne3 Heq_low3]]]]] | [w3 [Hw3 [Hdg3' [Hinstk3 [Hfa_ne3' Heq_dfn3]]]]]]];
          [ left; exact Heq_dfnu
          | right; left; exists v3; split; [left; exact Hv3 | auto]
          | right; right; exists w3; split; [left; exact Hw3 | auto] ]. }
        { intros v4 Hor4 Hdg4 Hfa4 Hfa4_ne; destruct Hor4 as [Hv_done4 | Hv_eq_a4];
          [ apply Hchild; [exact Hv_done4 | exact Hdg4 | exact Hfa4 | exact Hfa4_ne]
          | sets_unfold in Hv_eq_a4; subst v4; exfalso; apply Hfa_ne_a; exact Hfa4 ]. }
        { unfold fa_not_done_implies_eq_u; intros v5 Hnv5 Hfa5;
          apply Hfa_not_done; [intro Hv5; apply Hnv5; left; exact Hv5 | exact Hfa5]. }
      * (* Cross edge: ~ In a (stack s) *)
        destruct H2 as [Heq_s Hnv_stk]. subst s.
        rename H into Heq_s1. subst s1.
        assert (Hvis_a: a ∈ visited s0). { apply NNPP. exact H1. }
        assert (Ha_ne_u: a <> u). { intro Heq. subst a. apply Hnv_stk. exact Hinstk. }
        assert (Hfa_ne_a: fa s0 a <> u). {
          intro Hfa_eq_a. apply Hfa_not_done in Hfa_eq_a; [| exact Ha_not_done].
          apply Ha_ne_u. exact Hfa_eq_a. }
        unfold I.
        split. { (* forset_inv u (done ∪ [a]) s0 *)
          unfold forset_inv.
          split. exact Hwf. split. exact Huvis. split. exact Hinu_stk. split. exact Hlow_le.
          intros v Hor Hdg_v. destruct Hor as [Hv_done | Hv_eq_a].
          - apply Hforall; auto.
          - sets_unfold in Hv_eq_a. subst v. split.
            + intro Hfa_a_u. exfalso. apply Hfa_ne_a. exact Hfa_a_u.
            + intro Hinstk_a. exfalso. apply Hnv_stk. exact Hinstk_a. }
        split. { (* done_visited *) intros v Hor. destruct Hor as [Hv_done | Hv_eq_a].
          - apply Hdone_vis. exact Hv_done.
          - sets_unfold in Hv_eq_a. subst v. exact Hvis_a. }
        split. exact Hinstk. split. exact Horder. split. exact Hinj.
        split. { (* low_src *) unfold low_src. unfold low_src in Hsrc.
          destruct Hsrc as [Heq_dfnu | [[v [Hv [Hdg_v [Hfa_v [Hfa_ne_v Heq_low]]]]] | [w [Hw [Hdg_w [Hinstk_w [Hfa_ne_w Heq_dfn]]]]]]].
          - left. exact Heq_dfnu.
          - right. left. exists v. split; [left; exact Hv | auto].
          - right. right. exists w. split; [left; exact Hw | auto]. }
        split. { (* child IH *) intros v Hor Hdg_v Hfa_v Hfa_ne_v.
          destruct Hor as [Hv_done | Hv_eq_a].
          - apply Hchild; [exact Hv_done | exact Hdg_v | exact Hfa_v | exact Hfa_ne_v].
          - sets_unfold in Hv_eq_a. subst v. exfalso. apply Hfa_ne_a. exact Hfa_v. }
        split. { (* fa_child_of_u *) exact Hfa_child. }
        { (* fa_not_done *) unfold fa_not_done_implies_eq_u. intros v Hnv Hfa_v.
          apply Hfa_not_done; [intro Hv; apply Hnv; left; exact Hv | exact Hfa_v]. }
  Qed.

  (* ================================================================ *)
  (* 9. Main Theorem: Single-vertex Low-link Correctness               *)
  (* ================================================================ *)

  (** Frame property: existential pre, universal post.
      [frame_pre v s] = there exists an ancestor [anc] with done-set [d] and
      initial state [s0] s.t. all frame preconditions hold and [s = s0].
      [frame_post v _ s] = for all anc, d, s0 satisfying the preconditions,
      the post-state [s] satisfies all frame postconditions. *)
  Definition frame_pre (v: V) (s: @SCCSt V): Prop :=
    exists (anc: V) (d: V -> Prop) (s0: SCCSt),
      forset_inv anc d s0 /\ In anc (stack s0) /\ stack_dfn_order s0 /\
      dfn_injective s0 /\ low_src anc d s0 /\
      (forall w, d w -> dg_step g anc w -> fa s0 w = anc -> fa s0 w <> w ->
        scc_is_low_v s0 w) /\
      fa_child_of_u anc s0 /\ fa_not_done_implies_eq_u anc (d ∪ [v]) s0 /\
      done_visited d s0 /\ dfn s0 anc < timer s0 /\ ~ v ∈ visited s0 /\
      s = s0.

  Definition frame_post (v: V) (_: unit) (s: @SCCSt V): Prop :=
    forall (anc: V) (d: V -> Prop) (s0: SCCSt),
      forset_inv anc d s0 -> In anc (stack s0) -> stack_dfn_order s0 ->
      dfn_injective s0 -> low_src anc d s0 ->
      (forall w, d w -> dg_step g anc w -> fa s0 w = anc -> fa s0 w <> w ->
        scc_is_low_v s0 w) ->
      fa_child_of_u anc s0 -> fa_not_done_implies_eq_u anc (d ∪ [v]) s0 ->
      done_visited d s0 -> dfn s0 anc < timer s0 -> ~ v ∈ visited s0 ->
      forset_inv anc d s /\ In anc (stack s) /\ stack_dfn_order s /\
      dfn_injective s /\ low_src anc d s /\
      (forall w, d w -> dg_step g anc w -> fa s w = anc -> fa s w <> w ->
        scc_is_low_v s w) /\
      fa_child_of_u anc s /\ fa_not_done_implies_eq_u anc (d ∪ [v]) s /\
      done_visited d s /\ low_post v s /\ v ∈ visited s /\
      (fa s0 v = anc -> fa s v = anc).

  (** Convert the [∀]-encoded [frame_post] IH into the concrete [HW_frame]
      form that [forset_keep_forset_inv] expects. *)
  Lemma frame_IH_to_hw_frame (W: V -> program SCCSt unit)
        (IHframe: forall a, Hoare (frame_pre a) (W a) (frame_post a)):
    forall v (anc: V) (d: V -> Prop) (s0: SCCSt),
      forset_inv anc d s0 -> In anc (stack s0) -> stack_dfn_order s0 ->
      dfn_injective s0 -> low_src anc d s0 ->
      (forall w, d w -> dg_step g anc w -> fa s0 w = anc -> fa s0 w <> w ->
       scc_is_low_v s0 w) ->
      fa_child_of_u anc s0 -> fa_not_done_implies_eq_u anc (d ∪ [v]) s0 ->
      done_visited d s0 -> dfn s0 anc < timer s0 -> ~ v ∈ visited s0 ->
      Hoare (fun s' => s' = s0) (W v) (fun _ s' =>
        forset_inv anc d s' /\ In anc (stack s') /\ stack_dfn_order s' /\
        dfn_injective s' /\ low_src anc d s' /\
        (forall w, d w -> dg_step g anc w -> fa s' w = anc -> fa s' w <> w ->
         scc_is_low_v s' w) /\
        fa_child_of_u anc s' /\ fa_not_done_implies_eq_u anc (d ∪ [v]) s' /\
        done_visited d s' /\ low_post v s' /\ v ∈ visited s' /\
        (fa s0 v = anc -> fa s' v = anc)).
  Proof.
    intros v anc d s0 Hinv Hstack Horder Hinj Hsrc Hchild
           Hfa_child Hfa_not_done Hdone_vis Hdfn_lt Hnv.
    specialize (IHframe v).
    apply (@Hoare_conseq SCCSt unit
      (fun s' => s' = s0) (frame_pre v) (W v)
      (fun _ s' => forset_inv anc d s' /\ In anc (stack s') /\ stack_dfn_order s' /\
                  dfn_injective s' /\ low_src anc d s' /\
                  (forall w, d w -> dg_step g anc w -> fa s' w = anc -> fa s' w <> w ->
                    scc_is_low_v s' w) /\
                  fa_child_of_u anc s' /\ fa_not_done_implies_eq_u anc (d ∪ [v]) s' /\
                  done_visited d s' /\ low_post v s' /\ v ∈ visited s' /\
                  (fa s0 v = anc -> fa s' v = anc))
      (frame_post v)).
    { intros s1 Heq. subst s1. unfold frame_pre.
      exists anc, d, s0. split; [|split; [|split; [|split; [|split; [|split;
      [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]];
      try assumption. }
    { intros ret s' Hpost.
      unfold frame_post in Hpost.
      apply (Hpost anc d s0 Hinv Hstack Horder Hinj Hsrc Hchild
        Hfa_child Hfa_not_done Hdone_vis Hdfn_lt Hnv). }
    { exact IHframe. }
  Qed.

  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s /\ original_vvalid g u /\ stack_dfn_order s /\ dfn_injective s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => low_post u s).
  Proof.
    unfold tarjan_scc.
    (* Use Hoare_fix_mutual_conj: prove (1) low_pre -> low_post AND (2) frame_pre -> frame_post
       simultaneously via mutual fixpoint induction.  Then extract (1) and add extra pre's. *)
    pose proof (Hoare_fix_mutual_conj (Σ := @SCCSt V) (A := V) (B := unit) (C := unit)
      (tarjan_scc_f g) (fun v s => low_pre v s /\ stack_dfn_order s /\ dfn_injective s) frame_pre
      (fun v _ => low_post v) frame_post u) as [Hlow_raw Hframe_raw].
    { (* Step 1: (low_pre ∧ order ∧ inj) → low_post (F W a) *)
      intros W a IHlow IHframe.
      pose proof (frame_IH_to_hw_frame W IHframe) as HW_frame.
      unfold tarjan_scc_f.
      eapply (Hoare_bind (fun s => low_pre a s /\ stack_dfn_order s /\ dfn_injective s) (preloop a)
        (fun _ s => forset_inv a ∅ s /\ In a (stack s) /\
                    stack_dfn_order s /\ dfn_injective s /\
                    low s a = dfn s a /\
                    fa_child_of_u a s /\
                    fa_not_done_implies_eq_u a ∅ s)
        (fun _ => forset (fun v => dg_step g a v) (process_edge a W);;
                 If (fun s => low s a = dfn s a) (pop_scc a))
        (fun _ s => low_post a s)).
      { apply (Hoare_conseq_pre _ (fun s => wf_scc_state_pre a s /\ stack_dfn_order s /\ dfn_injective s)).
        { intros s [Hlp [Horder Hinj]]. split; [exact Hlp | split; [exact Horder | exact Hinj]]. }
        apply preloop_establishes_forset_precond. }
      { intros ret.
        eapply (Hoare_bind (fun s => forset_inv a ∅ s /\ In a (stack s) /\
                                    stack_dfn_order s /\ dfn_injective s /\
                                    low s a = dfn s a /\
                                    fa_child_of_u a s /\
                                    fa_not_done_implies_eq_u a ∅ s)
          (forset (fun v => dg_step g a v) (process_edge a W))
          (fun _ s => low_post a s /\ In a (stack s) /\ stack_dfn_order s /\ dfn_injective s)
          (fun _ => If (fun s => low s a = dfn s a) (pop_scc a))
          (fun _ s => low_post a s)).
        { apply (forset_keep_forset_inv a W HW_frame). }
        { intros ret2. apply Hoare_state_intro. intros s0 [Hlow_post_a [Hinstk' [Horder' Hinj']]].
          hoare_auto_s.
          - (* pop_scc a preserves low_post a: wf_scc_state via pop_scc_preserves_wf_scc_state *)
            unfold low_post.
            refine (@Hoare_conj _ _ _ (pop_scc a) (fun _ s => wf_scc_state s)
              (fun _ s => scc_is_low_v s a) _ _).
            { eapply Hoare_conseq_pre. 2: apply pop_scc_preserves_wf_scc_state.
              intros s1 Hs1. destruct Hs1. destruct Hlow_post_a as [Hwf _]. subst. exact Hwf. }
            { (* scc_is_low_v a after pop_scc: the self-witness a works for the
                 "minimum is achieved" part (low a = dfn a, preserved by pop_scc).
                 The lower bound follows from Hlow_post_a + the fact that pop_scc
                 only shrinks the stack, hence scc_low_tree can only shrink.
                 TODO: prove pop_scc_preserves_scc_is_low_v lemma. *)
              admit. }
          - destruct H as [Heq_s Hncond]. subst s. exact Hlow_post_a. } } }
    { (* Step 2: frame_pre a → frame_post (F W a).
         Key: for anc' ≠ a, each operation preserves anc''s invariants:
         - preloop a only modifies a (dfn, low, visited, stack for a)
         - forset calls W on children; IHframe gives frame for W
         - pop_scc a only pops from the top; anc' has smaller dfn, so is safe *)
      intros W a IHlow IHframe.
      pose proof (frame_IH_to_hw_frame W IHframe) as HW_frame.
      unfold tarjan_scc_f.
      (* Use Hoare_bind to compose: preloop ;; forset ;; if_else *)
      eapply (Hoare_bind (fun s => frame_pre a s) (preloop a)
        (fun _ s => frame_pre a s /\ forset_inv a ∅ s /\ In a (stack s) /\
                    stack_dfn_order s /\ dfn_injective s /\
                    low s a = dfn s a /\ fa_child_of_u a s /\
                    fa_not_done_implies_eq_u a ∅ s)
        (fun _ => forset (fun v => dg_step g a v) (process_edge a W);;
                 If (fun s => low s a = dfn s a) (pop_scc a))
        (frame_post a)).
      { (* ---- preloop a: preserve frame AND establish forset pre ---- *)
        apply Hoare_conseq_pre with
          (P2 := fun s => frame_pre a s /\ low_pre a s /\ stack_dfn_order s /\ dfn_injective s).
        { intros s Hfp. destruct Hfp as [anc0 [d0 [s00 [Hinv0 [Hstack0 [Horder0 [Hinj0
          [Hsrc0 [Hchild0 [Hfa_child0 [Hfa_not_done0 [Hdone_vis0 [Hdfn_lt0 [Hnv0 Heq0]]]]]]]]]]]]]].
          subst s. unfold low_pre, wf_scc_state_pre. destruct Hinv0 as [Hwf0 _].
          split; [| split; [| split; [| split]]].
          - exists anc0, d0, s00. repeat split; assumption.
          - exact (conj Hwf0 Hnv0).
          - exact Horder0.
          - exact Hinj0. }
        refine (@Hoare_conj _ _ _ (preloop a)
          (fun _ s => frame_pre a s)
          (fun _ s => forset_inv a ∅ s /\ In a (stack s) /\
                     stack_dfn_order s /\ dfn_injective s /\
                     low s a = dfn s a /\ fa_child_of_u a s /\
                     fa_not_done_implies_eq_u a ∅ s) _ _).
        { (* frame_pre a preserved: preloop only changes a's state.
             For any anc ≠ a witnessing frame_pre a, anc's invariants are unchanged. *)
          apply Hoare_state_intro. intros s0 Hpre.
          destruct Hpre as [[anc0 [d0 [s00 [Hinv0 [Hstack0 [Horder0 [Hinj0 [Hsrc0
            [Hchild0 [Hfa_child0 [Hfa_not_done0 [Hdone_vis0 [Hdfn_lt0 [Hnv0 Heq0]]]]]]]]]]]]]]
            [Hlp [Horder_s Hinj_s]]].
          subst s0.
          unfold Hoare. sets_unfold.
          intros s1 ret s2 Heq_s1 Hprog. subst s1.
          unfold frame_pre. exists anc0, d0, s00.
          (* preloop doesn't change fa, dfn(anc0), low(anc0), stack below a, visited(anc0).
             forset_inv anc0 d0 is preserved because anc0 ≠ a (since ~a ∈ visited s00 and
             anc0 ∈ visited s00). *)
          assert (Hanc_ne_a: anc0 <> a). {
            intro Heq. subst anc0. destruct Hinv0 as [_ [Hav _]]. exfalso. apply Hnv0. exact Hav. }
          (* All preloop lemmas show the individual properties are preserved *)
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]].
          (* 1. forset_inv anc0 d0 *)
          { (* preloop preserves wf_scc_state, anc0 ∈ visited, In anc0 (stack), low ≤ dfn, forall *)
            admit. }
          (* 2-13: the remaining 12 conjuncts are preserved by preloop *)
          all: admit. }
        { (* forset_precond established by preloop *)
          apply (Hoare_conseq_pre _ (fun s => low_pre a s /\ stack_dfn_order s /\ dfn_injective s)).
          { intros s [[_ [Hlp [Horder Hinj]]] _]. repeat split; assumption. }
          apply preloop_establishes_forset_precond. } }
      { (* ---- forset ;; if_else ---- *)
        intros _. intro_state.
        destruct H as [[anc0 [d0 [s00 [Hinv0 [Hstack0 [Horder0 [Hinj0 [Hsrc0
          [Hchild0 [Hfa_child0 [Hfa_not_done0 [Hdone_vis0 [Hdfn_lt0 [Hnv0 Heq0]]]]]]]]]]]]]]
          [Hfinv [Hinstk [Horder [Hinj [Hlow_eq [Hfa_child Hfa_not_done]]]]]]].
        subst s. (* s = s00 after intro_state *)
        eapply (Hoare_bind (fun s => forset_inv a ∅ s /\ In a (stack s) /\
                                    stack_dfn_order s /\ dfn_injective s /\
                                    low s a = dfn s a /\
                                    fa_child_of_u a s /\
                                    fa_not_done_implies_eq_u a ∅ s)
          (forset (fun v => dg_step g a v) (process_edge a W))
          (fun _ s => low_post a s /\ In a (stack s) /\ stack_dfn_order s /\ dfn_injective s)
          (fun _ => If (fun s => low s a = dfn s a) (pop_scc a))
          (frame_post a)).
        { apply (forset_keep_forset_inv a W HW_frame). }
        { intros _. intro_state.
          destruct H as [Hlow_post_a [Hinstk' [Horder' Hinj']]].
          unfold frame_post. intros anc' d' s0' Hinv' Hstack' Horder'' Hinj'' Hsrc'
            Hchild' Hfa_child' Hfa_not_done' Hdone_vis' Hdfn_lt' Hnv'.
          destruct (classic (anc' = a)) as [Heq_anc | Hne_anc].
          { subst anc'. destruct Hinv' as [Hsiv _]. unfold stack_in_visited in Hsiv.
            apply Hsiv in Hstack'. exfalso. apply Hnv'. exact Hstack'. }
          (* anc' ≠ a: if_else (pop_scc a or skip) preserves anc''s invariants *)
          hoare_auto_s.
          - (* pop_scc a: preserves forset_inv anc' d' (anc' is below a in stack) *)
            (* pop_scc only removes from top of stack; anc' has dfn < dfn a, so it's safe *)
            admit.
          - (* skip: state unchanged, frame preserved *)
            destruct H as [Heq_s Hncond]. subst s.
            (* Need: frame_post for anc'. Follows from IHframe (via frame_post of W)? No,
               we're in the if_else after forset. The frame for anc' should hold from the
               forset postcondition. But forset_keep_forset_inv's post doesn't include
               frame for anc' -- it only gives low_post a.
               Actually, the frame for anc' was preserved through the forset by HW_frame.
               We need to extract that information from the forset execution. *)
            admit. } } }
    (* Hlow_raw: Hoare (low_pre u ∧ stack_dfn_order ∧ dfn_injective) ... low_post u.
       Goal:     Hoare (low_pre u ∧ original_vvalid g u ∧ stack_dfn_order ∧ dfn_injective) ... low_post u.
       Apply Hoare_conseq_pre to add original_vvalid to the pre (it's trivially dropped). *)
    eapply Hoare_conseq_pre.
    - intros s [Hlp [Hov [Horder Hinj]]]. exact (conj Hlp (conj Horder Hinj)).
    - exact Hlow_raw.
  Admitted.

End IS_LOW.
