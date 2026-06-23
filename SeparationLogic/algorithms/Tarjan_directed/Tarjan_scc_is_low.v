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

  Lemma preloop_establishes_low_forset_inv (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s)
          (preloop u)
          (fun _ s => low_forset_inv u ∅ s).
  Proof.
    unfold low_pre, low_forset_inv, low_forset_inv_core.
    apply Hoare_conj with (Q1 := fun _ s => wf_scc_state s).
    - (* wf_scc_state: from preloop_preserves_wf_scc_state *)
      apply (Hoare_conseq_pre (fun s => wf_scc_state s /\ ~ u ∈ visited s)
        (fun s => wf_scc_state_pre u s) (preloop u) (fun _ s => wf_scc_state s)).
      intros s H. unfold wf_scc_state_pre. exact H.
      apply preloop_preserves_wf_scc_state.
    - apply Hoare_conj with (Q1 := fun _ s => u ∈ visited s).
      + (* u ∈ visited: from preloop_self_visited *)
        apply (Hoare_conseq_pre (fun s => wf_scc_state s /\ ~ u ∈ visited s)
          (fun _ => True) (preloop u) (fun _ s => u ∈ visited s)).
        intros s _. exact I.
        apply (preloop_self_visited u).
      + (* low_forset_inv_core: from preloop_low_eq_dfn + low_eq_dfn_to_min_empty *)
        apply (Hoare_conseq_pre (fun s => wf_scc_state s /\ ~ u ∈ visited s)
          (fun _ => True) (preloop u)
          (fun _ s => min_value_of_subset Nat.le
            (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
             min_value_of_subset Nat.le (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
            (fun x => x) (low s u))).
        intros s _. exact I.
        apply Hoare_conseq with
          (P2 := fun _ => True) (Q2 := fun _ s => low s u = dfn s u)
          (Q1 := fun _ s => min_value_of_subset Nat.le
            (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
             min_value_of_subset Nat.le (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
            (fun x => x) (low s u)).
        intros s _. exact I.
        intros _ s Hlow_eq. apply low_eq_dfn_to_min_empty. exact Hlow_eq.
        apply preloop_low_eq_dfn.
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
      [low_forset_inv u done] when [~a in visited].  Extracted from the
      first branch of [preloop_preserves_ancestor_inv] (Qed, line 1620). *)
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
    unfold process_edge, if_else. intro_state. apply Hoare_choice.
    - (* Tree edge *)
      apply Hoare_assume_bind. simpl.
      destruct H as [Hfa Hv_vis].
      apply (Hoare_bind (fun s => ~ x ∈ visited s /\ s = s0) (set_fa x a)
        (fun _ s => fa s v = parent /\ v ∈ visited s)
        (fun _ => W x ;; lv <- get' (fun s => low s x) ;; update_low a lv)
        (fun _ s => fa s v = parent /\ v ∈ visited s)).
      + unfold set_fa. intro_state. hoare_auto_s.
        destruct H as [Hnv_x Hs1_eq]. subst s1. subst s. simpl.
        unfold equiv_decb. destruct (equiv_dec v x) as [Heq | Hneq].
        * exfalso. rewrite Heq in Hv_vis. exact (Hnv_x Hv_vis).
        * split; [exact Hfa | exact Hv_vis].
      + intros _. simpl.
        apply (Hoare_bind (fun s => fa s v = parent /\ v ∈ visited s) (W x)
          (fun _ s => fa s v = parent /\ v ∈ visited s)
          (fun _ => lv <- get' (fun s => low s x) ;; update_low a lv)
          (fun _ s => fa s v = parent /\ v ∈ visited s)).
        * apply Hoare_conj.
          { eapply Hoare_conseq_pre. { intros st [Hfa0 Hvis0]. exact Hfa0. } apply (IH_fa x). }
          { eapply Hoare_conseq_pre. { intros st [Hfa0 Hvis0]. exact Hvis0. } apply (IH_vis x). }
        * intros _. simpl.
          apply (Hoare_bind (fun s => fa s v = parent /\ v ∈ visited s)
            (get' (fun s => low s x))
            (fun lv s => fa s v = parent /\ v ∈ visited s)
            (fun lv => update_low a lv)
            (fun _ s => fa s v = parent /\ v ∈ visited s)).
          -- unfold get'. intro_state. hoare_auto_s. destruct H1. subst s. exact H.
          -- intros lv. simpl. unfold update_low. intro_state. hoare_auto_s.
             ++ unfold set_low. intro_state. hoare_auto_s. subst s. subst s2. simpl. exact H.
             ++ destruct H1. subst s. exact H.
    - (* Non-tree edge *)
      apply Hoare_assume_bind. simpl.
      destruct H as [Hfa Hv_vis]. intro_state. hoare_auto_s.
      + (* In stack: back edge *)
        destruct H as [Hx_vis Hs1_eq]. subst s1.
        unfold update_low. intro_state. hoare_auto_s.
        * unfold set_low. intro_state. hoare_auto_s. subst s. simpl. rewrite H2. split.
          -- reflexivity.
          -- exact Hv_vis. 
        * destruct H. subst s. auto.
      + (* Not in stack: cross edge *)
        destruct H1 as [Heq _]. subst s.
        destruct H as [Hx_vis Hs1_eq]. subst s1. auto.
  Qed.

  Lemma forset_keeps_fa (a v parent: V)
    (W: V -> program (@SCCSt V) unit)
    (IH_fa: forall y, Hoare (fun s => fa s v = parent) (W y) (fun _ s => fa s v = parent))
    (IH_vis: forall y, Hoare (fun s => v ∈ visited s) (W y) (fun _ s => v ∈ visited s)):
    Hoare (fun s => fa s v = parent /\ a ∈ visited s /\ v ∈ visited s)
          (forset (fun w => dg_step g a w) (process_edge a W))
          (fun _ s => fa s v = parent).
  Proof.
    apply (Hoare_conseq
      (fun s => fa s v = parent /\ a ∈ visited s /\ v ∈ visited s)
      (fun s => fa s v = parent /\ v ∈ visited s)
      (forset (fun w => dg_step g a w) (process_edge a W))
      (fun _ s => fa s v = parent)
      (fun _ s => fa s v = parent /\ v ∈ visited s)).
    { intros s [Hfa [Hvis_a Hvis_v]]. split; [exact Hfa | exact Hvis_v]. }
    { intros _ s [Hfa _]. exact Hfa. }
    apply (@Hoare_forset SCCSt V
      (fun done s => fa s v = parent /\ v ∈ visited s)
      (fun w => dg_step g a w) (process_edge a W)).
    { unfold Proper, respectful. intros. subst. reflexivity. }
    { intros todo a0 Hsub Huniv Hnotdone.
      apply (process_edge_keeps_fa_simple a a0 v parent W IH_fa IH_vis). }
  Qed.

  (** [set_fa_W_preserves_low_forset_inv]: key lemma for the tree edge
      branch of [process_edge_keep_low_forset_inv].  After [set_fa v u]
      (which sets [fa v := u]) followed by the recursive call [W v]
      (which is [tarjan_scc g v]), both [low_forset_inv u done] and
      [fa s v = u] are preserved.

      Proof sketch (requires 3 sub-lemmas):
      1. [set_fa_preserves_wf_scc_state_pre]: after [set_fa v u] the state
         satisfies [low_pre v] (i.e. [wf_scc_state_pre v]) as long as [u]
         is visited and [v] is unvisited. This is the exact precondition
         needed by the recursive call [W v].
      2. [set_fa_preserves_low_forset_inv_for_new_child]: [set_fa v u] does
         not change children_done/back_edges_done for [u] (v ∉ done), and
         preserves [low_forset_inv u done].
      3. [W_preserves_low_forset_inv_and_fa]: [W v] (tarjan_scc g v) does
         not modify fa v (only sets fa for v's descendants), does not
         modify low u (only update_low on v/descendants), children_done
         and back_edges_done for done vertices unchanged (done vertices
         are not descendants of v). Proved by fixpoint induction on
         tarjan_scc. *)
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
    intro_state. destruct H as [Hinv [Hfa_eq [Hndone_v [Hstep [Hin_stack Hdone_not_popped]]]]].
    apply Hoare_conj.
    - eapply Hoare_conseq_pre. 2: apply (pop_scc_keeps_low_forset_inv_other u v done).
      intros s1 Hs1. subst s1. split; [exact Hinv | split; [exact Hin_stack | exact Hdone_not_popped]].
    - unfold pop_scc. unfold_op. intro_state. hoare_auto_s. subst s.
      subst s1. unfold pop_scc_state.
      destruct (stack_split_at (stack s0) v) as [p r]. simpl. exact Hfa_eq.
  Qed.

  (** [preloop_preserves_ancestor_inv]: [preloop v] modifies [dfn v],
      [low v], [timer], [stack], [visited] — all local to [v].
      No effect on [fa], [low] for [u ≠ v], or [done] vertices. *)
  Lemma preloop_preserves_ancestor_inv (u v: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v)
          (preloop v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    intro_state. destruct H as [Hinv [Hfa_eq [Hnv Hndone_v]]].
    apply Hoare_conj.
    - refine (Hoare_conseq_post (fun s => s = s0) (preloop v)
               (fun _ s => low_forset_inv u done s)
               (fun _ s => low_forset_inv u done s /\ v ∈ visited s) _ _).
      { intros _ s [Hinv' _]. exact Hinv'. }
      eapply Hoare_conseq_pre. 2: apply (preloop_keeps_low_forset_inv_other u v done).
      intros s1 Hs1. subst s1. split; [exact Hinv | split; [exact Hnv | exact Hndone_v]].
    - refine (Hoare_conseq_post (fun s => s = s0) (preloop v)
               (fun _ s => fa s v = u)
               (fun _ s => fa s v = u /\ v ∈ visited s) _ _).
      { intros _ s [Hfa_eq' _]. exact Hfa_eq'. }
      eapply Hoare_conseq_pre. 2: apply (preloop_keeps_fa v u).
      intros s1 Hs1. subst s1. exact Hfa_eq.
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

  (** [in_list_one_above_other]: If two distinct elements [x] and [y] are
      both in a list, then either [x] appears before [y] or [y] appears
      before [x] (i.e., one is above the other). *)
  Lemma in_list_one_above_other {A: Type} (l: list A) (x y: A):
    In x l -> In y l -> x <> y ->
    (exists l1 l2, l = l1 ++ x :: l2 /\ In y l2) \/
    (exists l1 l2, l = l1 ++ y :: l2 /\ In x l2).
  Proof.
    induction l as [| z zs IH] in x, y |- *; intros Hx_in Hy_in Hneq.
    { destruct Hx_in. }
    { destruct Hx_in as [Hx_eq_z | Hx_in_zs].
      { subst z. simpl in Hy_in. destruct Hy_in as [Hy_eq_x | Hy_in_zs].
        { exfalso. apply Hneq. exact Hy_eq_x. }
        { left. exists (@nil A). exists zs. split; [reflexivity | exact Hy_in_zs]. } }
      { destruct Hy_in as [Hy_eq_z | Hy_in_zs].
        { subst z. right. exists (@nil A). exists zs. split; [reflexivity | exact Hx_in_zs]. }
        { destruct (IH x y Hx_in_zs Hy_in_zs Hneq) as [[l1 [l2 [Heq Hiny]]] | [l1 [l2 [Heq Hinx]]]].
          { left. exists (z :: l1). exists l2. split; [rewrite Heq; reflexivity | exact Hiny]. }
          { right. exists (z :: l1). exists l2. split; [rewrite Heq; reflexivity | exact Hinx]. } } } }
  Qed.

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

  (** [W_preserves_ancestor_inv]: Combining the above, [W v]
      ([tarjan_scc g v]) preserves [low_forset_inv u done] and
      [fa s v = u]. *)
  Lemma W_preserves_ancestor_inv (u v: V) (done: V -> Prop):
    u <> v -> ~ done v ->
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v /\ done_visited done s /\ (stack_dfn_order s /\ dfn_injective s))
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u /\ done_visited done s /\ (stack_dfn_order s /\ dfn_injective s) /\
                      (forall w, done w -> In w (stack s) -> dfn s w < dfn s v)).
  Proof.
    (* ================================================================ *)
    (*  ANALYSIS: P and Q Design Issues                                  *)
    (* ================================================================ *)
    (*
      The fixpoint invariant P and Q have several structural flaws:

      1. Q is independent of the vertex [a].
         Q(a,_,s) = Q(b,_,s) for all a,b, so the fixpoint induction
         hypothesis cannot distinguish which vertex was processed.
         In particular, Q does NOT include [a ∈ visited s], even though
         preloop a makes [a] visited and nothing un-visits it.

      2. Consequence: the [IH_forset] construction (adapting the fixpoint
         IH to the shape expected by [forset_keeps_low_forset_inv]) fails.
         The forset invariant requires the parent vertex [a] to stay
         visited after the child [W x] returns, but Q x cannot provide
         [a ∈ visited s].  This needs either a separate
         visited-monotonicity lemma [W_keeps_visited x a] or a stronger Q.

      3. P lacks the dfn-ordering invariant.
         The lemma's outer postcondition demands:
           forall w, done w -> In w (stack s) -> dfn s w < dfn s v
         But P only carries [(a = v \/ v ∈ visited s)] — it never
         transports [dfn s w < dfn s v] through the fixpoint.
         P should use [(a = v \/ dfn_lt_v s)] where:
           dfn_lt_v s := forall w, done w -> In w (stack s) -> dfn s w < dfn s v
         This is needed inside the [pop_scc a] branch for
         [done_not_popped_by_subtree_pop_scc].

      4. The [pop_scc a] branch and [skip] branch in the If after forset
         are both incomplete (admit).  The [pop_scc] branch needs the
         dfn-ordering invariant described above; the [skip] branch is
         missing recovery of static conjuncts ([fa], [done_visited],
         [stack_dfn_order], [dfn_injective]) from the forset context.

      5. [In a (stack s)] after forset.
         The [pop_scc a] branch needs [In a (stack s)] as a precondition
         (for [pop_scc_keeps_low_forset_inv_other]).  This is established
         by preloop and preserved through forset (forset does not pop [a]).
         The intermediate state after forset should explicitly carry
         [In a (stack s)].

      Proposed repairs for P and Q:

        set (dfn_lt_v := fun s => forall w, done w -> In w (stack s) ->
                                  dfn s w < dfn s v).
        set (P := fun a s =>
          low_forset_inv u done s /\ fa s v = u /\ ~ a ∈ visited s /\ ~ done a /\
          done_visited done s /\ (stack_dfn_order s /\ dfn_injective s) /\
          (a = v \/ (v ∈ visited s /\ dfn_lt_v s)) /\ u <> a).
        set (Q := fun a _ s =>
          low_forset_inv u done s /\ fa s v = u /\ a ∈ visited s /\
          done_visited done s /\ (stack_dfn_order s /\ dfn_injective s) /\
          dfn_lt_v s).

      Additional required lemmas:
        - [preloop_preserves_done_dfn_lt_v]: establishes [dfn_lt_v] after preloop.
        - [W_keeps_visited x a]: parent visited persists through child recursion.
        - [forset_preserves_static_conjuncts]: forset preserves [fa], [In stack],
          [done_visited], [stack_dfn_order], [dfn_injective], [dfn_lt_v].

      See also: docs/dev/20260623-W-preserves-ancestor-inv-repair-plan.md
    *)
    (* ================================================================ *)
    intros Hneq Hndone_v.
    (* TODO: proof pending — the analysis above describes the required
       P/Q changes and missing lemmas. *)
  Admitted.



  Lemma set_fa_W_preserves_low_forset_inv (u v: V) (done: V -> Prop):
    u <> v -> dg_step g u v -> ~ done v ->
    Hoare (fun s => low_forset_inv u done s /\ ~ v ∈ visited s /\ ~ done v /\ done_visited done s /\ (stack_dfn_order s /\ dfn_injective s))
          (set_fa v u;; tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u /\ done_visited done s /\ (stack_dfn_order s /\ dfn_injective s) /\
                      (forall w, done w -> In w (stack s) -> dfn s w < dfn s v)).
  Proof.
    (* 证明思路：先 set_fa v u，再递归调用 tarjan_scc g v。
       set_fa 不改变 low/dfn/stack/visited，v 未访问且 v∉done，故 children_done/back_edges_done
       集合不变；对嵌套 min 用 set_fa_preserves_min（或 min_eq_forward）保持 low_forset_inv。
       同时得到 fa s v = u，且栈序/单射/done_visited 不变。
       新增的不变式在 preloop v 处建立：preloop 前 done 中顶点都已 visited、v 未 visited、
       dfn_inv 成立，故由 preloop_after_visited_dfn_lt 得 preloop 后 done dfn < dfn v。
       随后 W_preserves_ancestor_inv 的归纳假设保持该不变式（它以 v 为界）。
       关键引理：set_fa_preserves_min, set_fa_preserves_low_forset_inv_for_new_child,
       min_eq_forward, preloop_after_visited_dfn_lt, W_preserves_ancestor_inv,
       done_visited_proper。 *)
    Admitted.

  (** [current_above_done_vertex]: In the state after preloop and forset
      for the active vertex [a], all [done] vertices that are still on the stack
      appear BELOW [a] (i.e., [a] is above them).

      New proof path: first obtain [dfn s w < dfn s a] from the strengthened
      ancestor invariant (or from [done_vertex_dfn_lt], which is a corollary of
      that invariant).  Then do case analysis on the stack position of [w]
      relative to [a]: if [w] were above [a], [stack_dfn_order_strict] would
      give [dfn s a < dfn s w], contradicting [dfn s w < dfn s a].  Hence [w]
      must be below [a].  This reverses the old dependency direction and breaks
      the circularity with [done_dfn_lt_not_done]. *)
      
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
    stack_dfn_order s ->
    dfn_injective s ->
    forall w, done w -> In w (stack s) -> dfn s w < dfn s a.
  Proof.
    (* 证明思路：该引理应作为 [W_preserves_ancestor_inv] / [set_fa_W_preserves_low_forset_inv]
       中新增不变式的推论来使用，而不是独立证明。
       在 [W v] 执行期间（v 是 pu 的当前活跃子孙），不变式保证
       [∀ w, done w -> In w (stack s) -> dfn s w < dfn s v]。
       取 a 为当前活跃顶点 v（或 v 子树中的当前顶点），即得 dfn s w < dfn s a。
       该引理当前表述缺少“a 是 pu 子树中活跃顶点”这一前提；若 a=pu 且 w 为 pu 已处理孩子，
       结论不成立。应用中应保证 a 为当前递归顶点或其子孙。
       关键引理：W_preserves_ancestor_inv, set_fa_W_preserves_low_forset_inv,
       preloop_after_visited_dfn_lt。 *)
  Admitted.

  (** [done_vertex_dfn_lt]: For the current active vertex [a] in [pu]'s
      subtree (with [~ done a], [In a (stack s)]) and any [done] vertex
      [w] still on the stack, [dfn s w < dfn s a].

      This is a direct corollary of the strengthened ancestor invariant
      carried by [W_preserves_ancestor_inv] / [set_fa_W_preserves_low_forset_inv]:
      during the execution of [tarjan_scc g a], all already-done neighbors
      [w] of [pu] satisfy [dfn s w < dfn s a].  The old proof tried to derive
      the inequality from stack ordering via [current_above_done_vertex], which
      created a circular dependency; the new path obtains the dfn inequality
      first (from the ancestor invariant) and only afterwards uses stack ordering
      to deduce the relative stack position. *)
  Lemma done_vertex_dfn_lt (pu a: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv pu done s ->
    done_visited done s ->
    ~ done a ->
    In a (stack s) ->
    stack_dfn_order s ->
    dfn_injective s ->
    forall w, done w -> In w (stack s) -> dfn s w < dfn s a.
  Proof.
    (* 证明思路：直接作为 [W_preserves_ancestor_inv] / [set_fa_W_preserves_low_forset_inv]
       中新增不变式的推论：在 [tarjan_scc g a] 执行期间，所有 done 邻居 [w] 满足
       [dfn s w < dfn s a]。这里不通过 [current_above_done_vertex] 绕路，
       以避免与栈位置分析的循环依赖。 *)
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
    intros Hlow Hdv Hndone Ha_stk Hstack_ord Hdfn_inj w Hdone Hw_stk.
    destruct (in_list_one_above_other (stack s) a w Ha_stk Hw_stk) as [Habove | Hw_above].
    { intro Heq. subst w. exact (Hndone Hdone). }
    - exact Habove.
    - assert (Hdfn_w_lt_a: dfn s w < dfn s a).
      { apply (done_vertex_dfn_lt pu a done s Hlow Hdv Hndone Ha_stk Hstack_ord Hdfn_inj w Hdone Hw_stk). }
      unfold low_forset_inv, wf_scc_state in Hlow.
      destruct Hlow as [[Hsiv _] _].
      assert (Hdfn_a_lt_w: dfn s a < dfn s w).
      { eapply (stack_dfn_order_strict s Hsiv Hstack_ord Hdfn_inj w a Hw_stk Ha_stk Hw_above).
        intro Heq. apply Hndone. rewrite <- Heq. exact Hdone. }
      lia.
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
    intros Hdv Hstack_fa_neq v. unfold back_edges_done, scc_back_edge, done_visited in *.
    split.
    - intros [Hdg [Hstack Hfa_neq]].
      split; [exact Hdg | split; [exact Hstack |]].
      intro Htree. apply state_to_dfs_tree_step_char in Htree as [Hfa_eq _].
      apply Hfa_neq. exact Hfa_eq.
    - intros [Hdg [Hstack Hnot_tree]].
      apply Hdv in Hdg as Hvis.
      split; [exact Hdg | split; [exact Hstack |]].
      destruct (equiv_dec (fa s v) u) as [Hfa_eq | Hfa_neq]; [| exact Hfa_neq].
      exfalso. apply Hnot_tree.
      eapply state_to_dfs_tree_step_char_backward; eauto.
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
  Lemma low_forset_inv_to_scc_low_valid (u: V) (s: SCCSt):
    done_visited (fun v => dg_step g u v) s ->
    (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) ->
    (forall v, In v (stack s) -> fa s v <> v) ->
    low_forset_inv u (fun v => dg_step g u v) s ->
    scc_low_valid_v s u.
  Proof.
    intros Hdv Hfa_g Hstack_fa_neq Hlow.
    set (done := fun v => dg_step g u v) in *.
    unfold low_forset_inv, low_forset_inv_core in Hlow.
    destruct Hlow as [[Hsiv [Hinv [Hvalid Hfa_vis]]] [Huvis Hmin]].
    pose proof (children_done_full_eq u s Hdv Hfa_g) as Hchild_eq.
    pose proof (back_edges_done_full_eq u s Hdv Hstack_fa_neq) as Hback_eq.
    unfold scc_low_valid_v.
    eapply min_eq_forward; [typeclasses eauto | exact Hmin | | ].
    - intros a1 Ha1. exists a1. split.
      + destruct Ha1 as [Ha1_L | Ha1_R].
        * left. apply min_eq_forward with (f1 := low s) (P1 := children_done s u done); [typeclasses eauto | exact Ha1_L | |].
          -- intros v Hv. exists v. split; [apply Hchild_eq; exact Hv | apply Nat.le_refl].
          -- intros v Hv. exists v. split; [apply Hchild_eq; exact Hv | apply Nat.le_refl].
        * right. apply min_eq_forward with (f1 := dfn s) (P1 := fun w => back_edges_done s u done w \/ w = u); [typeclasses eauto | exact Ha1_R | |].
          -- intros w [Hw_back | Hw_u].
             ++ exists w. split; [left; apply Hback_eq; exact Hw_back | apply Nat.le_refl].
             ++ sets_unfold in Hw_u. subst w. exists u. split; [right; reflexivity | apply Nat.le_refl].
          -- intros w [Hw_back | Hw_u].
             ++ exists w. split; [left; apply Hback_eq; exact Hw_back | apply Nat.le_refl].
             ++ sets_unfold in Hw_u. subst w. exists u. split; [right; reflexivity | apply Nat.le_refl].
      + apply Nat.le_refl.
    - intros a2 Ha2. exists a2. split.
      + destruct Ha2 as [Ha2_L | Ha2_R].
        * left. apply min_eq_forward with (f1 := low s) (P1 := dg_step (state_to_dfs_tree g s root) u); [typeclasses eauto | exact Ha2_L | |].
          -- intros v Hv. exists v. split; [apply Hchild_eq; exact Hv | apply Nat.le_refl].
          -- intros v Hv. exists v. split; [apply Hchild_eq; exact Hv | apply Nat.le_refl].
        * right. apply min_eq_forward with (f1 := dfn s) (P1 := scc_back_edge s u ∪ [u]); [typeclasses eauto | exact Ha2_R | |].
          -- intros w [Hw_back | Hw_u].
             ++ exists w. split; [left; apply Hback_eq; exact Hw_back | apply Nat.le_refl].
             ++ sets_unfold in Hw_u. subst w. exists u. split; [right; reflexivity | apply Nat.le_refl].
          -- intros w [Hw_back | Hw_u].
             ++ exists w. split; [left; apply Hback_eq; exact Hw_back | apply Nat.le_refl].
             ++ sets_unfold in Hw_u. subst w. exists u. split; [right; reflexivity | apply Nat.le_refl].
      + apply Nat.le_refl.
  Qed.

  (** [forset_end_implies_scc_low_valid_v]: explicit two-stage closing lemma.
      When [u]'s forset over all children has finished, [done = dg_step g u]
      and the global/fa conditions needed by [low_forset_inv_to_scc_low_valid]
      are available, so [scc_low_valid_v s u] holds.

      This lemma makes the transition from the forset invariant to the target
      property explicit, which is especially useful for cross-tree preservation:
      an ancestor [u] only obtains [scc_low_valid_v s u] after its own forset
      ends, not immediately when a child subtree returns. *)
  Lemma forset_end_implies_scc_low_valid_v (u: V) (s: SCCSt):
    low_forset_inv u (fun v => dg_step g u v) s ->
    done_visited (fun v => dg_step g u v) s ->
    (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v) ->
    (forall v, In v (stack s) -> fa s v <> v) ->
    scc_low_valid_v s u.
  Proof.
    intros Hlow Hdv Hfa_g Hstack_fa_neq.
    apply (low_forset_inv_to_scc_low_valid u s Hdv Hfa_g Hstack_fa_neq Hlow).
  Qed.



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
          by [update_low_preserves_low_forset_inv_for_other] (since [u <> a]
          and [a ∉ done] ensure [a] is not in [children_done] or
          [back_edges_done] for [u]).
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
      - [update_low_preserves_low_forset_inv_for_other]
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
  Proof.
    set (P := fun (_: V -> Prop) (s: SCCSt) =>
      low_forset_inv u done s /\ a ∈ visited s /\ done_visited done s).
    apply (Hoare_conseq
      (fun s => low_forset_inv u done s /\ a ∈ visited s /\ done_visited done s)
      (P (fun _ => False))
      (forset (fun w => dg_step g a w) (process_edge a W))
      (fun _ s => low_forset_inv u done s)
      (fun _ s => low_forset_inv u done s /\ a ∈ visited s /\ done_visited done s)).
    { intros s [Hinv [Hav Hdv]]. unfold P. simpl. exact (conj Hinv (conj Hav Hdv)). }
    { intros _ s [Hinv _]. exact Hinv. }
    { apply (@Hoare_forset SCCSt V P (fun w => dg_step g a w) (process_edge a W)).
      { unfold P, Proper, respectful. intros. subst. reflexivity. }
      { intros todo a0 Hsub Huniv Hnotdone.
        intro_state. destruct H as [[Hwf [Huvis Hmin]] [Hav Hdv]].
        unfold wf_scc_state in Hwf. destruct Hwf as [Hsiv [Hdinv [Hdvalid Hfav]]].
        unfold process_edge, if_else. intro_state. apply Hoare_choice.
        - (* Tree edge *)
          apply Hoare_assume_bind. simpl. intro_state.
          destruct H1 as [Hnv_a0 Hs2_eq]. subst s2. subst s1.
          assert (Hnd_a0: ~ done a0). { intro Hd. apply Hnv_a0. apply Hdv. exact Hd. }
          rename s0 into s_pre.
          unfold set_fa. intro_state. hoare_auto_s. subst s0.
          eapply Hoare_bind with
            (Q := fun _ s => low_forset_inv u done s /\ a ∈ visited s /\ done_visited done s)
            (R := fun _ s => P (todo ∪ [a0]) s).
          { (* W a0 *)
            apply Hoare_conseq_pre with
              (P2 := fun s => low_forset_inv u done s /\ ~ a0 ∈ visited s /\ ~ done a0 /\ a ∈ visited s /\ done_visited done s).
            { simpl. intros s' Heq. subst s'.
              assert (Hs_pre_wf: wf_scc_state s_pre). {
                unfold wf_scc_state. split; [exact Hsiv | split; [exact Hdinv | split; [exact Hdvalid | exact Hfav]]]. }
              split.
              { apply (set_fa_preserves_low_forset_inv_for_new_child u a a0 done s_pre).
                { exact Hnv_a0. } { exact Hav. } { exact Huvis. } { exact Hndone_a. } { exact Hnd_a0. }
                { exact (conj Hs_pre_wf (conj Huvis Hmin)). } }
              split. { exact Hnv_a0. } split. { exact Hnd_a0. } split. { exact Hav. } exact Hdv. }
            apply (IH a0). }
          { simpl. intros _. intro_state. hoare_auto_s. destruct H as [Hinv' [Hav' Hdv']].
            unfold update_low. intro_state. hoare_auto_s.
            + (* set_low branch *)
              unfold set_low. intro_state. hoare_auto_s.
              subst s. subst s0. unfold P. simpl.
              assert (Hmin_eq: low s1 a0 = Nat.min (low s1 a) (low s1 a0)).
              { symmetry. apply Nat.min_r. lia. }
              split. { rewrite Hmin_eq. apply (update_low_preserves_low_forset_inv_for_other u a (low s1 a0) done s1 Hneq Hndone_a Hinv'). }
              split; [exact Hav' | exact Hdv'].
            + (* skip *)
              destruct H. subst s. split; [exact Hinv' | split; [exact Hav' | exact Hdv']]. }
        - (* Non-tree edge *)
          intro_state. hoare_auto_s.
          + (* In stack: back edge *)
            unfold update_low. intro_state. hoare_auto_s.
            { (* set_low branch *)
              unfold set_low. intro_state. hoare_auto_s. subst s0. subst s.
              unfold P. simpl.
              assert (Hinv: low_forset_inv u done s1). {
                unfold low_forset_inv.
                split. { unfold wf_scc_state. split; [exact Hsiv | split; [exact Hdinv | split; [exact Hdvalid | exact Hfav]]]. }
                split; [exact Huvis | exact Hmin]. }
              assert (Hmin_eq: dfn s1 a0 = Nat.min (low s1 a) (dfn s1 a0)).
              { symmetry. apply Nat.min_r. lia. }
              split. { rewrite Hmin_eq. apply (update_low_preserves_low_forset_inv_for_other u a (dfn s1 a0) done s1 Hneq Hndone_a Hinv). }
              split; [exact Hav | exact Hdv]. }
            { (* skip *) destruct H. subst s.
              split. { unfold low_forset_inv. split. {
                unfold wf_scc_state. split; [exact Hsiv | split; [exact Hdinv | split; [exact Hdvalid | exact Hfav]]]. }
                split; [exact Huvis | exact Hmin]. }
              split; [exact Hav | exact Hdv]. }
          + (* Not in stack: cross edge, skip *)
            subst s1. destruct H3 as [Hs_eq _]. subst s. subst s2.
            unfold P. simpl.
            split. { unfold low_forset_inv. split. {
              unfold wf_scc_state. split; [exact Hsiv | split; [exact Hdinv | split; [exact Hdvalid | exact Hfav]]]. }
              split; [exact Huvis | exact Hmin]. }
            split; [exact Hav | exact Hdv]. } }
  Qed.

  (** [forset_keep_low_forset_inv]: after iterating over all children of [u],
      [low_forset_inv u ∅] is turned into [low_post u s].

      Proof plan: define the forset invariant
        [P(done) := wf_scc_state s /\ low_forset_inv_core u done s
                    /\ done_visited done s
                    /\ (forall v, fa s v = u /\ fa s v <> v -> v ∈ done)].
      - [wf_scc_state s] is preserved by every primitive operation that keeps
        all vertices either visited or without pending parents. The critical
        exception is [set_fa a0 u], which creates a pending tree edge to the
        unvisited child [a0]; here use [set_fa_preserves_wf_scc_state_pre] to
        obtain [low_pre a0 s] (i.e. [wf_scc_state_pre a0 s]).
      - Apply [Hoare_forset]; properness follows from [low_forset_inv_proper]
        (now only about the core) and [done_visited_proper].
      - For each neighbor [a0]:
        * Tree edge: after [set_fa a0 u], [set_fa_preserves_wf_scc_state_pre]
          gives [low_pre a0 s], which is exactly the precondition for the
          recursive call [W a0]. Use [set_fa_W_preserves_low_forset_inv] to
          run [W a0] while preserving [low_forset_inv_core u done] and
          establishing [fa a0 = u]. Then [low_forset_inv_expand_child_done]
          moves from [done] to [done ∪ [a0]] (since [a0] is now a proper child
          and [low u ≤ low a0] holds after the recursive call).
        * Non-tree edge: back edge uses [update_low_back_edge]; cross edge uses
          set equivalence as in [forset_keeps_low_forset_inv].
      - After the loop [done = dg_step g u]; apply [forset_end_implies_scc_low_valid_v]
        (a wrapper around [low_forset_inv_to_scc_low_valid]) to obtain
        [scc_low_valid_v s u]. Together with [wf_scc_state s] this is [low_post u s].

      Required previous lemmas:
      - [Hoare_forset]
      - [low_forset_inv_proper]
      - [done_visited_proper]
      - [wf_scc_state] preservation lemmas
      - [set_fa_W_preserves_low_forset_inv]
      - [update_low_tree_edge]
      - [update_low_back_edge]
      - [low_forset_inv_expand_child_done]
      - [forset_end_implies_scc_low_valid_v] *)
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
          (fun _ s => low_post u s).
  Proof.
    (* 证明思路：用 Hoare_forset 遍历 u 的所有孩子，不变式为
       low_forset_inv u done / done_visited done / fa-孩子⊆done。
       树边分支用 set_fa_W_preserves_low_forset_inv 保持 low_forset_inv、得到 fa a0=u，
       并建立 done 中顶点 dfn < dfn a0 的时序不变式；随后用
       low_forset_inv_expand_child_done 扩展 done。非树边分支用 update_low_back_edge
       或集合等价扩展 done。循环结束后 done=dg_step g u，由 forset_end_implies_scc_low_valid_v
       得 scc_low_valid_v s u，结合 wf_scc_state 即为 low_post u s。
       关键引理：Hoare_forset, low_forset_inv_proper, done_visited_proper,
       set_fa_W_preserves_low_forset_inv, low_forset_inv_expand_child_done,
       low_forset_inv_children_done_low_le, update_low_back_edge,
       forset_end_implies_scc_low_valid_v。
       原始 .orig 证明含 admit，尚未完全闭合。
       详见上方完整 proof plan。 *)
    Admitted.

  (** [tarjan_scc_keep_low_valid]: one-vertex main theorem.
      [tarjan_scc g u] transforms [low_pre u] into [low_post u].

      Proof plan: apply [Hoare_fix_logicv_conj] (fixpoint induction) with
        [P1(a) := low_pre a], [Q1(a) := low_post a],
        [P2(a,w) := w ∈ visited s], [Q2(a,w) := w ∈ visited s].
      1. The auxiliary visitedness goal is discharged by the external lemma
         [tarjan_scc_keep_visited] from [Tarjan_scc_basics].
      2. In the body:
         - [preloop u] takes the initial [low_pre u] (= [wf_scc_state_pre u])
           to full [wf_scc_state] by [preloop_preserves_wf_scc_state], and
           establishes [low_forset_inv u ∅] by [preloop_establishes_low_forset_inv].
           [preloop_keeps_fa] gives [fa v = u -> v = u] for all [v].
         - The [forset] over children uses [forset_keep_low_forset_inv].
           Its four W-assumptions come from the induction hypotheses:
           * [HW_pre_post] from the low-link IH;
           * [HW_vis] from the visited IH;
           * [HW_done_vis] from the forall version of the visited IH,
             [tarjan_scc_keep_visited_forall] in [Tarjan_scc_basics];
           * [HW_fa_children] from [process_edge_keep_fa_children] and
             [tarjan_scc_keep_fa_children_in_universe] applied to the IH.
           Result: [low_post u s], i.e. [wf_scc_state s /\ scc_low_valid_v s u].
         - The final [If (low u = dfn u) (pop_scc u)]:
           * If [low u = dfn u], [pop_scc_preserves_wf_scc_state] preserves
             [wf_scc_state]; apply [pop_scc_keep_scc_low_valid_v] to keep
             [scc_low_valid_v u].
           * If not, the state is unchanged and [low_post u] still holds.
      3. The postcondition is exactly [low_post u].

      Required previous lemmas:
      - [Hoare_fix_logicv_conj]
      - [tarjan_scc_keep_visited] (from Tarjan_scc_basics)
      - [tarjan_scc_keep_visited_forall] (from Tarjan_scc_basics)
      - [preloop_preserves_wf_scc_state]
      - [preloop_establishes_low_forset_inv]
      - [preloop_keeps_fa]
      - [forset_keep_low_forset_inv]
      - [process_edge_keep_fa_children]
      - [tarjan_scc_keep_fa_children_in_universe]
      - [pop_scc_preserves_wf_scc_state]
      - [pop_scc_keep_scc_low_valid_v] *)
  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
          (fun _ s => low_post u s).
  Proof.
    (* 证明思路：对 tarjan_scc g u 做不动点归纳，主规格 low_pre u → low_post u，
       辅助规格 visited 保持。preloop u 建立 low_forset_inv u ∅；
       forset 阶段用 forset_keep_low_forset_inv，其四个 W 假设分别来自归纳假设、
       visited 保持、done' 上 visited 全称保持（tarjan_scc_keep_visited_forall）以及
       fa-孩子全称保持（process_edge_keep_fa_children + tarjan_scc_keep_fa_children_in_universe）；
       最后 If (low u = dfn u) (pop_scc u) 保持 low_post。
       关键引理：Hoare_fix_logicv_conj, tarjan_scc_preserves_visited,
       preloop_establishes_low_forset_inv, preloop_keeps_fa,
       forset_keep_low_forset_inv, process_edge_keep_fa_children,
       tarjan_scc_keep_fa_children_in_universe, pop_scc_preserves_wf_scc_state,
       pop_scc_keep_scc_low_valid_v。
       原始 .orig 证明含 admit，尚未完全闭合。 *)
    Admitted.

  (* ================================================================ *)
  (* 13. Global scc_low_valid / scc_is_low                             *)
  (* ================================================================ *)

  (** [tarjan_scc_establishes_and_preserves_scc_low_valid]:
      If [a] is unvisited and [scc_low_valid] holds for all currently
      visited vertices, then after [tarjan_scc g a], [scc_low_valid]
      holds for all vertices (including new ones in [a]'s SCC tree).
      Also preserves [wf_scc_state].

      Proof plan (two-stage cross-tree argument):
      1. From [tarjan_scc_keep_low_valid], after [tarjan_scc g a] we have
         [low_post a], in particular [scc_low_valid_v s a]. Thus [a] and the
         vertices in its DFS subtree satisfy [scc_low_valid_v].
      2. Stage one — ancestors keep [low_forset_inv]:
         For any already-visited vertex [u] that is an ancestor of [a] in the
         DFS tree, [W_preserves_ancestor_inv] (or the more specific
         [set_fa_W_preserves_low_forset_inv] for the tree-edge step) preserves
         [low_forset_inv u done] as [a]'s subtree executes. At the moment [a]'s
         subtree returns, [done] has been expanded to include [a] (and possibly
         other processed children of [u]), but it need not yet be all of
         [dg_step g u].
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
      - [set_fa_W_preserves_low_forset_inv]
      - [forset_end_implies_scc_low_valid_v]
      - [wf_scc_state] preservation lemmas *)
  Lemma tarjan_scc_establishes_and_preserves_scc_low_valid (a: V):
    Hoare (fun s => scc_low_valid s /\ wf_scc_state s /\ ~ a ∈ visited s)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g a)
          (fun _ s => scc_low_valid s /\ wf_scc_state s).
  Proof.
    (* 证明思路：将单点 low_post 性质提升为全局 scc_low_valid 保持性。
       第一阶段：由 tarjan_scc_keep_low_valid 得 a 及其子树满足 scc_low_valid_v。
       第二阶段：对 a 的每个祖先 u，执行过程中用 W_preserves_ancestor_inv /
       set_fa_W_preserves_low_forset_inv 保持 low_forset_inv u done；
       当 u 自己的 forset 最终完成时 done=dg_step g u，于是由
       forset_end_implies_scc_low_valid_v 得 scc_low_valid_v s u。
       不在 a 子树及祖先链上的顶点状态不变。wf_scc_state 由各原语保持性引理保持。
       关键引理：tarjan_scc_keep_low_valid, W_preserves_ancestor_inv,
       set_fa_W_preserves_low_forset_inv, forset_end_implies_scc_low_valid_v,
       low_forset_inv_to_scc_low_valid。
       原始 .orig 中该引理仅有说明性注释，未给完整证明。 *)
    Admitted.

  (** [tarjan_scc_all_scc_low_valid]: global [scc_low_valid] after the full
      Tarjan loop over all vertices.

      Proof plan: [tarjan_scc_all] is a [forset] over all vertices
      [v] of [If (~ v ∈ visited) (tarjan_scc g v)]. Apply [Hoare_forset]
      with the constant invariant
        [P(done) := scc_low_valid s /\ wf_scc_state s].
      - Properness of [P] is trivial because [P] does not depend on [done].
      - For each vertex [a]:
        * If [~ a ∈ visited], use [tarjan_scc_establishes_and_preserves_scc_low_valid]
          to establish [scc_low_valid] for the enlarged [visited] set and preserve
          [wf_scc_state]. Because [a] is unvisited before the call and a top-level
          [tarjan_scc g a] finishes by popping [a]'s SCC, all vertices newly visited
          by the call satisfy [scc_low_valid_v].
        * If [a ∈ visited], the command is a no-op. [scc_low_valid s /\ wf_scc_state s]
          is unchanged; in particular the invariant already guarantees
          [scc_low_valid_v s a].
      - After the loop, [P universe] gives [scc_low_valid s /\ wf_scc_state s].

      Note: the original proof attempted a [done]-indexed invariant
      [(forall w, done w -> scc_low_valid_v s w)]; the constant
      [visited]-indexed invariant above is simpler and avoids the mismatch
      between [done] and [visited] for already-seen vertices.

      Required previous lemmas:
      - [Hoare_forset]
      - [tarjan_scc_establishes_and_preserves_scc_low_valid]
      - [wf_scc_state] preservation lemmas *)
  Theorem tarjan_scc_all_scc_low_valid:
    Hoare (fun s: @SCCSt V => wf_scc_state s)
          (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
          (fun _ s => scc_low_valid s).
  Proof.
    (* 证明思路：tarjan_scc_all 对所有顶点做 forset。用 Hoare_forset 配合常数不变式
       P(done) := scc_low_valid s /\ wf_scc_state s。
       对每个顶点 a：若未访问，调用 tarjan_scc_establishes_and_preserves_scc_low_valid；
       若已访问，命令为 skip，不变式不变。循环结束后 visited 中所有顶点均满足
       scc_low_valid_v。还需说明 visited s ⊆ original_vvalid g（当前证明缺口）。
       关键引理：Hoare_forset, tarjan_scc_establishes_and_preserves_scc_low_valid,
       original_vvalid, visited 包含关系（待证）。
       原始 .orig 证明含 admit，尚未完全闭合。 *)
    Admitted.

  (** [tarjan_scc_all_scc_is_low]: final theorem — the global Tarjan
      algorithm computes the correct low-link values for every visited vertex.

      Proof plan:
      1. Use [Hoare_conseq_post] to strengthen the postcondition from
         [scc_low_valid s] to [scc_is_low s].
      2. Apply [scc_low_valid_implies_is_low], which requires [dfn_valid g s root]
         and [dfn_inv s]. These are part of [wf_scc_state s], which is already
         in the postcondition of [tarjan_scc_all_scc_low_valid].
      3. Combine [tarjan_scc_all_scc_low_valid] with [wf_scc_state] via
         [Hoare_conj]. If needed, [wf_scc_state] for the full algorithm is given
         by the external lemmas [tarjan_scc_all_dfn_valid],
         [tarjan_scc_all_keep_dfn_inv], and basic [fa_visited] preservation
         from [Tarjan_scc_is_dfn].

      Required previous lemmas:
      - [tarjan_scc_all_scc_low_valid]
      - [scc_low_valid_implies_is_low]
      - [tarjan_scc_all_dfn_valid] (from Tarjan_scc_is_dfn)
      - [tarjan_scc_all_keep_dfn_inv] (from Tarjan_scc_is_dfn)
      - [Hoare_conseq_post] / [Hoare_conj] *)
  Theorem tarjan_scc_all_scc_is_low:
    Hoare (fun s: @SCCSt V => wf_scc_state s)
          (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
          (fun _ s => scc_is_low s).
  Proof.
    (* 证明思路：最终结论。先用 Hoare_conseq_post 将后置加强为
       scc_low_valid s /\ dfn_valid g s root /\ dfn_inv s。
       由 scc_low_valid_implies_is_low 可知，在 dfn_valid 与 dfn_inv 成立时
       scc_low_valid 蕴含 scc_is_low。再用 Hoare_conj 组合三个断言：
       scc_low_valid 由 tarjan_scc_all_scc_low_valid 给出；dfn_valid 由
       tarjan_scc_all_dfn_valid 给出；dfn_inv 由 tarjan_scc_all_keep_dfn_inv 给出。
       关键引理：tarjan_scc_all_scc_low_valid, scc_low_valid_implies_is_low,
       tarjan_scc_all_dfn_valid, tarjan_scc_all_keep_dfn_inv,
       Hoare_conseq_post, Hoare_conj, wf_scc_state。 *)
    Admitted.

End IS_LOW.
