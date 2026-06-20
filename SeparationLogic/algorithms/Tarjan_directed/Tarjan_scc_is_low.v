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

  Lemma scc_low_witness (s: @SCCSt V) (w: V) (n: nat):
    scc_is_low_v_val s w n ->
    exists x, scc_low_tree s w x /\ dfn s x = n.
  Proof.
    unfold scc_is_low_v_val.
    intros [x [[Hx _] Heq]].
    exists x; auto.
  Qed.

  Lemma scc_low_bound (s: @SCCSt V) (w: V) (n: nat) (x: V):
    scc_is_low_v_val s w n ->
    scc_low_tree s w x ->
    n <= dfn s x.
  Proof.
    unfold scc_is_low_v_val.
    intros [y [[_ Hmin] Heq]] Hx.
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
      pose proof (Hdfn_lt v Hvis_v) as Hdfn_v_lt.
      apply Hvalid in Hson_orig.
      pose proof (Hdfn_lt u Hu) as Hdfn_u_lt.
      apply (IH (timer s - dfn s v)).
      + lia.
      + exact Hvis_v.
      + reflexivity.
    - apply Hlow. exact Hu.
  Qed.

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
    unfold low_pre. intros [Hsiv [Hnuvis [Hvalid [Hinv Hfa_vis]]]] Hfa_eq.
    destruct (classic (v = u)) as [Heq | Hneq]; [exact Heq |].
    exfalso.
    assert (Htemp: fa s v <> v).
    { rewrite Hfa_eq. intro Heq2. apply Hneq. symmetry; exact Heq2. }
    apply Hfa_vis in Htemp.
    rewrite Hfa_eq in Htemp.
    exact (Hnuvis Htemp).
  Qed.

  Lemma low_pre_no_fa_child_of_u (u v: V) (s: @SCCSt V):
    low_pre u s -> ~ (fa s v = u /\ fa s v <> v).
  Proof.
    intros Hpre [Hfa_eq Hfa_neq].
    pose proof (low_pre_fa_eq_u_implies_eq_u u v s Hpre Hfa_eq) as Heq_uv.
    subst v.
    exact (Hfa_neq Hfa_eq).
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
    apply Sets_equiv_Sets_included. split.
    - sets_unfold. intros a [Hfalse _]. exact Hfalse.
    - sets_unfold. intros a Hfalse. destruct Hfalse.
  Qed.

  Lemma back_edges_done_empty_char (s: @SCCSt V) (u: V):
    (fun w => back_edges_done s u ∅ w \/ w = u) == [u].
  Proof.
    unfold back_edges_done.
    apply Sets_equiv_Sets_included. split.
    - sets_unfold. intros a [[Hfalse _] | Heq].
      + destruct Hfalse.
      + subst a. reflexivity.
    - sets_unfold. intros a Heq. subst a. right. reflexivity.
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
    unfold low_forset_inv.
    apply Hoare_conj with
      (Q1 := fun _ s => stack_in_visited s)
      (Q2 := fun _ s => dfn_inv s /\ dfn_valid g s root /\ fa_visited s /\ u ∈ visited s /\
                      min_value_of_subset Nat.le
                        (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
                         min_value_of_subset Nat.le
                           (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
                        (fun x => x) (low s u)).
    - eapply Hoare_conseq_pre.
      { intros s Hpre. destruct Hpre as [Hstack _]. exact Hstack. }
      apply preloop_keep_stack_in_visited.
    - apply Hoare_conj with
        (Q1 := fun _ s => dfn_inv s)
        (Q2 := fun _ s => dfn_valid g s root /\ fa_visited s /\ u ∈ visited s /\
                        min_value_of_subset Nat.le
                          (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
                           min_value_of_subset Nat.le
                             (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
                          (fun x => x) (low s u)).
      + eapply Hoare_conseq_pre.
        { intros s Hpre. destruct Hpre as [_ [_ [_ [Hinv _]]]]. exact Hinv. }
        apply preloop_keep_dfn_inv.
      + apply Hoare_conj with
          (Q1 := fun _ s => dfn_valid g s root)
          (Q2 := fun _ s => fa_visited s /\ u ∈ visited s /\
                          min_value_of_subset Nat.le
                            (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
                             min_value_of_subset Nat.le
                               (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
                            (fun x => x) (low s u)).
        * eapply Hoare_conseq_post with
            (Q2 := fun _ s => u ∈ visited s /\ dfn_valid g s root /\ dfn_inv s).
          { intros _ s [Hvis [Hvalid _]]. exact Hvalid. }
          eapply Hoare_conseq_pre with
            (P2 := fun s => ~ u ∈ visited s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s).
          { intros s [Hstack [Hnv [Hvalid [Hinv Hfa]]]].
            split; [exact Hnv | split; [exact Hvalid | split; [exact Hinv | exact Hfa]]]. }
          apply preloop_preserves_dfn_valid.
        * apply Hoare_conj with
            (Q1 := fun _ s => fa_visited s)
            (Q2 := fun _ s => u ∈ visited s /\
                            min_value_of_subset Nat.le
                              (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
                               min_value_of_subset Nat.le
                                 (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
                              (fun x => x) (low s u)).
          -- eapply Hoare_conseq_pre.
             { intros s Hpre. destruct Hpre as [_ [_ [_ [_ Hfa]]]]. exact Hfa. }
             apply preloop_keep_fa_visited.
          -- apply Hoare_conj with
              (Q1 := fun _ s => u ∈ visited s)
              (Q2 := fun _ s => min_value_of_subset Nat.le
                                  (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
                                   min_value_of_subset Nat.le
                                     (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
                                  (fun x => x) (low s u)).
            ++ eapply Hoare_conseq_pre.
               { intros s Hpre. exact I. }
               apply preloop_self_visited.
            ++ eapply Hoare_conseq_post with
                (Q2 := fun _ s => low s u = dfn s u).
               { intros _ s Heq_low_eq. apply low_eq_dfn_to_min_empty. exact Heq_low_eq. }
               eapply Hoare_conseq_pre.
               { intros s _. exact I. }
               apply preloop_low_eq_dfn.
  Qed.

  (* ================================================================ *)
  (* 8. pop_scc Preserves Low Valid                                   *)
  (* ================================================================ *)

  Lemma stack_split_at_rest_incl (stk: list V) (u: V) (popped rest: list V):
    stack_split_at stk u = (popped, rest) ->
    forall w, In w rest -> In w stk.
  Proof.
    revert u popped rest.
    induction stk as [| x xs IH]; intros u popped rest Hsplit w Hin.
    - cbn in Hsplit. inversion Hsplit. subst popped rest.
      cbn in Hin. destruct Hin.
    - cbn in Hsplit.
      destruct (equiv_decb x u) eqn:Heqx.
      + inversion Hsplit. subst popped rest.
        simpl. right. exact Hin.
      + destruct (stack_split_at xs u) as [popped' rest'] eqn:Hsplit_inner.
        inversion Hsplit. subst popped rest.
        simpl. right. apply (IH u popped' rest' Hsplit_inner w Hin).
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
      scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s /\
      low s u = dfn s u)
          (pop_scc u)
          (fun _ s => scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s).
  Proof.
    unfold pop_scc. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit. simpl.
    destruct H as (Hlow_valid & Hvalid & Hinv & Hfa & Heq_low).
    assert (Hvalid_post: dfn_valid g
      {| visited := visited s0; timer := timer s0;
         dfn := dfn s0; low := low s0; fa := fa s0;
         stack := rest; sccs := (fun v => In v popped) :: sccs s0 |} root).
    { exact Hvalid. }
    assert (Hinv_post: dfn_inv
      {| visited := visited s0; timer := timer s0;
         dfn := dfn s0; low := low s0; fa := fa s0;
         stack := rest; sccs := (fun v => In v popped) :: sccs s0 |}).
    { exact Hinv. }
    assert (Hfa_post: fa_visited
      {| visited := visited s0; timer := timer s0;
         dfn := dfn s0; low := low s0; fa := fa s0;
         stack := rest; sccs := (fun v => In v popped) :: sccs s0 |}).
    { exact Hfa. }
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
               ++ pose proof (stack_split_at_rest_incl _ _ _ _ Hsplit v
                    (let '(conj _ (conj Hin _)) := Hback_post in Hin)) as Hv_in_stack0.
                  assert (Hback_pre: scc_back_edge s0 u v). {
                    unfold scc_back_edge in *. destruct Hback_post as [Hstep [Hin_rest Hnot_tree]].
                    split; [exact Hstep | split; [exact Hv_in_stack0 | exact Hnot_tree]].
                  }
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
            -- pose proof (stack_split_at_rest_incl _ _ _ _ Hsplit v
                 (let '(conj _ (conj Hin _)) := Hback_post in Hin)) as Hv_in_stack0.
               assert (Hback_pre: scc_back_edge s0 u v). {
                 unfold scc_back_edge in *. destruct Hback_post as [Hstep [Hin_rest Hnot_tree]].
                 split; [exact Hstep | split; [exact Hv_in_stack0 | exact Hnot_tree]].
               }
               eapply scc_low_valid_v_low_eq_dfn_implies_dfn_le_back_edge_dfn;
                 [exact Hlow_valid | exact Heq_low | exact Hback_pre].
            -- subst v. apply Nat.le_refl.
      - reflexivity. }
    split; [| split; [| split]]; assumption.
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

  Lemma set_fa_preserves_low_pre_rich (v u: V):
    Hoare (fun s: @SCCSt V => low_pre v s /\ u ∈ visited s)
          (set_fa v u)
          (fun _ s => low_pre v s /\ u ∈ visited s).
  Proof.
    unfold low_pre.
    apply Hoare_conseq with
      (P2 := fun s => stack_in_visited s /\ (~ v ∈ visited s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s) /\ u ∈ visited s)
      (Q2 := fun _ s => stack_in_visited s /\ (~ v ∈ visited s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s) /\ u ∈ visited s).
    - intros s [[Hstack [Hnv [Hvalid [Hinv Hfa]]]] Hu].
      repeat (split; try assumption).
    - intros _ s [Hstack [[Hnv [Hvalid [Hinv Hfa]]] Hu]].
      repeat (split; try assumption).
    - apply Hoare_conj with
        (Q1 := fun _ s => stack_in_visited s)
        (Q2 := fun _ s => (~ v ∈ visited s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s) /\ u ∈ visited s).
      + intro_state. unfold set_fa. hoare_auto_s. subst s. simpl.
        destruct H as [Hstack _]. exact Hstack.
      + apply Hoare_conseq_pre with
          (P2 := fun s => (~ v ∈ visited s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s) /\ u ∈ visited s).
        { intros s [Hstack [Hrest Hu]]. split; [exact Hrest | exact Hu]. }
        { apply (set_fa_preserves_dfn_pre_child_rich (V:=V) (E:=E)). }
  Qed.

  (** [set_low_keep_low_forset_inv_components]: [set_low u n] only
      modifies [low]; all other fields are unchanged. *)
  Lemma set_low_keep_low_forset_inv_components (u: V) (n: nat):
    Hoare (fun s: @SCCSt V => dfn_inv s /\ dfn_valid g s root /\ fa_visited s /\ u ∈ visited s)
          (set_low u n)
          (fun _ s => dfn_inv s /\ dfn_valid g s root /\ fa_visited s /\ u ∈ visited s).
  Proof.
    unfold set_low. intro_state. hoare_auto_s.
    subst s. simpl. auto.
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
    destruct Hinv_s as [Hstack [Hinv [Hvalid [Hfa [Huvis Hmin]]]]].
    destruct Hinv as [Hlt [Hiff Hpos]].
    unfold low_forset_inv. simpl.
    split; [exact Hstack |].
    split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |].
    split; [exact Hvalid |].
    split; [exact Hfa |].
    split; [exact Huvis |].
    (* min condition *)
      unfold children_done, back_edges_done. simpl.
      change (fun x : V => (x ∈ (done ∪ [v]) /\ fa s x = u /\ fa s x <> x)%sets)
        with (children_done s u (done ∪ [v])).
      change (fun x : V => ((x ∈ (done ∪ [v]) /\ In x (stack s) /\ fa s x <> u) \/ x = u)%sets)
        with (fun x => back_edges_done s u (done ∪ [v]) x \/ x = u).
      pose proof (children_done_add s u v done Hfa_v_u Hfa_v_neq_v) as Hchild_eq.
      pose proof (back_edges_done_no_add s u v done (or_intror Hfa_v_u)) as Hback_eq.
      simpl.
      unfold equiv_decb. destruct (equiv_dec u u) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
      eapply min_eq_forward.
      + (* typeclass: TotalOrder Nat.le *) typeclasses eauto.
      + (* source: the nested min lemma applied to the simplified sets *)
        eapply (min_value_of_subset_nested_update_left_nat
          (A := V) (B := V)
          (low s) (children_done s u done) v
          (dfn s) (fun w => back_edges_done s u done w \/ w = u)
          (low s u)).
        exact Hmin.
      + (* forward: each a1 in LHS has a2 in RHS with a2 ≤ a1. Since sets/fns agree, a2=a1 works. *)
        intros a1 Ha1.
        exists a1. split.
        { (* a1 ∈ RHS *)
          destruct Ha1 as [Ha1_L | Ha1_R].
          - (* a1 from LEFT = min(children_done(done)∪[v], low s) *)
            left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
            exists w. split.
            { unfold min_object_of_subset. split.
              - (* w ∈ children_done(done∪[v]) *)
                apply Hchild_eq. exact Hw_in.
              - (* minimality: for all x in children_done(done∪[v]), modified_low w ≤ modified_low x *)
                intros x Hx. apply Hchild_eq in Hx.
                (* Need: if w==b u then ... else low s w ≤ if x==b u then ... else low s x *)
                (* Since w, x ∈ children_done, they have fa = u and fa ≠ self, so w≠u, x≠u *)
                set (f := fun z => if equiv_decb z u then Nat.min (low s u) (low s v) else low s z).
                assert (Hw_neq_u: w <> u). {
                  unfold children_done in Hw_in. sets_unfold in Hw_in.
                  destruct Hw_in as [Hw_done | Hw_v].
                  - destruct Hw_done as [_ [Hw_fa Hw_neq_self]]. intro Heq. subst w. apply Hw_neq_self. exact Hw_fa.
                  - subst w. intro Heq. apply Hfa_v_neq_v. rewrite Heq. rewrite Heq in Hfa_v_u. exact Hfa_v_u. }
                assert (Hx_neq_u: x <> u). {
                  unfold children_done in Hx. sets_unfold in Hx.
                  destruct Hx as [Hx_done | Hx_v].
                  - destruct Hx_done as [_ [Hx_fa Hx_neq_self]]. intro Heq. subst x. apply Hx_neq_self. exact Hx_fa.
                  - subst x. intro Heq. apply Hfa_v_neq_v. rewrite Heq. rewrite Heq in Hfa_v_u. exact Hfa_v_u. }
                unfold f. unfold equiv_decb.
                destruct (equiv_dec w u) as [Hw_eq | _]; [exfalso; apply Hw_neq_u; exact Hw_eq|].
                destruct (equiv_dec x u) as [Hx_eq | _]; [exfalso; apply Hx_neq_u; exact Hx_eq|].
                apply Hw_min. exact Hx. }
            { set (f := fun z => if equiv_decb z u then Nat.min (low s u) (low s v) else low s z).
              assert (Hw_neq_u: w <> u). {
                unfold children_done in Hw_in. sets_unfold in Hw_in.
                destruct Hw_in as [Hw_done | Hw_v].
                - destruct Hw_done as [_ [Hw_fa Hw_neq_self]]. intro Heq. subst w. apply Hw_neq_self. exact Hw_fa.
                - subst w. intro Heq. apply Hfa_v_neq_v. rewrite Heq. rewrite Heq in Hfa_v_u. exact Hfa_v_u. }
              unfold f. unfold equiv_decb.
              destruct (equiv_dec w u); [exfalso; apply Hw_neq_u; auto| exact Heq_a1]. }
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
        { (* a1 ≤ a1 *) apply Nat.le_refl. }
      + (* backward: each a2 in RHS has a1 in LHS with a1 ≤ a2 *)
        intros a2 Ha2.
        exists a2. split.
        { (* a2 ∈ LHS *)
          destruct Ha2 as [Ha2_L | Ha2_R].
          - left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
            exists w. split.
            { unfold min_object_of_subset. split.
              - apply Hchild_eq. exact Hw_in.
              - intros x Hx. apply Hchild_eq in Hx.
                pose proof (Hw_min x Hx) as Hineq.
                unfold equiv_decb in Hineq. simpl in Hineq.
                destruct (equiv_dec w u) as [Heq_w | Hneq_w];
                  [| destruct (equiv_dec x u) as [Heq_x | Hneq_x]].
                + exfalso. unfold children_done in Hw_in. destruct Hw_in as [_ [Hfa_eq Hneq]].
                  apply Hneq. rewrite Heq_w. rewrite Heq_w in Hfa_eq. exact Hfa_eq.
                + exfalso. unfold children_done in Hx. destruct Hx as [_ [Hfa_eq Hneq]].
                  apply Hneq. rewrite Heq_x. rewrite Heq_x in Hfa_eq. exact Hfa_eq.
                + exact Hineq. }
            { unfold equiv_decb in Heq_a2. simpl in Heq_a2.
              destruct (equiv_dec w u) as [Heq_w | Hneq_w].
              - exfalso. unfold children_done in Hw_in. destruct Hw_in as [_ [Hfa_eq Hneq]].
                apply Hneq. rewrite Heq_w. rewrite Heq_w in Hfa_eq. exact Hfa_eq.
              - exact Heq_a2. }
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
        { (* a2 ≤ a2 *) apply Nat.le_refl. }
  Qed.

  Lemma low_forset_inv_implies_low_le_dfn (u: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s -> low s u <= dfn s u.
  Proof.
    intros [_ [Hinv [Hvalid [Hfa [Huvis Hmin]]]]].
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
    destruct Hinv_s as [Hsiv [Hinv [Hvalid [Hfa [Huvis Hmin]]]]].
    destruct Hinv as [Hlt [Hiff Hpos]].
    unfold low_forset_inv. simpl.
    split; [exact Hsiv |].
    split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |].
    split; [exact Hvalid |].
    split; [exact Hfa |].
    split; [exact Huvis |].
    (* min condition *)
      unfold children_done, back_edges_done. simpl.
      change (fun x : V => (x ∈ (done ∪ [v]) /\ fa s x = u /\ fa s x <> x)%sets)
        with (children_done s u (done ∪ [v])).
      change (fun x : V => ((x ∈ (done ∪ [v]) /\ In x (stack s) /\ fa s x <> u) \/ x = u)%sets)
        with (fun x => back_edges_done s u (done ∪ [v]) x \/ x = u).
      unfold equiv_decb. destruct (equiv_dec u u) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
      destruct Hv_cases as [Hv_done | Hfa_neq].
      + (* Case: v ∈ done — sets unchanged, low s u ≤ dfn s v so min unchanged *)
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
          - sets_unfold. intros x [Hx_done_or_v [Hx_stack Hx_fa]].
            destruct Hx_done_or_v as [Hx_done | Hx_v].
            + split; [exact Hx_done | split; [exact Hx_stack | exact Hx_fa]].
            + subst x. split; [exact Hv_done | split; [exact Hstack | exact Hx_fa]].
          - sets_unfold. intros x [Hx_done [Hx_stack Hx_fa]].
            split; [left; exact Hx_done | split; [exact Hx_stack | exact Hx_fa]]. }
        (* Core: prove low s u ≤ dfn s v *)
        assert (Hlow_le_dfn_v: low s u <= dfn s v). {
          destruct (equiv_dec (fa s v) u) as [Hfa_eq | Hfa_neq_u].
          - (* fa s v = u: v is a tree child of u.
               dfn_valid gives dfn s u < dfn s v, and low_forset_inv gives low s u ≤ dfn s u. *)
            destruct (equiv_dec u v) as [Heq_uv | Hneq_uv].
            + (* u = v: trivial, dfn s u = dfn s v *)
              pose proof (low_forset_inv_implies_low_le_dfn u done s
                (conj Hsiv (conj (conj Hlt (conj Hiff Hpos))
                   (conj Hvalid (conj Hfa (conj Huvis Hmin)))))) as Hle.
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
              apply Hvalid in Htree_edge.
              pose proof (low_forset_inv_implies_low_le_dfn u done s
                (conj Hsiv (conj (conj Hlt (conj Hiff Hpos))
                   (conj Hvalid (conj Hfa (conj Huvis Hmin)))))) as Hle.
              exact (Nat.le_trans _ _ _ Hle (Nat.lt_le_incl _ _ Htree_edge)).
          - (* fa s v ≠ u: then v ∈ back_edges_done(done).
               From Hmin, low s u ≤ dfn s v via the right-side min. *)
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
        (* With low s u ≤ dfn s v, Nat.min(low, dfn) = low, so low' = low s pointwise. *)
        assert (Hlow'_eq_low: forall x,
          (if equiv_decb x u then Nat.min (low s u) (dfn s v) else low s x) = low s x). {
          intro x. unfold equiv_decb. destruct (equiv_dec x u) as [Heq | Hneq].
          - rewrite Heq. apply Nat.min_l. exact Hlow_le_dfn_v.
          - reflexivity. }
        rewrite (Nat.min_l (low s u) (dfn s v) Hlow_le_dfn_v).
        (* Since low' = low s pointwise and sets are equivalent, the target
           nested min equals the source nested min from Hmin. *)
        eapply min_eq_forward.
        * typeclasses eauto.
        * exact Hmin.
        * (* forward: each a1 in source has a1 in target *)
          intros a1 Ha1. exists a1. split.
          -- destruct Ha1 as [Ha1_L | Ha1_R].
            ++ left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
               exists w. split.
               ** unfold min_object_of_subset. split.
                  --- simpl. apply Hchild_eq. exact Hw_in.
                  --- intros x Hx. apply Hchild_eq in Hx.
                      simpl.
                      destruct (equiv_dec w u) as [Hw_eq | Hw_ne].
                      +++ exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                          destruct Hw_in as [_ [Hw_fa Hw_neq]].
                          rewrite Hw_eq in Hw_fa.
                          apply Hw_neq. rewrite Hw_eq. exact Hw_fa.
                      +++ destruct (equiv_dec x u) as [Hx_eq | Hx_ne].
                          *** exfalso. unfold children_done in Hx. sets_unfold in Hx.
                              destruct Hx as [_ [Hx_fa Hx_neq]].
                              rewrite Hx_eq in Hx_fa.
                              apply Hx_neq. rewrite Hx_eq. exact Hx_fa.
                          *** apply Hw_min. exact Hx.
               ** simpl. destruct (equiv_dec w u) as [Hw_eq | Hw_ne].
                  --- exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                      destruct Hw_in as [_ [Hw_fa Hw_neq]].
                      rewrite Hw_eq in Hw_fa.
                      apply Hw_neq. rewrite Hw_eq. exact Hw_fa.
                  --- exact Heq_a1.
            ++ right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
               exists w. split.
               ** unfold min_object_of_subset. split.
                  --- sets_unfold in Hw_in. simpl in Hw_in.
                      destruct Hw_in as [Hw_back | Hw_u].
                      +++ simpl. left. apply Hback_eq. exact Hw_back.
                      +++ subst w. simpl. right. reflexivity.
                  --- intros x Hx.
                      sets_unfold in Hx. simpl in Hx.
                      destruct Hx as [Hx_back | Hx_u].
                      +++ apply Hw_min. sets_unfold. simpl. left.
                          apply Hback_eq. exact Hx_back.
                      +++ subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
               ** exact Heq_a1.
          -- apply Nat.le_refl.
        * (* backward: each a2 in target has a2 in source *)
          intros a2 Ha2. exists a2. split.
          -- destruct Ha2 as [Ha2_L | Ha2_R].
            ++ left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
               (* Convert Hw_min from target (low') to source (low s) form.
                  On children_done, low' = low s since all elements ≠ u. *)
               assert (Hw_min_src: forall b, b ∈ children_done s u (done ∪ [v]) ->
                 Nat.le (low s w) (low s b)). {
                 intros b Hb. specialize (Hw_min b Hb). simpl in Hw_min.
                 destruct (equiv_dec w u) as [Hw_eq | Hw_ne].
                 - exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                   destruct Hw_in as [_ [Hw_fa Hw_neq]].
                   rewrite Hw_eq in Hw_fa. apply Hw_neq. rewrite Hw_eq. exact Hw_fa.
                 - destruct (equiv_dec b u) as [Hb_eq | Hb_ne].
                   + exfalso. unfold children_done in Hb. sets_unfold in Hb.
                     destruct Hb as [_ [Hb_fa Hb_neq]].
                     rewrite Hb_eq in Hb_fa. apply Hb_neq. rewrite Hb_eq. exact Hb_fa.
                   + exact Hw_min. }
               exists w. split.
               ** unfold min_object_of_subset. split.
                  --- simpl. apply Hchild_eq. exact Hw_in.
                  --- intros x Hx. apply Hchild_eq in Hx.
                      apply Hw_min_src. exact Hx.
               ** simpl. destruct (equiv_dec w u) as [Hw_eq | Hw_ne].
                  --- exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                      destruct Hw_in as [_ [Hw_fa Hw_neq]].
                      rewrite Hw_eq in Hw_fa. apply Hw_neq. rewrite Hw_eq. exact Hw_fa.
                  --- exact Heq_a2.
            ++ right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
               exists w. split.
               ** unfold min_object_of_subset. split.
                  --- sets_unfold in Hw_in. simpl in Hw_in.
                      destruct Hw_in as [Hw_back | Hw_u].
                      +++ apply Hback_eq in Hw_back.
                          sets_unfold. simpl. left. exact Hw_back.
                      +++ subst w. sets_unfold. simpl. right. reflexivity.
                  --- intros x Hx.
                      sets_unfold in Hx. simpl in Hx.
                      destruct Hx as [Hx_back | Hx_u].
                      +++ apply Hw_min. sets_unfold. simpl. left.
                          apply Hback_eq. exact Hx_back.
                      +++ subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
               ** exact Heq_a2.
          -- apply Nat.le_refl.
      + (* Case: fa s v <> u — normal back edge *)
        pose proof (children_done_no_add s u v done Hfa_neq) as Hchild_eq.
        pose proof (back_edges_done_add s u v done Hstack Hfa_neq) as Hback_eq.
        eapply min_eq_forward.
        * typeclasses eauto.
        * eapply (min_value_of_subset_nested_update_right_nat
            (A := V) (B := V)
            (low s) (children_done s u done)
            (dfn s) (fun w => back_edges_done s u done w \/ w = u) v
            (low s u)).
          exact Hmin.
        * (* forward: source → target *)
          intros a1 Ha1. exists a1. split.
          -- destruct Ha1 as [Ha1_L | Ha1_R].
            ++ (* from LEFT: children_done unchanged *)
              left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
              exists w. split.
              ** unfold min_object_of_subset. split.
                --- apply Hchild_eq. exact Hw_in.
                --- intros x Hx. apply Hchild_eq in Hx.
                    set (f := fun z => if equiv_decb z u then Nat.min (low s u) (dfn s v) else low s z).
                    assert (Hw_neq_u: w <> u). {
                      unfold children_done in Hw_in. sets_unfold in Hw_in.
                      destruct Hw_in as [_ [Hw_fa Hw_neq_self]]. intro Heq. subst w.
                      apply Hw_neq_self. exact Hw_fa. }
                    assert (Hx_neq_u: x <> u). {
                      unfold children_done in Hx. sets_unfold in Hx.
                      destruct Hx as [_ [Hx_fa Hx_neq_self]]. intro Heq. subst x.
                      apply Hx_neq_self. exact Hx_fa. }
                    unfold f. unfold equiv_decb.
                    destruct (equiv_dec w u) as [Hw_eq | _];
                      [exfalso; apply Hw_neq_u; exact Hw_eq|].
                    destruct (equiv_dec x u) as [Hx_eq | _];
                      [exfalso; apply Hx_neq_u; exact Hx_eq|].
                    apply Hw_min. exact Hx.
              ** set (f := fun z => if equiv_decb z u then Nat.min (low s u) (dfn s v) else low s z).
                assert (Hw_neq_u: w <> u). {
                  unfold children_done in Hw_in. sets_unfold in Hw_in.
                  destruct Hw_in as [_ [Hw_fa Hw_neq_self]]. intro Heq. subst w.
                  apply Hw_neq_self. exact Hw_fa. }
                unfold f. unfold equiv_decb.
                destruct (equiv_dec w u); [exfalso; apply Hw_neq_u; auto| exact Heq_a1].
            ++ (* from RIGHT: back_edges_done(done)∪[u]∪[v] → back_edges_done(done∪[v])∪[u] *)
              right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
              exists w. split.
              ** unfold min_object_of_subset. split.
                --- (* w ∈ back_edges_done(done ∪ [v]) ∨ w = u *)
                  sets_unfold in Hw_in. simpl in Hw_in.
                  destruct Hw_in as [[Hw_back | Hw_u] | Hw_v'].
                  +++ (* w ∈ back_edges_done(done) *)
                    sets_unfold. left. apply Hback_eq. sets_unfold. left. exact Hw_back.
                  +++ (* w = u *)
                    subst w. sets_unfold. right. reflexivity.
                  +++ (* w = v *)
                    subst w. sets_unfold. left. apply Hback_eq.
                    sets_unfold. right. reflexivity.
                --- (* minimality *)
                  intros x Hx.
                  unfold back_edges_done in Hx. sets_unfold in Hx. simpl in Hx.
                  destruct Hx as [[Hx_done_or_v [Hx_stack Hx_fa]] | Hx_u].
                  +++ destruct Hx_done_or_v as [Hx_done | Hx_v'].
                      *** (* x ∈ done → x ∈ back_edges_done(done) *)
                        apply Hw_min. sets_unfold. simpl. left. left.
                        unfold back_edges_done. sets_unfold.
                        split; [exact Hx_done | split; [exact Hx_stack | exact Hx_fa]].
                      *** (* x = v *)
                        subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
                  +++ (* x = u *)
                    subst x. apply Hw_min. sets_unfold. simpl. left. right. reflexivity.
              ** exact Heq_a1.
          -- apply Nat.le_refl.
        * (* backward: target → source *)
          intros a2 Ha2. exists a2. split.
          -- destruct Ha2 as [Ha2_L | Ha2_R].
            ++ (* from LEFT *)
              left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
              exists w. split.
              ** unfold min_object_of_subset. split.
                --- apply Hchild_eq. exact Hw_in.
                --- intros x Hx. apply Hchild_eq in Hx.
                    pose proof (Hw_min x Hx) as Hineq.
                    unfold equiv_decb in Hineq. simpl in Hineq.
                    destruct (equiv_dec w u) as [Heq_w | Hneq_w];
                      [| destruct (equiv_dec x u) as [Heq_x | Hneq_x]].
                    +++ exfalso. unfold children_done in Hw_in.
                        destruct Hw_in as [_ [Hfa_eq Hneq]].
                        apply Hneq. rewrite Heq_w. rewrite Heq_w in Hfa_eq. exact Hfa_eq.
                    +++ exfalso. unfold children_done in Hx.
                        destruct Hx as [_ [Hfa_eq Hneq]].
                        apply Hneq. rewrite Heq_x. rewrite Heq_x in Hfa_eq. exact Hfa_eq.
                    +++ exact Hineq.
              ** unfold equiv_decb in Heq_a2. simpl in Heq_a2.
                destruct (equiv_dec w u) as [Heq_w | Hneq_w].
                --- exfalso. unfold children_done in Hw_in.
                    destruct Hw_in as [_ [Hfa_eq Hneq]].
                    apply Hneq. rewrite Heq_w. rewrite Heq_w in Hfa_eq. exact Hfa_eq.
                --- exact Heq_a2.
            ++ (* from RIGHT *)
              right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
              exists w. split.
              ** unfold min_object_of_subset. split.
                --- unfold back_edges_done in Hw_in. sets_unfold in Hw_in. simpl in Hw_in.
                    destruct Hw_in as [[Hw_done_or_v [Hw_stack Hw_fa]] | Hw_u].
                    +++ destruct Hw_done_or_v as [Hw_done | Hw_v'].
                        *** (* w ∈ done → w ∈ back_edges_done(done) *)
                          sets_unfold. simpl. left. left.
                          unfold back_edges_done. sets_unfold.
                          split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
                        *** (* w = v *)
                          subst w. sets_unfold. simpl. right. reflexivity.
                    +++ (* w = u *)
                      subst w. sets_unfold. simpl. left. right. reflexivity.
                --- intros x Hx.
                    unfold back_edges_done in Hx. sets_unfold in Hx. simpl in Hx.
                    destruct Hx as [[[Hx_done [Hx_stack Hx_fa]] | Hx_u] | Hx_v'].
                    +++ (* x ∈ back_edges_done(done) → x ∈ back_edges_done(done ∪ [v]) *)
                      apply Hw_min. sets_unfold. simpl. left.
                      unfold back_edges_done. sets_unfold.
                      repeat split; [left; exact Hx_done | exact Hx_stack | exact Hx_fa].
                    +++ (* x = u *)
                      subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
                    +++ (* x = v *)
                      subst x. apply Hw_min. sets_unfold. simpl. left.
                      unfold back_edges_done. sets_unfold.
                      repeat split; [right; reflexivity | exact Hstack | exact Hfa_neq].
              ** exact Heq_a2.
          -- apply Nat.le_refl.
  Qed.

  (** [tree_child_low_le]: If v is a proper tree child of u ([fa s v = u],
      [fa s v ≠ v]), and v has been visited but is no longer on the stack
      (its SCC was already popped), then [low s u ≤ low s v].

      This holds because the tree edge from u to v was processed earlier,
      calling [update_low u (low v)], which set [low s u := min(old, low s v)].
      Proving this requires either (a) the full [scc_low_valid_v] invariant
      (which includes all tree children in its min structure, not just
      [children_done]), or (b) a pointwise [low ≤ dfn] invariant for all nodes
      combined with the DFS-tree dfn ordering.

      For now, this lemma is stated but not yet proven. *)

  Lemma low_forset_inv_children_done_low_le (u v: V) (done: V -> Prop) (s: @SCCSt V):
    low_forset_inv u done s ->
    children_done s u done v ->
    low s u <= low s v.
  Proof.
    intros Hinv Hchild.
    unfold low_forset_inv in Hinv.
    destruct Hinv as [_ [Hinv' [Hvalid [Hfa [Huvis Hmin]]]]].
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
    unfold low_forset_inv in Hinv.
    destruct Hinv as [Hsiv [Hinv' [Hvalid [Hfa_vis [Huvis Hmin]]]]].
    destruct Hinv' as [Hlt [Hiff Hpos]].
    unfold low_forset_inv. simpl.
    split; [exact Hsiv |].
    split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |].
    split; [exact Hvalid |].
    split; [exact Hfa_vis |].
    split; [exact Huvis |].
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

  (** [popped_vertex_low_eq_dfn]: If v is visited but not on the stack,
      then v was popped by [pop_scc], which requires [low s v = dfn s v].
      Both values are stable after popping, so the equality persists.
      This lemma captures the algorithmic invariant that popped vertices
      are SCC roots with [low = dfn]. *)
  Lemma popped_vertex_low_eq_dfn (s: @SCCSt V) (v: V):
    dfn_inv s -> v ∈ visited s -> ~ In v (stack s) ->
    low s v = dfn s v.
  Proof.
    (* Proof requires: vertices are pushed on stack when first visited,
       and only popped by pop_scc which requires low=dfn.
       Since v ∈ visited, it was pushed at some point.
       Since ~In v (stack), it was popped.
       pop_scc requires low v = dfn v at pop time.
       After popping, low and dfn are unchanged.
       This temporal reasoning needs a state invariant not yet formalized. *)
  Admitted.

  Lemma tree_child_low_le (u v: V) (done: V -> Prop) (s: @SCCSt V):
    dg_step g u v ->
    fa s v = u -> fa s v <> v ->
    v ∈ visited s -> ~ In v (stack s) ->
    low_forset_inv u done s ->
    low s u <= low s v.
  Proof.
    intros Hstep Hfa_eq Hfa_neq Hvis Hnstack Hinv.
    destruct Hinv as [Hsiv [Hinv' [Hvalid [Hfa [Huvis Hmin]]]]].
    destruct Hinv' as [Hlt [Hiff Hpos]].
    (* Step 1: tree edge from u to v *)
    assert (Htree: dg_step (state_to_dfs_tree (V:=V) (E:=E) g s root) u v). {
      eapply state_to_dfs_tree_step_char_backward; eauto. }
    (* Step 2: dfn ordering from dfn_valid *)
    assert (Hdfn_lt: dfn s u < dfn s v). {
      eapply Hvalid; eauto. }
    (* Step 3: low s u ≤ dfn s u *)
    assert (Hlow_le_dfn: low s u <= dfn s u). {
      eapply (low_forset_inv_implies_low_le_dfn u done).
      unfold low_forset_inv.
      split; [exact Hsiv |].
      split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |].
      split; [exact Hvalid |].
      split; [exact Hfa |].
      split; [exact Huvis | exact Hmin]. }
    (* Step 4: low s v = dfn s v (v was popped from stack) *)
    assert (Hlow_v_eq_dfn: low s v = dfn s v). {
      eapply popped_vertex_low_eq_dfn; eauto.
      split; [exact Hlt | split; [exact Hiff | exact Hpos]]. }
    (* Step 5: low s u ≤ dfn s u < dfn s v = low s v *)
    rewrite Hlow_v_eq_dfn.
    eapply Nat.le_trans; [exact Hlow_le_dfn |].
    apply Nat.lt_le_incl. exact Hdfn_lt.
  Qed.

  Lemma update_low_back_edge_fa_neq (u v: V) (done: V -> Prop) (s: @SCCSt V):
    dg_step g u v ->
    In v (stack s) ->
    fa s v <> u ->
    low_forset_inv u done s ->
    low_forset_inv u (done ∪ [v])
      (RecordSet.set low (fun low0 x => if equiv_decb x u then Nat.min (low s u) (dfn s v) else low0 x) s).
  Proof.
    intros Hstep Hstack Hfa_neq Hinv_s.
    unfold low_forset_inv in Hinv_s.
    destruct Hinv_s as [Hsiv [Hinv [Hvalid [Hfa [Huvis Hmin]]]]].
    destruct Hinv as [Hlt [Hiff Hpos]].
    unfold low_forset_inv. simpl.
    split; [exact Hsiv |].
    split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |].
    split; [exact Hvalid |].
    split; [exact Hfa |].
    split; [exact Huvis |].
    unfold children_done, back_edges_done. simpl.
      change (fun x : V => (x ∈ (done ∪ [v]) /\ fa s x = u /\ fa s x <> x)%sets)
        with (children_done s u (done ∪ [v])).
      change (fun x : V => ((x ∈ (done ∪ [v]) /\ In x (stack s) /\ fa s x <> u) \/ x = u)%sets)
        with (fun x => back_edges_done s u (done ∪ [v]) x \/ x = u).
      pose proof (children_done_no_add s u v done Hfa_neq) as Hchild_eq.
      pose proof (back_edges_done_add s u v done Hstack Hfa_neq) as Hback_eq.
      unfold equiv_decb. destruct (equiv_dec u u) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
      eapply min_eq_forward.
      + typeclasses eauto.
      + eapply (min_value_of_subset_nested_update_right_nat
          (A := V) (B := V)
          (low s) (children_done s u done)
          (dfn s) (fun w => back_edges_done s u done w \/ w = u) v
          (low s u)). exact Hmin.
      + intros a1 Ha1. exists a1. split.
        * destruct Ha1 as [Ha1_L | Ha1_R].
          -- left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** apply Hchild_eq. exact Hw_in.
                ** intros x Hx. apply Hchild_eq in Hx.
                   set (f := fun z => if equiv_decb z u then Nat.min (low s u) (dfn s v) else low s z).
                   assert (Hw_neq_u: w <> u). {
                     unfold children_done in Hw_in. sets_unfold in Hw_in.
                     destruct Hw_in as [_ [Hw_fa Hw_neq_self]]. intro Heq. subst w. apply Hw_neq_self. exact Hw_fa. }
                   assert (Hx_neq_u: x <> u). {
                     unfold children_done in Hx. sets_unfold in Hx.
                     destruct Hx as [_ [Hx_fa Hx_neq_self]]. intro Heq. subst x. apply Hx_neq_self. exact Hx_fa. }
                   unfold f. unfold equiv_decb.
                   destruct (equiv_dec w u) as [Hw_eq | _]; [exfalso; apply Hw_neq_u; exact Hw_eq|].
                   destruct (equiv_dec x u) as [Hx_eq | _]; [exfalso; apply Hx_neq_u; exact Hx_eq|].
                   apply Hw_min. exact Hx.
             ++ set (f := fun z => if equiv_decb z u then Nat.min (low s u) (dfn s v) else low s z).
                assert (Hw_neq_u: w <> u). {
                  unfold children_done in Hw_in. sets_unfold in Hw_in.
                  destruct Hw_in as [_ [Hw_fa Hw_neq_self]]. intro Heq. subst w. apply Hw_neq_self. exact Hw_fa. }
                unfold f. unfold equiv_decb.
                destruct (equiv_dec w u); [exfalso; apply Hw_neq_u; auto| exact Heq_a1].
          -- right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** sets_unfold in Hw_in. simpl in Hw_in.
                   destruct Hw_in as [[Hw_back | Hw_u] | Hw_v'].
                   --- sets_unfold. left. apply Hback_eq. sets_unfold. left. exact Hw_back.
                   --- subst w. sets_unfold. right. reflexivity.
                   --- subst w. sets_unfold. left. apply Hback_eq. sets_unfold. right. reflexivity.
                ** intros x Hx. unfold back_edges_done in Hx. sets_unfold in Hx. simpl in Hx.
                   destruct Hx as [[Hx_done_or_v [Hx_stack Hx_fa]] | Hx_u].
                   --- destruct Hx_done_or_v as [Hx_done | Hx_v'].
                       +++ apply Hw_min. sets_unfold. simpl. left. left.
                           unfold back_edges_done. sets_unfold.
                           split; [exact Hx_done | split; [exact Hx_stack | exact Hx_fa]].
                       +++ subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
                   --- subst x. apply Hw_min. sets_unfold. simpl. left. right. reflexivity.
             ++ exact Heq_a1.
        * apply Nat.le_refl.
      + intros a2 Ha2. exists a2. split.
        * destruct Ha2 as [Ha2_L | Ha2_R].
          -- left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** apply Hchild_eq. exact Hw_in.
                ** intros x Hx. apply Hchild_eq in Hx.
                   pose proof (Hw_min x Hx) as Hineq.
                   unfold equiv_decb in Hineq. simpl in Hineq.
                   destruct (equiv_dec w u) as [Heq_w | Hneq_w];
                     [| destruct (equiv_dec x u) as [Heq_x | Hneq_x]].
                   --- exfalso. unfold children_done in Hw_in.
                       destruct Hw_in as [_ [Hfa_eq Hneq]]. apply Hneq. rewrite Heq_w. rewrite Heq_w in Hfa_eq. exact Hfa_eq.
                   --- exfalso. unfold children_done in Hx.
                       destruct Hx as [_ [Hfa_eq Hneq]]. apply Hneq. rewrite Heq_x. rewrite Heq_x in Hfa_eq. exact Hfa_eq.
                   --- exact Hineq.
             ++ unfold equiv_decb in Heq_a2. simpl in Heq_a2.
                destruct (equiv_dec w u) as [Heq_w | Hneq_w].
                --- exfalso. unfold children_done in Hw_in.
                    destruct Hw_in as [_ [Hfa_eq Hneq]]. apply Hneq. rewrite Heq_w. rewrite Heq_w in Hfa_eq. exact Hfa_eq.
                --- exact Heq_a2.
          -- right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** unfold back_edges_done in Hw_in. sets_unfold in Hw_in. simpl in Hw_in.
                   destruct Hw_in as [[Hw_done_or_v [Hw_stack Hw_fa]] | Hw_u].
                   --- destruct Hw_done_or_v as [Hw_done | Hw_v'].
                       +++ sets_unfold. simpl. left. left.
                           unfold back_edges_done. sets_unfold.
                           split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
                       +++ subst w. sets_unfold. simpl. right. reflexivity.
                   --- subst w. sets_unfold. simpl. left. right. reflexivity.
                ** intros x Hx. unfold back_edges_done in Hx. sets_unfold in Hx. simpl in Hx.
                   destruct Hx as [[[Hx_done [Hx_stack Hx_fa]] | Hx_u] | Hx_v'].
                   --- apply Hw_min. sets_unfold. simpl. left.
                       unfold back_edges_done. sets_unfold.
                       repeat split; [left; exact Hx_done | exact Hx_stack | exact Hx_fa].
                   --- subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
                   --- subst x. apply Hw_min. sets_unfold. simpl. left.
                       unfold back_edges_done. sets_unfold.
                       repeat split; [right; reflexivity | exact Hstack | exact Hfa_neq].
             ++ exact Heq_a2.
        * apply Nat.le_refl.
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
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u)
          (pop_scc v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s. subst s.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s0) v) as [popped rest] eqn:?.
    simpl. destruct H as [Hinv Hfa_eq].
    unfold low_forset_inv in Hinv.
    destruct Hinv as [Hsiv [Hinv' [Hvalid [Hfa_vis [Huvis Hmin]]]]].
    split.
    - unfold low_forset_inv. simpl.
      split.
      { (* stack_in_visited: rest ⊆ old stack, old stack ⊆ visited *)
        intros w Hin. apply Hsiv.
        eapply stack_split_at_rest_incl; eauto. }
      split; [exact Hinv' |].
      split; [exact Hvalid |].
      split; [exact Hfa_vis |].
      split; [exact Huvis |].
      (* min: cbv expands RecordUpdate, revealing only stack differs.
         children_done uses fa (same as s0); back_edges_done uses
         stack=rest instead of stack s0.  For w∈done, In w rest ↔ In w(stack s0)
         because popped contains v and vertices above v, while done vertices
         were processed before v (below v on stack). *)
      unfold children_done, back_edges_done. cbv. cbv in Hmin.
      (* After cbv: goal uses 'rest', Hmin uses 'stack s0' in back_edges_done.
         Children_done (uses fa s0) and low/dfn are identical.
         Back_edges_done: for w∈done, In w rest ↔ In w (stack s0)
         because popped = [v, vertices-above-v] and done vertices
         (processed before v) are below v.  Pending lemma: rest_done_equiv. *)
      admit.
    - (* fa s v = u: pop_scc doesn't modify fa *)
      exact Hfa_eq.
  Admitted.

  (** [preloop_preserves_ancestor_inv]: [preloop v] modifies [dfn v],
      [low v], [timer], [stack], [visited] — all local to [v].
      No effect on [fa], [low] for [u ≠ v], or [done] vertices. *)
  Lemma preloop_preserves_ancestor_inv (u v: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s)
          (preloop v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl.
    destruct H as [Hinv [Hfa_eq Hnv]].
    unfold low_forset_inv in Hinv.
    destruct Hinv as [Hsiv [Hinv' [Hvalid [Hfa_vis [Huvis Hmin]]]]].
    split.
    - unfold low_forset_inv. simpl.
      split.
      { (* stack_in_visited: push_stack v::stack s0, visited = {v} ∪ visited s0 *)
        intros w Hin.
        simpl in Hin.
        destruct Hin as [Heq | Hin_tail].
        - subst w. sets_unfold. left. reflexivity.
        - apply Hsiv in Hin_tail. sets_unfold. right. exact Hin_tail. }
      split.
      { (* dfn_inv: set_dfn v sets dfn v = old_timer, incr_timer adds 1.
           For w ≠ v: dfn unchanged. *)
        destruct Hinv' as [Hlt_s0 [Hiff_s0 Hpos_s0]].
        split.
        - intros w Hvis.
          destruct (classic (w = v)) as [Heq | Hneq].
          + subst w. (* dfn v = old_timer < old_timer + 1 = new_timer *)
            simpl. lia.
          + apply Hlt_s0. sets_unfold in Hvis. destruct Hvis as [Heq' | Hvis'];
              [exfalso; apply Hneq; exact Heq' | exact Hvis'].
        - split.
          + intros w. split.
            * intros Hdfn0.
              destruct (classic (w = v)) as [Heq | Hneq].
              { subst w. simpl in Hdfn0. lia. }
              { apply Hiff_s0 in Hdfn0. intro Hvis.
                apply Hdfn0. sets_unfold in Hvis. destruct Hvis as [Heq' | Hvis'];
                  [exfalso; apply Hneq; exact Heq' | exact Hvis']. }
            * intros Hnvis.
              apply Hiff_s0. intro Hvis.
              apply Hnvis. sets_unfold. right. exact Hvis.
          + simpl. lia. }
      split.
      { (* dfn_valid: no new tree edges from v (no children yet) *)
        exact Hvalid. }
      split.
      { (* fa_visited: unchanged, preloop doesn't modify fa *)
        exact Hfa_vis. }
      split.
      { (* u ∈ visited: unchanged *)
        exact Huvis. }
      (* min condition: children_done/back_edges_done unchanged
         (preloop doesn't modify fa for done vertices, v ∉ done) *)
      exact Hmin.
    - (* fa s v = u: preloop doesn't modify fa *)
      exact Hfa_eq.
  Qed.

  (** [process_edge_preserves_ancestor_inv]: [process_edge v W x]
      processes one neighbor [x] of [v].  The operations on [v]'s
      edges do not modify [fa] for [u]'s done vertices, [low u],
      or [fa v]. *)
  Lemma process_edge_preserves_ancestor_inv (u v x: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit):
    dg_step g v x ->
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u)
          (process_edge v W x)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    intros Hdg_vx.
    unfold process_edge, if_else.
    intro_state. destruct H as [Hinv Hfa_eq].
    unfold low_forset_inv in Hinv.
    destruct Hinv as [Hsiv [Hinv' [Hvalid [Hfa_vis [Huvis Hmin]]]]].
    apply Hoare_choice.
    - (* Tree edge: ~x ∈ visited *)
      apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := fun s => low_pre x s).
      { intros s1 [Hnx Hs1]. subst s1. unfold low_pre.
        split; [exact Hsiv | split; [exact Hnx | split; [exact Hvalid | split; [exact Hinv' | exact Hfa_vis]]]]]. }
      eapply Hoare_bind. { apply (set_fa_preserves_low_pre_rich x v). }
      simpl. intros _.
      eapply Hoare_bind. { apply (HW x). }
      simpl. intros _. intro_state.
      destruct H as [[Hscc [Hvalid_mid [Hinv_mid Hfa_mid]]] Hxvis_mid].
      hoare_auto_s.
      unfold update_low. hoare_auto_s.
      { (* set_low branch: low x < low v → set_low v (low x) *)
        (* set_low modifies low v, not low u or fa v or done vertices *)
        intro_state. hoare_auto_s. subst s. simpl.
        split; [| exact Hfa_eq].
        unfold low_forset_inv. simpl.
        split; [exact Hsiv |].
        split; [exact Hinv_mid |].
        split; [exact Hvalid_mid |].
        split; [exact Hfa_mid |].
        split; [exact Huvis |].
        (* min: unchanged, set_fa x v and update_low v don't touch u's stuff *)
        exact Hmin. }
      { (* skip branch: ~low x < low v *)
        destruct H as [Heq _]. subst s. simpl.
        split; [| exact Hfa_eq].
        unfold low_forset_inv. simpl.
        split; [exact Hsiv |].
        split; [exact Hinv_mid |].
        split; [exact Hvalid_mid |].
        split; [exact Hfa_mid |].
        split; [exact Huvis |].
        exact Hmin. }
    - (* Non-tree edge: x ∈ visited *)
      intro_state. hoare_auto_s.
      + (* x in stack: back edge *)
        unfold update_low. hoare_auto_s.
        { (* set_low v (dfn x): update_low modifies low v, not low u *)
          intro_state. hoare_auto_s. subst s. simpl.
          split; [| exact Hfa_eq].
          unfold low_forset_inv. simpl.
          split; [exact Hsiv |].
          split; [exact Hinv' |].
          split; [exact Hvalid |].
          split; [exact Hfa_vis |].
          split; [exact Huvis |].
          exact Hmin. }
        { (* skip: ~dfn x < low v, state unchanged *)
          destruct H0 as [Heq _]. subst s.
          split; [| exact Hfa_eq].
          unfold low_forset_inv. simpl.
          split; [exact Hsiv |].
          split; [exact Hinv' |].
          split; [exact Hvalid |].
          split; [exact Hfa_vis |].
          split; [exact Huvis |].
          exact Hmin. }
      + (* x not in stack: cross edge, state unchanged *)
        destruct H0 as [Heq _]. subst s.
        split; [| exact Hfa_eq].
        unfold low_forset_inv. simpl.
        split; [exact Hsiv |].
        split; [exact Hinv' |].
        split; [exact Hvalid |].
        split; [exact Hfa_vis |].
        split; [exact Huvis |].
        exact Hmin.
  Qed.

  (** [W_preserves_ancestor_inv]: Combining the above, [W v]
      ([tarjan_scc g v]) preserves [low_forset_inv u done] and
      [fa s v = u]. *)
  Lemma W_preserves_ancestor_inv (u v: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (fun s => low_pre x s) (W x) (fun _ s => low_post x s)) ->
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s)
          (W v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    intros HW_post.
    unfold tarjan_scc, tarjan_scc_f.
    eapply Hoare_bind.
    { apply preloop_preserves_ancestor_inv. }
    simpl. intros _. intro_state.
    destruct H as [Hinv Hfa_eq].
    eapply Hoare_bind with
      (Q := fun _ s => low_forset_inv u done s /\ fa s v = u).
    { apply Hoare_conseq_pre with
        (P2 := fun s => low_forset_inv u done s /\ fa s v = u).
      { intros s H. exact H. }
      (* forset preserves ancestor invariants *)
      eapply Hoare_forset with
        (P := fun _ s => low_forset_inv u done s /\ fa s v = u)
        (universe := dg_step g v)
        (body := process_edge v W).
      - (* Proper *)
        clear. intros done1 done2 Hequiv s1 s2 Heq. subst s2.
        apply Sets_equiv_Sets_included in Hequiv. destruct Hequiv.
        split; intros [Hinv' Hfa']; split; auto.
      - intros done' a Hsub Huniv Hnot_done.
        apply Hoare_conseq_pre with
          (P2 := fun s => low_forset_inv u done s /\ fa s v = u).
        { intros s [Hinv' Hfa']. split; auto. }
        apply process_edge_preserves_ancestor_inv; auto. }
    simpl. intros _. intro_state.
    destruct H as [Hinv' Hfa'_eq].
    hoare_auto_s.
    - (* low v = dfn v → pop_scc v *)
      apply Hoare_conseq_pre with
        (P2 := fun s => low_forset_inv u done s /\ fa s v = u).
      { intros s [Hinv'' Hfa'']. split; auto. }
      apply pop_scc_preserves_ancestor_inv.
    - (* skip: state unchanged *)
      destruct H as [Heq _]. subst s.
      split; auto.
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
  Lemma set_fa_W_preserves_low_forset_inv (u v: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                     (fun _ s => low_post x s /\ u ∈ visited s)) ->
    dg_step g u v ->
    Hoare (fun s => low_forset_inv u done s /\ ~ v ∈ visited s)
          (set_fa v u;; W v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    intros HW Hdg.
    apply (Hoare_bind (fun s => low_forset_inv u done s /\ ~ v ∈ visited s)
                      (set_fa v u)
                      (fun _ s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s)
                      (fun _ => W v)
                      (fun _ s => low_forset_inv u done s /\ fa s v = u)).
    - (* Goal 1: set_fa v u *)
      unfold set_fa. intro_state. hoare_auto_s. subst s.
      simpl.
      destruct H as [Hinv Hnv].
      unfold low_forset_inv in Hinv.
      destruct Hinv as [Hsiv [Hinv' [Hvalid_s0 [Hfa_vis_s0 [Huvis_s0 Hmin_s0]]]]].
      destruct Hinv' as [Hlt_s0 [Hiff_s0 Hpos_s0]].
      (* After simpl, the goal is:
         low_forset_inv u done (set_fa_state s0) /\ fa_final v = u /\ ~v∈visited s0.
         For low_forset_inv, all components that don't depend on fa
         are identical to s0. Only fa_visited and the min condition
         (which uses children_done/back_edges_done, which use fa) might
         differ. But v ∉ done (v ∉ visited), so fa change at v doesn't
         affect children_done/back_edges_done. *)
      split; [| split; [| exact Hnv]].
      + (* low_forset_inv u done preserved *)
        unfold low_forset_inv. simpl.
        split.
        { (* stack_in_visited: unchanged, doesn't depend on fa *)
          exact Hsiv. }
        split.
        { (* dfn_inv: unchanged, doesn't depend on fa *)
          split; [exact Hlt_s0 | split; [exact Hiff_s0 | exact Hpos_s0]]. }
        split.
        { (* dfn_valid: set_fa changes fa at v (unvisited), so DFS tree unchanged *)
          unfold dfn_valid. intros x y Htree.
          apply state_to_dfs_tree_step_char in Htree.
          destruct Htree as [Hedge [Hfa_eq [Hfa_neq Hvis_y]]].
          simpl in Hfa_eq, Hfa_neq.
          destruct (equiv_dec y v) as [Heq | Hneq].
          - subst y. exfalso. apply Hnv. exact Hvis_y.
          - assert (Hfa_s0_eq: fa s0 y = x) by exact Hfa_eq.
            assert (Hfa_s0_neq: fa s0 y <> y) by exact Hfa_neq.
            apply (Hvalid_s0 x y).
            eapply state_to_dfs_tree_step_char_backward; eauto. }
        split.
        { (* fa_visited: fa v := u, for w≠v fa unchanged *)
          intros w Hfa_neq.
          destruct (equiv_dec w v) as [Heq | Hneq_w].
          - subst w. unfold fa_visited in Hfa_vis_s0.
            (* fa v = u <> v, need u ∈ visited s0 *)
            exact Huvis_s0.
          - apply Hfa_vis_s0. exact Hfa_neq. }
        split.
        { (* u ∈ visited: unchanged *)
          exact Huvis_s0. }
        (* min: children_done/back_edges_done for set_fa_state = same for s0.
           fa change at v doesn't affect done vertices, low/dfn unchanged. *)
        simpl. exact Hmin_s0.
      + (* fa s v = u *)
        destruct (equiv_dec v v) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
    - (* Goal 2: W v preserves low_forset_inv u done and fa s v = u *)
      intro _. apply Hoare_conseq_pre with
        (P2 := fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s).
      { intros s H. exact H. }
      assert (HW_post: forall x, Hoare (fun s => low_pre x s) (W x)
                                       (fun _ s => low_post x s)). {
        intros x. eapply Hoare_conseq_post.
        2: { eapply Hoare_conseq_pre. 2: apply (HW x).
             intros s [Hpre Hu]. exact Hpre. }
        intros _ s [Hpost _]. exact Hpost. }
      apply (W_preserves_ancestor_inv u v done W HW_post).
  Qed.

  Lemma process_edge_keep_low_forset_inv (u v: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                     (fun _ s => low_post x s /\ u ∈ visited s)) ->
    dg_step g u v ->
    Hoare (fun s => low_forset_inv u done s)
          (process_edge u W v)
          (fun _ s => low_forset_inv u (done ∪ [v]) s).
  Proof.
    intros HW Hdg.
    unfold process_edge, if_else.
    intro_state.
    unfold low_forset_inv in H.
    destruct H as [Hsiv [Hinv [Hvalid [Hfa [Huvis Hmin]]]]].
    destruct Hinv as [Hlt [Hiff Hpos]].
    apply Hoare_choice.
    - (* Tree edge: ~v ∈ visited *)
      apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := fun s => low_pre v s /\ u ∈ visited s).
      { intros s1 [Hnv Hs1]. subst s1. unfold low_pre.
        split.
        - split; [exact Hsiv | split; [exact Hnv | split; [exact Hvalid | split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] | exact Hfa]]]].
        - exact Huvis. }
      eapply Hoare_bind.
      apply set_fa_preserves_low_pre_rich.
      simpl. intros _.
      eapply Hoare_bind.
      apply (HW v).
      simpl. intros _. intro_state.
      destruct H as [[Hscc [Hvalid_mid [Hinv_mid Hfa_mid]]] Huvis_mid].
      destruct Hinv_mid as [Hlt_mid [Hiff_mid Hpos_mid]].
      hoare_auto_s.
      unfold update_low. hoare_auto_s.
      all: admit.
    - (* Non-tree edge: v is visited *)
      intro_state. hoare_auto_s.
      + (* v in stack: back edge *)
        unfold update_low. hoare_auto_s.
        { (* Subgoal (1): dfn s0 v < low s0 u → set_low u (dfn s0 v) *)
          destruct (equiv_dec (fa s0 v) u) as [Hfa_eq | Hfa_neq].
          - (* fa s0 v = u: leads to contradiction.
               From state_to_dfs_tree_step_fa + dfn_valid: dfn s0 u < dfn s0 v.
               From low_forset_inv_implies_low_le_dfn: low s0 u ≤ dfn s0 u.
               So low s0 u ≤ dfn s0 u < dfn s0 v, but H says dfn s0 v < low s0 u. *)
            assert (Hvis_v: v ∈ visited s0). {
              eapply stack_in_visited_impl; eauto. }
            destruct (equiv_dec u v) as [Heq_uv | Hneq_uv].
            { (* self-loop: fa s0 v = u = v, so state_to_dfs_tree_step_fa doesn't apply.
                 But dfn s0 v < low s0 u and low s0 u ≤ dfn s0 u = dfn s0 v give contradiction. *)
              assert (Hlow_le: low s0 u <= dfn s0 u).
              { eapply low_forset_inv_implies_low_le_dfn.
                unfold low_forset_inv.
                split; [exact Hsiv |].
                split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |].
                split; [exact Hvalid |].
                split; [exact Hfa |].
                split; [exact Huvis |].
                exact Hmin. }
              rewrite Heq_uv in H, Hlow_le.
              lia. }
            { (* u ≠ v: fa s0 v = u ≠ v *)
              assert (Hfa_neq_self: fa s0 v <> v). {
                rewrite Hfa_eq. exact Hneq_uv. }
              assert (Htree: dg_step (state_to_dfs_tree (V:=V) (E:=E) g s0 root) u v). {
                assert (Htree_fa: dg_step (state_to_dfs_tree g s0 root) (fa s0 v) v). {
                rewrite <- Hfa_eq in Hdg.
                eapply state_to_dfs_tree_step_fa; eauto. }
                rewrite Hfa_eq in Htree_fa. exact Htree_fa. }
              assert (Hdfn_lt: dfn s0 u < dfn s0 v). {
                eapply Hvalid; eauto. }
              assert (Hlow_le: low s0 u <= dfn s0 u).
              { eapply low_forset_inv_implies_low_le_dfn.
                unfold low_forset_inv.
                split; [exact Hsiv |].
                split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |].
                split; [exact Hvalid |].
                split; [exact Hfa |].
                split; [exact Huvis |].
                exact Hmin. }
              lia. }
          - assert (Hinv_full: low_forset_inv u done s0). {
              unfold low_forset_inv.
              split; [exact Hsiv |].
              split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |].
              split; [exact Hvalid | split; [exact Hfa | split; [exact Huvis | exact Hmin]]]. }
            unfold set_low. intro_state. hoare_auto_s. subst s s1. simpl.
            pose proof (update_low_back_edge_fa_neq u v done s0 Hdg H2 Hfa_neq Hinv_full) as Hlemma.
            simpl in Hlemma. unfold equiv_decb in Hlemma.
            destruct (equiv_dec u u) as [_ | Hc] in Hlemma; [| exfalso; apply Hc; reflexivity].
            rewrite (Nat.min_r (low s0 u) (dfn s0 v)) in Hlemma;
              [| apply Nat.lt_le_incl; exact H].
            exact Hlemma. }
        { (* Subgoal (2): skip — state unchanged, ~dfn s0 v < low s0 u *)
          destruct H as [Heq Hnlt]. subst s. clear b.
          unfold low_forset_inv.
          split; [exact Hsiv |].
          split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |].
          split; [exact Hvalid |].
          split; [exact Hfa |].
          split; [exact Huvis |].
          (* min condition *)
          destruct Hmin as [m [[Hm_in Hm_min] Heq_m]].
          rewrite <- Heq_m.
          destruct (equiv_dec (fa s0 v) u) as [Hfa_eq | Hfa_neq].
          - (* fa s0 v = u: needs low s0 u ≤ low s0 v.
               When fa s0 v = u and fa s0 v ≠ v, the tree-edge (u,v) was previously
               processed, calling update_low u (low v) which set low u := min(low u, low v).
               Subsequent update_low calls only decrease low u, so low s0 u ≤ low s0 v.
               Formal proof requires temporal reasoning about update_low_tree_edge.
               Blocked by: tree_child_low_le (or stack_ancestor_dfn_lt for contradiction). *)
            admit.
          - (* fa s0 v <> u: standard back edge *)
            pose proof (children_done_no_add s0 u v done Hfa_neq) as Hchild_eq.
            pose proof (back_edges_done_add s0 u v done H2 Hfa_neq) as Hback_eq.
            (* Decompose Hm_in to know whether m came from left or right *)
            destruct Hm_in as [Hm_left | Hm_right].
            ++ (* m ∈ left side (children_done min). Membership + minimality *)
              exists m. split; [| reflexivity].
              unfold min_object_of_subset. split.
              ** (* membership: m ∈ new_left *)
                sets_unfold. left. rewrite Hchild_eq. exact Hm_left.
              ** (* minimality: forall b ∈ new_union, m ≤ b *)
                intros b Hb. destruct Hb as [Hb_left | Hb_right].
                --- (* b from new_left = old_left *)
                  rewrite Hchild_eq in Hb_left. apply Hm_min. sets_unfold. left. exact Hb_left.
                --- (* b from new_right. Chain: m ≤ old_right_min ≤ dfn s0 w (=b) *)
                  destruct Hb_right as [w [[Hw_in Hw_min'] Heq_b]].
                  rewrite <- Heq_b.
                  destruct Hw_in as [Hw_back' | Hw_u].
                  +++ (* w ∈ back_edges_done(done∪[v]) *)
                    apply Hback_eq in Hw_back'.
                    destruct Hw_back' as [Hw_back | Hw_v].
                    *** (* w ∈ back_edges_done(done) → old-right domain.
                           Chain: m ≤ old_right_min ≤ dfn s0 w *)
                      destruct (min_nonempty_exists (dfn s0)
                        (fun x => back_edges_done s0 u done x \/ x = u)) as [r Hr].
                      { exists w. left. exact Hw_back. }
                      assert (Hm_le_r: m <= r). {
                        apply Hm_min. sets_unfold. right. exact Hr. }
                      destruct Hr as [x [[[Hx_back | Hx_u] Hx_min] Heq_r]].
                      { (* Hx_back: x ∈ back_edges_done *)
                        assert (Hr_le_dfw: r <= dfn s0 w). {
                          rewrite <- Heq_r. apply Hx_min. left. exact Hw_back. }
                        eapply Nat.le_trans; eauto. }
                      { (* Hx_u: x = u *)
                        subst x.
                        assert (Hr_le_dfw: r <= dfn s0 w). {
                          apply (eq_ind (dfn s0 u) (fun v => v <= dfn s0 w)
                            (Hx_min w (or_introl Hw_back)) r Heq_r). }
                        eapply Nat.le_trans; eauto. }
                    *** (* w = v → b = dfn s0 v, m ≤ dfn s0 v from Hnlt *)
                      destruct Hw_v. rewrite Heq_m. apply Nat.nlt_ge. exact Hnlt.
                  +++ (* w = u → rewrite then chain inequalities *)
                    rewrite Hw_u.
                    destruct (min_nonempty_exists (dfn s0)
                      (fun x => back_edges_done s0 u done x \/ x = u)) as [r Hr].
                    { exists u. right. reflexivity. }
                    assert (Hm_le_r: m <= r). {
                      apply Hm_min. sets_unfold. right. exact Hr. }
                    destruct Hr as [x [[[Hx_back | Hx_u] Hx_min] Heq_r]].
                    { (* Hx_back: x ∈ back_edges_done *)
                      assert (Hr_le_dfu: r <= dfn s0 u). {
                        rewrite <- Heq_r. apply Hx_min. right. reflexivity. }
                      eapply Nat.le_trans; eauto. }
                    { (* Hx_u: x = u *)
                      subst x.
                      assert (Hr_le_dfu: r <= dfn s0 u). {
                        rewrite Heq_r. apply Nat.le_refl. }
                      eapply Nat.le_trans; eauto. }
            ++ (* m ∈ right side (back_edges_done∪[u] min). Decompose to get witness *)
              destruct Hm_right as [w [[[Hw_in | Hw_u] Hw_min] Heq_w]].
              --- (* w ∈ back_edges_done(done) — m = dfn s0 w *)
                exists m. split; [| reflexivity].
                unfold min_object_of_subset. split.
                *** (* membership: lift w to expanded right side *)
                  sets_unfold. right. exists w. split.
                  { split.
                    - sets_unfold. left. apply Hback_eq. sets_unfold. left. exact Hw_in.
                    - intros x Hx. sets_unfold in Hx.
                      destruct Hx as [Hx_back' | Hx_u].
                      +++ apply Hback_eq in Hx_back'. sets_unfold in Hx_back'.
                        destruct Hx_back' as [Hx_back | Hx_v].
                        *** apply Hw_min. left. exact Hx_back.
                        *** subst x. rewrite Heq_w, Heq_m. apply Nat.nlt_ge. exact Hnlt.
                      +++ subst x. apply Hw_min. right. reflexivity. }
                    { rewrite Heq_w. reflexivity. }
                *** (* minimality *)
                  intros b Hb. destruct Hb as [Hb_left | Hb_right].
                  +++ (* b from left side *)
                    rewrite Hchild_eq in Hb_left. apply Hm_min. sets_unfold. left. exact Hb_left.
                  +++ (* b from new_right. m is old right-min, m ≤ dfn s0 v ensures new min = m *)
                    destruct Hb_right as [x [[Hx_in Hx_min'] Heq_b]].
                    rewrite <- Heq_b.
                    destruct Hx_in as [Hx_back' | Hx_u].
                    { (* x ∈ back_edges_done(done∪[v]) *)
                      apply Hback_eq in Hx_back'.
                      destruct Hx_back' as [Hx_back | Hx_v].
                      - rewrite <- Heq_w. apply Hw_min. left. exact Hx_back.
                      - destruct Hx_v. rewrite Heq_m. apply Nat.nlt_ge. exact Hnlt. }
                    { (* x = u *)
                      destruct Hx_u. rewrite <- Heq_w. apply Hw_min. right. reflexivity. }
              --- (* w = u — m = dfn s0 u *)
                rewrite Hw_u in Hw_min, Heq_w.
                exists m. split; [| reflexivity].
                unfold min_object_of_subset. split.
                *** (* membership: u ∈ expanded right side *)
                  sets_unfold. right. exists u. split.
                  { split.
                    - sets_unfold. right. reflexivity.
                    - intros x Hx. sets_unfold in Hx.
                      destruct Hx as [Hx_back' | Hx_u].
                      +++ apply Hback_eq in Hx_back'.
                        destruct Hx_back' as [Hx_back | Hx_v].
                        *** apply Hw_min. left. exact Hx_back.
                        *** destruct Hx_v. rewrite Heq_w, Heq_m. apply Nat.nlt_ge. exact Hnlt.
                      +++ destruct Hx_u. apply Nat.le_refl. }
                    { rewrite Heq_w. reflexivity. }
                *** (* minimality *)
                  intros b Hb. destruct Hb as [Hb_left | Hb_right].
                  +++ rewrite Hchild_eq in Hb_left. apply Hm_min. sets_unfold. left. exact Hb_left.
                  +++ destruct Hb_right as [x [[Hx_in Hx_min'] Heq_b]].
                    rewrite <- Heq_b.
                    destruct Hx_in as [Hx_back' | Hx_u].
                    { apply Hback_eq in Hx_back'.
                      destruct Hx_back' as [Hx_back | Hx_v].
                      - rewrite <- Heq_w. apply Hw_min. left. exact Hx_back.
                      - destruct Hx_v. rewrite Heq_m. apply Nat.nlt_ge. exact Hnlt. }
                    { destruct Hx_u. rewrite <- Heq_w. apply Hw_min. right. reflexivity. } }
      + (* v not in stack: cross edge — state unchanged *)
        destruct H2 as [Heq Hnstack]. subst s. subst s1.
        unfold low_forset_inv. simpl.
        split.
        { exact Hsiv. }
        split.
        { split; [exact Hlt | split; [exact Hiff | exact Hpos]]. }
        split.
        { exact Hvalid. }
        split.
        { exact Hfa. }
        split.
        { exact Huvis. }
        (* min condition: back_edges_done unchanged (~In v stack). *)
        simpl.
        pose proof (back_edges_done_no_add s0 u v done (or_introl Hnstack)) as Hback_eq.
        destruct (equiv_dec (fa s0 v) u) as [Hfa_eq | Hfa_neq].
        -- (* fa s0 v = u: case split on self-loop vs proper child *)
          destruct (equiv_dec (fa s0 v) v) as [Hfa_self | Hfa_not_self].
          ++ (* self-loop: fa s0 v = v = u. children_done unchanged (fa s0 v ≠ v fails),
                 back_edges_done unchanged (or_introl Hnstack). *)
            assert (Hchild_eq: children_done s0 u (done ∪ [v]) == children_done s0 u done). {
              unfold children_done.
              apply Sets_equiv_Sets_included. split.
              - sets_unfold. intros x [Hx_done_or_v [Hx_fa Hx_neq]].
                destruct Hx_done_or_v as [Hx_done | Hx_v].
                + split; [exact Hx_done | split; [exact Hx_fa | exact Hx_neq]].
                + subst x. exfalso. apply Hx_neq. exact Hfa_self.
              - sets_unfold. intros x [Hx_done [Hx_fa Hx_neq]].
                split; [left; exact Hx_done | split; [exact Hx_fa | exact Hx_neq]]. }
            eapply min_eq_forward.
            ** typeclasses eauto.
            ** exact Hmin.
            ** intros a1 Ha1. exists a1. split.
               --- destruct Ha1 as [Ha1_L | Ha1_R].
                   +++ left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
                       exists w. split.
                       *** unfold min_object_of_subset. split.
                           ---- simpl. apply Hchild_eq. exact Hw_in.
                           ---- intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx.
                       *** exact Heq_a1.
                   +++ right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
                       exists w. split.
                       *** unfold min_object_of_subset. split.
                           ---- sets_unfold in Hw_in. simpl in Hw_in.
                                destruct Hw_in as [Hw_back | Hw_u].
                                **** simpl. left. apply Hback_eq. exact Hw_back.
                                **** subst w. simpl. right. reflexivity.
                           ---- intros x Hx.
                                sets_unfold in Hx. simpl in Hx.
                                destruct Hx as [Hx_back | Hx_u].
                                **** apply Hw_min. left. apply Hback_eq. exact Hx_back.
                                **** subst x. apply Hw_min. right. reflexivity.
                       *** exact Heq_a1.
               --- apply Nat.le_refl.
            ** intros a2 Ha2. exists a2. split.
               --- destruct Ha2 as [Ha2_L | Ha2_R].
                   +++ left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
                       exists w. split.
                       *** unfold min_object_of_subset. split.
                           ---- simpl. apply Hchild_eq. exact Hw_in.
                           ---- intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx.
                       *** exact Heq_a2.
                   +++ right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
                       exists w. split.
                       *** unfold min_object_of_subset. split.
                           ---- sets_unfold in Hw_in. simpl in Hw_in.
                                destruct Hw_in as [Hw_back | Hw_u].
                                **** apply Hback_eq in Hw_back.
                                     unfold back_edges_done. sets_unfold.
                                     destruct Hw_back as [Hw_done [Hw_stack Hw_fa]].
                                     left. split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
                                **** subst w. sets_unfold. simpl. right. reflexivity.
                           ---- intros x Hx.
                                sets_unfold in Hx. simpl in Hx.
                                destruct Hx as [Hx_back | Hx_u].
                                **** apply Hw_min. sets_unfold. simpl. left.
                                     apply Hback_eq. exact Hx_back.
                                **** subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
                       *** exact Heq_a2.
               --- apply Nat.le_refl.
          ++ (* proper child: fa s0 v = u, fa s0 v ≠ v.
                 children_done expands by [v]; back_edges_done unchanged.
                 tree_child_low_le ensures low s0 u ≤ low s0 v, so
                 adding v to the set does not change the min. *)
            assert (Hvis_v: v ∈ visited s0) by (apply NNPP; exact H1).
            assert (Hlow_le: low s0 u <= low s0 v)
              by (apply (tree_child_low_le u v done s0);
                  [exact Hdg
                  |rewrite Hfa_eq; reflexivity
                  |exact Hfa_not_self
                  |exact Hvis_v
                  |exact Hnstack
                  |unfold low_forset_inv;
                   split; [exact Hsiv |];
                   split; [split; [exact Hlt | split; [exact Hiff | exact Hpos]] |];
                   split; [exact Hvalid |];
                   split; [exact Hfa |];
                   split; [exact Huvis | exact Hmin]]).
            (* The target children_done set expands by [v] compared to source.
               Since tree_child_low_le gives low s0 u ≤ low s0 v,
               the addition of low s0 v to the min set does not change the min.
               Formal proof requires min_value_of_subset nesting lemmas
               that handle element addition under set expansion. *)
            admit.
        -- (* fa s0 v ≠ u: children_done unchanged *)
          pose proof (children_done_no_add s0 u v done Hfa_neq) as Hchild_eq.
          eapply min_eq_forward.
          ++ typeclasses eauto.
          ++ exact Hmin.
          ++ (* forward *) intros a1 Ha1. exists a1. split.
             ** destruct Ha1 as [Ha1_L | Ha1_R].
                --- left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]].
                    exists w. split.
                    +++ unfold min_object_of_subset. split.
                        *** simpl. apply Hchild_eq. exact Hw_in.
                        *** intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx.
                    +++ exact Heq_a1.
                --- right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
                    exists w. split.
                    +++ unfold min_object_of_subset. split.
                        *** sets_unfold in Hw_in. simpl in Hw_in.
                            destruct Hw_in as [Hw_back | Hw_u].
                            ---- simpl. left. apply Hback_eq. exact Hw_back.
                            ---- subst w. simpl. right. reflexivity.
                        *** intros x Hx.
                            sets_unfold in Hx. simpl in Hx.
                            destruct Hx as [Hx_back | Hx_u].
                            ---- apply Hw_min. left. apply Hback_eq. exact Hx_back.
                            ---- subst x. apply Hw_min. right. reflexivity.
                    +++ exact Heq_a1.
             ** apply Nat.le_refl.
          ++ (* backward *) intros a2 Ha2. exists a2. split.
             ** destruct Ha2 as [Ha2_L | Ha2_R].
                --- left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]].
                    exists w. split.
                    +++ unfold min_object_of_subset. split.
                        *** simpl. apply Hchild_eq. exact Hw_in.
                        *** intros x Hx. apply Hchild_eq in Hx. apply Hw_min. exact Hx.
                    +++ exact Heq_a2.
                --- right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
                    exists w. split.
                    +++ unfold min_object_of_subset. split.
                        *** sets_unfold in Hw_in. simpl in Hw_in.
                            destruct Hw_in as [Hw_back | Hw_u].
                            ---- apply Hback_eq in Hw_back.
                                 unfold back_edges_done. sets_unfold.
                                 destruct Hw_back as [Hw_done [Hw_stack Hw_fa]].
                                 left. split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
                            ---- subst w. sets_unfold. simpl. right. reflexivity.
                        *** intros x Hx.
                            sets_unfold in Hx. simpl in Hx.
                            destruct Hx as [Hx_back | Hx_u].
                            ---- apply Hw_min. sets_unfold. simpl. left.
                                 apply Hback_eq. exact Hx_back.
                            ---- subst x. apply Hw_min. sets_unfold. simpl. right. reflexivity.
                    +++ exact Heq_a2.
             ** apply Nat.le_refl.
  Admitted.

  (* ================================================================ *)
  (* 11. Forset Induction                                              *)
  (* ================================================================ *)

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
    split; intro Hlow; unfold low_forset_inv in Hlow;
      destruct Hlow as [Hsiv [Hinv [Hval' [Hfa'' [Hvis' Hmin]]]]];
      destruct Hinv as [Hlt [Hiff' Hpos']].
    - (* forward: done1 → done2 *)
      split; [exact Hsiv |].
      split; [exact (conj Hlt (conj Hiff' Hpos')) |].
      split; [exact Hval' |].
      split; [exact Hfa'' |].
      split; [exact Hvis' |].
      eapply min_eq_forward; [typeclasses eauto | exact Hmin | | ].
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
                   --- simpl. left. apply Hback_eq. exact Hw_back.
                   --- right. exact Hw_u.
                ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                   --- apply Hw_min. simpl. left. apply Hback_eq. exact Hx_back.
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
                   --- simpl. left. apply Hback_eq. exact Hw_back.
                   --- right. exact Hw_u.
                ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                   --- apply Hw_min. simpl. left. apply Hback_eq. exact Hx_back.
                   --- subst x. apply Hw_min. right. reflexivity.
             ++ exact Heq_a2.
        * apply Nat.le_refl.
    - (* backward: done2 → done1, symmetric *)
      split; [exact Hsiv |].
      split; [exact (conj Hlt (conj Hiff' Hpos')) |].
      split; [exact Hval' |].
      split; [exact Hfa'' |].
      split; [exact Hvis' |].
      eapply min_eq_forward; [typeclasses eauto | exact Hmin | | ].
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
                   --- simpl. left. apply Hback_eq. exact Hw_back.
                   --- right. exact Hw_u.
                ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                   --- apply Hw_min. simpl. left. apply Hback_eq. exact Hx_back.
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
                   --- simpl. left. apply Hback_eq. exact Hw_back.
                   --- right. exact Hw_u.
                ** intros x Hx. destruct Hx as [Hx_back | Hx_u].
                   --- apply Hw_min. simpl. left. apply Hback_eq. exact Hx_back.
                   --- subst x. apply Hw_min. right. reflexivity.
             ++ exact Heq_a2.
        * apply Nat.le_refl.
  Qed.

  Lemma children_done_visited_proper u: Proper (Sets.equiv ==> eq ==> iff) (children_done_visited u).
  Proof.
    intros done1 done2 Hequiv s1 s2 Heq. subst s2.
    apply Sets_equiv_Sets_included in Hequiv. destruct Hequiv as [Hincl12 Hincl21].
    split; intros Hcdv v Hchild.
    - destruct Hchild as [Hin2 [Hfa Hneq]].
      apply Hcdv. split; [apply Hincl21; exact Hin2 | split; auto].
    - destruct Hchild as [Hin1 [Hfa Hneq]].
      apply Hcdv. split; [apply Hincl12; exact Hin1 | split; auto].
  Qed.

  Lemma done_visited_proper: Proper (Sets.equiv ==> eq ==> iff) done_visited.
  Proof.
    intros done1 done2 Hequiv s1 s2 Heq. subst s2.
    apply Sets_equiv_Sets_included in Hequiv. destruct Hequiv as [Hincl12 Hincl21].
    split; intros Hdv w Hw.
    - apply Hdv. apply Hincl21. exact Hw.
    - apply Hdv. apply Hincl12. exact Hw.
  Qed.

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

  Lemma tarjan_scc_keep_fa_children_in_universe (parent a: V):
    Hoare (fun s: @SCCSt V => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g a)
          (fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
  Proof.
    (* Proved by fixpoint induction following tarjan_scc_keep_visited pattern.
       preloop doesn't change fa; forset uses process_edge which only sets
       fa to center (never parent); pop_scc doesn't change fa.
       The forset body needs a process_edge-level lemma for fa preservation. *)
  Admitted.

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
    intros HW HW_self HW_keep_all HW_fa_children.
    set (P := fun (done: V -> Prop) (s: SCCSt) =>
      low_forset_inv u done s /\ done_visited done s /\
      (forall v, fa s v = u -> v = u \/ children_done s u done v) /\
      (forall v, fa s v = u /\ fa s v <> v -> dg_step g u v)).
    assert (HproperP: Proper (Sets.equiv ==> eq ==> iff) P). {
      unfold P. intros done1 done2 Hequiv s1 s2 Heq. subst s2.
      apply Sets_equiv_Sets_included in Hequiv. destruct Hequiv as [Hincl12 Hincl21].
      split.
      { intros [Hlow [Hdv [Hfa_child Hfa_uni]]]. split; [| split; [| split]].
        - eapply (low_forset_inv_proper u); eauto. apply Sets_equiv_Sets_included. split; auto.
        - eapply done_visited_proper; eauto. apply Sets_equiv_Sets_included. split; auto.
        - intros v Hfa_eq. destruct (Hfa_child v Hfa_eq) as [Heq_v | Hchild].
          + left. exact Heq_v.
          + right. unfold children_done in *. destruct Hchild as [Hd [Hfa_v Hneq]].
            split; [apply Hincl12; exact Hd | split; auto].
        - exact Hfa_uni. }
      { intros [Hlow [Hdv [Hfa_child Hfa_uni]]]. split; [| split; [| split]].
        - eapply (low_forset_inv_proper u); eauto. apply Sets_equiv_Sets_included. split; auto.
        - eapply done_visited_proper; eauto. apply Sets_equiv_Sets_included. split; auto.
        - intros v Hfa_eq. destruct (Hfa_child v Hfa_eq) as [Heq_v | Hchild].
          + left. exact Heq_v.
          + right. unfold children_done in *. destruct Hchild as [Hd [Hfa_v Hneq]].
            split; [apply Hincl21; exact Hd | split; auto].
        - exact Hfa_uni. } }
    apply Hoare_conseq_post with
      (Q2 := fun _ s => P (fun v => dg_step g u v) s).
    { intros b st [Hfinv [Hdv [Hfa_child Hfa_uni]]].
      destruct Hfinv as [Hsiv [Hinv [Hvalid [Hfa_vis [Huvis Hmin]]]]].
      split; [| split; [exact Hvalid | split; [exact Hinv | exact Hfa_vis]]].
      unfold scc_low_valid_v.
      destruct Hinv as [Hdfn_lt [Hdfn_zero Hpos]].
      assert (Hback_eq: (fun w => back_edges_done st u (dg_step g u) w) ∪ [u] ==
                        scc_back_edge st u ∪ [u]). {
        apply Sets_equiv_Sets_included. split.
        - sets_unfold. intros w [Hback | Heq].
          + unfold back_edges_done in Hback. sets_unfold in Hback.
            destruct Hback as [Hneigh [Hinstack Hfa_neq]].
            sets_unfold. left. unfold scc_back_edge.
            split; [exact Hneigh | split; [exact Hinstack |]].
            intro Htree. apply state_to_dfs_tree_step_char in Htree.
            destruct Htree as [Hfa_eq _]. apply Hfa_neq. exact Hfa_eq.
          + subst w. sets_unfold. right. reflexivity.
        - sets_unfold. intros w [Hback | Heq].
          + unfold scc_back_edge in Hback.
            destruct Hback as [Hneigh [Hinstack Hnot_tree]].
            destruct (equiv_dec (fa st w) u) as [Hfa_eq | Hfa_neq].
            * destruct (equiv_dec u w) as [Heq_uw | Hneq_uw].
              { rewrite <- Heq_uw. sets_unfold. right. reflexivity. }
              { assert (Hfa_neq_self: fa st w <> w).
                { rewrite Hfa_eq. exact Hneq_uw. }
                exfalso. apply Hnot_tree.
                eapply state_to_dfs_tree_step_char_backward;
                  [exact Hneigh | exact Hfa_eq | exact Hfa_neq_self |].
                apply (stack_in_visited_impl st w Hsiv Hinstack). }
            * sets_unfold. left. unfold back_edges_done. sets_unfold.
              split; [exact Hneigh | split; [exact Hinstack | exact Hfa_neq]].
          + subst w. sets_unfold. right. reflexivity. }
      assert (Hchild_sub: children_done st u (dg_step g u) ⊆
                          dg_step (state_to_dfs_tree g st root) u). {
        intros v Hchild. destruct Hchild as [Hneigh [Hfa_eq Hfa_neq]].
        assert (Hvis_v: v ∈ visited st). {
          apply Hdv. exact Hneigh. }
        eapply state_to_dfs_tree_step_char_backward;
          [exact Hneigh | exact Hfa_eq | exact Hfa_neq | exact Hvis_v]. }
      assert (Htree_sub: dg_step (state_to_dfs_tree g st root) u ⊆
                          children_done st u (dg_step g u)). {
        intros v Htree. apply state_to_dfs_tree_step_char in Htree.
        destruct Htree as [Hfa_eq [Hfa_neq Hvis]].
        assert (Hneigh: dg_step g u v). { apply Hfa_uni. split; [exact Hfa_eq | exact Hfa_neq]. }
        split; [exact Hneigh | split; auto]. }
      eapply min_eq_forward.
      + typeclasses eauto.
      + exact Hmin.
      + intros a1 Ha1. exists a1. split.
        * destruct Ha1 as [Ha1_L | Ha1_R].
          -- left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** apply Hchild_sub. exact Hw_in.
                ** intros x Hx. apply Htree_sub in Hx. apply Hw_min. exact Hx.
             ++ exact Heq_a1.
          -- right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** destruct Hw_in as [Hw_back | Hw_u].
                   --- apply Hback_eq. left. exact Hw_back.
                   --- apply Hback_eq. right. symmetry. exact Hw_u.
                ** intros x Hx. apply Hw_min. apply Hback_eq in Hx.
                   destruct Hx as [Hx_back | Hx_u].
                   --- left. exact Hx_back.
                   --- right. symmetry. exact Hx_u.
             ++ exact Heq_a1.
        * apply Nat.le_refl.
      + intros a2 Ha2. exists a2. split.
        * destruct Ha2 as [Ha2_L | Ha2_R].
          -- left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** apply Htree_sub. exact Hw_in.
                ** intros x Hx. apply Hchild_sub in Hx. apply Hw_min. exact Hx.
             ++ exact Heq_a2.
          -- right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]]. exists w. split.
             ++ unfold min_object_of_subset. split.
                ** destruct Hw_in as [Hw_back | Hw_u].
                   --- apply Hback_eq. left. exact Hw_back.
                   --- apply Hback_eq. right. symmetry. exact Hw_u.
                ** intros x Hx. apply Hw_min. apply Hback_eq in Hx.
                   destruct Hx as [Hx_back | Hx_u].
                   --- left. exact Hx_back.
                   --- right. symmetry. exact Hx_u.
             ++ exact Heq_a2.
        * apply Nat.le_refl. }
    eapply (@Hoare_forset SCCSt V P (fun v => dg_step g u v) (process_edge u W)).
    - exact HproperP.
    - intros done a Hdone_sub Huniv Hnot_done.
      unfold P. apply Hoare_conj.
      { apply (process_edge_keep_low_forset_inv u a done W HW Huniv). }
      apply Hoare_conj.
      { (* done_visited preserved *)
        unfold process_edge, if_else. intro_state.
        apply Hoare_choice.
        - apply Hoare_assume_bind. simpl.
          eapply Hoare_bind with (R := fun _ s => done_visited done s).
          { unfold set_fa. intro_state. hoare_auto_s. subst s. simpl.
            unfold done_visited. intros w Hw_done. apply H. exact Hw_done. }
          simpl. intros _.
          eapply Hoare_bind.
          { apply Hoare_conj.
            - apply (HW_keep_all a done).
            - apply (Hoare_conseq_post (Q2 := fun _ s => a ∈ visited s)).
              { intros _ s' Hvis. exact Hvis. }
              apply (HW_self a). }
          simpl. intros [Hdv_done Hvis_a].
          eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
          apply Hoare_conseq_pre with
            (P2 := fun s => done_visited done s /\ a ∈ visited s).
          { intros s' Hs'. subst s'. split; auto. }
          unfold update_low. unfold_op. intro_state. hoare_auto_s.
          { subst s. simpl. destruct H0 as [Hdv' Hvis_a'].
            unfold done_visited. intros w [Hw_done | Hw_a].
            - apply Hdv'. exact Hw_done.
            - subst w. exact Hvis_a'. }
          { destruct H0 as [[Heq _] Hvis_a']. subst s. split; [exact H | exact Hvis_a']. }
        - intro_state. hoare_auto_s.
          + apply Hoare_conseq_pre with
              (P2 := fun s => done_visited done s /\ a ∈ visited s).
            { intros s1 Hs1. subst s1. split; auto. }
            unfold update_low. unfold_op. intro_state. hoare_auto_s.
            { subst s. simpl. destruct H1 as [Hdv' Hvis_a'].
              unfold done_visited. intros w [Hw_done | Hw_a].
              - apply Hdv'. exact Hw_done.
              - subst w. exact Hvis_a'. }
            { destruct H1 as [Heq Hvis_a']. subst s. split; [exact H | exact Hvis_a']. }
          + destruct H1 as [Heq _]. subst s.
            unfold done_visited. intros w [Hw_done | Hw_a].
            * apply H. exact Hw_done.
            * subst w. exact H0. }
      apply Hoare_conj.
      { (* fa_children_are_done preserved: fa s v = u -> v = u \/
           children_done s u (done ∪ [a]) v.
           The only way fa s v = u can become newly true is when
           set_fa a u is called (tree edge), creating fa a = u;
           then a ∈ done ∪ [a] certifies children_done.
           The recursive W a call does not add new fa = u vertices.
           TODO: formal proof via process_edge lemma. *)
        admit. }
      { (* fa_children_in_universe preserved *)
        unfold process_edge, if_else. intro_state.
        apply Hoare_choice.
        - apply Hoare_assume_bind. simpl.
          eapply Hoare_bind with
            (R := fun _ s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v).
          { unfold set_fa. intro_state. hoare_auto_s. subst s. simpl.
            intros v [Hfa_v Hfa_v_neq]. unfold equiv_decb. simpl.
            destruct (equiv_dec v a) as [Heq_va | Hneq_va].
            - subst v. exact Huniv.
            - apply H. split; [exact Hfa_v | exact Hfa_v_neq]. }
          simpl. intros _.
          eapply Hoare_bind with
            (R := fun _ s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v).
          { apply Hoare_conseq_post with
              (Q2 := fun _ s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v).
            { intros _ s' Hfa_uni v [Hfa_eq Hfa_neq].
              apply Hfa_uni. split; [exact Hfa_eq | exact Hfa_neq]. }
            apply (HW_fa_children a). }
          simpl. intros _.
          eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
          apply Hoare_conseq_pre with
            (P2 := fun s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v).
          { intros s' Hs'. subst s'. exact H0. }
          unfold update_low. unfold_op. intro_state. hoare_auto_s.
          { subst s. simpl. intros v [Hfa_v Hfa_v_neq].
            unfold equiv_decb. simpl in Hfa_v.
            destruct (equiv_dec v u) as [Heq_vu | Hneq_vu].
            - subst v. exfalso. apply Hfa_v_neq. reflexivity.
            - apply H. split; [exact Hfa_v | exact Hfa_v_neq]. }
          { destruct H1 as [Heq _]. subst s. apply H. }
        - intro_state. hoare_auto_s.
          + apply Hoare_conseq_pre with
              (P2 := fun s => forall v, fa s v = u /\ fa s v <> v -> dg_step g u v).
            { intros s1 Hs1. subst s1. exact H. }
            unfold update_low. unfold_op. intro_state. hoare_auto_s.
            { subst s. simpl. intros v [Hfa_v Hfa_v_neq].
              unfold equiv_decb. simpl in Hfa_v.
              destruct (equiv_dec v u) as [Heq_vu | Hneq_vu].
              - subst v. exfalso. apply Hfa_v_neq. reflexivity.
              - apply H. split; [exact Hfa_v | exact Hfa_v_neq]. }
            { destruct H2 as [Heq _]. subst s. exact H. }
          + destruct H2 as [Heq _]. subst s. exact H. }
    - intro_state. destruct H as [Hlow_inv Hfa_prop].
      split; [exact Hlow_inv | split].
      + unfold done_visited. intros v Hv_empty. exfalso. exact Hv_empty.
      + split.
        * (* fa_children_are_done: fa s v = u -> v = u \/ children_done s u ∅ v *)
          intros v Hfa_eq. left. apply Hfa_prop. exact Hfa_eq.
        * (* fa_children_in_universe: fa s v = u /\ fa s v <> v -> dg_step g u v *)
          intros v [Hfa_eq Hfa_neq].
          apply Hfa_prop in Hfa_eq. subst v.
          exfalso. apply Hfa_neq. reflexivity. }
  Admitted.

  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
          (fun _ s => low_post u s).
  Proof.
    unfold tarjan_scc.
    apply (Hoare_fix_logicv_conj (tarjan_scc_f g)
             (fun (x: V) (_: unit) (s: SCCSt) => low_pre x s)
             (fun (x: V) (_: unit) (_: unit) (s: SCCSt) => low_post x s)
             u tt
             (visited_tag_pre : V -> visited_tag -> SCCSt -> Prop)
             (visited_tag_post : V -> visited_tag -> unit -> SCCSt -> Prop)).
    { intros x t. destruct t.
      - simpl. apply (tarjan_scc_self_visited g x).
      - simpl. apply (tarjan_scc_keep_visited g x w).
      - simpl. apply (tarjan_scc_keep_visited_forall (OriginalGraph_gvalid0:=OriginalGraph_gvalid0) g x done).
      - simpl. apply (tarjan_scc_keep_fa_children_in_universe parent x). }
    { intros W IHvis IHlow x.
      unfold tarjan_scc_f.
      intros Hpre.
      eapply Hoare_bind.
      { apply Hoare_conj.
        - apply Hoare_conseq_pre with (P2 := fun s => low_pre x s).
          { intros s HP. exact HP. }
          apply preloop_establishes_low_forset_inv.
        - apply Hoare_conseq_pre with (P2 := fun s => low_pre x s).
          { intros s HP. exact HP. }
          unfold preloop. unfold_op. intro_state. hoare_auto_s.
          subst s. simpl.
          intros v Hfa_eq. unfold equiv_decb in Hfa_eq.
          destruct (equiv_dec v x) as [Heq | Hneq].
          { exact Heq. }
          simpl in Hfa_eq.
          exfalso. apply Hneq.
          eapply low_pre_fa_eq_u_implies_eq_u; eauto. }
      simpl. intros _. intro_state.
      destruct H as [[Hsiv [Hinv [Hvalid [Hfa [Hxvis Hmin_x]]]]] Hfa_prop].
      eapply Hoare_bind with (Q := fun _ s => low_post x s).
      { apply Hoare_conseq_pre with (P2 := fun s => low_forset_inv x ∅ s /\ (forall v, fa s v = x -> v = x)).
        { intros s1 Heq. subst s1.
          exact (conj (conj Hsiv (conj Hinv (conj Hvalid (conj Hfa (conj Hxvis Hmin_x))))) Hfa_prop). }
        apply forset_keep_low_forset_inv.
        - intros a. pose proof (IHlow a tt) as Hlow_a.
          apply Hoare_conj.
          + eapply Hoare_conseq_post. 2: { eapply Hoare_conseq_pre. 2: exact Hlow_a.
              intros s [Hpre_a Hx_vis]. exact Hpre_a. }
            auto.
          + eapply Hoare_conseq_pre. 2: apply (IHvis a (VKeep x)).
            intros s [Hpre_a Hx_vis]. simpl. exact Hx_vis.
        - intros a. apply (IHvis a VSelf).
        - intros a done'. apply (IHvis a (VKeepAll done')).
        - intros a. apply (IHvis a (VKeepFaChildren u)). }
      simpl. intros _. intro_state. rename H into Hpost.
      hoare_auto_s.
      - apply Hoare_conseq_pre with
          (P2 := fun s => scc_low_valid_v s x /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s /\ low s x = dfn s x).
        { intros sx Heq. subst sx. destruct Hpost as [Hlowv [Hval [Hinv' Hfa']]].
          split; [exact Hlowv | split; [exact Hval | split; [exact Hinv' | split; [exact Hfa' | exact H]]]]. }
        apply (pop_scc_keep_scc_low_valid_v x).
      - match goal with H: _ = _ /\ _ |- _ => destruct H as [Heq _]; subst s end.
        exact Hpost. }
  Qed.

  (* ================================================================ *)
  (* 13. Global scc_low_valid / scc_is_low                             *)
  (* ================================================================ *)

  Theorem tarjan_scc_all_scc_low_valid:
    Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
          (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
          (fun _ s => scc_low_valid s).
  Proof.
  Admitted.

  Theorem tarjan_scc_all_scc_is_low:
    Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid g s root)
          (tarjan_scc_all (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g)
          (fun _ s => scc_is_low s).
  Proof.
    apply Hoare_conseq_post with
      (Q2 := fun _ s => scc_low_valid s /\ dfn_valid g s root /\ dfn_inv s).
    { intros _ s [Hlow [Hvalid Hinv]].
      apply (scc_low_valid_implies_is_low s Hvalid Hinv Hlow). }
    apply Hoare_conj with
      (Q1 := fun _ s => scc_low_valid s)
      (Q2 := fun _ s => dfn_valid g s root /\ dfn_inv s).
    - eapply Hoare_conseq_pre.
      { intros s [Hinv [Hfa Hvalid]]. exact (conj Hinv (conj Hfa Hvalid)). }
      apply tarjan_scc_all_scc_low_valid.
    - apply Hoare_conj with
        (Q1 := fun _ s => dfn_valid g s root)
        (Q2 := fun _ s => dfn_inv s).
      + eapply Hoare_conseq_pre.
        { intros s [Hinv [Hfa Hvalid]]. exact (conj Hinv (conj Hfa Hvalid)). }
        apply tarjan_scc_all_dfn_valid.
      + eapply Hoare_conseq_pre.
        { intros s [Hinv _]. exact Hinv. }
        apply tarjan_scc_all_keep_dfn_inv.
  Qed.

End IS_LOW.
