Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relations.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From MaxMinLib Require Import MaxMin Interface.
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

  Definition back_edges_done (s: @SCCSt V) (u: V) (done: V -> Prop) (v: V): Prop :=
    v ∈ done /\ In v (stack s) /\ fa s v <> u.

  Definition low_forset_inv (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
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
    ~ u ∈ visited s /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s.

  Definition low_post (u: V) (s: @SCCSt V): Prop :=
    scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s.

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
      (Q1 := fun _ s => dfn_inv s)
      (Q2 := fun _ s => dfn_valid g s root /\ fa_visited s /\ u ∈ visited s /\
                      min_value_of_subset Nat.le
                        (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
                         min_value_of_subset Nat.le
                           (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
                        (fun x => x) (low s u)).
    - eapply Hoare_conseq_pre.
      { intros s Hpre. destruct Hpre as [_ [_ [Hinv _]]]. exact Hinv. }
      apply preloop_keep_dfn_inv.
    - apply Hoare_conj with
        (Q1 := fun _ s => dfn_valid g s root)
        (Q2 := fun _ s => fa_visited s /\ u ∈ visited s /\
                        min_value_of_subset Nat.le
                          (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
                           min_value_of_subset Nat.le
                             (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
                          (fun x => x) (low s u)).
      + eapply Hoare_conseq_post with
          (Q2 := fun _ s => u ∈ visited s /\ dfn_valid g s root /\ dfn_inv s).
        { intros _ s [Hvis [Hvalid _]]. exact Hvalid. }
        apply preloop_preserves_dfn_valid.
      + apply Hoare_conj with
          (Q1 := fun _ s => fa_visited s)
          (Q2 := fun _ s => u ∈ visited s /\
                          min_value_of_subset Nat.le
                            (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
                             min_value_of_subset Nat.le
                               (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
                            (fun x => x) (low s u)).
        * eapply Hoare_conseq_pre.
          { intros s Hpre. destruct Hpre as [_ [_ [_ Hfa]]]. exact Hfa. }
          apply preloop_keep_fa_visited.
        * apply Hoare_conj with
            (Q1 := fun _ s => u ∈ visited s)
            (Q2 := fun _ s => min_value_of_subset Nat.le
                                (min_value_of_subset Nat.le (children_done s u ∅) (low s) ∪
                                 min_value_of_subset Nat.le
                                   (fun w => back_edges_done s u ∅ w \/ w = u) (dfn s))
                                (fun x => x) (low s u)).
          -- eapply Hoare_conseq_pre.
             { intros s Hpre. exact I. }
             apply preloop_self_visited.
          -- eapply Hoare_conseq_post with
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
    apply (set_fa_preserves_dfn_pre_child_rich (V:=V) (E:=E)).
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
    low_forset_inv u done s ->
    low_forset_inv u (done ∪ [v])
      (RecordSet.set low (fun low0 x => if equiv_decb x u then Nat.min (low s u) (low s v) else low0 x) s).
  Proof.
    intros Hinv_s.
    unfold low_forset_inv in Hinv_s.
    destruct Hinv_s as [Hinv [Hvalid [Hfa [Huvis Hmin]]]].
    unfold low_forset_inv. simpl.
    destruct Hinv as [Hlt [Hiff Hpos]].
    (* Helper: children_done and back_edges_done don't depend on low *)
    assert (Hchild: children_done
      (RecordSet.set low (fun low0 x => if equiv_decb x u then Nat.min (low s u) (low s v) else low0 x) s) u (done ∪ [v])
      == children_done s u (done ∪ [v])).
    { unfold children_done. simpl. reflexivity. }
    assert (Hback: (fun w => back_edges_done
      (RecordSet.set low (fun low0 x => if equiv_decb x u then Nat.min (low s u) (low s v) else low0 x) s) u (done ∪ [v]) w \/ w = u)
      == (fun w => back_edges_done s u (done ∪ [v]) w \/ w = u)).
    { unfold back_edges_done. simpl. reflexivity. }
    rewrite Hchild, Hback.
    split.
    { split; [exact Hlt | split; [exact Hiff | exact Hpos]]. }
    split.
    { exact Hvalid. }
    split.
    { exact Hfa. }
    split.
    { exact Huvis. }
    simpl.
    eapply (min_value_of_subset_nested_update_left_nat
      (A := V) (B := V)
      (low s) (children_done s u done) v
      (dfn s) (fun w => back_edges_done s u done w \/ w = u)
      (low s u)).
    exact Hmin.
  Qed.

  Lemma process_edge_keep_low_forset_inv (u v: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                     (fun _ s => low_post x s /\ u ∈ visited s)) ->
    Hoare (fun s => low_forset_inv u done s)
          (process_edge u W v)
          (fun _ s => low_forset_inv u (done ∪ [v]) s).
  Proof.
    intros HW.
    unfold process_edge, if_else.
    intro_state.
    unfold low_forset_inv in H.
    destruct H as [Hinv [Hvalid [Hfa [Huvis Hmin]]]].
    destruct Hinv as [Hlt [Hiff Hpos]].
    apply Hoare_choice.
    - (* Tree edge: ~v ∈ visited *)
      apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := fun s => low_pre v s /\ u ∈ visited s).
      { intros s1 [Hnv Hs1]. subst s1. unfold low_pre.
        split.
        - split; [exact Hnv |].
          split; [exact Hvalid |].
          split; [| exact Hfa].
          split; [exact Hlt | split; [exact Hiff | exact Hpos]].
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
      - (* low v < low u: set_low branch *)
        unfold set_low.
        eapply Hoare_conseq_post.
        apply Hoare_update'.
        simpl. intros _ s2 Heq. destruct Heq. simpl.
        apply update_low_tree_edge.
        unfold low_forset_inv.
        split; [split; [exact Hlt_mid | split; [exact Hiff_mid | exact Hpos_mid]] |].
        split; [exact Hvalid_mid |].
        split; [exact Hfa_mid |].
        split; [exact Huvis_mid |].
        exact Hmin.
      - (* skip: low v >= low u, state unchanged *)
        destruct H2 as [Heq_s _]. subst s.
        unfold low_forset_inv. simpl.
        split.
        { split; [exact Hlt_mid | split; [exact Hiff_mid | exact Hpos_mid]]. }
        split.
        { exact Hvalid_mid. }
        split.
        { exact Hfa_mid. }
        split.
        { exact Huvis_mid. }
        (* min condition: since low v >= low u, old min still works *)
        simpl.
        rewrite Nat.min_l; [| lia].
        (* Old Hmin from original state s0 still applies because:
           children_done s1 u done and low values are same as in s0.
           Need to show Hmin for s1, not just s0.
           For now, admit — this requires showing s1 preserves the min condition. *)
        admit.
    - (* Non-tree edge: v is visited *)
      intro_state. hoare_auto_s.
      + (* v in stack: back edge *)
        intro_state. hoare_auto_s. subst s. simpl.
        eapply Hoare_bind with (Q := fun dv s => s = s0).
        eapply Hoare_conseq_post.
        2: apply Hoare_get'.
        simpl. intros dv s [Heq_s Heq_dv]. subst s. subst dv. simpl.
        eapply Hoare_bind with (Q := fun old_low s => s = s0).
        eapply Hoare_conseq_post.
        2: apply Hoare_get'.
        simpl. intros old_low s [Heq_s Heq_old]. subst s. subst old_low. simpl.
        unfold set_low.
        eapply Hoare_conseq_post.
        { intros _ s' Heq. pose proof Heq as Heq'. move Heq at bottom. revert s' Heq. intros s Heq. subst s. simpl.
          unfold low_forset_inv. simpl.
          split.
          { split; [exact Hlt | split; [exact Hiff | exact Hpos]]. }
          split.
          { exact Hvalid. }
          split.
          { exact Hfa. }
          split.
          { exact Huvis. }
          simpl.
          eapply (min_value_of_subset_nested_update_right_nat
            (A := V) (B := V)
            (low s0) (children_done s0 u done)
            (dfn s0) (fun w => back_edges_done s0 u done w \/ w = u) v
            (low s0 u)).
          exact Hmin. }
        apply Hoare_update'.
      + (* v not in stack: cross edge — skip *)
        destruct H2 as [Heq _]. subst s.
        unfold low_forset_inv. simpl.
        split.
        { split; [exact Hlt | split; [exact Hiff | exact Hpos]]. }
        split.
        { exact Hvalid. }
        split.
        { exact Hfa. }
        split.
        { exact Huvis. }
        (* min condition unchanged — cross edge adds nothing to either set *)
        simpl.
        (* This is true because neither children_done nor back_edges_done gains v.
           Since we don't have fa v ≠ u or fa v = u guarantees here, we leave this as an admit
           for now. The proof requires cross_edge_fa_cases to show fa v ≠ u, then children_done_no_add
           and back_edges_done_no_add to show the sets are unchanged. *)
        admit.
  Admitted.

  (* ================================================================ *)
  (* 11. Forset Induction                                              *)
  (* ================================================================ *)

  Lemma forset_keep_low_forset_inv (u: V) (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (fun s => low_pre x s /\ u ∈ visited s) (W x)
                     (fun _ s => low_post x s /\ u ∈ visited s)) ->
    Hoare (fun s => low_forset_inv u ∅ s)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => scc_low_valid_v s u /\ dfn_valid g s root /\ dfn_inv s /\ fa_visited s).
  Proof.
  Admitted.

  (* ================================================================ *)
  (* 12. tarjan_scc Core Theorem                                       *)
  (* ================================================================ *)

  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
          (fun _ s => low_post u s).
  Proof.
  Admitted.

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
  Admitted.

End IS_LOW.
