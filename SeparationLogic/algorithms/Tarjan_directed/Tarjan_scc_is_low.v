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

  Lemma stack_split_at_popped_fresh (stk: list V) (v: V):
    forall (popped rest: list V),
      stack_split_at stk v = (popped, rest) ->
      forall w, In w stk -> ~ In w popped -> In w rest.
  Proof.
    induction stk as [| x xs IH]; intros popped rest Hsplit w Hin Hnot_popped.
    - cbn in Hsplit. inversion Hsplit. subst popped rest.
      cbn in Hin. destruct Hin.
    - cbn in Hsplit.
      destruct (equiv_decb x v) eqn:Heqx.
      + (* x = v: split returns (x::nil, xs) *)
        injection Hsplit; intros; subst popped rest.
        cbn in Hin. destruct Hin as [-> | Hin_xs].
        * cbn in Hnot_popped. exfalso. apply Hnot_popped. left. reflexivity.
        * exact Hin_xs.
      + (* x <> v *)
        case_eq (stack_split_at xs v). intros popped' rest' Hsplit_inner.
        rewrite Hsplit_inner in Hsplit. cbn in Hsplit.
        injection Hsplit; intros; subst popped rest.
        cbn in Hin. destruct Hin as [-> | Hin_xs].
        * cbn in Hnot_popped. exfalso. apply Hnot_popped. left. reflexivity.
        * apply (IH popped' rest' Hsplit_inner w Hin_xs).
          intro Hw. apply Hnot_popped. cbn. right. exact Hw.
  Qed.

  Lemma stack_split_at_covers (stk: list V) (v: V):
    forall (popped rest: list V),
      stack_split_at stk v = (popped, rest) ->
      forall w, In w stk -> In w popped \/ In w rest.
  Proof.
    induction stk as [| x xs IH]; intros popped rest Hsplit w Hin.
    - cbn in Hsplit. inversion Hsplit. subst popped rest.
      cbn in Hin. destruct Hin.
    - cbn in Hsplit.
      destruct (equiv_decb x v) eqn:Heqx.
      + injection Hsplit; intros; subst popped rest.
        cbn in Hin. destruct Hin as [-> | Hin_xs].
        * left. left. reflexivity.
        * right. exact Hin_xs.
      + case_eq (stack_split_at xs v). intros popped' rest' Hsplit_inner.
        rewrite Hsplit_inner in Hsplit. cbn in Hsplit.
        injection Hsplit; intros; subst popped rest.
        cbn in Hin. destruct Hin as [-> | Hin_xs].
        * left. left. reflexivity.
        * destruct (IH popped' rest' Hsplit_inner w Hin_xs) as [Hpop | Hrest].
          -- left. right. exact Hpop.
          -- right. exact Hrest.
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

  Lemma set_low_preserves_low_forset_inv (u v: V) (done: V -> Prop) (n: nat):
    u <> v -> ~ done v ->
    Hoare (fun s: @SCCSt V => low_forset_inv u done s)
          (set_low v n)
          (fun _ s => low_forset_inv u done s).
  Proof.
    intros Hne Hndone.
    unfold set_low. intro_state. hoare_auto_s. subst s. simpl.
    unfold low_forset_inv in H. destruct H as [Hsiv [Hinv [Hvalid [Hfa [Huvis Hmin]]]]].
    unfold low_forset_inv. simpl.
    split; [exact Hsiv |].
    split; [exact Hinv |].
    split; [exact Hvalid |].
    split; [exact Hfa |].
    split; [exact Huvis |].
    unfold equiv_decb. destruct (equiv_dec u v) as [Heq | Hneq].
    { exfalso. apply Hne. exact Heq. }
    assert (Hlow_eq: forall w, done w ->
      (fun x : V => if if equiv_dec x v then true else false then n else low s0 x) w = low s0 w). {
      intros w0 Hw0_done.
      destruct (equiv_dec w0 v) as [Heq_w | Hneq_w]; [| reflexivity].
      assert (w0 = v). { rewrite Heq_w. reflexivity. }
      subst w0. contradiction. }
    eapply min_eq_forward.
    - typeclasses eauto.
    - exact Hmin.
    - intros a0 Ha0. exists a0. split; [| apply Nat.le_refl].
      destruct Ha0 as [Ha1 | Ha2].
      + left. destruct Ha1 as [w [[Hw_in Hw_min] Heq_a]].
        exists w. split.
        * unfold min_object_of_subset. split.
          -- simpl. exact Hw_in.
          -- intros x Hx. simpl in Hx.
             destruct Hw_in as [Hw_done [Hw_fa Hw_neq]].
             destruct Hx as [Hx_done [Hx_fa Hx_neq]].
             simpl in Hx_fa, Hx_neq.
             rewrite (Hlow_eq w Hw_done). rewrite (Hlow_eq x Hx_done).
             apply Hw_min. split; [exact Hx_done | split; auto].
        * destruct Hw_in as [Hw_done _]. rewrite (Hlow_eq w Hw_done). exact Heq_a.
      + right. destruct Ha2 as [w [[Hw_in Hw_min] Heq_a]].
        exists w. split.
        * unfold min_object_of_subset. split.
          -- simpl. exact Hw_in.
          -- intros x Hx. simpl in Hx.
             destruct Hw_in as [Hw_back | Hw_u];
             [ destruct Hw_back as [Hw_done [Hw_stack Hw_fa]];
               destruct Hx as [Hx_back | Hx_u];
               [ destruct Hx_back as [Hx_done [Hx_stack Hx_fa']];
                 simpl in Hx_stack; apply Hw_min;
                 left; split; [exact Hx_done | split; [exact Hx_stack | exact Hx_fa']]
               | subst x; apply Hw_min; right; reflexivity ]
             | subst w; destruct Hx as [Hx_back | Hx_u];
               [ destruct Hx_back as [Hx_done [Hx_stack Hx_fa']];
                 simpl in Hx_stack; apply Hw_min;
                 left; split; [exact Hx_done | split; [exact Hx_stack | exact Hx_fa']]
               | subst x; apply Hw_min; right; reflexivity ] ].
        * exact Heq_a.
    - intros a0 Ha0. exists a0. split; [| apply Nat.le_refl].
      destruct Ha0 as [Ha1 | Ha2].
      + left. destruct Ha1 as [w [[Hw_in Hw_min] Heq_a]].
        exists w. split.
        * unfold min_object_of_subset. split.
          -- simpl in Hw_in. exact Hw_in.
          -- intros x Hx. simpl in Hx.
             destruct Hw_in as [Hw_done [Hw_fa Hw_neq]].
             destruct Hx as [Hx_done [Hx_fa Hx_neq]].
             simpl in Hw_fa, Hw_neq, Hx_fa, Hx_neq.
             assert (Hweq: (fun x : V => if if equiv_dec x v then true else false then n else low s0 x) w = low s0 w). { apply Hlow_eq. exact Hw_done. }
             assert (Hxeq: (fun x : V => if if equiv_dec x v then true else false then n else low s0 x) x = low s0 x). { apply Hlow_eq. exact Hx_done. }
             rewrite <- Hweq. rewrite <- Hxeq. apply Hw_min. split; [exact Hx_done | split; auto].
        * destruct Hw_in as [Hw_done _].
          assert (Hweq: (fun x : V => if if equiv_dec x v then true else false then n else low s0 x) w = low s0 w). { apply Hlow_eq. exact Hw_done. }
          rewrite <- Hweq. exact Heq_a.
      + right. destruct Ha2 as [w [[Hw_in Hw_min] Heq_a]].
        exists w. split.
        * unfold min_object_of_subset. split.
          -- simpl in Hw_in. exact Hw_in.
          -- intros x Hx. simpl in Hx.
             destruct Hw_in as [Hw_back | Hw_u];
             [ destruct Hw_back as [Hw_done [Hw_stack Hw_fa]];
               destruct Hx as [Hx_back | Hx_u];
               [ destruct Hx_back as [Hx_done [Hx_stack Hx_fa']];
                 simpl in Hx_stack; apply Hw_min;
                 left; split; [exact Hx_done | split; [exact Hx_stack | exact Hx_fa']]
               | subst x; apply Hw_min; right; reflexivity ]
             | subst w; destruct Hx as [Hx_back | Hx_u];
               [ destruct Hx_back as [Hx_done [Hx_stack Hx_fa']];
                 simpl in Hx_stack; apply Hw_min;
                 left; split; [exact Hx_done | split; [exact Hx_stack | exact Hx_fa']]
               | subst x; apply Hw_min; right; reflexivity ] ].
        * exact Heq_a.
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
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ done v /\
                   dg_step g u v /\ In v (stack s) /\
                   forall w, done w -> forall popped' rest',
                     stack_split_at (stack s) v = (popped', rest') ->
                     ~ In w popped')
          (pop_scc v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s. subst s.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s0) v) as [popped rest] eqn:?.
    simpl.
    destruct H as [Hinv [Hfa_eq [Hndone [Hdg [Hv_in_stack Hdone_not_popped]]]]].
    unfold low_forset_inv in Hinv.
    destruct Hinv as [Hsiv [Hinv' [Hvalid [Hfa_vis [Huvis Hmin]]]]].
    split.
    - unfold low_forset_inv. simpl.
      split.
      { intros w Hin. apply Hsiv. eapply stack_split_at_rest_incl; eauto. }
      split; [exact Hinv' |].
      split; [exact Hvalid |].
      split; [exact Hfa_vis |].
      split; [exact Huvis |].
      eapply min_eq_forward.
      { typeclasses eauto. }
      { exact Hmin. }
      { (* forward: a1 in source set -> exists a2 in target set with a2 <= a1 *)
        intros a1 Ha1.
        destruct Ha1 as [Ha1_left | Ha1_right].
        - exists a1. split; [left; exact Ha1_left | apply Nat.le_refl].
        - destruct Ha1_right as [a0 [[Hright_in Hright_min] Heq_a0]].
          destruct Hright_in as [[Hdone [Hin_stk0 Hfa_neq]] | Heq_u].
          + exists a1. split.
            { right. unfold min_value_of_subset.
              exists a0. split.
              { split.
                - left. split; [exact Hdone |].
                  split; [| exact Hfa_neq].
                  destruct (classic (In a0 rest)) as [Hr | Hnr]; [exact Hr |].
                  destruct (stack_split_at_covers (stack s0) v popped rest Heqp a0
                    Hin_stk0) as [Hpop | Hrest]; [| exfalso; apply Hnr; exact Hrest].
                  exfalso. exact (Hdone_not_popped a0 Hdone popped rest eq_refl Hpop).
                - intros b0 Hb0.
                  destruct Hb0 as [[Hdone_b [Hin_rest_b Hfa_neq_b]] | Heq_ub].
                  + apply Hright_min. left. split; [exact Hdone_b |].
                    split; [eapply stack_split_at_rest_incl; eauto | exact Hfa_neq_b].
                  + subst b0. apply Hright_min. right. reflexivity. }
              { exact Heq_a0. } }
            { apply Nat.le_refl. }
          + subst a0. exists a1. split.
            { right. unfold min_value_of_subset.
              exists u. split.
              { split.
                - right. reflexivity.
                - intros b0 Hb0.
                  destruct Hb0 as [[Hdone_b [Hin_rest_b Hfa_neq_b]] | Heq_ub].
                  + apply Hright_min. left. split; [exact Hdone_b |].
                    split; [eapply stack_split_at_rest_incl; eauto | exact Hfa_neq_b].
                  + subst b0. apply Hright_min. right. reflexivity. }
              { exact Heq_a0. } }
            { apply Nat.le_refl. } }
      { (* backward: a2 in target set -> exists a1 in source set with a1 <= a2 *)
        intros a2 Ha2.
        destruct Ha2 as [Ha2_left | Ha2_right].
        - exists a2. split; [left; exact Ha2_left | apply Nat.le_refl].
        - destruct Ha2_right as [a0 [[Hright_in Hright_min] Heq_a0]].
          destruct Hright_in as [[Hdone [Hin_rest Hfa_neq]] | Heq_u].
          + exists a2. split.
            { right. unfold min_value_of_subset.
              exists a0. split.
              { split.
                - left. split; [exact Hdone |].
                  split; [eapply stack_split_at_rest_incl; eauto | exact Hfa_neq].
                - intros b0 Hb0.
                  destruct Hb0 as [[Hdone_b [Hin_stk0_b Hfa_neq_b]] | Heq_ub].
                  + apply Hright_min. left. split; [exact Hdone_b |].
                    split.
                    { apply (stack_split_at_popped_fresh (stack s0) v popped rest Heqp b0 Hin_stk0_b).
                      exact (Hdone_not_popped b0 Hdone_b popped rest eq_refl). }
                    { exact Hfa_neq_b. }
                  + subst b0. apply Hright_min. right. reflexivity. }
              { exact Heq_a0. } }
            { apply Nat.le_refl. }
          + subst a0. exists a2. split.
            { right. unfold min_value_of_subset.
              exists u. split.
              { split.
                - right. reflexivity.
                - intros b0 Hb0.
                  destruct Hb0 as [[Hdone_b [Hin_stk0_b Hfa_neq_b]] | Heq_ub].
                  + apply Hright_min. left. split; [exact Hdone_b |].
                    split.
                    { apply (stack_split_at_popped_fresh (stack s0) v popped rest Heqp b0 Hin_stk0_b).
                      exact (Hdone_not_popped b0 Hdone_b popped rest eq_refl). }
                    { exact Hfa_neq_b. }
                  + subst b0. apply Hright_min. right. reflexivity. }
              { exact Heq_a0. } }
            { apply Nat.le_refl. } }
    - (* fa s v = u: pop_scc doesn't modify fa *)
      exact Hfa_eq.
  Qed.

  (** [preloop_preserves_ancestor_inv]: [preloop v] modifies [dfn v],
      [low v], [timer], [stack], [visited] — all local to [v].
      No effect on [fa], [low] for [u ≠ v], or [done] vertices. *)
  Lemma preloop_preserves_ancestor_inv (u v: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v)
          (preloop v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    intro_state. destruct H as [Hinv [Hfa_eq [Hnv Hndone]]].
    unfold low_forset_inv in Hinv.
    destruct Hinv as [Hsiv [Hinv' [Hvalid [Hfa_vis [Huvis Hmin]]]]].
    apply Hoare_conj.
    - unfold low_forset_inv. apply Hoare_conj.
      + eapply Hoare_conseq_pre.
        2: apply (preloop_keep_stack_in_visited v).
        intros s1 Hs1. subst s1. exact Hsiv.
      + apply Hoare_conj.
        * eapply Hoare_conseq_pre.
          2: apply (preloop_keep_dfn_inv v).
          intros s1 Hs1. subst s1. exact Hinv'.
        * apply Hoare_conj.
          -- eapply Hoare_conseq_post with
               (Q1 := fun _ s => dfn_valid g s root)
               (Q2 := fun _ s => v ∈ visited s /\ dfn_valid g s root /\ dfn_inv s).
             { intros _ s1 [Hvis1 [Hvalid1 _]]. exact Hvalid1. }
             eapply Hoare_conseq_pre.
             2: apply preloop_preserves_dfn_valid.
             intros s1 Hs1. subst s1. split.
             +++ exact Hnv.
             +++ split.
                 **** exact Hvalid.
                 **** split.
                      ----- exact Hinv'.
                      ----- exact Hfa_vis.
          -- apply Hoare_conj.
             ++ eapply Hoare_conseq_pre.
                2: apply (preloop_keep_fa_visited v).
                intros s1 Hs1. subst s1. exact Hfa_vis.
             ++ apply Hoare_conj.
                ** eapply Hoare_conseq_pre.
                   2: apply (preloop_keep_visited v u).
                   intros s1 Hs1. subst s1. exact Huvis.
                ** unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s.
                   set (u := fa s0 v).
                   set (s := {| visited := visited s0 ∪ [v]; timer := S (timer s0); fa := fa s0;
                                dfn := fun x => if x ==b v then timer s0 else dfn s0 x;
                                low := fun x => if x ==b v then timer s0 else low s0 x;
                                stack := v :: stack s0; sccs := sccs s0 |}).
                   assert (Hchild_eq: children_done s u done == children_done s0 u done).
                   { unfold children_done. apply Sets_equiv_Sets_included. split; sets_unfold; intros x [Hx_done [Hx_fa Hx_neq]];
                       repeat split; auto. }
                   assert (Hback_eq: back_edges_done s u done == back_edges_done s0 u done).
                   { unfold back_edges_done. apply Sets_equiv_Sets_included. split; sets_unfold; intros x [Hx_done [Hx_stack Hx_fa]];
                       repeat split; auto.
                     - destruct Hx_stack as [Heq | Hin]; [subst x; exfalso; apply Hx_fa; unfold u; simpl; reflexivity | exact Hin].
                     - right. exact Hx_stack. }
                   assert (Hlow_child: forall w, w ∈ children_done s0 u done -> low s w = low s0 w).
                   { intros w0 Hw0. unfold children_done in Hw0. sets_unfold in Hw0.
                     destruct Hw0 as [Hw0_done [Hw0_fa Hw0_neq]].
                     unfold s. simpl. unfold equiv_decb. destruct (equiv_dec w0 v) as [Heq | Hneq].
                     - exfalso. rewrite Heq in Hw0_done. apply Hndone. exact Hw0_done.
                     - reflexivity. }
                   assert (Hlow_back: forall w, w ∈ back_edges_done s0 u done -> low s w = low s0 w).
                   { intros w0 Hw0. unfold back_edges_done in Hw0. sets_unfold in Hw0.
                     destruct Hw0 as [Hw0_done [Hw0_stack Hw0_fa]].
                     unfold s. simpl. unfold equiv_decb. destruct (equiv_dec w0 v) as [Heq | Hneq].
                     - exfalso. rewrite Heq in Hw0_done. apply Hndone. exact Hw0_done.
                     - reflexivity. }
                   assert (Hlow_u: low s u = low s0 u).
                   { unfold s. simpl. unfold equiv_decb. destruct (equiv_dec u v) as [Heq | Hneq].
                     - exfalso. apply Hnv. unfold u in Heq. rewrite <- Heq. exact Huvis.
                     - reflexivity. }
                   assert (Hlow_all: forall w, children_done s0 u done w \/ back_edges_done s0 u done w \/ w = u -> low s w = low s0 w).
                   { intros w0 [Hw0 | [Hw0 | Hw0]].
                     - apply Hlow_child. exact Hw0.
                     - apply Hlow_back. exact Hw0.
                     - subst w0. exact Hlow_u. }
                   rewrite Hlow_u. eapply min_eq_forward.
                   --- typeclasses eauto.
                   --- exact Hmin.
                   --- intros a1 Ha1. exists a1. split.
                       +++ destruct Ha1 as [Ha1_L | Ha1_R].
                           *** left. destruct Ha1_L as [w [[Hw_in Hw_min] Heq_a1]]. exists w. split.
                               ---- unfold min_object_of_subset. split.
                                    ++++ apply Hchild_eq. exact Hw_in.
                                    ++++ intros x Hx. apply Hchild_eq in Hx.
                                         rewrite (Hlow_all w (or_introl Hw_in)).
                                         rewrite (Hlow_all x (or_introl Hx)).
                                         apply Hw_min. exact Hx.
                               ---- unfold s. destruct (equiv_dec w v) as [Heq_wv | Hneq_wv].
                                    { exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                                      destruct Hw_in as [Hw_done _]. rewrite Heq_wv in Hw_done. apply Hndone. exact Hw_done. }
                                    unfold s. simpl. unfold equiv_decb. destruct (equiv_dec w v) as [Heq | Hneq].
                                    { exfalso. unfold children_done in Hw_in. sets_unfold in Hw_in.
                                      destruct Hw_in as [Hw_done _]. rewrite Heq in Hw_done. apply Hndone. exact Hw_done. }
                                    { exact Heq_a1. }
                           *** right. destruct Ha1_R as [w [[Hw_in Hw_min] Heq_a1]].
                               assert (Hdfn_w: dfn s w = dfn s0 w).
                               { unfold s. destruct (equiv_dec w v) as [Heq_wv | Hneq_wv].
                                 - exfalso. destruct Hw_in as [Hw_back | Hw_u].
                                   + unfold back_edges_done in Hw_back. sets_unfold in Hw_back.
                                     destruct Hw_back as [Hw_done _]. rewrite Heq_wv in Hw_done.
                                     apply Hndone. exact Hw_done.
                                   + subst w. unfold u in Heq_wv. rewrite <- Heq_wv in Hnv. apply Hnv. exact Huvis.
                                 - unfold s. simpl. unfold equiv_decb. destruct (equiv_dec w v) as [Heq | Hneq].
                                   + contradiction.
                                   + reflexivity. }
                               assert (Hdfn_u: dfn s u = dfn s0 u).
                               { unfold s. destruct (equiv_dec u v) as [Heq_uv | Hneq_uv].
                                 - exfalso. apply Hnv. unfold u in Heq_uv. rewrite <- Heq_uv. exact Huvis.
                                 - unfold s. simpl. unfold equiv_decb. destruct (equiv_dec u v) as [Heq | Hneq].
                                   + contradiction.
                                   + reflexivity. }
                               exists w. split.
                               ---- unfold min_object_of_subset. split.
                                    ++++ destruct Hw_in as [Hw_back | Hw_u].
                                         { left. apply Hback_eq. exact Hw_back. }
                                         { right. exact Hw_u. }
                                    ++++ intros x Hx. destruct Hx as [Hx_back | Hx_u].
                                         { assert (Hdfn_x: dfn s x = dfn s0 x).
                                           { unfold s. destruct (equiv_dec x v) as [Heq_xv | Hneq_xv].
                                             - exfalso. unfold back_edges_done in Hx_back. sets_unfold in Hx_back.
                                               destruct Hx_back as [Hx_done _]. rewrite Heq_xv in Hx_done.
                                               apply Hndone. exact Hx_done.
                                             - unfold s. simpl. unfold equiv_decb. destruct (equiv_dec x v) as [Heq | Hneq].
                                               + contradiction.
                                               + reflexivity. }
                                           rewrite Hdfn_w. rewrite Hdfn_x. apply Hw_min. left. apply Hback_eq. exact Hx_back. }
                                         { subst x. rewrite Hdfn_w. rewrite Hdfn_u. apply Hw_min. right. reflexivity. }
                               ---- unfold s. destruct (equiv_dec w v) as [Heq_wv | Hneq_wv].
                                    { exfalso. destruct Hw_in as [Hw_back | Hw_u].
                                      - unfold back_edges_done in Hw_back. sets_unfold in Hw_back.
                                        destruct Hw_back as [Hw_done _]. rewrite Heq_wv in Hw_done.
                                        apply Hndone. exact Hw_done.
                                      - subst w. unfold u in Heq_wv. rewrite <- Heq_wv in Hnv. apply Hnv. exact Huvis. }
                                    unfold s. simpl. unfold equiv_decb. destruct (equiv_dec w v) as [Heq | Hneq].
                                    { exfalso. destruct Hw_in as [Hw_back | Hw_u].
                                      - unfold back_edges_done in Hw_back. sets_unfold in Hw_back.
                                        destruct Hw_back as [Hw_done _]. rewrite Heq in Hw_done. apply Hndone. exact Hw_done.
                                      - subst w. unfold u in Heq. rewrite <- Heq in Hnv. apply Hnv. exact Huvis. }
                                    { exact Heq_a1. }
                       +++ apply Nat.le_refl.
                   --- intros a2 Ha2. exists a2. split.
                       +++ destruct Ha2 as [Ha2_L | Ha2_R].
                           *** left. destruct Ha2_L as [w [[Hw_in Hw_min] Heq_a2]]. exists w. split.
                               ---- unfold min_object_of_subset. split.
                                    ++++ apply Hchild_eq. exact Hw_in.
                                    ++++ intros x Hx.
                                         assert (Hlw_w: low s w = low s0 w).
                                         { apply Hlow_child. apply Hchild_eq. exact Hw_in. }
                                         assert (Hlw_x: low s x = low s0 x).
                                         { apply Hlow_child. apply Hchild_eq. exact Hx. }
                                         rewrite <- Hlw_w. rewrite <- Hlw_x. apply Hw_min. exact Hx.
                               ---- assert (Hlw_w: low s w = low s0 w).
                                    { apply Hlow_child. apply Hchild_eq. exact Hw_in. }
                                    rewrite <- Hlw_w. exact Heq_a2.
                           *** right. destruct Ha2_R as [w [[Hw_in Hw_min] Heq_a2]].
                               assert (Hdfn_w: dfn s w = dfn s0 w).
                               { unfold s. destruct (equiv_dec w v) as [Heq_wv | Hneq_wv].
                                 - exfalso. destruct Hw_in as [Hw_back | Hw_u].
                                   + unfold back_edges_done in Hw_back. sets_unfold in Hw_back.
                                     destruct Hw_back as [Hw_done _]. rewrite Heq_wv in Hw_done.
                                     apply Hndone. exact Hw_done.
                                   + subst w. unfold u in Heq_wv. rewrite <- Heq_wv in Hnv. apply Hnv. exact Huvis.
                                 - unfold s. simpl. unfold equiv_decb. destruct (equiv_dec w v) as [Heq | Hneq].
                                   + contradiction.
                                   + reflexivity. }
                               assert (Hdfn_u: dfn s u = dfn s0 u).
                               { unfold s. destruct (equiv_dec u v) as [Heq_uv | Hneq_uv].
                                 - exfalso. apply Hnv. unfold u in Heq_uv. rewrite <- Heq_uv. exact Huvis.
                                 - unfold s. simpl. unfold equiv_decb. destruct (equiv_dec u v) as [Heq | Hneq].
                                   + contradiction.
                                   + reflexivity. }
                               exists w. split.
                               ---- unfold min_object_of_subset. split.
                                    ++++ destruct Hw_in as [Hw_back | Hw_u].
                                         { left. apply Hback_eq. exact Hw_back. }
                                         { right. exact Hw_u. }
                                    ++++ intros x Hx. destruct Hx as [Hx_back | Hx_u].
                                         { assert (Hdfn_x: dfn s x = dfn s0 x).
                                           { unfold s. destruct (equiv_dec x v) as [Heq_xv | Hneq_xv].
                                             - exfalso. unfold back_edges_done in Hx_back. sets_unfold in Hx_back.
                                               destruct Hx_back as [Hx_done _]. rewrite Heq_xv in Hx_done.
                                               apply Hndone. exact Hx_done.
                                             - unfold s. simpl. unfold equiv_decb. destruct (equiv_dec x v) as [Heq | Hneq].
                                               + contradiction.
                                               + reflexivity. }
                                           rewrite <- Hdfn_w. rewrite <- Hdfn_x. apply Hw_min. left. apply Hback_eq. exact Hx_back. }
                                         { subst x. unfold u in Hdfn_u. rewrite <- Hdfn_w. rewrite <- Hdfn_u. apply Hw_min. right. reflexivity. }
                               ---- rewrite <- Hdfn_w. exact Heq_a2.
                       +++ apply Nat.le_refl.
    - unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl. reflexivity.
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
    ~ done v -> fa s v = u ->
    low_forset_inv u done s ->
    low_forset_inv u done (RecordSet.set low (fun low0 x => if equiv_decb x v then Nat.min (low s v) n else low0 x) s).
  Admitted.

  (** [set_fa_preserves_low_forset_inv_for_new_child]: When [~ x ∈ visited],
      [u ∈ visited], and [~ done v], setting [fa x := v] does not affect
      [low_forset_inv u done].  The key insight: [x ≠ u] (since x is
      unvisited but u is visited), so [children_done u done] (which requires
      [fa = u]) and [back_edges_done u done] are unchanged. *)
  Lemma set_fa_preserves_low_forset_inv_for_new_child (u v x: V) (done: V -> Prop) (s0: @SCCSt V):
    ~ x ∈ visited s0 -> v ∈ visited s0 -> u ∈ visited s0 -> ~ done v -> fa s0 v = u ->
    low_forset_inv u done s0 ->
    low_forset_inv u done (RecordSet.set fa (fun _ x0 => if equiv_decb x0 x then v else fa s0 x0) s0).
  Proof. Admitted.

  Lemma process_edge_preserves_ancestor_inv (u v x: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit)
    (HW: forall x, Hoare (fun s => low_pre x s /\ v ∈ visited s) (W x)
                        (fun _ s => low_post x s /\ v ∈ visited s))
    (HW_keep_all: forall (a: V) (done': V -> Prop),
                    Hoare (fun s => forall w, done' w -> w ∈ visited s) (W a)
                          (fun _ s => forall w, done' w -> w ∈ visited s)):
    u <> v -> ~ done v -> dg_step g v x ->
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ v ∈ visited s)
          (process_edge v W x)
          (fun _ s => low_forset_inv u done s /\ fa s v = u /\ v ∈ visited s).
  Proof.
    (* Proof strategy: three branches of process_edge.
       Tree edge: set_fa x v ;; W x ;; get' low x ;; update_low v lv.
         - set_fa x v: use set_fa_preserves_low_forset_inv_for_new_child.
         - W x: use HW + HW_keep_all to preserve u's invariant.
           The remaining admit here is that W x preserves all six
           components of low_forset_inv u done (not just the ones in
           low_post x = dfn_valid + dfn_inv + fa_visited).
         - get' low x: pure read.
         - update_low v lv: use update_low_preserves_low_forset_inv_for_other.
       Back edge (in stack): get' dfn x ;; update_low v dv.
         - get': pure read.
         - update_low: use update_low_preserves_low_forset_inv_for_other.
       Cross edge (not in stack): skip, invariant trivially preserved. *)
  Admitted.





  (** [W_preserves_ancestor_inv]: Combining the above, [W v]
      ([tarjan_scc g v]) preserves [low_forset_inv u done] and
      [fa s v = u]. *)
  (** [preloop_keeps_low_forset_inv_other]: [preloop a] preserves
      [low_forset_inv u done] when [~a in visited].  Extracted from the
      first branch of [preloop_preserves_ancestor_inv] (Qed, line 1620). *)
  Lemma preloop_keeps_low_forset_inv_other (u a: V) (done: V -> Prop):
    Hoare (fun s => low_forset_inv u done s /\ ~ a ∈ visited s)
          (preloop a)
          (fun _ s => low_forset_inv u done s /\ a ∈ visited s).
  Proof. Admitted.

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
    (* Proof: same as the first branch of pop_scc_preserves_ancestor_inv (Qed).
       The additional preconditions ensure done vertices are not in the
       popped SCC, so back_edges_done and the min condition are unchanged. *)
  Admitted.

  (** [forset_keeps_low_forset_inv]: [forset (process_edge a W)] preserves
      [low_forset_inv u done] given the fixpoint IH. *)
  Lemma forset_keeps_low_forset_inv (u a: V) (done: V -> Prop)
    (W: V -> program (@SCCSt V) unit)
    (IH: forall x, Hoare (fun s => low_forset_inv u done s /\ ~ x ∈ visited s) (W x)
                         (fun _ s => low_forset_inv u done s)):
    Hoare (fun s => low_forset_inv u done s /\ a ∈ visited s)
          (forset (fun w => dg_step g a w) (process_edge a W))
          (fun _ s => low_forset_inv u done s).
  Proof. Admitted.

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

  (** [pop_scc_keeps_fa]: [pop_scc a] does not modify [fa]. *)
  Lemma pop_scc_keeps_fa (a: V):
    Hoare (fun s => True)
          (pop_scc a)
          (fun _ s => True).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s.
  Qed.

  (** [forset_keeps_fa]: [forset (process_edge a W)] preserves
      [fa s v = parent] given the fixpoint IH. *)
  Lemma forset_keeps_fa (a v parent: V)
    (W: V -> program (@SCCSt V) unit)
    (IH: forall y, Hoare (fun s => fa s v = parent) (W y) (fun _ s => fa s v = parent)):
    Hoare (fun s => fa s v = parent /\ a ∈ visited s)
          (forset (fun w => dg_step g a w) (process_edge a W))
          (fun _ s => fa s v = parent).
  Proof. Admitted.


  Lemma W_preserves_ancestor_inv (u v: V) (done: V -> Prop):
    u <> v -> ~ done v ->
    Hoare (fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    (* Proof strategy (see 20260620-tarjan-scc-is-low-repair-plan.md Step 3):
       Use Hoare_conj to split into (A) low_forset_inv preservation and
       (B) fa s v = u preservation.  Each is proved by Hoare_fix with
       a state-only invariant that does not depend on the fixpoint variable.
       The body (tarjan_scc_f) is decomposed into preloop / forset / pop_scc.
       Sub-lemmas are provided above for each step.
       
       Part A: Hoare_fix with P a s := low_forset_inv u done s /\ ~a in visited
       Part B: Hoare_fix with P a s := fa s v = u (constant in a)
       
       The remaining admitted sub-lemmas need:
       - preloop_keeps_low_forset_inv_other: preloop a preserves u's invariant
       - forset_keeps_low_forset_inv: forset preserves u's invariant (uses IH)
       - pop_scc_keeps_low_forset_inv_other: pop_scc a preserves u's invariant
       - forset_keeps_fa: forset preserves fa s v = u (uses IH) *)
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
    intros Hndone Hmin_s0. set (f := fun (fa0 : V -> V) (x : V) => if equiv_decb x v then u else fa0 x).
    assert (Hchild_eq: children_done (set fa f s0) u done == children_done s0 u done). {
      unfold children_done. simpl. apply Sets_equiv_Sets_included. split; sets_unfold.
      - intros w [Hw_done [Hw_fa Hw_neq]]. unfold f in Hw_fa, Hw_neq; simpl in Hw_fa, Hw_neq. unfold equiv_decb in Hw_fa, Hw_neq. destruct (equiv_dec w v) as [Heqw | Hneqw]. + rewrite Heqw in Hw_done. exfalso. exact (Hndone Hw_done). + split; [exact Hw_done | split; [exact Hw_fa | exact Hw_neq]].
      - intros w [Hw_done [Hw_fa Hw_neq]]. unfold f; simpl; unfold equiv_decb. destruct (equiv_dec w v) as [Heqw | Hneqw]. + rewrite Heqw in Hw_done. exfalso. exact (Hndone Hw_done). + split; [exact Hw_done | split; [exact Hw_fa | exact Hw_neq]]. }
    assert (Hback_eq: back_edges_done (set fa f s0) u done == back_edges_done s0 u done). {
      unfold back_edges_done. simpl. apply Sets_equiv_Sets_included. split; sets_unfold.
      - intros w [Hw_done [Hw_stack Hw_fa]]. unfold f in Hw_fa; simpl in Hw_fa; unfold equiv_decb in Hw_fa. destruct (equiv_dec w v) as [Heqw | Hneqw]. + rewrite Heqw in Hw_done. exfalso. exact (Hndone Hw_done). + split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]].
      - intros w [Hw_done [Hw_stack Hw_fa]]. unfold f; simpl; unfold equiv_decb. destruct (equiv_dec w v) as [Heqw | Hneqw]. + rewrite Heqw in Hw_done. exfalso. exact (Hndone Hw_done). + split; [exact Hw_done | split; [exact Hw_stack | exact Hw_fa]]. }
    unfold f.
    apply min_eq_forward with (f1 := fun x : nat => x) (f2 := fun x : nat => x) (P1 := fun n => min_value_of_subset Nat.le (children_done s0 u done) (low s0) n \/ min_value_of_subset Nat.le (fun w => back_edges_done s0 u done w \/ w = u) (dfn s0) n) (P2 := fun n => min_value_of_subset Nat.le (children_done (RecordSet.set fa (fun _ x => if equiv_decb x v then u else fa s0 x) s0) u done) (low s0) n \/ min_value_of_subset Nat.le (fun w => back_edges_done (RecordSet.set fa (fun _ x => if equiv_decb x v then u else fa s0 x) s0) u done w \/ w = u) (dfn s0) n) (n := low s0 u); [typeclasses eauto|exact Hmin_s0| |].
    { intros a1 Ha1; destruct Ha1 as [Ha1|Ha1].
      - destruct Ha1 as [w' [[Hw_in Hw_min] Heq_a1]]; exists a1; split; [left; exists w'; split; [unfold min_object_of_subset; split; [apply Hchild_eq; exact Hw_in|intros x Hx; apply Hchild_eq in Hx; apply Hw_min; exact Hx]|exact Heq_a1]|apply Nat.le_refl].
      - destruct Ha1 as [w' [[Hw_in Hw_min] Heq_a1]]; exists a1; split; [right; exists w'; split; [unfold min_object_of_subset; split; [destruct Hw_in as [Hw_back|Hw_u]; [left; apply Hback_eq; exact Hw_back|right; exact Hw_u]|intros x Hx; destruct Hx as [Hx_back|Hx_u]; [apply Hw_min; left; apply Hback_eq; exact Hx_back|subst x; apply Hw_min; right; reflexivity]]|exact Heq_a1]|apply Nat.le_refl]. }
    { intros a2 Ha2; destruct Ha2 as [Ha2|Ha2].
      - destruct Ha2 as [w' [[Hw_in Hw_min] Heq_a2]]; exists a2; split; [left; exists w'; split; [unfold min_object_of_subset; split; [apply Hchild_eq; exact Hw_in|intros x Hx; apply Hchild_eq in Hx; apply Hw_min; exact Hx]|exact Heq_a2]|apply Nat.le_refl].
      - destruct Ha2 as [w' [[Hw_in Hw_min] Heq_a2]]; exists a2; split; [right; exists w'; split; [unfold min_object_of_subset; split; [destruct Hw_in as [Hw_back|Hw_u]; [left; apply Hback_eq; exact Hw_back|right; exact Hw_u]|intros x Hx; destruct Hx as [Hx_back|Hx_u]; [apply Hw_min; left; apply Hback_eq; exact Hx_back|subst x; apply Hw_min; right; reflexivity]]|exact Heq_a2]|apply Nat.le_refl]. }
  Qed.

  Lemma set_fa_W_preserves_low_forset_inv (u v: V) (done: V -> Prop):
    u <> v -> dg_step g u v -> ~ done v ->
    Hoare (fun s => low_forset_inv u done s /\ ~ v ∈ visited s /\ ~ done v)
          (set_fa v u;; tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g v)
          (fun _ s => low_forset_inv u done s /\ fa s v = u).
  Proof.
    intros Hneq_uv Hdg Hndone_param.
    apply (Hoare_bind (fun s => low_forset_inv u done s /\ ~ v ∈ visited s /\ ~ done v)
                      (set_fa v u)
                      (fun _ s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v)
                      (fun _ => tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g v)
                      (fun _ s => low_forset_inv u done s /\ fa s v = u)).
    { unfold set_fa. intro_state. hoare_auto_s. subst s. simpl.
      destruct H as [Hinv [Hnv Hndone]].
      unfold low_forset_inv in Hinv.
      destruct Hinv as [Hsiv [Hinv' [Hvalid_s0 [Hfa_vis_s0 [Huvis_s0 Hmin_s0]]]]].
      destruct Hinv' as [Hlt_s0 [Hiff_s0 Hpos_s0]].
      split.
      - unfold low_forset_inv. simpl.
        split; [exact Hsiv |].
        split; [split; [exact Hlt_s0 | split; [exact Hiff_s0 | exact Hpos_s0]] |].
        split; [unfold dfn_valid; intros x y Htree; apply Hvalid_s0; unfold dg_step in Htree; destruct Htree as [e [Htree' [Hfst Hsnd]]]; unfold original_step in Htree'; simpl in Htree'; destruct Htree' as [w [Hwvis [Hwfa [Hwfst Hwsnd]]]]; assert (Hwneq: w <> v) by (intro Heq; rewrite Heq in Hwvis; exact (Hnv Hwvis)); unfold equiv_decb in Hwfa, Hwfst; destruct (equiv_dec w v) as [Heq | Hneq]; [exfalso; rewrite Heq in Hwvis; exact (Hnv Hwvis) |]; unfold dg_step; exists e; split; [| split]; auto; unfold original_step; exists w; repeat split; auto |].
        split; [intros w Hfa_neq; destruct (equiv_dec w v) as [Heq | Hneq_w]; [rewrite Heq in *; simpl; unfold equiv_decb; destruct (equiv_dec v v) as [_ | Hc]; [| exfalso; apply Hc; reflexivity]; exact Huvis_s0 | unfold set_fa in Hfa_neq; simpl in Hfa_neq; unfold equiv_decb in Hfa_neq; destruct (equiv_dec w v) as [Heq' | Hneq'] in Hfa_neq; [exfalso; apply Hneq_w; exact Heq' |]; unfold set_fa; simpl; unfold equiv_decb; destruct (equiv_dec w v) as [Heq'' | Hneq'']; [exfalso; apply Hneq_w; exact Heq'' |]; apply Hfa_vis_s0; exact Hfa_neq] |].
        split; [exact Huvis_s0 |].
        apply (set_fa_preserves_min u v done s0 Hndone Hmin_s0).
      - split; [| split; [exact Hnv | exact Hndone]].
        simpl; unfold equiv_decb; destruct (equiv_dec v v) as [_ | Hc]; [reflexivity | exfalso; apply Hc; reflexivity]. }
    intros _. apply Hoare_conseq_pre with (P2 := fun s => low_forset_inv u done s /\ fa s v = u /\ ~ v ∈ visited s /\ ~ done v). { intros s H. exact H. } apply (W_preserves_ancestor_inv u v done Hneq_uv Hndone_param).
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
    split; intro Hlow; unfold low_forset_inv in Hlow;
      destruct Hlow as [Hsiv [Hinv [Hval' [Hfa'' [Hvis' Hmin]]]]];
      destruct Hinv as [Hlt [Hiff' Hpos']].
    - (* forward: done1 → done2 *)
      split; [exact Hsiv |].
      split; [exact (conj Hlt (conj Hiff' Hpos')) |].
      split; [exact Hval' |].
      split; [exact Hfa'' |].
      split; [exact Hvis' |].
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
    intros Hdg HW. unfold process_edge, if_else. intro_state. apply Hoare_choice.
    { (* Tree edge *) apply Hoare_assume_bind. simpl. eapply Hoare_bind.
      { (* set_fa v u *)
        unfold set_fa. intro_state. hoare_auto_s.
        instantiate (1 := fun (_:unit) (s:SCCSt) => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w).
        match goal with Hconj: _ /\ _ |- _ => destruct Hconj as [Hnv Hs1]; subst s1 end. simpl.
        intros w0 [Hfa_eq Hfa_neq]. simpl in Hfa_eq. unfold equiv_decb in Hfa_eq.
        destruct (equiv_dec w0 v) as [Heq | Hneq_w].
        { rewrite Heq in *. simpl in *.
          destruct (equiv_dec u parent) as [Heq_up | Hneq_up].
          { rewrite Heq_up in Hdg. exact Hdg. }
          { exfalso. apply Hneq_up. rewrite H2 in Hfa_eq.
            match type of Hfa_eq with context [set fa ?g ?s0] =>
              pose proof (@set_get SCCSt (V -> V) fa _ g s0) as Hg;
              pattern (fa (set fa g s0)) in Hfa_eq; rewrite Hg in Hfa_eq;
              simpl in Hfa_eq; unfold equiv_decb in Hfa_eq;
              destruct (equiv_dec v v) as [e | n] in Hfa_eq;
              [exact Hfa_eq | exfalso; apply n; reflexivity] end. } }
        { rewrite H2 in Hfa_eq, Hfa_neq. simpl in Hfa_eq, Hfa_neq.
          unfold equiv_decb in Hfa_eq, Hfa_neq.
          destruct (equiv_dec w0 v) as [e | n] in Hfa_eq.
          { exfalso. apply Hneq_w. exact e. }
          { destruct (equiv_dec w0 v) as [e' | n'] in Hfa_neq.
            { exfalso. apply Hneq_w. exact e'. }
            { apply H. split; assumption. } } } }
      { simpl. intros _. eapply Hoare_bind.
        { apply HW. }
        { simpl. intros _. eapply Hoare_bind.
          { instantiate (1 := fun (lv: nat) (s: SCCSt) => forall w, fa s w = parent /\ fa s w <> w -> dg_step g parent w).
            unfold get'. intro_state. hoare_auto_s.
            destruct H2, H3. subst s. eapply H1. split; assumption. }
          { simpl. intros lv. unfold update_low. intro_state. hoare_auto_s.
            { unfold set_low. intro_state. hoare_auto_s.
              rewrite H4, H3 in H5. destruct H5. eapply H1. split; assumption. }
            { destruct H2, H3. subst s. eapply H1. split; assumption. } } } } }
    { (* Non-tree edge *) intro_state. hoare_auto_s.
      { (* In stack: update_low u (dfn s0 v) *)
        unfold update_low. intro_state. hoare_auto_s.
        { (* lv < low: set_low, fa unchanged *)
          unfold set_low. intro_state. hoare_auto_s.
          rewrite H5, H4 in H6. destruct H6. eapply H. split; assumption. }
        { (* skip: fa unchanged *)
          destruct H1. subst s. destruct H4. eapply H. split; assumption. } }
      { (* Not in stack: skip, fa unchanged *)
        destruct H3. subst s. destruct H4. rewrite H1 in H3, H4. eapply H. split; assumption. } }
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
    { simpl. intros _.
      eapply Hoare_bind with (R := fun _ s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v).
      { (* forset: Hoare_forset provides a ∈ universe = dg_step g a a0 *)
        apply (@Hoare_forset SCCSt V
          (fun done s => forall v, fa s v = parent /\ fa s v <> v -> dg_step g parent v)
          (fun v => dg_step g a v) (process_edge a W)).
        { unfold Proper, respectful. intros. subst. reflexivity. }
        { intros todo a0 Hsub Huniv Hnotdone.
          apply process_edge_keep_fa_children.
          { exact Huniv. }
          { intros x. apply IH. } } }
      { simpl. intros _.
        intro_state. hoare_auto_s.
        { (* pop_scc a: fa unchanged *)
          unfold pop_scc. intro_state. hoare_auto_s. subst s. simpl.
          unfold pop_scc_state.
          destruct (stack_split_at (stack s0) a) as [popped rest] eqn:Heqp; simpl.
          match goal with Hfa: fa ?s' ?v = _ /\ _ |- _ => destruct Hfa as [Hfa_eq Hfa_neq] end.
          match goal with Heq: ?x = s0 |- _ => rewrite Heq in Hfa_eq, Hfa_neq end.
          unfold pop_scc_state in Hfa_eq, Hfa_neq.
          rewrite Heqp in Hfa_eq, Hfa_neq. simpl in Hfa_eq, Hfa_neq.
          eapply H. split; eauto. }
        { (* skip: fa unchanged *)
          destruct H1. subst s. destruct H2. eapply H. split; assumption. } } }
  Qed.

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
  Proof. Admitted.

  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s: @SCCSt V => low_pre u s)
          (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
          (fun _ s => low_post u s).
  Proof. Admitted.

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
