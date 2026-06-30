Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn
  Tarjan_scc_low_defs Tarjan_scc_low_pure Tarjan_scc_low_primitives.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section LOW_SEGMENT.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

  Definition stack_segment_reachable_closed
             (a: V) (s: @SCCSt V): Prop :=
    forall v w,
      In v (stack s) ->
      dfn s a <= dfn s v ->
      dg_reachable g v w ->
      w ∈ visited s.

  Definition stack_segment (a: V) (s: @SCCSt V) (x: V): Prop :=
    In x (stack s) /\ dfn s a <= dfn s x.

  Definition reachable_closed_from
             (a: V) (s: @SCCSt V): Prop :=
    forall w,
      dg_reachable g a w ->
      w ∈ visited s.

  Definition stack_segment_covered_from
             (a: V) (s: @SCCSt V): Prop :=
    forall v,
      In v (stack s) ->
      dfn s a <= dfn s v ->
      dg_reachable g a v.

  Definition root_segment_reachable_contract
             (a: V) (s: @SCCSt V): Prop :=
    reachable_closed_from a s /\
    stack_segment_covered_from a s.

  Lemma root_segment_reachable_contract_implies_segment_closed
        (a: V) (s: @SCCSt V):
    root_segment_reachable_contract a s ->
    stack_segment_reachable_closed a s.
  Proof.
    intros [Hclosed Hcovered].
    unfold stack_segment_reachable_closed.
    intros v w Hv_stack Hdfn Hreach.
    unfold reachable_closed_from in Hclosed.
    apply Hclosed.
    eapply dg_reachable_trans with (y := v).
    - apply Hcovered; auto.
    - exact Hreach.
  Qed.

  Definition processed_reachable_from
             (u: V) (done: V -> Prop) (s: @SCCSt V) (x: V): Prop :=
    x = u \/
    exists v,
      done v /\
      dg_step g u v /\
      dg_reachable g v x.

  Definition pending_root_escape
             (u: V) (done: V -> Prop) (s: @SCCSt V)
             (x w: V): Prop :=
    exists a,
      dg_reachable g x u /\
      dg_step g u a /\
      ~ done a /\
      dg_reachable g a w.

  Definition old_stack_escape_anchor
             (u: V) (s: @SCCSt V) (x w: V): Prop :=
    exists b,
      In b (stack s) /\
      dfn s b < dfn s u /\
      low s u <= dfn s b /\
      dg_reachable g x b /\
      dg_reachable g b w.

  Definition segment_escape_accounted
             (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall x w,
      stack_segment u s x ->
      dg_reachable g x w ->
      ~ w ∈ visited s ->
      pending_root_escape u done s x w \/
      old_stack_escape_anchor u s x w.

  Definition stack_segment_covered_by_done
             (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall x,
      In x (stack s) ->
      dfn s u <= dfn s x ->
      processed_reachable_from u done s x.

  Definition low_iteration_segment_inv
             (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    low_iteration_inv g root u done s /\
    segment_escape_accounted u done s /\
    stack_segment_covered_by_done u done s /\
    stack_dfn_order s /\
    dfn_injective s.

  Definition low_iteration_segment_entry
             (u: V) (s: @SCCSt V): Prop :=
    low_iteration_segment_inv u ∅ s.

  Definition low_iteration_segment_done
             (u: V) (s: @SCCSt V): Prop :=
    low_iteration_segment_inv u (dg_step g u) s.

  Definition active_done_child_segment_summaries
             (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    forall a,
      done a ->
      dg_step g u a ->
      fa s a = u ->
      fa s a <> a ->
      In a (stack s) ->
      low_iteration_segment_done a s.

  Definition low_iteration_segment_loop_inv
             (u: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    low_iteration_segment_inv u done s /\
    active_done_child_segment_summaries u done s.

  Definition low_iteration_segment_loop_entry
             (u: V) (s: @SCCSt V): Prop :=
    low_iteration_segment_loop_inv u ∅ s.

  Definition low_iteration_segment_loop_done
             (u: V) (s: @SCCSt V): Prop :=
    low_iteration_segment_loop_inv u (dg_step g u) s.

  Lemma processed_reachable_from_mono
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V) (x: V):
    processed_reachable_from u done1 s x ->
    (forall v, done1 v -> done2 v) ->
    processed_reachable_from u done2 s x.
  Proof.
    intros Hproc Hsub.
    unfold processed_reachable_from in Hproc |- *.
    destruct Hproc as [Hx | (v & Hdone & Hstep & Hreach)].
    - left. exact Hx.
    - right. exists v. split; [apply Hsub; exact Hdone |].
      split; [exact Hstep | exact Hreach].
  Qed.

  Lemma processed_reachable_from_proper
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V) (x: V):
    done1 == done2 ->
    (processed_reachable_from u done1 s x <->
     processed_reachable_from u done2 s x).
  Proof.
    intros Hequiv.
    split; intros Hproc.
    - eapply processed_reachable_from_mono; [exact Hproc |].
      intros v Hv. apply (proj1 (Hequiv v)). exact Hv.
    - eapply processed_reachable_from_mono; [exact Hproc |].
      intros v Hv. apply (proj2 (Hequiv v)). exact Hv.
  Qed.

  Lemma pending_root_escape_proper
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V) (x w: V):
    done1 == done2 ->
    (pending_root_escape u done1 s x w <->
     pending_root_escape u done2 s x w).
  Proof.
    intros Hequiv.
    unfold pending_root_escape.
    split.
    - intros (a & Hxu & Hua & Hnot_done & Haw).
      exists a.
      split; [exact Hxu |].
      split; [exact Hua |].
      split; [| exact Haw].
      intros Hdone2. apply Hnot_done. apply (proj2 (Hequiv a)). exact Hdone2.
    - intros (a & Hxu & Hua & Hnot_done & Haw).
      exists a.
      split; [exact Hxu |].
      split; [exact Hua |].
      split; [| exact Haw].
      intros Hdone1. apply Hnot_done. apply (proj1 (Hequiv a)). exact Hdone1.
  Qed.

  Lemma segment_escape_accounted_proper
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V):
    done1 == done2 ->
    (segment_escape_accounted u done1 s <->
     segment_escape_accounted u done2 s).
  Proof.
    intros Hequiv.
    unfold segment_escape_accounted.
    split; intros Haccount x w Hseg Hreach Hnot_vis;
      specialize (Haccount x w Hseg Hreach Hnot_vis) as [Hpending | Hanchor].
    - left.
      apply (proj1 (pending_root_escape_proper u done1 done2 s x w Hequiv)).
      exact Hpending.
    - right. exact Hanchor.
    - left.
      apply (proj2 (pending_root_escape_proper u done1 done2 s x w Hequiv)).
      exact Hpending.
    - right. exact Hanchor.
  Qed.

  Lemma segment_escape_accounted_antimono
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V):
    segment_escape_accounted u done1 s ->
    (forall v, done2 v -> done1 v) ->
    segment_escape_accounted u done2 s.
  Proof.
    intros Haccount Hsub.
    unfold segment_escape_accounted in Haccount |- *.
    intros x w Hseg Hreach Hnot_vis.
    specialize (Haccount x w Hseg Hreach Hnot_vis) as [Hpending | Hanchor].
    - left.
      unfold pending_root_escape in Hpending |- *.
      destruct Hpending as (a & Hxu & Hua & Hnot_done1 & Haw).
      exists a. split; [exact Hxu | split; [exact Hua | split; [| exact Haw]]].
      intros Hdone2. apply Hnot_done1. apply Hsub. exact Hdone2.
    - right. exact Hanchor.
  Qed.

  Lemma stack_segment_covered_by_done_proper
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V):
    done1 == done2 ->
    (stack_segment_covered_by_done u done1 s <->
     stack_segment_covered_by_done u done2 s).
  Proof.
    intros Hequiv.
    unfold stack_segment_covered_by_done.
    split; intros Hcovered x Hx_stack Hdfn.
    - apply (proj1 (processed_reachable_from_proper u done1 done2 s x Hequiv)).
      apply Hcovered; auto.
    - apply (proj2 (processed_reachable_from_proper u done1 done2 s x Hequiv)).
      apply Hcovered; auto.
  Qed.

  Lemma stack_segment_covered_by_done_mono
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V):
    stack_segment_covered_by_done u done1 s ->
    (forall v, done1 v -> done2 v) ->
    stack_segment_covered_by_done u done2 s.
  Proof.
    intros Hcovered Hsub.
    unfold stack_segment_covered_by_done in Hcovered |- *.
    intros x Hstack Hdfn.
    eapply processed_reachable_from_mono; [apply Hcovered; eauto |].
    exact Hsub.
  Qed.

  Lemma low_iteration_segment_inv_proper
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V):
    done1 == done2 ->
    (low_iteration_segment_inv u done1 s <->
     low_iteration_segment_inv u done2 s).
  Proof.
    intros Hequiv.
    pose proof (low_iteration_inv_proper g root u) as Hiter_proper.
    specialize (Hiter_proper done1 done2 Hequiv s s eq_refl).
    destruct Hiter_proper as [Hiter12 Hiter21].
    destruct (segment_escape_accounted_proper u done1 done2 s Hequiv)
      as [Haccount12 Haccount21].
    destruct (stack_segment_covered_by_done_proper u done1 done2 s Hequiv)
      as [Hcovered12 Hcovered21].
    split; intros Hseg.
    - destruct Hseg as [Hiter [Haccount [Hcovered [Hord Hinj]]]].
      split; [apply Hiter12; exact Hiter |].
      split; [apply Haccount12; exact Haccount |].
      split; [apply Hcovered12; exact Hcovered |].
      split; [exact Hord | exact Hinj].
    - destruct Hseg as [Hiter [Haccount [Hcovered [Hord Hinj]]]].
      split; [apply Hiter21; exact Hiter |].
      split; [apply Haccount21; exact Haccount |].
      split; [apply Hcovered21; exact Hcovered |].
      split; [exact Hord | exact Hinj].
  Qed.

  Lemma active_done_child_segment_summaries_proper
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V):
    done1 == done2 ->
    (active_done_child_segment_summaries u done1 s <->
     active_done_child_segment_summaries u done2 s).
  Proof.
    intros Hequiv.
    unfold active_done_child_segment_summaries.
    split; intros Hsum a Hdone Hdg Hfa Hfa_ne Hstack.
    - apply Hsum; auto.
      apply (proj2 (Hequiv a)). exact Hdone.
    - apply Hsum; auto.
      apply (proj1 (Hequiv a)). exact Hdone.
  Qed.

  Lemma low_iteration_segment_loop_inv_proper
        (u: V) (done1 done2: V -> Prop) (s: @SCCSt V):
    done1 == done2 ->
    (low_iteration_segment_loop_inv u done1 s <->
     low_iteration_segment_loop_inv u done2 s).
  Proof.
    intros Hequiv.
    destruct (low_iteration_segment_inv_proper u done1 done2 s Hequiv)
      as [Hseg12 Hseg21].
    destruct (active_done_child_segment_summaries_proper u done1 done2 s Hequiv)
      as [Hsum12 Hsum21].
    unfold low_iteration_segment_loop_inv.
    split; intros [Hseg Hsum].
    - split; [apply Hseg12; exact Hseg | apply Hsum12; exact Hsum].
    - split; [apply Hseg21; exact Hseg | apply Hsum21; exact Hsum].
  Qed.

  Lemma low_iteration_segment_loop_inv_forget
        (u: V) (done: V -> Prop) (s: @SCCSt V):
    low_iteration_segment_loop_inv u done s ->
    low_iteration_segment_inv u done s.
  Proof.
    intros [Hseg _]. exact Hseg.
  Qed.

  Lemma low_iteration_done_root_implies_segment_closed
        (u: V) (s: @SCCSt V):
    low_iteration_done g root u s ->
    segment_escape_accounted u (dg_step g u) s ->
    stack_segment_covered_by_done u (dg_step g u) s ->
    low s u = dfn s u ->
    stack_segment_reachable_closed u s.
  Proof.
    intros _Hdone Haccount _Hcovered Hroot.
    unfold stack_segment_reachable_closed.
    intros v w Hv_stack Hdfn Hreach_vw.
    destruct (classic (w ∈ visited s)) as [Hvis | Hnot_vis]; [exact Hvis |].
    exfalso.
    unfold segment_escape_accounted in Haccount.
    specialize (Haccount v w (conj Hv_stack Hdfn) Hreach_vw Hnot_vis)
      as [Hpending | Hanchor].
    - unfold pending_root_escape in Hpending.
      destruct Hpending as (a & _Hvu & Hua & Hnot_done & _Haw).
      apply Hnot_done. exact Hua.
    - unfold old_stack_escape_anchor in Hanchor.
      destruct Hanchor as (b & _Hb_stack & Hb_lt & Hlow_le & _Hvb & _Hbw).
      rewrite Hroot in Hlow_le. lia.
  Qed.

  Lemma low_iteration_segment_done_root_implies_segment_closed
        (u: V) (s: @SCCSt V):
    low_iteration_segment_done u s ->
    low s u = dfn s u ->
    stack_segment_reachable_closed u s.
  Proof.
    intros Hseg Hroot.
    unfold low_iteration_segment_done, low_iteration_segment_inv in Hseg.
    destruct Hseg as [Hiter [Haccount [Hcovered [Hord Hinj]]]].
    apply low_iteration_done_root_implies_segment_closed; auto.
    unfold low_iteration_done.
    split; [exact Hiter | split; [exact Hord | exact Hinj]].
  Qed.

  Lemma child_segment_coverage_lifts_to_parent
        (u a: V) (done: V -> Prop) (s: @SCCSt V):
    dg_step g u a ->
    stack_segment_covered_by_done a (dg_step g a) s ->
    forall x,
      stack_segment a s x ->
      processed_reachable_from u (done ∪ [a]) s x.
  Proof.
    intros Hstep_ua Hcovered x Hseg_x.
    unfold stack_segment in Hseg_x.
    destruct Hseg_x as [Hx_stack Hdfn_ax].
    specialize (Hcovered x Hx_stack Hdfn_ax) as Hproc_child.
    unfold processed_reachable_from in Hproc_child |- *.
    right. exists a.
    split.
    - sets_unfold. right. reflexivity.
    - split; [exact Hstep_ua |].
      destruct Hproc_child as [Hx_eq_a | (v & _Hstep_av_done & Hstep_av & Hreach_vx)].
      + subst x. apply dg_reachable_refl'.
      + eapply dg_step_reachable_reachable; eauto.
  Qed.

  Lemma segment_escape_accounted_lift_from_anchor
        (u x b w: V) (done: V -> Prop) (s: @SCCSt V):
    stack_segment u s b ->
    dg_reachable g x b ->
    dg_reachable g b w ->
    segment_escape_accounted u done s ->
    ~ w ∈ visited s ->
    pending_root_escape u done s b w \/
    old_stack_escape_anchor u s b w ->
    pending_root_escape u done s x w \/
    old_stack_escape_anchor u s x w.
  Proof.
    intros _Hseg_b Hxb _Hbw _Haccount _Hnot_vis Hcase.
    destruct Hcase as [Hpending | Hanchor].
    - left.
      unfold pending_root_escape in Hpending |- *.
      destruct Hpending as (a & Hbu & Hua & Hnot_done & Haw).
      exists a.
      split.
      + eapply dg_reachable_trans; [exact Hxb | exact Hbu].
      + split; [exact Hua |].
        split; [exact Hnot_done | exact Haw].
    - right.
      unfold old_stack_escape_anchor in Hanchor |- *.
      destruct Hanchor as (c & Hc_stack & Hc_lt & Hlow_le & Hbc & Hcw).
      exists c.
      split; [exact Hc_stack |].
      split; [exact Hc_lt |].
      split; [exact Hlow_le |].
      split.
      + eapply dg_reachable_trans; [exact Hxb | exact Hbc].
      + exact Hcw.
  Qed.

  Lemma update_low_preserves_stack_segment_covered_by_done
        (u: V) (done: V -> Prop) (n: nat):
    Hoare (stack_segment_covered_by_done u done)
          (update_low u n)
          (fun _ s => stack_segment_covered_by_done u done s).
  Proof.
    unfold update_low.
    apply Hoare_normalize. intros snap Hcovered.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lu.
    unfold If. intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold set_low. intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H1 as [Hlt Heq_s1]. subst s1. subst s.
      unfold stack_segment_covered_by_done in Hcovered |- *.
      intros x Hx_stack Hdfn.
      simpl in Hx_stack, Hdfn.
      apply Hcovered; auto.
    - intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H2 as [Heq_s1 _]. subst s1. subst s.
      exact Hcovered.
  Qed.

  Lemma update_low_preserves_segment_escape_accounted
        (u: V) (done: V -> Prop) (n: nat):
    Hoare (segment_escape_accounted u done)
          (update_low u n)
          (fun _ s => segment_escape_accounted u done s).
  Proof.
    unfold update_low.
    apply Hoare_normalize. intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lu.
    unfold If. intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold set_low. intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H1 as [Hlt Heq_s1]. subst s1. subst s.
      unfold segment_escape_accounted in Haccount |- *.
      intros x w Hseg_x Hreach_xw Hnot_vis_w.
      simpl in Hseg_x, Hnot_vis_w.
      specialize (Haccount x w Hseg_x Hreach_xw Hnot_vis_w)
        as [Hpending | Hanchor].
      + left. exact Hpending.
      + right.
        unfold old_stack_escape_anchor in Hanchor |- *.
        destruct Hanchor as (anc & Hanc_stack & Hanc_lt & Hlow_le & Hxanc & Hancw).
        exists anc.
        simpl.
        split; [exact Hanc_stack |].
        split; [exact Hanc_lt |].
        split.
        * unfold equiv_decb.
          destruct (equiv_dec u u) as [_ | Hneq].
          -- lia.
          -- exfalso. apply Hneq. reflexivity.
        * split; [exact Hxanc | exact Hancw].
    - intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H2 as [Heq_s1 _]. subst s1. subst s.
      exact Haccount.
  Qed.

  Lemma get_dfn_update_low_preserves_segment_escape_accounted
        (u a: V) (done: V -> Prop):
    Hoare (segment_escape_accounted u done)
          (dv <- get' (fun s => dfn s a);; update_low u dv)
          (fun _ s => segment_escape_accounted u done s).
  Proof.
    apply Hoare_normalize. intros snap Haccount.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: { apply (update_low_preserves_segment_escape_accounted u done dv). }
    intros st [Heq _]. subst st. exact Haccount.
  Qed.

  Lemma get_dfn_update_low_preserves_stack_segment_covered_by_done
        (u a: V) (done: V -> Prop):
    Hoare (stack_segment_covered_by_done u done)
          (dv <- get' (fun s => dfn s a);; update_low u dv)
          (fun _ s => stack_segment_covered_by_done u done s).
  Proof.
    apply Hoare_normalize. intros snap Hcovered.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    eapply Hoare_conseq_pre.
    2: { apply (update_low_preserves_stack_segment_covered_by_done u done dv). }
    intros st [Heq _]. subst st. exact Hcovered.
  Qed.

  Lemma update_low_preserves_segment_escape_accounted_old
        (u: V) (done: V -> Prop) (n: nat):
    Hoare (fun s => segment_escape_accounted u done s /\ n >= low s u)
          (update_low u n)
          (fun _ s => segment_escape_accounted u done s).
  Proof.
    unfold update_low.
    apply Hoare_normalize. intros snap [Haccount Hge].
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros lu.
    unfold If. intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      unfold set_low. intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H1 as [Hlt Heq_s1]. subst s1. subst s.
      exfalso. simpl in Hlt. lia.
    - intro_state. hoare_auto_s.
      destruct H as [Heq_snap Heq_lu]. subst s0. subst lu.
      destruct H2 as [Heq_s1 _]. subst s1. subst s.
      exact Haccount.
  Qed.

  Lemma update_low_stack_edge_old_anchor
        (u a: V) (done: V -> Prop):
    Hoare (fun s =>
             dg_step g u a /\
             In a (stack s) /\
             dfn s a < dfn s u)
          (dv <- get' (fun s => dfn s a);; update_low u dv)
          (fun _ s =>
             forall x w,
               dg_reachable g x u ->
               dg_reachable g a w ->
               old_stack_escape_anchor u s x w).
  Proof.
    apply Hoare_normalize. intros snap Hpre.
    eapply Hoare_bind. { apply Hoare_get'. }
    simpl. intros dv.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - destruct H as [Heq_snap Hdv]. subst s0. subst dv.
      destruct Hpre as [Hstep [Ha_stack Ha_lt]].
      subst s. unfold RecordSet.set. simpl.
      repeat intro.
      unfold old_stack_escape_anchor.
      exists a.
      split; [exact Ha_stack |].
      split; [exact Ha_lt |].
      split.
      + simpl. unfold equiv_decb.
        destruct (equiv_dec u u) as [_ | Hneq].
        * reflexivity.
        * exfalso. apply Hneq. reflexivity.
      + split.
        * eapply dg_reachable_trans.
          -- match goal with
             | Hreach: dg_reachable g _ u |- _ => exact Hreach
             end.
          -- apply dg_reachable_step. exact Hstep.
        * match goal with
          | Hreach: dg_reachable g a _ |- _ => exact Hreach
          end.
    - destruct H as [Heq_snap Hdv]. subst s0. subst dv.
      destruct Hpre as [Hstep [Ha_stack Ha_lt]].
      destruct H1 as [Heq_state Hnot_lt]. subst.
      repeat intro.
      unfold old_stack_escape_anchor.
      exists a.
      split; [exact Ha_stack |].
      split; [exact Ha_lt |].
      split; [lia |].
      split.
      + eapply dg_reachable_trans.
        * match goal with
          | Hreach: dg_reachable g _ u |- _ => exact Hreach
          end.
        * apply dg_reachable_step. exact Hstep.
      + match goal with
        | Hreach: dg_reachable g a _ |- _ => exact Hreach
        end.
  Qed.

  Lemma low_iteration_segment_extend_done_stack_old_extras
        (u a: V) (done: V -> Prop):
    Hoare (fun s =>
             low_iteration_segment_inv u done s /\
             dg_step g u a /\
             ~ done a /\
             a ∈ visited s /\
             In a (stack s) /\
             dfn s a < dfn s u)
          (dv <- get' (fun s => dfn s a);; update_low u dv)
          (fun _ s =>
             segment_escape_accounted u (done ∪ [a]) s /\
             stack_segment_covered_by_done u (done ∪ [a]) s).
  Proof.
    apply Hoare_conj with
      (Q1 := fun _ s => segment_escape_accounted u (done ∪ [a]) s)
      (Q2 := fun _ s => stack_segment_covered_by_done u (done ∪ [a]) s).
    - eapply Hoare_conseq_post.
      2: {
        apply Hoare_conj with
          (Q1 := fun _ s => segment_escape_accounted u done s)
          (Q2 := fun _ s =>
                   forall x w,
                     dg_reachable g x u ->
                     dg_reachable g a w ->
                     old_stack_escape_anchor u s x w).
        - eapply Hoare_conseq_pre.
          2: { apply (get_dfn_update_low_preserves_segment_escape_accounted u a done). }
          intros st [Hseg [_Hdg [_Hndone [_Hvis [_Hstack Hlt]]]]].
          unfold low_iteration_segment_inv in Hseg.
          destruct Hseg as [_Hiter [Haccount [_Hcovered [_Hord _Hinj]]]].
          exact Haccount.
        - eapply Hoare_conseq_pre.
          2: { apply (update_low_stack_edge_old_anchor u a done). }
          intros st [_Hseg [Hdg [_Hndone [_Hvis [Hstack Hlt]]]]].
          split; [exact Hdg |].
          split; [exact Hstack | exact Hlt]. }
      intros _ st [Haccount Hanchor].
      unfold segment_escape_accounted in Haccount |- *.
      intros x w Hseg_x Hreach_xw Hnot_vis_w.
      specialize (Haccount x w Hseg_x Hreach_xw Hnot_vis_w)
        as [Hpending | Hanchor_old].
      + unfold pending_root_escape in Hpending.
        destruct Hpending as (b & Hxu & Hub & Hnot_done_b & Hbw).
        destruct (equiv_dec b a) as [Hb_eq_a | Hb_ne_a].
        * right.
          rewrite Hb_eq_a in Hub, Hbw.
          apply Hanchor; auto.
        * left.
          unfold pending_root_escape.
          exists b.
          split; [exact Hxu |].
          split; [exact Hub |].
          split; [| exact Hbw].
          intros Hdone_new.
          apply Hnot_done_b.
          sets_unfold in Hdone_new.
          destruct Hdone_new as [Hdone_old | Hb_eq_a].
          { exact Hdone_old. }
          { exfalso. apply Hb_ne_a. symmetry. exact Hb_eq_a. }
      + right. exact Hanchor_old.
    - eapply Hoare_conseq_post.
      2: {
        eapply Hoare_conseq_pre.
        2: { apply (get_dfn_update_low_preserves_stack_segment_covered_by_done u a done). }
        intros st [Hseg [_Hdg [_Hndone [_Hvis [_Hstack _Hlt]]]]].
        unfold low_iteration_segment_inv in Hseg.
        destruct Hseg as [_Hiter [_Haccount [Hcovered [_Hord _Hinj]]]].
        exact Hcovered. }
      intros b st Hcovered.
      eapply stack_segment_covered_by_done_mono; [exact Hcovered |].
      intros v Hv. sets_unfold. left. exact Hv.
  Qed.

  Lemma low_iteration_segment_extend_done_nonstack_extras
        (u a: V) (done: V -> Prop) (s: @SCCSt V):
    low_iteration_segment_inv u done s ->
    dg_step g u a ->
    ~ done a ->
    a ∈ visited s ->
    ~ In a (stack s) ->
    segment_escape_accounted u (done ∪ [a]) s /\
    stack_segment_covered_by_done u (done ∪ [a]) s.
  Proof.
    intros Hseg _Hdg _Hndone Hvis_a Hnot_stack_a.
    unfold low_iteration_segment_inv in Hseg.
    destruct Hseg as [Hiter [Haccount_old [Hcovered [_Hord _Hinj]]]].
    unfold low_iteration_inv in Hiter.
    destruct Hiter as
      (_Hwf & Hsettled & _Huvis & _Hustack & _Hdonevis &
       _Hclosed & _Htree_closed & _Hfront & _Hsrc & _Hchild &
       _Hfa_child & _Hfa_not).
    split.
    - unfold segment_escape_accounted in Haccount_old |- *.
      intros x w Hseg_x Hreach_xw Hnot_vis_w.
      specialize (Haccount_old x w Hseg_x Hreach_xw Hnot_vis_w)
        as [Hpending | Hanchor].
      + unfold pending_root_escape in Hpending |- *.
        destruct Hpending as (v & Hxu & Hstep_uv & Hnot_done_v & Hreach_vw).
        destruct (equiv_dec v a) as [Hv_eq_a | Hv_ne_a].
        * destruct Hv_eq_a.
          exfalso.
          apply Hnot_vis_w.
          eapply Hsettled; [exact Hvis_a | exact Hnot_stack_a | exact Hreach_vw].
        * left.
          exists v.
          split; [exact Hxu |].
          split; [exact Hstep_uv |].
          split; [| exact Hreach_vw].
          intros Hdone_new.
          sets_unfold in Hdone_new.
          destruct Hdone_new as [Hdone_old | Hv_eq_a].
          -- apply Hnot_done_v. exact Hdone_old.
          -- apply Hv_ne_a. symmetry. exact Hv_eq_a.
      + right. exact Hanchor.
    - unfold stack_segment_covered_by_done.
      intros x Hx_stack Hdfn.
      specialize (Hcovered x Hx_stack Hdfn) as Hproc.
      eapply processed_reachable_from_mono; [exact Hproc |].
      intros v Hv. sets_unfold. left. exact Hv.
  Qed.

End LOW_SEGMENT.
