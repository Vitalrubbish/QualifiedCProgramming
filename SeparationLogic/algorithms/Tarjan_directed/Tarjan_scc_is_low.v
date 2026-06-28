Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From Algorithms.Tarjan_directed Require Import
  SCC_basic Tarjan_scc Tarjan_scc_basics Tarjan_scc_is_dfn
  Tarjan_scc_low_defs Tarjan_scc_low_pure Tarjan_scc_low_primitives.

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
  (* Independent recursive frames                                    *)
  (* ================================================================ *)

  Definition Q_fa_stable (u: V) (s0: @SCCSt V) (_: unit) (s: @SCCSt V): Prop :=
    (forall w, w ∈ visited s0 -> w ∈ visited s) /\
    (forall w, w ∈ visited s0 -> fa s w = fa s0 w).

  Definition Q_stack_frame (u: V) (s0: @SCCSt V) (_: unit) (s: @SCCSt V): Prop :=
    forall anc,
      In anc (stack s0) ->
      dfn s0 anc < dfn s0 u ->
      In anc (stack s).

  Definition Q_low_valid (u: V) (s0: @SCCSt V) (_: unit) (s: @SCCSt V): Prop :=
    low_valid_post g root u s /\
    u ∈ visited s /\
    stack_dfn_order s /\
    dfn_injective s.

  Lemma Q_fa_stable_old_visited
        (u: V) (s0 s: @SCCSt V) (w: V):
    Q_fa_stable u s0 tt s ->
    w ∈ visited s0 ->
    w ∈ visited s.
  Proof.
    destruct 1; auto.
  Qed.

  Lemma Q_fa_stable_old_fa
        (u: V) (s0 s: @SCCSt V) (w: V):
    Q_fa_stable u s0 tt s ->
    w ∈ visited s0 ->
    fa s w = fa s0 w.
  Proof.
    destruct 1; auto.
  Qed.

  Lemma Q_fa_stable_done_fa
        (u: V) (done: V -> Prop) (s0 s: @SCCSt V) (w: V):
    Q_fa_stable u s0 tt s ->
    done_visited done s0 ->
    done w ->
    fa s w = fa s0 w.
  Proof.
    intros Hqs Hdv Hdone.
    unfold done_visited in Hdv.
    apply Q_fa_stable_old_fa with u; auto.
  Qed.

  Lemma Q_fa_stable_preserves_old_parent
        (u parent child: V) (s0 s: @SCCSt V):
    Q_fa_stable u s0 tt s ->
    child ∈ visited s0 ->
    fa s0 child = parent ->
    fa s child = parent.
  Proof.
    intros Hqs Hch Hfa0.
    erewrite Q_fa_stable_old_fa; eauto.
  Qed.

  (* Support lemmas for the eventual LFix proof of [Q_fa_stable].  These
     are stated here, rather than proved yet, to pin down the exact frame
     contracts needed from the primitive/forset layers. *)
  Lemma preloop_keep_fa_no_restriction (u w: V) (faw: V):
    Hoare (fun s: @SCCSt V => fa s w = faw)
          (preloop u)
          (fun _ s => fa s w = faw).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl. reflexivity.
  Qed.

  Lemma preloop_keep_fa_forall (u: V) (P: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             s = s0 /\ forall w, P w -> fa s w = fa s0 w)
          (preloop u)
          (fun _ s => forall w, P w -> fa s w = fa s0 w).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl. destruct H as [Heq Hfa]. subst s1.
    apply Hfa. exact H2.
  Qed.

  Lemma set_fa_keep_fa_forall (v p: V) (P: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             s = s0 /\
             (forall w, P w -> fa s w = fa s0 w) /\
             ~ P v)
          (set_fa v p)
          (fun _ s => forall w, P w -> fa s w = fa s0 w).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl. destruct H as [Heq [Hfa HnotP]]. subst s1.
    unfold equiv_decb. destruct (equiv_dec w v).
    - exfalso. apply HnotP. rewrite <- e. exact H2.
    - apply Hfa. exact H2.
  Qed.

  Lemma set_fa_keep_fa_forall_fixed
        (v p: V) (Q: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             (forall w, Q w -> fa s w = fa s0 w) /\
             ~ Q v)
          (set_fa v p)
          (fun _ s => forall w, Q w -> fa s w = fa s0 w).
  Proof.
    unfold set_fa. intro_state. hoare_auto_s.
    subst s. simpl. destruct H as [Hfa HnotQ].
    unfold equiv_decb. destruct (equiv_dec w v).
    - exfalso. apply HnotQ. rewrite <- e. exact H2.
    - apply Hfa. exact H2.
  Qed.

  Lemma pop_scc_keep_fa_forall (u: V) (P: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             s = s0 /\ forall w, P w -> fa s w = fa s0 w)
          (pop_scc u)
          (fun _ s => forall w, P w -> fa s w = fa s0 w).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s.
    subst s. unfold pop_scc_state.
    destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
    destruct H as [Heq Hfa]. subst s1.
    rewrite Hsplit. simpl. auto.
  Qed.

  Lemma update_low_keep_fa_forall (u: V) (n: nat) (P: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             s = s0 /\ forall w, P w -> fa s w = fa s0 w)
          (update_low u n)
          (fun _ s => forall w, P w -> fa s w = fa s0 w).
  Proof.
    unfold update_low. intro_state. hoare_auto_s.
    - unfold set_low. intro_state. hoare_auto_s.
      subst s. simpl. subst s2.
      destruct H as [Heq Hfa]. subst s1. auto.
    - destruct H1 as [Heq _]. subst s.
      destruct H as [Heq' Hfa]. subst s1. auto.
  Qed.

  Lemma pop_scc_keep_fa_forall_fixed (u: V) (Q: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V => forall w, Q w -> fa s w = fa s0 w)
          (pop_scc u)
          (fun _ s => forall w, Q w -> fa s w = fa s0 w).
  Proof.
    unfold Hoare. intros s1 r s2 Hfa Hrun w HQ.
    pose proof (pop_scc_keep_fa u w (fa s0 w)) as Hpop.
    unfold Hoare in Hpop.
    exact (Hpop s1 r s2 (Hfa w HQ) Hrun).
  Qed.

  Lemma get_low_update_low_keep_fa_forall
        (u v: V) (P: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             s = s0 /\ forall w, P w -> fa s w = fa s0 w)
          (lv <- get' (fun s => low s v);; update_low u lv)
          (fun _ s => forall w, P w -> fa s w = fa s0 w).
  Proof.
    intro_state. hoare_auto_s.
    destruct H as [Heq Hfa]. subst s1.
    unfold update_low. intro_state. hoare_auto_s.
    - unfold set_low. intro_state. hoare_auto_s.
      subst s. simpl. subst s1. auto.
    - destruct H as [Heq' _]. subst s. auto.
  Qed.

  Lemma update_low_keep_fa_forall_fixed
        (u: V) (n: nat) (Q: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V => forall w, Q w -> fa s w = fa s0 w)
          (update_low u n)
          (fun _ s => forall w, Q w -> fa s w = fa s0 w).
  Proof.
    unfold update_low. intro_state. hoare_auto_s.
    - unfold set_low. intro_state. hoare_auto_s.
      subst s. simpl. subst s2. auto.
    - destruct H1 as [Heq _]. subst s. auto.
  Qed.

  Lemma get_low_update_low_keep_fa_forall_fixed
        (u v: V) (Q: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V => forall w, Q w -> fa s w = fa s0 w)
          (lv <- get' (fun s => low s v);; update_low u lv)
          (fun _ s => forall w, Q w -> fa s w = fa s0 w).
  Proof.
    apply Hoare_normalize. intros snap Hsnap.
    apply Hoare_conseq_post with
      (Q2 := fun (_: unit) s => forall w, Q w -> fa s w = fa snap w).
    - intros r s Hpres w HQ.
      transitivity (fa snap w); [apply Hpres | apply Hsnap]; exact HQ.
    - apply Hoare_conseq_pre with
        (P2 := fun s =>
                 s = snap /\ forall w, Q w -> fa s w = fa snap w).
      { intros s Heq. subst s. split; [reflexivity | intros w _; reflexivity]. }
      apply get_low_update_low_keep_fa_forall.
  Qed.

  Lemma get_dfn_update_low_keep_fa_forall
        (u v: V) (P: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             s = s0 /\ forall w, P w -> fa s w = fa s0 w)
          (dv <- get' (fun s => dfn s v);; update_low u dv)
          (fun _ s => forall w, P w -> fa s w = fa s0 w).
  Proof.
    intro_state. hoare_auto_s.
    destruct H as [Heq Hfa]. subst s1.
    unfold update_low. intro_state. hoare_auto_s.
    - unfold set_low. intro_state. hoare_auto_s.
      subst s. simpl. subst s1. auto.
    - destruct H as [Heq' _]. subst s. auto.
  Qed.

  Lemma get_dfn_update_low_keep_fa_forall_fixed
        (u v: V) (Q: V -> Prop) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V => forall w, Q w -> fa s w = fa s0 w)
          (dv <- get' (fun s => dfn s v);; update_low u dv)
          (fun _ s => forall w, Q w -> fa s w = fa s0 w).
  Proof.
    apply Hoare_normalize. intros snap Hsnap.
    apply Hoare_conseq_post with
      (Q2 := fun (_: unit) s => forall w, Q w -> fa s w = fa snap w).
    - intros r s Hpres w HQ.
      transitivity (fa snap w); [apply Hpres | apply Hsnap]; exact HQ.
    - apply Hoare_conseq_pre with
        (P2 := fun s =>
                 s = snap /\ forall w, Q w -> fa s w = fa snap w).
      { intros s Heq. subst s. split; [reflexivity | intros w _; reflexivity]. }
      apply get_dfn_update_low_keep_fa_forall.
  Qed.

  Lemma process_edge_keep_fa_forall
        (u v: V) (W: V -> program (@SCCSt V) unit)
        (Q: V -> Prop) (s0: @SCCSt V):
    (forall x,
       Hoare (fun s: @SCCSt V =>
                forall w, Q w -> fa s w = fa s0 w)
             (W x)
             (fun _ s => forall w, Q w -> fa s w = fa s0 w)) ->
    Hoare (fun s: @SCCSt V =>
             (forall w, Q w -> fa s w = fa s0 w) /\
             (Q v -> v ∈ visited s))
          (process_edge u W v)
          (fun _ s => forall w, Q w -> fa s w = fa s0 w).
  Proof.
    intros HW.
    unfold process_edge, if_else.
    intro_state. destruct H as [Hfa HQvis].
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      eapply Hoare_bind.
      { apply Hoare_conseq_pre with
          (P2 := fun s => (forall w, Q w -> fa s w = fa s0 w) /\ ~ Q v).
        - intros st [Hnv Heq]. subst st. split; auto.
        - apply set_fa_keep_fa_forall_fixed. }
      simpl. intros _.
      eapply Hoare_bind.
      { apply HW. }
      simpl. intros _.
      apply get_low_update_low_keep_fa_forall_fixed.
    - intro_state. hoare_auto_s.
      + apply Hoare_conseq_pre with
          (P2 := fun s => forall w, Q w -> fa s w = fa s0 w).
        { intros st Hst. subst st. exact Hfa. }
        apply update_low_keep_fa_forall_fixed.
      + destruct H2 as [Hs _]. subst s. subst s2.
        apply Hfa. exact H3.
  Qed.

  Lemma forset_process_edge_keep_fa_forall
        (u: V) (W: V -> program (@SCCSt V) unit)
        (Pdone: V -> Prop) (s0: @SCCSt V):
    (forall x,
       Hoare (fun s: @SCCSt V =>
                forall w, Pdone w -> fa s w = fa s0 w)
             (W x)
             (fun _ s => forall w, Pdone w -> fa s w = fa s0 w)) ->
    (forall x,
       Hoare (fun s: @SCCSt V =>
                forall w, Pdone w -> w ∈ visited s)
             (W x)
             (fun _ s => forall w, Pdone w -> w ∈ visited s)) ->
    Hoare (fun s: @SCCSt V =>
             (forall w, Pdone w -> fa s w = fa s0 w) /\
             (forall w, Pdone w -> w ∈ visited s))
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s =>
             (forall w, Pdone w -> fa s w = fa s0 w) /\
             (forall w, Pdone w -> w ∈ visited s)).
  Proof.
    intros HWfa HWvis.
    unfold forset. hoare_fix_nolv_auto (V -> Prop).
    simpl. intros W0 IH0 todo.
    unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
    - eapply Hoare_bind with
        (R := fun _ s =>
                (forall w, Pdone w -> fa s w = fa s0 w) /\
                (forall w, Pdone w -> w ∈ visited s)).
      { apply Hoare_conj.
        - apply Hoare_conseq_pre with
            (P2 := fun s =>
                     (forall w, Pdone w -> fa s w = fa s0 w) /\
                     (Pdone a -> a ∈ visited s)).
          { intros st Hst. subst st. destruct H as [Hfa Hvis].
            split; [exact Hfa | intros Ha; apply Hvis; exact Ha]. }
          apply process_edge_keep_fa_forall.
          intros x. apply HWfa.
        - apply Hoare_conseq_pre with
            (P2 := fun s => forall w, Pdone w -> w ∈ visited s).
          { intros st Hst. subst st. exact (proj2 H). }
          apply process_edge_keep_visited_forall.
          intros x. apply HWvis. }
      simpl. intros _.
      apply IH0.
  Qed.

  (* This is the frame theorem directly needed for recursive calls
     discovered by the tree-edge branch.  The whole low-link proof should
     use this unvisited-entry variant.

     Proof sketch (follows tarjan_scc_keep_fa_visited from is_dfn.v):
     - Hoare_fix_logicv_conj with C := SCCSt gives an IH parameterised
       over an arbitrary snapshot.
     - Auxiliary property: d ∈ visited s (tarjan_scc_keep_visited).
     - Induction step for tarjan_scc_f g W a:
       1. preloop a: establishes a ∈ visited, preserves Q_fa_stable a c
          via preloop_keep_fa_forall / preloop_keep_visited_forall.
       2. forset (process_edge a W): the heavy part — needs a concrete-P
          forset lemma analogous to forset_process_edge_keep_fa_forall
          but with P snap w := w ∈ visited snap (avoids the generic-P
          mismatch after set_fa changes fa v).
       3. If (low s a = dfn s a) (pop_scc a): both branches preserve
          Q_fa_stable a c via pop_scc_keep_fa_forall / pop_scc_keep_visited_forall.
   *)
  Theorem tarjan_scc_keep_fa_stable_unvisited (u: V) (s0: @SCCSt V):
    Hoare (fun s => s = s0 /\ ~ u ∈ visited s0)
          (tarjan_scc g u)
          (Q_fa_stable u s0).
  Proof.
    unfold Hoare, Q_fa_stable. intros s1 r s2 [Heq Hunvis] Hrun.
    subst s1. split.
    - pose proof (@Tarjan_scc_basics.tarjan_scc_keep_visited_forall
                    V E equiv0 H0 g OriginalGraph_gvalid0
                    u (fun w => w ∈ visited s0)) as Hvisited.
      unfold Hoare in Hvisited.
      eapply Hvisited; eauto.
    - intros w Hw.
      destruct (equiv_dec u w) as [Heq | Hneq].
      { rewrite <- Heq in Hw. contradiction. }
      pose proof (@Tarjan_scc_basics.tarjan_scc_keep_fa
                    V E equiv0 H0 g u w (fa s0 w)) as Hfa.
      unfold Hoare in Hfa.
      specialize (Hfa s0 r s2).
      destruct (Hfa (conj Hneq (conj Hw eq_refl)) Hrun) as [_ Hfa_eq].
      exact Hfa_eq.
  Qed.

  (* ================================================================ *)
  (* Stack-frame support                                             *)
  (* ================================================================ *)

  Lemma Q_stack_frame_old_stack
        (u anc: V) (s0 s: @SCCSt V):
    Q_stack_frame u s0 tt s ->
    In anc (stack s0) ->
    dfn s0 anc < dfn s0 u ->
    In anc (stack s).
  Proof.
    intros Hframe Hanc Hlt. apply Hframe; auto.
  Qed.

  Lemma stack_split_at_keeps_lower_dfn_vertex
        (s: @SCCSt V) (u anc: V) (popped rest: list V):
    stack_dfn_order s ->
    In anc (stack s) ->
    In u (stack s) ->
    dfn s anc < dfn s u ->
    stack_split_at (stack s) u = (popped, rest) ->
    In anc rest.
  Proof.
    intros Hord Hanc Hu Hlt Hsplit.
    destruct (stack_split_at_decomp (stack s) u Hu popped rest Hsplit)
      as [prefix Hstk].
    assert (Hin_decomp: In anc (prefix ++ u :: rest)).
    { rewrite <- Hstk. exact Hanc. }
    apply List.in_app_or in Hin_decomp.
    destruct Hin_decomp as [Hin_prefix | [Hanc_eq_u | Hanc_rest]].
    - destruct (in_split _ _ Hin_prefix) as [l1 [l2 Hprefix]].
      subst prefix.
      assert (Habove:
                exists l1' l2',
                  stack s = l1' ++ anc :: l2' /\ In u l2').
      { exists l1. exists (l2 ++ u :: rest). split.
        - rewrite Hstk. rewrite <- app_assoc. reflexivity.
        - rewrite List.in_app_iff. right. simpl. left. reflexivity. }
      specialize (Hord anc u Hanc Hu Habove). lia.
    - subst anc. lia.
    - exact Hanc_rest.
  Qed.

  Lemma pop_scc_keeps_older_stack_vertex
        (s: @SCCSt V) (u anc: V):
    stack_dfn_order s ->
    In anc (stack s) ->
    In u (stack s) ->
    dfn s anc < dfn s u ->
    In anc (stack (pop_scc_state s u)).
  Proof.
    intros Hord Hanc Hu Hlt.
    unfold pop_scc_state.
    destruct (stack_split_at (stack s) u) as [popped rest] eqn:Hsplit.
    simpl.
    eapply stack_split_at_keeps_lower_dfn_vertex; eauto.
  Qed.

  Lemma pop_scc_establishes_stack_frame_for_root
        (u: V) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             s = s0 /\ stack_dfn_order s /\ In u (stack s))
          (pop_scc u)
          (Q_stack_frame u s0).
  Proof.
    unfold pop_scc. intro_state. hoare_auto_s.
    destruct H as [Heq [Hord Hu]]. subst s. subst s1.
    intros anc Hanc Hlt.
    apply pop_scc_keeps_older_stack_vertex; auto.
  Qed.

  Lemma preloop_preserves_Q_stack_frame
        (u cur: V) (s0: @SCCSt V):
    Hoare (Q_stack_frame cur s0 tt)
          (preloop u)
          (Q_stack_frame cur s0).
  Proof.
    unfold Hoare. intros s1 r s2 Hframe Hrun anc Hanc Hlt.
    assert (Hin1: In anc (stack s1)) by (apply Hframe; auto).
    pose proof (preloop_keep_in_stack u anc) as Hkeep.
    unfold Hoare in Hkeep.
    exact (Hkeep s1 r s2 Hin1 Hrun).
  Qed.

  Lemma set_fa_preserves_Q_stack_frame
        (v p cur: V) (s0: @SCCSt V):
    Hoare (Q_stack_frame cur s0 tt)
          (set_fa v p)
          (Q_stack_frame cur s0).
  Proof.
    unfold Hoare. intros s1 r s2 Hframe Hrun anc Hanc Hlt.
    assert (Hin1: In anc (stack s1)) by (apply Hframe; auto).
    pose proof (set_fa_keep_in_stack v p anc) as Hkeep.
    unfold Hoare in Hkeep.
    exact (Hkeep s1 r s2 Hin1 Hrun).
  Qed.

  Lemma update_low_preserves_Q_stack_frame
        (u cur: V) (n: nat) (s0: @SCCSt V):
    Hoare (Q_stack_frame cur s0 tt)
          (update_low u n)
          (Q_stack_frame cur s0).
  Proof.
    unfold Hoare. intros s1 r s2 Hframe Hrun anc Hanc Hlt.
    assert (Hin1: In anc (stack s1)) by (apply Hframe; auto).
    pose proof (update_low_keep_in_stack u anc n) as Hkeep.
    unfold Hoare in Hkeep.
    exact (Hkeep s1 r s2 Hin1 Hrun).
  Qed.

  Lemma get_low_update_low_preserves_Q_stack_frame
        (u v cur: V) (s0: @SCCSt V):
    Hoare (Q_stack_frame cur s0 tt)
          (lv <- get' (fun s => low s v);; update_low u lv)
          (Q_stack_frame cur s0).
  Proof.
    unfold Hoare. intros s1 r s2 Hframe Hrun anc Hanc Hlt.
    assert (Hin1: In anc (stack s1)) by (apply Hframe; auto).
    pose proof (get_low_update_low_keep_in_stack u v anc) as Hkeep.
    unfold Hoare in Hkeep.
    exact (Hkeep s1 r s2 Hin1 Hrun).
  Qed.

  Lemma get_dfn_update_low_preserves_Q_stack_frame
        (u v cur: V) (s0: @SCCSt V):
    Hoare (Q_stack_frame cur s0 tt)
          (dv <- get' (fun s => dfn s v);; update_low u dv)
          (Q_stack_frame cur s0).
  Admitted.

  Theorem tarjan_scc_keep_stack_frame (u: V) (s0: @SCCSt V):
    Hoare (fun s => s = s0 /\ stack_dfn_order s /\ dfn_injective s)
          (tarjan_scc g u)
          (Q_stack_frame u s0).
  Admitted.

  (* Compatibility name kept for older local scripts. *)
  Theorem tarjan_scc_keep_fa (u: V) (s_init: @SCCSt V):
    Hoare (fun s => s = s_init /\ ~ u ∈ visited s_init)
          (tarjan_scc g u)
          (fun _ s => forall w,
             w ∈ visited s_init -> fa s w = fa s_init w).
  Proof.
    apply Hoare_conseq_post with (Q2 := Q_fa_stable u s_init).
    - intros r s Hstable. exact (proj2 Hstable).
    - apply tarjan_scc_keep_fa_stable_unvisited.
  Qed.

  (* ================================================================ *)
  (* Forset phase contracts                                          *)
  (* ================================================================ *)

  Definition low_continuation_contract
             (W: V -> program (@SCCSt V) unit)
             (u a: V) (done: V -> Prop) (s0: @SCCSt V): Prop :=
    ~ a ∈ visited s0 ->
    low_iteration_inv g root u done s0 ->
    stack_dfn_order s0 ->
    dfn_injective s0 ->
    Hoare (fun s => s = s0)
          (W a)
          (fun _ s =>
             Q_low_valid a s0 tt s /\
             Q_fa_stable a s0 tt s /\
             Q_stack_frame a s0 tt s /\
             low_iteration_inv g root u done s /\
             (fa s0 a = u -> fa s a = u)).

  Lemma process_edge_preserves_low_iteration
        (u a: V) (done: V -> Prop) (s0: @SCCSt V)
        (W: V -> program (@SCCSt V) unit):
    low_continuation_contract W u a done s0 ->
    dg_step g u a ->
    ~ done a ->
    Hoare (fun s => s = s0 /\ low_iteration_inv g root u done s /\
                     stack_dfn_order s /\ dfn_injective s /\
                     dg_step g u a /\ ~ done a)
          (process_edge u W a)
          (fun _ s => low_iteration_inv g root u (done ∪ [a]) s /\
                      stack_dfn_order s /\ dfn_injective s).
  Admitted.

  Lemma forset_preserves_low_iteration
        (u: V) (W: V -> program (@SCCSt V) unit):
    (forall a done s0,
       dg_step g u a ->
       ~ done a ->
       low_continuation_contract W u a done s0) ->
    Hoare (fun s => low_iteration_entry g root u s)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => low_iteration_done g root u s).
  Admitted.

  (* ================================================================ *)
  (* Top-level low-link theorems                                     *)
  (* ================================================================ *)

  Theorem tarjan_scc_keep_low_valid (u: V):
    Hoare (fun s => low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
          (tarjan_scc g u)
          (fun _ s => low_valid_post g root u s /\
                      u ∈ visited s /\
                      stack_dfn_order s /\
                      dfn_injective s).
  Admitted.

  Theorem tarjan_scc_keep_is_low (u: V):
    Hoare (fun s => low_pre g root u s /\ stack_dfn_order s /\ dfn_injective s)
          (tarjan_scc g u)
          (fun _ s => low_post g root u s /\
                      u ∈ visited s /\
                      stack_dfn_order s /\
                      dfn_injective s).
  Admitted.

End IS_LOW.
