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

  Definition Q_active_stack_frame (u: V) (s0: @SCCSt V) (_: unit) (s: @SCCSt V): Prop :=
    In u (stack s) /\
    dfn s u = dfn s0 u /\
    Q_stack_frame u s0 tt s /\
    (forall anc,
       In anc (stack s0) ->
       dfn s0 anc < dfn s0 u ->
       dfn s anc = dfn s0 anc).

  Definition active_stack_frames
             (frames: list (V * @SCCSt V)) (s: @SCCSt V): Prop :=
    forall cur s0, In (cur, s0) frames -> Q_active_stack_frame cur s0 tt s.

  Definition active_stack_frames_below
             (frames: list (V * @SCCSt V)) (u: V) (s: @SCCSt V): Prop :=
    forall cur s0, In (cur, s0) frames -> dfn s cur < dfn s u.

  Definition active_base
             (frames: list (V * @SCCSt V)) (s: @SCCSt V): Prop :=
    active_stack_frames frames s /\
    wf_scc_state g root s /\
    stack_dfn_order s /\
    dfn_injective s.

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
  Proof.
    unfold Hoare. intros s1 r s2 Hframe Hrun anc Hanc Hlt.
    assert (Hin1: In anc (stack s1)) by (apply Hframe; auto).
    pose proof (get_dfn_update_low_keep_in_stack u v anc) as Hkeep.
    unfold Hoare in Hkeep.
    exact (Hkeep s1 r s2 Hin1 Hrun).
  Qed.

  Lemma process_edge_preserves_Q_stack_frame
        (u v cur: V) (s0: @SCCSt V)
        (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (Q_stack_frame cur s0 tt) (W x)
                     (Q_stack_frame cur s0)) ->
    Hoare (Q_stack_frame cur s0 tt)
          (process_edge u W v)
          (Q_stack_frame cur s0).
  Proof.
    intros HW.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    (* Tree edge *)
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := Q_stack_frame cur s0 tt).
      { intros st [Hnv Heq_st]. subst st. exact H. }
      intro_state.
      apply Hoare_conseq_pre with (P2 := Q_stack_frame cur s0 tt).
      { intros st Heq_st. subst st. exact H1. }
      eapply Hoare_bind with (R := fun (_: unit) s => Q_stack_frame cur s0 tt s).
      * apply (set_fa_preserves_Q_stack_frame v u cur s0).
      * intro u_; destruct u_.
        eapply Hoare_bind with (R := fun (_: unit) s => Q_stack_frame cur s0 tt s);
          [ apply (HW v)
          | intro u_'; destruct u_'; apply (get_low_update_low_preserves_Q_stack_frame u v cur s0) ].
    (* Non-tree edge *)
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := Q_stack_frame cur s0 tt).
      { intros st [Hnv Heq_st]. subst st. exact H. }
      intro_state. hoare_auto_s.
      + eapply Hoare_conseq_pre with (P2 := Q_stack_frame cur s0 tt).
        2: { eapply (update_low_preserves_Q_stack_frame u cur _ s0). }
        simpl. intros st Heq_st. subst st. exact H1.
      + destruct H2 as [Heq _]. subst s. exact H1.
  Qed.

  Lemma forset_preserves_Q_stack_frame
        (u cur: V) (s0: @SCCSt V)
        (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (Q_stack_frame cur s0 tt) (W x)
                     (Q_stack_frame cur s0)) ->
    Hoare (Q_stack_frame cur s0 tt)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (Q_stack_frame cur s0).
  Proof.
    intros HW.
    unfold forset. hoare_fix_nolv_auto (V -> Prop).
    simpl. intros W0 IH0 todo.
    unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
    eapply Hoare_bind with (R := fun (_: unit) s => Q_stack_frame cur s0 tt s).
    { apply Hoare_conseq_pre with (P2 := Q_stack_frame cur s0 tt).
      { intros st Hst. subst st. exact H. }
      apply process_edge_preserves_Q_stack_frame. intros x. apply HW. }
    intro u_; destruct u_. apply IH0.
  Qed.

  Lemma if_pop_preserves_Q_stack_frame
        (u cur: V) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             Q_stack_frame cur s0 tt s /\
             stack_dfn_order s /\
             In u (stack s) /\
             (forall anc,
                In anc (stack s0) ->
                dfn s0 anc < dfn s0 cur ->
                dfn s anc < dfn s u))
          (If (fun s => low s u = dfn s u) (pop_scc u))
          (Q_stack_frame cur s0).
  Proof.
    unfold If.
    intro_state. destruct H as [Hframe [Hord [Hu_stack Hbelow]]].
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      refine (Hoare_conseq_pre _
               (fun s =>
                  Q_stack_frame cur s0 tt s /\
                  stack_dfn_order s /\
                  In u (stack s) /\
                  (forall anc,
                     In anc (stack s0) ->
                     dfn s0 anc < dfn s0 cur ->
                     dfn s anc < dfn s u))
               (pop_scc u) (Q_stack_frame cur s0) _ _); [ | ].
      { intros st [Hlow Heq_st]. subst st.
        split; [exact Hframe | split; [exact Hord | split; [exact Hu_stack | exact Hbelow]]]. }
      { unfold pop_scc. intro_state. hoare_auto_s.
        destruct H as [Hframe_pop [Hord_pop [Hu_stack_pop Hbelow_pop]]].
        subst s. unfold Q_stack_frame. intros anc Hanc Hlt.
        eapply pop_scc_keeps_older_stack_vertex.
        - exact Hord_pop.
        - apply Hframe_pop; auto.
        - exact Hu_stack_pop.
        - apply Hbelow_pop; auto. }
    - intro_state. hoare_auto_s.
      destruct H1 as [Hs _]. subst s. subst s2. exact Hframe.
  Qed.

  Lemma preloop_establishes_Q_stack_frame_entry
        (u: V) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V => s = s0)
          (preloop u)
          (Q_stack_frame u s0).
  Proof.
    unfold preloop. unfold_op. intro_state. hoare_auto_s.
    subst s. simpl. unfold Q_stack_frame.
    intros anc Hanc Hlt. simpl. right. exact Hanc.
  Qed.

  Theorem tarjan_scc_keep_stack_frame (u: V) (s0: @SCCSt V):
    Hoare (fun s => s = s0 /\
                    low_pre g root u s /\
                    stack_dfn_order s /\
                    dfn_injective s)
          (tarjan_scc g u)
          (Q_stack_frame u s0).
  Proof.
    unfold Hoare, Q_stack_frame, low_pre, wf_scc_state.
    intros s1 r s2 Hpre Hrun anc Hanc Hlt.
    destruct Hpre as [Heq [Hlow_pre [Hord Hinj]]].
    destruct Hlow_pre as [Hwf Hnot_u_vis].
    destruct Hwf as [_ [Hdfn_inv _]].
    subst s1.
    destruct Hdfn_inv as [_ [Hdfn_zero _]].
    pose proof (proj2 (Hdfn_zero u) Hnot_u_vis) as Hu_zero.
    rewrite Hu_zero in Hlt. lia.
  Qed.

  Lemma Q_active_stack_frame_self_stack
        (u: V) (s0 s: @SCCSt V):
    Q_active_stack_frame u s0 tt s ->
    In u (stack s).
  Proof.
    intros [Hu _]. exact Hu.
  Qed.

  Lemma Q_active_stack_frame_self_dfn
        (u: V) (s0 s: @SCCSt V):
    Q_active_stack_frame u s0 tt s ->
    dfn s u = dfn s0 u.
  Proof.
    intros [_ [Hdfn _]]. exact Hdfn.
  Qed.

  Lemma Q_active_stack_frame_old_stack
        (u anc: V) (s0 s: @SCCSt V):
    Q_active_stack_frame u s0 tt s ->
    In anc (stack s0) ->
    dfn s0 anc < dfn s0 u ->
    In anc (stack s).
  Proof.
    intros [_ [_ [Hframe _]]] Hanc Hlt.
    apply Hframe; auto.
  Qed.

  Lemma Q_active_stack_frame_old_dfn
        (u anc: V) (s0 s: @SCCSt V):
    Q_active_stack_frame u s0 tt s ->
    In anc (stack s0) ->
    dfn s0 anc < dfn s0 u ->
    dfn s anc = dfn s0 anc.
  Proof.
    intros [_ [_ [_ Hdfn]]] Hanc Hlt.
    apply Hdfn; auto.
  Qed.

  Lemma Q_active_stack_frame_pop_below
        (u pop_root anc: V) (s0 s: @SCCSt V):
    Q_active_stack_frame u s0 tt s ->
    dfn s u < dfn s pop_root ->
    In anc (stack s0) ->
    dfn s0 anc < dfn s0 u ->
    dfn s anc < dfn s pop_root.
  Proof.
    intros Hactive Hu_pop Hanc Hlt.
    rewrite (Q_active_stack_frame_old_dfn u anc s0 s Hactive Hanc Hlt).
    rewrite <- (Q_active_stack_frame_self_dfn u s0 s Hactive) in Hlt.
    lia.
  Qed.

  Lemma Q_active_stack_frame_current
        (u: V) (s: @SCCSt V):
    In u (stack s) ->
    Q_active_stack_frame u s tt s.
  Proof.
    intros Hu. repeat split; auto.
    unfold Q_stack_frame. intros anc Hanc Hlt. exact Hanc.
  Qed.

  Lemma preloop_preserves_Q_active_stack_frame
        (v cur: V) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             Q_active_stack_frame cur s0 tt s /\
             stack_in_visited s /\
             ~ v ∈ visited s)
          (preloop v)
          (Q_active_stack_frame cur s0).
  Proof.
    unfold Hoare. intros s1 r s2 [Hactive [Hstack_in Hnv]] Hrun.
    unfold Q_active_stack_frame in Hactive |- *.
    destruct Hactive as [Hu_stack [Hdfn_eq [Hframe Hdfn_anc]]].
    split; [| split; [| split]].
    - (* In cur (stack s2) *)
      pose proof (preloop_keep_in_stack v cur) as Hkeep.
      unfold Hoare in Hkeep. exact (Hkeep s1 r s2 Hu_stack Hrun).
    - (* dfn s2 cur = dfn s0 cur *)
      pose proof (preloop_keep_dfn v cur (dfn s0 cur)) as Hkeep.
      unfold Hoare in Hkeep.
      eapply Hkeep; [| exact Hrun].
      split; [| split]; auto.
      { intro Heq; subst cur. apply Hnv. apply (Hstack_in _ Hu_stack). }
    - (* Q_stack_frame cur s0 tt s2 *)
      unfold Q_stack_frame. intros anc Hanc Hlt.
      assert (Hin1: In anc (stack s1)) by (apply Hframe; auto).
      pose proof (preloop_keep_in_stack v anc) as Hkeep.
      unfold Hoare in Hkeep.
      exact (Hkeep s1 r s2 Hin1 Hrun).
    - (* forall anc, dfn s2 anc = dfn s0 anc *)
      intros anc Hanc Hlt.
      assert (Hanc_s1: In anc (stack s1)) by (apply Hframe; auto).
      assert (Hneq: v <> anc).
      { intro Heq; subst anc. apply Hnv. apply (Hstack_in _ Hanc_s1). }
      pose proof (preloop_keep_dfn v anc (dfn s0 anc)) as Hkeep.
      unfold Hoare in Hkeep.
      apply (Hkeep s1 r s2 (conj Hneq (conj (Hstack_in _ Hanc_s1) (Hdfn_anc anc Hanc Hlt))) Hrun).
  Qed.

  Lemma set_fa_preserves_Q_active_stack_frame
        (v p cur: V) (s0: @SCCSt V):
    Hoare (Q_active_stack_frame cur s0 tt)
          (set_fa v p)
          (Q_active_stack_frame cur s0).
  Proof.
    unfold Hoare. intros s1 r s2 Hactive Hrun.
    unfold Q_active_stack_frame in Hactive |- *.
    destruct Hactive as [Hu_stack [Hdfn_eq [Hframe Hdfn_anc]]].
    split; [| split; [| split]].
    - (* In cur (stack s2) *)
      pose proof (set_fa_keep_in_stack v p cur) as Hkeep.
      unfold Hoare in Hkeep. exact (Hkeep s1 r s2 Hu_stack Hrun).
    - (* dfn s2 cur = dfn s0 cur *)
      pose proof (set_fa_keep_dfn v cur p (dfn s0 cur)) as Hkeep.
      unfold Hoare in Hkeep.
      exact (Hkeep s1 r s2 Hdfn_eq Hrun).
    - (* Q_stack_frame cur s0 tt s2 *)
      pose proof (set_fa_preserves_Q_stack_frame v p cur s0) as Hpres.
      unfold Hoare in Hpres.
      exact (Hpres s1 r s2 Hframe Hrun).
    - (* forall anc, dfn s2 anc = dfn s0 anc *)
      intros anc Hanc Hlt.
      pose proof (set_fa_keep_dfn v anc p (dfn s0 anc)) as Hkeep.
      unfold Hoare in Hkeep.
      exact (Hkeep s1 r s2 (Hdfn_anc anc Hanc Hlt) Hrun).
  Qed.

  Lemma update_low_preserves_Q_active_stack_frame
        (u cur: V) (n: nat) (s0: @SCCSt V):
    Hoare (Q_active_stack_frame cur s0 tt)
          (update_low u n)
          (Q_active_stack_frame cur s0).
  Proof.
    unfold Hoare. intros s1 r s2 Hactive Hrun.
    unfold Q_active_stack_frame in Hactive |- *.
    destruct Hactive as [Hu_stack [Hdfn_eq [Hframe Hdfn_anc]]].
    pose proof (update_low_keep_in_stack u cur n) as Hkeep_stack.
    pose proof (update_low_keep_dfn u cur n (dfn s0 cur)) as Hkeep_dfn_cur.
    pose proof (update_low_preserves_Q_stack_frame u cur n s0) as Hpres_frame.
    unfold Hoare in Hkeep_stack, Hkeep_dfn_cur, Hpres_frame.
    split; [| split; [| split]].
    - exact (Hkeep_stack s1 r s2 Hu_stack Hrun).
    - exact (Hkeep_dfn_cur s1 r s2 Hdfn_eq Hrun).
    - exact (Hpres_frame s1 r s2 Hframe Hrun).
    - intros anc Hanc Hlt.
      pose proof (update_low_keep_dfn u anc n (dfn s0 anc)) as Hkeep_dfn.
      unfold Hoare in Hkeep_dfn.
      exact (Hkeep_dfn s1 r s2 (Hdfn_anc anc Hanc Hlt) Hrun).
  Qed.

  Lemma get_low_update_low_preserves_Q_active_stack_frame
        (u v cur: V) (s0: @SCCSt V):
    Hoare (Q_active_stack_frame cur s0 tt)
          (lv <- get' (fun s => low s v);; update_low u lv)
          (Q_active_stack_frame cur s0).
  Proof.
    intro_state. eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    apply Hoare_conseq_pre with (P2 := Q_active_stack_frame cur s0 tt).
    { intros st Hst. destruct Hst. subst st. exact H. }
    apply update_low_preserves_Q_active_stack_frame.
  Qed.

  Lemma get_dfn_update_low_preserves_Q_active_stack_frame
        (u v cur: V) (s0: @SCCSt V):
    Hoare (Q_active_stack_frame cur s0 tt)
          (dv <- get' (fun s => dfn s v);; update_low u dv)
          (Q_active_stack_frame cur s0).
  Proof.
    intro_state. eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    apply Hoare_conseq_pre with (P2 := Q_active_stack_frame cur s0 tt).
    { intros st Hst. destruct Hst. subst st. exact H. }
    apply update_low_preserves_Q_active_stack_frame.
  Qed.

  Lemma process_edge_preserves_Q_active_stack_frame
        (u v cur: V) (s0: @SCCSt V)
        (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (Q_active_stack_frame cur s0 tt) (W x)
                     (Q_active_stack_frame cur s0)) ->
    Hoare (Q_active_stack_frame cur s0 tt)
          (process_edge u W v)
          (Q_active_stack_frame cur s0).
  Proof.
    intros HW.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := Q_active_stack_frame cur s0 tt).
      { intros st [Hnv Heq_st]. subst st. exact H. }
      intro_state.
      apply Hoare_conseq_pre with (P2 := Q_active_stack_frame cur s0 tt).
      { intros st Heq_st. subst st. exact H1. }
      eapply Hoare_bind with (R := fun (_: unit) s => Q_active_stack_frame cur s0 tt s).
      * exact (set_fa_preserves_Q_active_stack_frame v u cur s0).
      * intro u_; destruct u_.
        eapply Hoare_bind with (R := fun (_: unit) s => Q_active_stack_frame cur s0 tt s).
        -- exact (HW v).
        -- intro u_'; destruct u_'.
           exact (get_low_update_low_preserves_Q_active_stack_frame u v cur s0).
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := Q_active_stack_frame cur s0 tt).
      { intros st [Hnv Heq_st]. subst st. exact H. }
      intro_state. hoare_auto_s.
      + eapply Hoare_conseq_pre with (P2 := Q_active_stack_frame cur s0 tt).
        2: { exact (update_low_preserves_Q_active_stack_frame u cur (dfn s2 v) s0). }
        simpl. intros st Heq_st. subst st. exact H1.
      + destruct H2 as [Heq _]. subst s. exact H1.
  Qed.

  Lemma forset_preserves_Q_active_stack_frame
        (u cur: V) (s0: @SCCSt V)
        (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (Q_active_stack_frame cur s0 tt) (W x)
                     (Q_active_stack_frame cur s0)) ->
    Hoare (Q_active_stack_frame cur s0 tt)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (Q_active_stack_frame cur s0).
  Proof.
    intros HW.
    unfold forset. hoare_fix_nolv_auto (V -> Prop).
    simpl. intros W0 IH0 todo.
    unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
    eapply Hoare_bind with (R := fun (_: unit) s => Q_active_stack_frame cur s0 tt s).
    { apply Hoare_conseq_pre with (P2 := Q_active_stack_frame cur s0 tt).
      { intros st Hst. subst st. exact H. }
      apply process_edge_preserves_Q_active_stack_frame. intros x. apply HW. }
    intro u_; destruct u_. apply IH0.
  Qed.

  Lemma preloop_preserves_active_stack_frames
        (v: V) (frames: list (V * @SCCSt V)):
    Hoare (fun s: @SCCSt V =>
             active_stack_frames frames s /\
             stack_in_visited s /\
             ~ v ∈ visited s)
          (preloop v)
          (fun _ s => active_stack_frames frames s).
  Proof.
    unfold Hoare, active_stack_frames.
    intros s1 r s2 [Hframes [Hstack_in Hnv]] Hrun cur s0 Hin.
    pose proof (preloop_preserves_Q_active_stack_frame v cur s0) as Hpre.
    unfold Hoare in Hpre.
    exact (Hpre s1 r s2 (conj (Hframes cur s0 Hin) (conj Hstack_in Hnv)) Hrun).
  Qed.

  Lemma set_fa_preserves_active_stack_frames
        (v p: V) (frames: list (V * @SCCSt V)):
    Hoare (active_stack_frames frames)
          (set_fa v p)
          (fun _ s => active_stack_frames frames s).
  Proof.
    unfold Hoare, active_stack_frames.
    intros s1 r s2 Hframes Hrun cur s0 Hin.
    pose proof (set_fa_preserves_Q_active_stack_frame v p cur s0) as Hset.
    unfold Hoare in Hset.
    exact (Hset s1 r s2 (Hframes cur s0 Hin) Hrun).
  Qed.

  Lemma update_low_preserves_active_stack_frames
        (u: V) (n: nat) (frames: list (V * @SCCSt V)):
    Hoare (active_stack_frames frames)
          (update_low u n)
          (fun _ s => active_stack_frames frames s).
  Proof.
    unfold Hoare, active_stack_frames.
    intros s1 r s2 Hframes Hrun cur s0 Hin.
    pose proof (update_low_preserves_Q_active_stack_frame u cur n s0) as Hupd.
    unfold Hoare in Hupd.
    exact (Hupd s1 r s2 (Hframes cur s0 Hin) Hrun).
  Qed.

  Lemma get_low_update_low_preserves_active_stack_frames
        (u v: V) (frames: list (V * @SCCSt V)):
    Hoare (active_stack_frames frames)
          (lv <- get' (fun s => low s v);; update_low u lv)
          (fun _ s => active_stack_frames frames s).
  Proof.
    intro_state. eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    apply Hoare_conseq_pre with (P2 := active_stack_frames frames).
    { intros st Hst. destruct Hst. subst st. exact H. }
    apply update_low_preserves_active_stack_frames.
  Qed.

  Lemma process_edge_preserves_active_stack_frames
        (u v: V) (frames: list (V * @SCCSt V))
        (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (active_stack_frames frames) (W x)
                     (fun _ s => active_stack_frames frames s)) ->
    Hoare (active_stack_frames frames)
          (process_edge u W v)
          (fun _ s => active_stack_frames frames s).
  Proof.
    intros HW.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := active_stack_frames frames).
      { intros st [Hnv Heq_st]. subst st. exact H. }
      intro_state.
      apply Hoare_conseq_pre with (P2 := active_stack_frames frames).
      { intros st Heq_st. subst st. exact H1. }
      eapply Hoare_bind with (R := fun (_: unit) s => active_stack_frames frames s).
      * exact (set_fa_preserves_active_stack_frames v u frames).
      * intro u_; destruct u_.
        eapply Hoare_bind with (R := fun (_: unit) s => active_stack_frames frames s).
        -- exact (HW v).
        -- intro u_'; destruct u_'.
           exact (get_low_update_low_preserves_active_stack_frames u v frames).
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := active_stack_frames frames).
      { intros st [Hnv Heq_st]. subst st. exact H. }
      intro_state. hoare_auto_s.
      + eapply Hoare_conseq_pre with (P2 := active_stack_frames frames).
        2: { eapply update_low_preserves_active_stack_frames. }
        simpl. intros st Heq_st. subst st. exact H1.
      + destruct H2 as [Heq _]. subst s. exact H1.
  Qed.

  Lemma forset_preserves_active_stack_frames
        (u: V) (frames: list (V * @SCCSt V))
        (W: V -> program (@SCCSt V) unit):
    (forall x, Hoare (active_stack_frames frames) (W x)
                     (fun _ s => active_stack_frames frames s)) ->
    Hoare (active_stack_frames frames)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => active_stack_frames frames s).
  Proof.
    intros HW.
    unfold forset. hoare_fix_nolv_auto (V -> Prop).
    simpl. intros W0 IH0 todo.
    unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
    eapply Hoare_bind with (R := fun (_: unit) s => active_stack_frames frames s).
    { apply Hoare_conseq_pre with (P2 := active_stack_frames frames).
      { intros st Hst. subst st. exact H. }
      apply process_edge_preserves_active_stack_frames. intros x. apply HW. }
    intro u_; destruct u_. apply IH0.
  Qed.


  Lemma if_pop_preserves_Q_active_stack_frame
        (pop_root cur: V) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             Q_active_stack_frame cur s0 tt s /\
             stack_dfn_order s /\
             In pop_root (stack s) /\
             dfn s cur < dfn s pop_root)
          (If (fun s => low s pop_root = dfn s pop_root) (pop_scc pop_root))
          (Q_active_stack_frame cur s0).
  Proof.
    unfold If.
    intro_state. destruct H as [Hactive [Hord [Hpop_stack Hcur_lt_pop]]].
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      refine (Hoare_conseq_pre _
               (fun s =>
                  Q_active_stack_frame cur s0 tt s /\
                  stack_dfn_order s /\
                  In pop_root (stack s) /\
                  dfn s cur < dfn s pop_root)
               (pop_scc pop_root) (Q_active_stack_frame cur s0) _ _); [ | ].
      { intros st [Hlow Heq_st]. subst st.
        split; [exact Hactive | split; [exact Hord | split; [exact Hpop_stack | exact Hcur_lt_pop]]]. }
      { unfold pop_scc. intro_state. hoare_auto_s.
        destruct H as [Hactive_pop [Hord_pop [Hpop_stack_pop Hcur_lt_pop']]].
        subst s. unfold Q_active_stack_frame in Hactive_pop |- *.
        destruct Hactive_pop as [Hcur_stack [Hcur_dfn [Hframe Hanc_dfn]]].
        split; [| split; [| split]].
        - eapply pop_scc_keeps_older_stack_vertex.
          + exact Hord_pop.
          + exact Hcur_stack.
          + exact Hpop_stack_pop.
          + exact Hcur_lt_pop'.
        - unfold pop_scc_state.
          destruct (stack_split_at (stack s2) pop_root) as [popped rest] eqn:?.
          simpl. exact Hcur_dfn.
        - unfold Q_stack_frame. intros anc Hanc Hlt.
          eapply pop_scc_keeps_older_stack_vertex.
          + exact Hord_pop.
          + apply Hframe; auto.
          + exact Hpop_stack_pop.
          + rewrite (Hanc_dfn anc Hanc Hlt).
            rewrite <- Hcur_dfn in Hlt.
            lia.
        - intros anc Hanc Hlt.
          unfold pop_scc_state.
          destruct (stack_split_at (stack s2) pop_root) as [popped rest] eqn:?.
          simpl. apply Hanc_dfn; auto. }
    - intro_state. hoare_auto_s.
      destruct H1 as [Hs _]. subst s. subst s2. exact Hactive.
  Qed.

  Lemma if_pop_preserves_active_stack_frames
        (pop_root: V) (frames: list (V * @SCCSt V)):
    Hoare (fun s: @SCCSt V =>
             active_stack_frames frames s /\
             stack_dfn_order s /\
             In pop_root (stack s) /\
             active_stack_frames_below frames pop_root s)
          (If (fun s => low s pop_root = dfn s pop_root) (pop_scc pop_root))
          (fun _ s => active_stack_frames frames s).
  Proof.
    unfold Hoare, active_stack_frames, active_stack_frames_below.
    intros s1 r s2 [Hframes [Hord [Hpop_stack Hbelow]]] Hrun cur s0 Hin.
    pose proof (if_pop_preserves_Q_active_stack_frame pop_root cur s0) as Hif.
    unfold Hoare in Hif.
    exact (Hif s1 r s2
             (conj (Hframes cur s0 Hin)
               (conj Hord (conj Hpop_stack (Hbelow cur s0 Hin))))
             Hrun).
  Qed.

  Lemma if_pop_preserves_active_base
        (pop_root: V) (frames: list (V * @SCCSt V)):
    Hoare (fun s: @SCCSt V =>
             active_base frames s /\
             In pop_root (stack s) /\
             active_stack_frames_below frames pop_root s)
          (If (fun s => low s pop_root = dfn s pop_root) (pop_scc pop_root))
          (fun _ s => active_base frames s).
  Proof.
    unfold active_base.
    apply Hoare_conj with
      (Q1 := fun _ s => active_stack_frames frames s)
      (Q2 := fun _ s => wf_scc_state g root s /\ stack_dfn_order s /\ dfn_injective s).
    - eapply Hoare_conseq_pre.
      2: apply if_pop_preserves_active_stack_frames.
      intros s [[Hframes [Hwf [Hord Hinj]]] [Hpop Hbelow]].
      split; [exact Hframes | split; [exact Hord | split; [exact Hpop | exact Hbelow]]].
    - unfold If. intro_state. destruct H as [[Hframes [Hwf [Hord Hinj]]] [Hpop Hbelow]].
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        apply Hoare_conj with
          (Q1 := fun _ s => wf_scc_state g root s)
          (Q2 := fun _ s => stack_dfn_order s /\ dfn_injective s).
        * eapply Hoare_conseq_pre.
          2: apply (pop_scc_preserves_wf_scc_state g root pop_root).
          intros st [Hlow Heq]. subst st. exact Hwf.
        * apply Hoare_conj.
          -- eapply Hoare_conseq_pre.
             2: apply (pop_scc_preserves_stack_dfn_order pop_root).
             intros st [Hlow Heq]. subst st. split; auto.
          -- unfold pop_scc. intro_state. hoare_auto_s.
             destruct H as [_ Heq]. subst s1. subst s. unfold pop_scc_state.
             destruct (stack_split_at (stack s0) pop_root) as [popped rest] eqn:?.
             simpl. exact Hinj.
      + intro_state. hoare_auto_s.
        destruct H1 as [Heq _]. subst.
        split; [exact Hwf | split; [exact Hord | exact Hinj]].
  Qed.

  Theorem tarjan_scc_preserves_Q_active_stack_frame
          (child cur: V) (s0: @SCCSt V):
    Hoare (fun s: @SCCSt V =>
             Q_active_stack_frame cur s0 tt s /\
             dfn s cur < timer s /\
             low_pre g root child s /\
             stack_dfn_order s /\
             dfn_injective s)
          (tarjan_scc g child)
          (Q_active_stack_frame cur s0).
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
             Q_active_stack_frame u s0 tt s /\
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
