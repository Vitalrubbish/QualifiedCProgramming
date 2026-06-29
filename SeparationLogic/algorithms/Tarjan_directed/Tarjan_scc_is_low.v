Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
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

  Definition active_stack_frames_below_timer
             (frames: list (V * @SCCSt V)) (s: @SCCSt V): Prop :=
    forall cur s0, In (cur, s0) frames -> dfn s cur < timer s.

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

  Lemma active_base_frame_visited
        (frames: list (V * @SCCSt V)) (u: V) (s0 s: @SCCSt V):
    active_base frames s ->
    In (u, s0) frames ->
    u ∈ visited s.
  Proof.
    intros [Hframes [Hwf _]] Hin.
    unfold wf_scc_state in Hwf.
    destruct Hwf as [Hstack_in _].
    apply Hstack_in.
    exact (Q_active_stack_frame_self_stack u s0 s (Hframes u s0 Hin)).
  Qed.

  Lemma active_base_tail
        (u: V) (su: @SCCSt V) (frames: list (V * @SCCSt V)) (s: @SCCSt V):
    active_base ((u, su) :: frames) s ->
    active_base frames s.
  Proof.
    intros [Hframes Hrest].
    split; [| exact Hrest].
    intros cur s0 Hin.
    apply Hframes. simpl. right. exact Hin.
  Qed.

  Lemma active_stack_frames_below_transport
        (frames: list (V * @SCCSt V)) (u: V) (su s: @SCCSt V):
    active_stack_frames ((u, su) :: frames) su ->
    active_stack_frames ((u, su) :: frames) s ->
    active_stack_frames_below frames u su ->
    active_stack_frames_below frames u s.
  Proof.
    unfold active_stack_frames, active_stack_frames_below.
    intros Hpre Hpost Hbelow cur s0 Hin.
    pose proof (Hpre cur s0 (or_intror Hin)) as Hcur_pre.
    pose proof (Hpost cur s0 (or_intror Hin)) as Hcur_post.
    pose proof (Hpost u su (or_introl eq_refl)) as Hu_post.
    specialize (Hbelow cur s0 Hin).
    rewrite (Q_active_stack_frame_self_dfn cur s0 s Hcur_post).
    rewrite <- (Q_active_stack_frame_self_dfn cur s0 su Hcur_pre).
    rewrite (Q_active_stack_frame_self_dfn u su s Hu_post).
    exact Hbelow.
  Qed.

  Lemma set_fa_preserves_active_base_for_child
        (u v: V) (frames: list (V * @SCCSt V)):
    Hoare (fun s: @SCCSt V =>
             active_base frames s /\
             u ∈ visited s /\
             ~ v ∈ visited s)
          (set_fa v u)
          (fun _ s => active_base frames s /\ low_pre g root v s).
  Proof.
    unfold active_base, low_pre.
    apply Hoare_conseq_post with
      (Q2 := fun _ s =>
               active_stack_frames frames s /\
               ((wf_scc_state g root s /\ ~ v ∈ visited s) /\
                (stack_dfn_order s /\ dfn_injective s))).
    { intros _ s [Hframes [[Hwf Hnvis] [Hord Hinj]]].
      split; [split; [exact Hframes | split; [exact Hwf | split; [exact Hord | exact Hinj]]] | split; auto]. }
    apply Hoare_conj with
      (Q1 := fun _ s => active_stack_frames frames s)
      (Q2 := fun _ s =>
               (wf_scc_state g root s /\ ~ v ∈ visited s) /\
               (stack_dfn_order s /\ dfn_injective s)).
    - eapply Hoare_conseq_pre.
      2: apply set_fa_preserves_active_stack_frames.
      intros s [[Hframes _] _]. exact Hframes.
    - apply Hoare_conj with
        (Q1 := fun _ s => wf_scc_state g root s /\ ~ v ∈ visited s)
        (Q2 := fun _ s => stack_dfn_order s /\ dfn_injective s).
      + eapply Hoare_conseq_post.
        2: { eapply Hoare_conseq_pre.
             2: apply (set_fa_preserves_wf_scc_state_pre g root v u).
             intros s [[Hframes [Hwf [Hord Hinj]]] [Huvis Hnvis]].
             split; [exact Hwf | split; [exact Huvis | exact Hnvis]]. }
        intros _ s [[Hwf Hnvis] _]. split; auto.
      + apply Hoare_conj.
        * eapply Hoare_conseq_pre.
          2: apply (set_fa_keep_stack_dfn_order v u).
          intros s [[Hframes [Hwf [Hord Hinj]]] _]. exact Hord.
        * eapply Hoare_conseq_pre.
          2: apply (set_fa_keep_dfn_injective v u).
          intros s [[Hframes [Hwf [Hord Hinj]]] _]. exact Hinj.
  Qed.

  Lemma get_low_update_low_preserves_active_base
        (u v: V) (frames: list (V * @SCCSt V))
        (su: @SCCSt V):
    In (u, su) frames ->
    Hoare (active_base frames)
          (lv <- get' (fun s => low s v);; update_low u lv)
          (fun _ s => active_base frames s).
  Proof.
    intros Hin_frame.
    apply Hoare_normalize. intros snap Hbase_snap.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    unfold active_base.
    apply Hoare_conj with
      (Q1 := fun _ s => active_stack_frames frames s)
      (Q2 := fun _ s => wf_scc_state g root s /\ stack_dfn_order s /\ dfn_injective s).
    - eapply Hoare_conseq_pre.
      2: apply update_low_preserves_active_stack_frames.
      intros st [Heq _]. subst st. exact (proj1 Hbase_snap).
    - apply Hoare_conj with
        (Q1 := fun _ s => wf_scc_state g root s)
        (Q2 := fun _ s => stack_dfn_order s /\ dfn_injective s).
      + eapply Hoare_conseq_pre.
        2: apply (update_low_preserves_wf_scc_state g root u lv).
        intros st [Heq _]. subst st.
        split.
        * exact (proj1 (proj2 Hbase_snap)).
        * exact (active_base_frame_visited frames u su snap Hbase_snap Hin_frame).
      + apply Hoare_conj.
        * eapply Hoare_conseq_pre.
          2: apply (update_low_keep_stack_dfn_order u lv).
          intros st [Heq _]. subst st.
          exact (proj1 (proj2 (proj2 Hbase_snap))).
        * eapply Hoare_conseq_pre.
          2: apply (update_low_keep_dfn_injective u lv).
          intros st [Heq _]. subst st.
          exact (proj2 (proj2 (proj2 Hbase_snap))).
  Qed.

  Lemma update_low_preserves_active_base_with_frame
        (u: V) (n: nat) (frames: list (V * @SCCSt V))
        (su: @SCCSt V):
    In (u, su) frames ->
    Hoare (active_base frames)
          (update_low u n)
          (fun _ s => active_base frames s).
  Proof.
    intros Hin_frame.
    unfold active_base.
    apply Hoare_conj with
      (Q1 := fun _ s => active_stack_frames frames s)
      (Q2 := fun _ s => wf_scc_state g root s /\ stack_dfn_order s /\ dfn_injective s).
    - eapply Hoare_conseq_pre.
      2: apply update_low_preserves_active_stack_frames.
      intros s [Hframes _]. exact Hframes.
    - apply Hoare_conj with
        (Q1 := fun _ s => wf_scc_state g root s)
        (Q2 := fun _ s => stack_dfn_order s /\ dfn_injective s).
      + eapply Hoare_conseq_pre.
        2: apply (update_low_preserves_wf_scc_state g root u n).
        intros s Hbase.
        split.
        * exact (proj1 (proj2 Hbase)).
        * exact (active_base_frame_visited frames u su s Hbase Hin_frame).
      + apply Hoare_conj.
        * eapply Hoare_conseq_pre.
          2: apply (update_low_keep_stack_dfn_order u n).
          intros s [_ [_ [Hord _]]]. exact Hord.
        * eapply Hoare_conseq_pre.
          2: apply (update_low_keep_dfn_injective u n).
          intros s [_ [_ [_ Hinj]]]. exact Hinj.
  Qed.

  Lemma process_edge_preserves_active_base
        (u v: V) (frames: list (V * @SCCSt V)) (su: @SCCSt V)
        (W: V -> program (@SCCSt V) unit):
    In (u, su) frames ->
    (forall x,
       Hoare (fun s => active_base frames s /\ low_pre g root x s)
             (W x)
             (fun _ s => active_base frames s)) ->
    Hoare (active_base frames)
          (process_edge u W v)
          (fun _ s => active_base frames s).
  Proof.
    intros Hin_frame HW.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with
        (P2 := fun s => active_base frames s /\
                       u ∈ visited s /\ ~ v ∈ visited s).
      { intros st [Hnv Heq]. subst st.
        split; [exact H | split; [| exact Hnv]].
        exact (active_base_frame_visited frames u su s0 H Hin_frame). }
      eapply Hoare_bind with
        (Q := fun (_: unit) s => active_base frames s /\ low_pre g root v s).
      { apply set_fa_preserves_active_base_for_child. }
      simpl. intros _.
      eapply Hoare_bind with (Q := fun (_: unit) s => active_base frames s).
      { apply HW. }
      simpl. intros _.
      apply get_low_update_low_preserves_active_base with (su := su).
      exact Hin_frame.
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with (P2 := active_base frames).
      { intros st [_ Heq]. subst st. exact H. }
      intro_state. hoare_auto_s.
      + eapply Hoare_conseq_pre.
        2: { apply update_low_preserves_active_base_with_frame with (su := su). exact Hin_frame. }
        intros st Heq. subst st. exact H1.
      + destruct H2 as [Heq _]. subst s. exact H1.
  Qed.

  Lemma forset_preserves_active_base
        (u: V) (frames: list (V * @SCCSt V)) (su: @SCCSt V)
        (W: V -> program (@SCCSt V) unit):
    In (u, su) frames ->
    (forall x,
       Hoare (fun s => active_base frames s /\ low_pre g root x s)
             (W x)
             (fun _ s => active_base frames s)) ->
    Hoare (active_base frames)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => active_base frames s).
  Proof.
    intros Hin_frame HW.
    unfold forset. hoare_fix_nolv_auto (V -> Prop).
    simpl. intros W0 IH0 todo.
    unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
    eapply Hoare_bind with (Q := fun (_: unit) s => active_base frames s).
    { apply Hoare_conseq_pre with (P2 := active_base frames).
      { intros st Hst. subst st. exact H. }
      apply process_edge_preserves_active_base with (su := su); auto. }
    intro u_; destruct u_. apply IH0.
  Qed.

  Theorem tarjan_scc_preserves_active_base
          (u: V) (frames: list (V * @SCCSt V)):
    Hoare (fun s: @SCCSt V =>
             active_base frames s /\
             low_pre g root u s /\
             active_stack_frames_below_timer frames s)
          (tarjan_scc g u)
          (fun _ s => active_base frames s).
  Proof.
    unfold tarjan_scc.
    apply (Hoare_fix_logicv (tarjan_scc_f g)
             (fun (x: V) (frames: list (V * @SCCSt V)) (s: SCCSt) =>
                active_base frames s /\
                low_pre g root x s /\
                active_stack_frames_below_timer frames s)
             (fun (_: V) (frames: list (V * @SCCSt V)) (_: unit) (s: SCCSt) =>
                active_base frames s)
             u frames).
    intros W IH x active_frames.
    unfold tarjan_scc_f.
    apply Hoare_normalize. intros snap Hsnap.
    eapply Hoare_bind with
      (Q := fun (_: unit) (s: SCCSt) =>
              active_base ((x, s) :: active_frames) s /\
              active_stack_frames_below active_frames x s).
    - apply Hoare_conj with
        (Q1 := fun _ s => active_base ((x, s) :: active_frames) s)
        (Q2 := fun _ s => active_stack_frames_below active_frames x s).
      + unfold active_base.
        apply Hoare_conj with
          (Q1 := fun _ s => active_stack_frames ((x, s) :: active_frames) s)
          (Q2 := fun _ s => wf_scc_state g root s /\ stack_dfn_order s /\ dfn_injective s).
        * unfold active_stack_frames.
          intros s_pre r s_post Hpre Hrun cur s_cur Hin.
          destruct Hin as [Hin_head | Hin_tail].
          -- inversion Hin_head; subst cur s_cur.
             pose proof (preloop_in_stack x) as Hstk.
             unfold Hoare in Hstk.
             apply Q_active_stack_frame_current.
             exact (Hstk s_pre r s_post I Hrun).
          -- pose proof (preloop_preserves_Q_active_stack_frame x cur s_cur) as Hpreloop.
             unfold Hoare in Hpreloop.
             subst s_pre.
             destruct Hsnap as [[Hframes [Hwf _]] [[Hwf_pre Hnvis] Hbelow_timer]].
             unfold wf_scc_state in Hwf.
             eapply Hpreloop; [| exact Hrun].
             split; [exact (Hframes cur s_cur Hin_tail) | split; [exact (proj1 Hwf) | exact Hnvis]].
        * eapply Hoare_conseq
            with (P2 := fun s => low_pre g root x s /\ stack_dfn_order s /\ dfn_injective s)
                 (Q2 := fun _ s => low_iteration_entry g root x s).
          intros s_pre Hpre.
          subst s_pre.
          destruct Hsnap as [[Hframes [Hwf [Hord Hinj]]] [Hlow Hbelow_timer]].
          split; [exact Hlow | split; [exact Hord | exact Hinj]].
          intros _ s Hentry.
          unfold low_iteration_entry, low_iteration_inv in Hentry.
          destruct Hentry as [[Hwf [_ [_ _]]] [Hord Hinj]].
          split; [exact Hwf | split; [exact Hord | exact Hinj]].
          apply (preloop_establishes_low_iteration_entry g root x).
      + unfold Hoare. intros s_pre r s_post Hpre Hrun.
        subst s_pre.
        unfold active_stack_frames_below.
        intros cur s_cur Hin.
        destruct Hsnap as [[Hframes [Hwf [Hord Hinj]]] [[Hwf_pre Hnvis] Hbelow_timer]].
        pose proof (Hframes cur s_cur Hin) as Hactive_cur.
        rewrite (Q_active_stack_frame_self_dfn cur s_cur s_post).
        2: {
          pose proof (preloop_preserves_Q_active_stack_frame x cur s_cur) as Hpreloop.
          unfold Hoare in Hpreloop.
          unfold wf_scc_state in Hwf.
          eapply Hpreloop; [| exact Hrun].
          split; [exact Hactive_cur | split; [exact (proj1 Hwf) | exact Hnvis]]. }
        pose proof (preloop_dfn_set x (timer snap)) as Hdfn_x.
        unfold Hoare in Hdfn_x.
        rewrite (Hdfn_x snap r s_post eq_refl Hrun).
        rewrite <- (Q_active_stack_frame_self_dfn cur s_cur snap Hactive_cur).
        exact (Hbelow_timer cur s_cur Hin).
    - simpl. intros _.
      apply Hoare_normalize. intros pre_snap Hpre_snap.
      eapply Hoare_bind with
        (Q := fun (_: unit) (s: SCCSt) =>
                active_base ((x, pre_snap) :: active_frames) s).
      + eapply Hoare_conseq_pre.
        2: { apply forset_preserves_active_base with (su := pre_snap).
             - simpl. left. reflexivity.
             - intros y.
               eapply Hoare_conseq_pre.
               2: apply (IH y ((x, pre_snap) :: active_frames)).
               intros st [Hbase Hlow].
               split; [exact Hbase | split; [exact Hlow | ]].
               unfold active_stack_frames_below_timer.
               intros cur s_cur Hin.
               pose proof Hbase as Hbase_all.
               destruct Hbase as [Hframes_base [Hwf_base [Hord_base Hinj_base]]].
               unfold wf_scc_state in Hwf_base.
               destruct Hwf_base as [_ [Hinv _]].
               destruct Hinv as [Htimer_lt _].
               apply Htimer_lt.
               exact (active_base_frame_visited ((x, pre_snap) :: active_frames)
                       cur s_cur st Hbase_all Hin). }
        intros st Heq. subst st. exact (proj1 Hpre_snap).
      + simpl. intros _.
        eapply Hoare_conseq_pre.
        2: { apply if_pop_preserves_active_base. }
        intros st Hbase.
        split.
        * exact (active_base_tail x pre_snap active_frames st Hbase).
        * split.
          -- exact (Q_active_stack_frame_self_stack x pre_snap st
                      ((proj1 Hbase) x pre_snap (or_introl eq_refl))).
          -- eapply active_stack_frames_below_transport.
             ++ exact (proj1 (proj1 Hpre_snap)).
             ++ exact (proj1 Hbase).
             ++ exact (proj2 Hpre_snap).
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
  Proof.
    eapply Hoare_conseq
      with (P2 := fun s =>
              active_base ((cur, s0) :: nil) s /\
              low_pre g root child s /\
              active_stack_frames_below_timer ((cur, s0) :: nil) s)
           (Q2 := fun _ s => active_base ((cur, s0) :: nil) s).
    - intros s [Hactive [Hcur_timer [Hlow [Hord Hinj]]]].
      pose proof Hlow as Hlow_copy.
      split.
      + unfold active_base, active_stack_frames.
        unfold low_pre in Hlow.
        destruct Hlow as [Hwf Hnvis].
        split.
        * intros cur' s0' Hin.
          destruct Hin as [Hin | []].
          inversion Hin. subst cur' s0'. exact Hactive.
        * split; [exact Hwf | split; [exact Hord | exact Hinj]].
      + split; [exact Hlow_copy | ].
        unfold active_stack_frames_below_timer.
        intros cur' s0' Hin.
        destruct Hin as [Hin | []].
        inversion Hin. subst cur' s0'. exact Hcur_timer.
    - intros b s Hbase.
      exact ((proj1 Hbase) cur s0 (or_introl eq_refl)).
    - apply (tarjan_scc_preserves_active_base child ((cur, s0) :: nil)).
  Qed.

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

  Theorem tarjan_scc_keep_root_fa (u fau: V):
    Hoare (fun s: @SCCSt V => fa s u = fau)
          (tarjan_scc g u)
          (fun _ s => fa s u = fau).
  Proof.
    unfold tarjan_scc.
    apply (Hoare_fix_logicv_conj (tarjan_scc_f g)
             (fun (x: V) (fav: V) (s: SCCSt) => fa s x = fav)
             (fun (x: V) (fav: V) (_: unit) (s: SCCSt) => fa s x = fav)
             u fau
             (fun (x: V) (p: V * V) (s: SCCSt) =>
                x <> fst p /\ fst p ∈ visited s /\ fa s (fst p) = snd p)
             (fun (_: V) (p: V * V) (_: unit) (s: SCCSt) =>
                fst p ∈ visited s /\ fa s (fst p) = snd p)).
    - intros x p.
      destruct p as [tracked fav]. simpl.
      apply (Tarjan_scc_basics.tarjan_scc_keep_fa
               (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g x tracked fav).
    - intros W IHother IHself x fav.
      unfold tarjan_scc_f.
      eapply Hoare_bind.
      + apply Hoare_conj with
          (Q1 := fun _ s => fa s x = fav)
          (Q2 := fun _ s => x ∈ visited s).
        * apply preloop_keep_fa_no_restriction.
        * eapply Hoare_conseq_pre.
          2: { apply preloop_self_visited. }
          intros st _; exact I.
      + simpl. intros _.
        eapply Hoare_bind with
          (Q := fun _ s => x ∈ visited s /\ fa s x = fav).
        * eapply Hoare_conseq_pre.
          2: {
            apply (Tarjan_scc_basics.forset_process_edge_keep_fa
                     (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0)
                     g x x W fav).
            intros y.
            apply (IHother y (x, fav)). }
          intros st [Hfa Hvis].
          split; [exact Hvis | exact Hfa].
        * simpl. intros _.
          unfold If. intro_state. hoare_auto_s.
          -- eapply Hoare_conseq_pre.
             2: { apply (pop_scc_keep_fa x x fav). }
             intros st Heq. subst st. exact (proj2 H).
          -- destruct H1 as [Heq _]. subst s. exact (proj2 H).
  Qed.

  (* ================================================================ *)
  (* Forset phase contracts                                          *)
  (* ================================================================ *)

  Definition low_continuation_contract
             (W: V -> program (@SCCSt V) unit)
             (u a: V) (done: V -> Prop) (s0: @SCCSt V): Prop :=
    dg_step g u a ->
    ~ done a ->
    Hoare (fun s =>
             s = s0 /\
             low_iteration_inv g root u done s /\
             stack_dfn_order s /\
             dfn_injective s /\
             ~ a ∈ visited s)
          (set_fa a u;; W a;;
           lv <- get' (fun s => low s a);;
           update_low u lv)
          (fun _ s =>
             low_iteration_inv g root u (done ∪ [a]) s /\
             stack_dfn_order s /\
             dfn_injective s).

  Definition low_tree_child_after_set_fa
             (u a: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    wf_scc_state_pre g root a s /\
    u ∈ visited s /\
    In u (stack s) /\
    done_visited done s /\
    low_frontier g u done s /\
    low_src g u done s /\
    children_low_valid g root u done s /\
    fa_child_of_u g u s /\
    fa_not_done_implies_eq_u u (done ∪ [a]) s /\
    fa s a = u /\
    stack_dfn_order s /\
    dfn_injective s.

  Definition low_tree_child_parent_pending
             (u a: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    wf_scc_state g root s /\
    u ∈ visited s /\
    In u (stack s) /\
    done_visited done s /\
    low_frontier g u done s /\
    low_src g u done s /\
    children_low_valid g root u done s /\
    fa_child_of_u g u s /\
    fa_not_done_implies_eq_u u (done ∪ [a]) s /\
    stack_dfn_order s /\
    dfn_injective s /\
    dg_step g u a /\
    ~ done a /\
    a ∈ visited s /\
    fa s a = u /\
    fa s a <> a.

  Definition low_tree_child_after_recursive
             (u a: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    low_tree_child_parent_pending u a done s /\
    scc_low_valid_v g root s a.

  Lemma set_fa_establishes_pending_fa_not_done
        (u a: V) (done: V -> Prop):
    Hoare (fun s: @SCCSt V =>
             low_iteration_inv g root u done s /\
             ~ done a)
          (set_fa a u)
          (fun _ s => fa_not_done_implies_eq_u u (done ∪ [a]) s).
  Proof.
    unfold set_fa.
    intro_state. hoare_auto_s.
    subst s. unfold RecordSet.set. simpl.
    unfold fa_not_done_implies_eq_u.
    destruct H as [Hiter Hndone].
    destruct Hiter as (_ & _ & _ & _ & _ & _ & _ & _ & Hfa_not).
    intros w Hnot_done Hfa_w.
    simpl in Hfa_w. unfold equiv_decb in Hfa_w.
    destruct (equiv_dec w a) as [Hw_eq_a | Hw_neq_a].
    - destruct Hw_eq_a.
      exfalso. apply Hnot_done. sets_unfold. right. reflexivity.
    - apply Hfa_not; [| exact Hfa_w].
      intro Hdone_v. apply Hnot_done. sets_unfold. left. exact Hdone_v.
  Qed.

  Lemma low_iteration_extend_done_nonstack_pure
        (u a: V) (done: V -> Prop):
    forall s: @SCCSt V,
      low_iteration_inv g root u done s ->
      stack_dfn_order s ->
      dfn_injective s ->
      dg_step g u a ->
      ~ done a ->
      a ∈ visited s ->
      ~ In a (stack s) ->
      low_iteration_inv g root u (done ∪ [a]) s /\
      stack_dfn_order s /\
      dfn_injective s.
  Proof.
    intros s Hiter Hord Hinj Hdg Hndone Hvis Hnot_stack.
    destruct Hiter as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc &
                       Hchild & Hfa_child & Hfa_not).
    split; [| split; [exact Hord | exact Hinj]].
    unfold low_iteration_inv.
    split; [exact Hwf | split; [exact Huvis | split; [exact Hustack |]]].
    split.
    - unfold done_visited in Hdonevis |- *.
      intros w Hw. sets_unfold in Hw. destruct Hw as [Hdone_w | Hw_eq].
      + apply Hdonevis. exact Hdone_w.
      + subst w. exact Hvis.
    - split.
      + unfold low_frontier in Hfront |- *.
        destruct Hfront as [Hle Hfront]. split; [exact Hle |].
        intros v Hv_done Hv_dg.
        sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
        * apply Hfront; auto.
        * subst v. split.
          -- intro Hfa_a.
             specialize (Hfa_not a Hndone Hfa_a). subst a.
             contradiction.
          -- intro Ha_stack. contradiction.
      + split.
        * unfold low_src in Hsrc |- *.
          destruct Hsrc as [Hsrc | [(v & Hdone_v & Hdg_v & Hfa_v & Hfa_neq_v & Hlow_v) |
                                   (w & Hdone_w & Hdg_w & Hstack_w & Hfa_neq_w & Hlow_w)]].
          -- left. exact Hsrc.
          -- right. left. exists v. repeat split; auto. sets_unfold. left. exact Hdone_v.
          -- right. right. exists w. repeat split; auto. sets_unfold. left. exact Hdone_w.
        * split.
          -- unfold children_low_valid in Hchild |- *.
             intros v Hv_done Hv_dg Hfa_v Hfa_neq_v.
             sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
             ++ apply Hchild; auto.
             ++ subst v.
                specialize (Hfa_not a Hndone Hfa_v). subst a.
                contradiction.
          -- split.
             ++ exact Hfa_child.
             ++ unfold fa_not_done_implies_eq_u in Hfa_not |- *.
                intros v Hnot_done Hfa_v.
                apply Hfa_not; [| exact Hfa_v].
                intro Hdone_v. apply Hnot_done. sets_unfold. left. exact Hdone_v.
  Qed.

  Lemma low_iteration_extend_done_skip_nonstack
        (u a: V) (done: V -> Prop):
    Hoare (fun s: @SCCSt V =>
             low_iteration_inv g root u done s /\
             stack_dfn_order s /\
             dfn_injective s /\
             dg_step g u a /\
             ~ done a /\
             a ∈ visited s /\
             ~ In a (stack s))
          (return tt)
          (fun _ s =>
             low_iteration_inv g root u (done ∪ [a]) s /\
             stack_dfn_order s /\
             dfn_injective s).
  Proof.
    intro_state. hoare_auto_s.
    subst s.
    destruct H as [Hiter [Hord [Hinj [Hdg [Hndone [Hvis Hnot_stack]]]]]].
    eapply low_iteration_extend_done_nonstack_pure; eauto.
  Qed.

  Lemma low_iteration_extend_done_assume_nonstack
        (u a: V) (done: V -> Prop):
    Hoare (fun s: @SCCSt V =>
             low_iteration_inv g root u done s /\
             stack_dfn_order s /\
             dfn_injective s /\
             dg_step g u a /\
             ~ done a /\
             a ∈ visited s)
          (assume (fun s => ~ In a (stack s)))
          (fun _ s =>
             low_iteration_inv g root u (done ∪ [a]) s /\
             stack_dfn_order s /\
             dfn_injective s).
  Proof.
    eapply Hoare_conseq_post.
    2: { apply Hoare_assume. }
    intros r s Hpost.
    destruct Hpost as [[Hiter [Hord [Hinj [Hdg [Hndone Hvis]]]]] Hnot_stack].
    eapply low_iteration_extend_done_nonstack_pure; eauto.
  Qed.

  Lemma get_dfn_update_low_current_extends_low_iteration_stack
        (u a: V) (done: V -> Prop):
    Hoare (fun s: @SCCSt V =>
             low_iteration_inv g root u done s /\
             stack_dfn_order s /\
             dfn_injective s /\
             dg_step g u a /\
             ~ done a /\
             a ∈ visited s /\
             In a (stack s))
          (dv <- get' (fun s => dfn s a);; update_low u dv)
          (fun _ s =>
             low_iteration_inv g root u (done ∪ [a]) s /\
             stack_dfn_order s /\
             dfn_injective s).
  Proof.
    apply Hoare_normalize. intros snap Hsnap.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - destruct H as [Heq_snap Hdv]. subst s0. subst dv.
      subst s.
      unfold RecordSet.set. simpl.
      destruct Hsnap as [Hiter [Hord [Hinj [Hdg [Hndone [Hvis Hstack_a]]]]]].
      destruct Hiter as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc &
                         Hchild & Hfa_child & Hfa_not).
      split; [| split].
      + unfold low_iteration_inv.
        split.
        * unfold wf_scc_state in Hwf |- *.
          destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]].
          split; [exact Hsiv | split; [exact Hinv | split; [exact Hvalid | exact Hfa_vis]]].
        * split; [exact Huvis | split; [exact Hustack |]].
          split.
          -- unfold done_visited in Hdonevis |- *.
             intros w Hw. sets_unfold in Hw. destruct Hw as [Hdone_w | Hw_eq].
             ++ apply Hdonevis. exact Hdone_w.
             ++ subst w. exact Hvis.
          -- split.
             ++ unfold low_frontier in Hfront |- *.
                destruct Hfront as [Hle Hfront].
                split.
                { simpl. unfold equiv_decb.
                  destruct (equiv_dec u u) as [_ | Hc];
                    [assert (dfn snap a <= dfn snap u) by lia; exact H
                    | exfalso; apply Hc; reflexivity]. }
                intros v Hv_done Hv_dg.
                sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
                ** specialize (Hfront v Hv_done Hv_dg) as [Hfa_part Hstack_part].
                   split; intros Hcase.
                   --- simpl. unfold equiv_decb.
                       destruct (equiv_dec u u) as [_ | Hc];
                         [destruct (equiv_dec v u) as [Hv_eq_u | Hv_neq_u];
                            [lia |
                             assert (dfn snap a <= low snap v) by
                               (simpl in Hcase; pose proof (Hfa_part Hcase); lia); exact H]
                         | exfalso; apply Hc; reflexivity].
                   --- simpl. unfold equiv_decb.
                       destruct (equiv_dec u u) as [_ | Hc];
                         [assert (dfn snap a <= dfn snap v) by
                            (pose proof (Hstack_part Hcase); lia); exact H
                         | exfalso; apply Hc; reflexivity].
                ** subst v.
                   split;
                     [ intros Hfa_a;
                       simpl; unfold equiv_decb;
                       destruct (equiv_dec u u) as [_ | Hc];
                       [ destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq_u];
                         [ lia
                         | specialize (Hfa_not a Hndone Hfa_a); contradiction ]
                       | exfalso; apply Hc; reflexivity ]
                     | intros _;
                       simpl; unfold equiv_decb;
                       destruct (equiv_dec u u) as [_ | Hc];
                       [ lia | exfalso; apply Hc; reflexivity ] ].
             ++ split.
                ** unfold low_src in Hsrc |- *.
                   unfold equiv_decb.
                   destruct (equiv_dec u u) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
	                   destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq_u].
	                   { left. simpl. unfold equiv_decb.
	                     destruct (equiv_dec u u) as [_ | Hc];
	                       [rewrite Ha_eq_u; reflexivity | exfalso; apply Hc; reflexivity]. }
		                   { right. right. exists a.
		                     split; [sets_unfold; right; reflexivity |].
		                     split; [exact Hdg |].
		                     split; [exact Hstack_a |].
		                     split.
		                     - intro Hfa_a. specialize (Hfa_not a Hndone Hfa_a). contradiction.
		                     - simpl. unfold equiv_decb.
		                       destruct (equiv_dec u u) as [_ | Hc];
		                         [destruct (equiv_dec a u) as [Ha_eq_u' | Ha_neq_u'];
		                          [contradiction | reflexivity]
		                         | exfalso; apply Hc; reflexivity]. }
                ** split.
	                   --- unfold children_low_valid in Hchild |- *.
	                       intros v Hv_done Hv_dg Hfa_v Hfa_neq_v.
	                       sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
	                       { apply (set_low_preserves_scc_low_valid_v_when_not_child g root v u (dfn snap a) snap).
	                         - intro Hv_eq_u. subst v. contradiction.
	                         - intro Htree_vu.
	                           unfold wf_scc_state in Hwf.
	                           destruct Hwf as [_ [_ [Hvalid _]]].
	                           assert (Hvu_lt: dfn snap v < dfn snap u).
	                           { apply Hvalid. exact Htree_vu. }
	                           assert (Huv_lt: dfn snap u < dfn snap v).
	                           { eapply fa_parent_dfn_lt; eauto. }
	                           lia.
	                         - apply Hchild; auto. }
	                       { rewrite Hv_eq in Hfa_v.
	                         destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq_u].
	                         - exfalso. apply Hfa_neq_v.
	                           simpl in Hfa_v |- *.
	                           rewrite Hfa_v.
	                           rewrite <- Hv_eq.
	                           symmetry. exact Ha_eq_u.
	                         - simpl in Hfa_v.
	                           rewrite <- Hv_eq in Hfa_v.
	                           specialize (Hfa_not a Hndone Hfa_v). contradiction. }
	                   --- split.
	                       { exact Hfa_child. }
	                       { unfold fa_not_done_implies_eq_u in Hfa_not |- *.
	                         intros v Hnot_done Hfa_v.
	                         apply Hfa_not; [| exact Hfa_v].
	                         intro Hdone_v. apply Hnot_done. sets_unfold. left. exact Hdone_v. }
      + unfold stack_dfn_order. simpl. exact Hord.
      + exact Hinj.
    - destruct H1 as [Heq_state Hnot_lt]. subst s.
      destruct Hsnap as [Hiter [Hord [Hinj [Hdg [Hndone [Hvis Hstack_a]]]]]].
      destruct Hiter as (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc &
                         Hchild & Hfa_child & Hfa_not).
      destruct H as [Heq_snap Hdv]. subst s0. subst dv.
      split; [| split; [exact Hord | exact Hinj]].
      unfold low_iteration_inv.
      split; [exact Hwf | split; [exact Huvis | split; [exact Hustack |]]].
      split.
      + unfold done_visited in Hdonevis |- *.
        intros w Hw. sets_unfold in Hw. destruct Hw as [Hdone_w | Hw_eq].
        * apply Hdonevis. exact Hdone_w.
        * subst w. exact Hvis.
      + split.
        * unfold low_frontier in Hfront |- *.
          destruct Hfront as [Hle Hfront]. split; [exact Hle |].
          intros v Hv_done Hv_dg.
          sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
          -- apply Hfront; auto.
          -- subst v. split.
	             ++ intro Hfa_a.
	                destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq_u].
	                ** rewrite Ha_eq_u. lia.
	                ** specialize (Hfa_not a Hndone Hfa_a). contradiction.
	             ++ intro Hstack_a'. lia.
        * split.
          -- unfold low_src in Hsrc |- *.
             destruct Hsrc as [Hsrc | [(v & Hdone_v & Hdg_v & Hfa_v & Hfa_neq_v & Hlow_v) |
                                      (w & Hdone_w & Hdg_w & Hstack_w & Hfa_neq_w & Hlow_w)]].
             ++ left. exact Hsrc.
             ++ right. left. exists v. repeat split; auto. sets_unfold. left. exact Hdone_v.
             ++ right. right. exists w. repeat split; auto. sets_unfold. left. exact Hdone_w.
          -- split.
             ++ unfold children_low_valid in Hchild |- *.
                intros v Hv_done Hv_dg Hfa_v Hfa_neq_v.
                sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
                ** apply Hchild; auto.
	                ** subst v.
	                   destruct (equiv_dec a u) as [Ha_eq_u | Ha_neq_u].
	                   --- exfalso. apply Hfa_neq_v.
	                       rewrite Hfa_v. symmetry. exact Ha_eq_u.
	                   --- specialize (Hfa_not a Hndone Hfa_v). contradiction.
             ++ split.
                ** exact Hfa_child.
                ** unfold fa_not_done_implies_eq_u in Hfa_not |- *.
                   intros v Hnot_done Hfa_v.
                   apply Hfa_not; [| exact Hfa_v].
                   intro Hdone_v. apply Hnot_done. sets_unfold. left. exact Hdone_v.
  Qed.

  Lemma get_low_update_low_tree_child_extends_low_iteration
        (u a: V) (done: V -> Prop):
    Hoare (low_tree_child_after_recursive u a done)
          (lv <- get' (fun s => low s a);; update_low u lv)
          (fun _ s =>
             low_iteration_inv g root u (done ∪ [a]) s /\
             stack_dfn_order s /\
             dfn_injective s).
  Proof.
    apply Hoare_normalize. intros snap Hsnap.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    unfold update_low. unfold_op. intro_state. hoare_auto_s.
    - destruct H as [Heq_snap Hlv]. subst s0. subst lv.
      subst s. unfold RecordSet.set. simpl.
      destruct Hsnap as [Hpending Hvalid_a].
      destruct Hpending as
        (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc & Hchild &
         Hfa_child & Hfa_not & Hord & Hinj & Hdg & Hndone & Hvis &
         Hfa_a & Hfa_neq_a).
      assert (Ha_neq_u: a <> u).
      { intro Ha_eq. subst a. apply Hfa_neq_a. exact Hfa_a. }
      assert (Hlow_a_dfn_a: low snap a <= dfn snap a).
      { apply (scc_low_valid_v_bound_self g root). exact Hvalid_a. }
      assert (Hdfn_u_lt_a: dfn snap u < dfn snap a).
      { pose proof Hwf as [_ [_ [Hdfn_valid _]]].
        eapply fa_parent_dfn_lt; eauto. }
      split; [| split; [unfold stack_dfn_order; simpl; exact Hord | exact Hinj]].
      unfold low_iteration_inv.
      split.
      + unfold wf_scc_state in Hwf |- *.
        destruct Hwf as [Hsiv [Hinv [Hvalid Hfa_vis]]].
        split; [exact Hsiv | split; [exact Hinv | split; [exact Hvalid | exact Hfa_vis]]].
      + split; [exact Huvis | split; [exact Hustack |]].
        split.
        * unfold done_visited in Hdonevis |- *.
          intros w Hw. sets_unfold in Hw. destruct Hw as [Hdone_w | Hw_eq].
          -- apply Hdonevis. exact Hdone_w.
          -- subst w. exact Hvis.
        * split.
          -- unfold low_frontier in Hfront |- *.
             destruct Hfront as [Hle Hfront].
             split.
             ++ simpl. unfold equiv_decb.
                destruct (equiv_dec u u) as [_ | Hc];
                  [lia | exfalso; apply Hc; reflexivity].
             ++ intros v Hv_done Hv_dg.
                sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
                ** specialize (Hfront v Hv_done Hv_dg) as [Hfa_part Hstack_part].
                   split.
                   { intros Hcase.
                       simpl. unfold equiv_decb.
                       destruct (equiv_dec u u) as [_ | Hc].
                       - destruct (equiv_dec v u) as [Hv_eq_u | Hv_neq_u].
                         + lia.
                         + pose proof (Hfa_part Hcase). lia.
                       - exfalso. apply Hc. reflexivity. }
                   { intros Hcase.
                       simpl. unfold equiv_decb.
                       destruct (equiv_dec u u) as [_ | Hc].
                       - pose proof (Hstack_part Hcase). lia.
                       - exfalso. apply Hc. reflexivity. }
                ** subst v. split; intros _.
                   --- simpl. unfold equiv_decb.
                       destruct (equiv_dec u u) as [_ | Hc];
                         [destruct (equiv_dec a u) as [Ha_eq_u | _];
                          [exfalso; apply Ha_neq_u; exact Ha_eq_u | lia]
                         | exfalso; apply Hc; reflexivity].
                   --- simpl. unfold equiv_decb.
                       destruct (equiv_dec u u) as [_ | Hc];
                         [lia | exfalso; apply Hc; reflexivity].
          -- split.
             ++ unfold low_src.
                right. left. exists a.
                split; [sets_unfold; right; reflexivity |].
                split; [exact Hdg |].
                split.
                { simpl. unfold equiv_decb.
                   destruct (equiv_dec a u) as [Ha_eq_u | _].
                   - exfalso. apply Ha_neq_u. exact Ha_eq_u.
                   - exact Hfa_a. }
                ** split.
                   { simpl. unfold equiv_decb.
                       destruct (equiv_dec a u) as [Ha_eq_u | _].
                       - exfalso. apply Ha_neq_u. exact Ha_eq_u.
                       - exact Hfa_neq_a. }
                   { simpl. unfold equiv_decb.
                       destruct (equiv_dec u u) as [_ | Hc];
                         [destruct (equiv_dec a u) as [Ha_eq_u | _];
                          [exfalso; apply Ha_neq_u; exact Ha_eq_u | reflexivity]
                         | exfalso; apply Hc; reflexivity]. }
             ++ split.
                ** unfold children_low_valid in Hchild |- *.
                   intros v Hv_done Hv_dg Hfa_v Hfa_neq_v.
                   sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
                   { apply (set_low_preserves_scc_low_valid_v_when_not_child g root v u (low snap a) snap).
                     - intro Hv_eq_u. destruct Hv_eq_u. apply Hfa_neq_v. exact Hfa_v.
                     - intro Htree_vu.
                         unfold wf_scc_state in Hwf.
                         destruct Hwf as [_ [_ [Hvalid _]]].
                         assert (Hvu_lt: dfn snap v < dfn snap u).
                         { apply Hvalid. exact Htree_vu. }
                         assert (Huv_lt: dfn snap u < dfn snap v).
                         { eapply fa_parent_dfn_lt; eauto. }
                         lia.
                     - apply Hchild; auto. }
                   { subst v.
                     apply (set_low_preserves_scc_low_valid_v_when_not_child g root a u (low snap a) snap).
                     - exact Ha_neq_u.
                     - intro Htree_au.
                         unfold wf_scc_state in Hwf.
                         destruct Hwf as [_ [_ [Hvalid _]]].
                         assert (Hau_lt: dfn snap a < dfn snap u).
                         { apply Hvalid. exact Htree_au. }
                         lia.
                     - exact Hvalid_a. }
                ** split.
                   --- exact Hfa_child.
                   --- exact Hfa_not.
    - destruct H1 as [Heq_state Hnot_lt]. subst s.
      destruct H as [Heq_snap Hlv]. subst s0. subst lv.
      destruct Hsnap as [Hpending Hvalid_a].
      destruct Hpending as
        (Hwf & Huvis & Hustack & Hdonevis & Hfront & Hsrc & Hchild &
         Hfa_child & Hfa_not & Hord & Hinj & Hdg & Hndone & Hvis &
         Hfa_a & Hfa_neq_a).
      assert (Ha_neq_u: a <> u).
      { intro Ha_eq. subst a. apply Hfa_neq_a. exact Hfa_a. }
      assert (Hlow_a_dfn_a: low snap a <= dfn snap a).
      { apply (scc_low_valid_v_bound_self g root). exact Hvalid_a. }
      split; [| split; [exact Hord | exact Hinj]].
      unfold low_iteration_inv.
      split; [exact Hwf | split; [exact Huvis | split; [exact Hustack |]]].
      split.
      + unfold done_visited in Hdonevis |- *.
        intros w Hw. sets_unfold in Hw. destruct Hw as [Hdone_w | Hw_eq].
        * apply Hdonevis. exact Hdone_w.
        * subst w. exact Hvis.
      + split.
        * unfold low_frontier in Hfront |- *.
          destruct Hfront as [Hle Hfront]. split; [exact Hle |].
          intros v Hv_done Hv_dg.
          sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
          { apply Hfront; auto. }
          { subst v. split; intros; lia. }
        * split.
          -- unfold low_src in Hsrc |- *.
             destruct Hsrc as [Hsrc | [(v & Hdone_v & Hdg_v & Hfa_v & Hfa_neq_v & Hlow_v) |
                                      (w & Hdone_w & Hdg_w & Hstack_w & Hfa_neq_w & Hlow_w)]].
             ++ left. exact Hsrc.
             ++ right. left. exists v. repeat split; auto. sets_unfold. left. exact Hdone_v.
             ++ right. right. exists w. repeat split; auto. sets_unfold. left. exact Hdone_w.
          -- split.
             ++ unfold children_low_valid in Hchild |- *.
                intros v Hv_done Hv_dg Hfa_v Hfa_neq_v.
                sets_unfold in Hv_done. destruct Hv_done as [Hv_done | Hv_eq].
                ** apply Hchild; auto.
                ** subst v. exact Hvalid_a.
             ++ split.
                ** exact Hfa_child.
                ** exact Hfa_not.
  Qed.

  Lemma low_continuation_contract_from_tree_child_frame
        (W: V -> program (@SCCSt V) unit)
        (u a: V) (done: V -> Prop) (s0: @SCCSt V):
    Hoare (low_tree_child_after_set_fa u a done)
          (W a)
          (fun _ s => low_tree_child_after_recursive u a done s) ->
    low_continuation_contract W u a done s0.
  Proof.
    intros HW Hdg Hndone.
    unfold low_continuation_contract.
    eapply Hoare_bind with
      (Q := fun _ s => low_tree_child_after_set_fa u a done s).
    - eapply Hoare_conseq_post.
      2: {
        apply Hoare_conj with
          (Q1 := fun _ s =>
             wf_scc_state_pre g root a s /\
             u ∈ visited s /\
             In u (stack s) /\
             done_visited done s /\
             low_frontier g u done s /\
	             low_src g u done s /\
	             children_low_valid g root u done s /\
	             fa_child_of_u g u s /\
	             fa s a = u)
	          (Q2 := fun _ s =>
	             fa_not_done_implies_eq_u u (done ∪ [a]) s /\
	             stack_dfn_order s /\
	             dfn_injective s).
	        - eapply Hoare_conseq_pre.
	          2: { apply (set_fa_establishes_low_iteration_before_new_child g root u a done). }
	          intros st [Heq [Hiter [Hord [Hinj Hnvis]]]].
	          split; [exact Hiter |].
	          split; [exact Hnvis |].
	          split; [exact Hndone | exact Hdg].
	        - apply Hoare_conj.
	          + eapply Hoare_conseq_pre.
	            2: { apply (set_fa_establishes_pending_fa_not_done u a done). }
	            intros st [Heq [Hiter [Hord [Hinj Hnvis]]]].
	            split; [exact Hiter | exact Hndone].
	          + apply Hoare_conj.
	            * eapply Hoare_conseq_pre.
	              2: { apply (set_fa_keep_stack_dfn_order a u). }
	              intros st [Heq [Hiter [Hord [Hinj Hnvis]]]]. exact Hord.
	            * eapply Hoare_conseq_pre.
	              2: { apply (set_fa_keep_dfn_injective a u). }
	              intros st [Heq [Hiter [Hord [Hinj Hnvis]]]]. exact Hinj. }
	      intros r st [Hset [Hfa_not_pending [Hord Hinj]]].
      unfold low_tree_child_after_set_fa.
      destruct Hset as
        (Hwfpre & Huvis & Hustack & Hdonevis & Hfront & Hsrc &
         Hchild & Hfa_child & Hfa_a).
      split; [exact Hwfpre |].
      split; [exact Huvis |].
      split; [exact Hustack |].
      split; [exact Hdonevis |].
      split; [exact Hfront |].
	      split; [exact Hsrc |].
	      split; [exact Hchild |].
	      split; [exact Hfa_child |].
	      split; [exact Hfa_not_pending |].
	      split; [exact Hfa_a |].
	      split; [exact Hord | exact Hinj].
    - simpl. intros _.
      eapply Hoare_bind.
      + exact HW.
      + simpl. intros _.
        eapply Hoare_conseq_pre.
        2: { apply get_low_update_low_tree_child_extends_low_iteration. }
        intros st Hrec.
        unfold low_tree_child_after_recursive in Hrec.
        exact Hrec.
  Qed.

  Definition low_tree_child_frame_contract
             (W: V -> program (@SCCSt V) unit): Prop :=
    forall u a done,
      dg_step g u a ->
      ~ done a ->
      Hoare (low_tree_child_after_set_fa u a done)
            (W a)
            (fun _ s => low_tree_child_after_recursive u a done s).

  Definition low_tree_child_pending_contract
             (W: V -> program (@SCCSt V) unit): Prop :=
    forall u a done,
      dg_step g u a ->
      ~ done a ->
      Hoare (low_tree_child_after_set_fa u a done)
            (W a)
            (fun _ s => low_tree_child_parent_pending u a done s).

  Lemma low_tree_child_after_set_fa_low_pre
        (u a: V) (done: V -> Prop) (s: @SCCSt V):
    low_tree_child_after_set_fa u a done s ->
    low_pre g root a s.
  Proof.
    unfold low_tree_child_after_set_fa, low_pre, wf_scc_state_pre.
    intros (Hwfpre & _).
    exact Hwfpre.
  Qed.

  Lemma low_tree_child_after_set_fa_active_base_parent
        (u a: V) (done: V -> Prop) (s: @SCCSt V):
    low_tree_child_after_set_fa u a done s ->
    active_base ((u, s) :: nil) s.
  Proof.
    unfold low_tree_child_after_set_fa, active_base, active_stack_frames.
    intros (Hwfpre & _Huvis & Hustack & _Hdonevis & _Hfront & _Hsrc &
            _Hchild & _Hfa_child & _Hfa_not & _Hfa_a & Hord & Hinj).
    unfold wf_scc_state_pre in Hwfpre.
    destruct Hwfpre as [Hwf _Hnot_a].
    split.
    - intros cur s0 Hin.
      destruct Hin as [Hin | []].
      inversion Hin. subst cur s0.
      apply Q_active_stack_frame_current.
      exact Hustack.
    - split; [exact Hwf | split; [exact Hord | exact Hinj]].
  Qed.

  Lemma low_tree_child_after_set_fa_parent_below_timer
        (u a: V) (done: V -> Prop) (s: @SCCSt V):
    low_tree_child_after_set_fa u a done s ->
    active_stack_frames_below_timer ((u, s) :: nil) s.
  Proof.
    unfold low_tree_child_after_set_fa, active_stack_frames_below_timer.
    intros (Hwfpre & Huvis & _).
    unfold wf_scc_state_pre, wf_scc_state in Hwfpre.
    destruct Hwfpre as [[_ [Hinv _]] _].
    destruct Hinv as [Htimer_lt _].
    intros cur s0 Hin.
    destruct Hin as [Hin | []].
    inversion Hin. subst cur s0.
    apply Htimer_lt. exact Huvis.
  Qed.

  Lemma tarjan_scc_preserves_parent_active_base_from_after_set_fa
        (u a: V) (done: V -> Prop) (snap: @SCCSt V):
    Hoare (fun s => s = snap /\ low_tree_child_after_set_fa u a done s)
          (tarjan_scc g a)
          (fun _ s => active_base ((u, snap) :: nil) s).
  Proof.
    eapply Hoare_conseq_pre.
    2: { apply (tarjan_scc_preserves_active_base a ((u, snap) :: nil)). }
    intros st [Heq Hset].
    subst st.
    split.
    - apply (low_tree_child_after_set_fa_active_base_parent u a done).
      exact Hset.
    - split.
      + apply (low_tree_child_after_set_fa_low_pre u a done).
        exact Hset.
      + apply (low_tree_child_after_set_fa_parent_below_timer u a done).
        exact Hset.
  Qed.

  Lemma active_base_singleton_parent_fields
        (u: V) (snap s: @SCCSt V):
    active_base ((u, snap) :: nil) s ->
    wf_scc_state g root s /\
    u ∈ visited s /\
    In u (stack s) /\
    stack_dfn_order s /\
    dfn_injective s.
  Proof.
    intros Hbase.
    destruct Hbase as [Hframes [Hwf [Hord Hinj]]].
    pose proof (Hframes u snap (or_introl eq_refl)) as Hactive.
    split; [exact Hwf |].
    split.
    - unfold wf_scc_state in Hwf.
      destruct Hwf as [Hstack_in _].
      apply Hstack_in.
      exact (Q_active_stack_frame_self_stack u snap s Hactive).
    - split; [exact (Q_active_stack_frame_self_stack u snap s Hactive) |].
      split; [exact Hord | exact Hinj].
  Qed.

  Lemma tarjan_scc_preserves_parent_stack_fields_from_after_set_fa
        (u a: V) (done: V -> Prop) (snap: @SCCSt V):
    Hoare (fun s => s = snap /\ low_tree_child_after_set_fa u a done s)
          (tarjan_scc g a)
          (fun _ s =>
             wf_scc_state g root s /\
             u ∈ visited s /\
             In u (stack s) /\
             stack_dfn_order s /\
             dfn_injective s).
  Proof.
    eapply Hoare_conseq
      with
        (P2 := fun s => s = snap /\ low_tree_child_after_set_fa u a done s)
        (Q2 := fun _ s => active_base ((u, snap) :: nil) s).
    - intros st Hpre. exact Hpre.
    - intros _ st Hbase.
      apply (active_base_singleton_parent_fields u snap).
      exact Hbase.
    - apply (tarjan_scc_preserves_parent_active_base_from_after_set_fa u a done snap).
  Qed.

  Lemma tarjan_scc_preserves_done_visited_from_after_set_fa
        (u a: V) (done: V -> Prop) (snap: @SCCSt V):
    Hoare (fun s => s = snap /\ low_tree_child_after_set_fa u a done s)
          (tarjan_scc g a)
          (fun _ s => done_visited done s).
  Proof.
    eapply Hoare_conseq
      with
        (P2 := fun s => done_visited done s)
        (Q2 := fun _ s => forall v, done v -> v ∈ visited s).
    - intros st [Heq Hset].
      subst st.
      unfold low_tree_child_after_set_fa in Hset.
      destruct Hset as (_ & _ & _ & Hdonevis & _).
      exact Hdonevis.
    - intros _ st Hdonevis.
      unfold done_visited.
      exact Hdonevis.
    - apply tarjan_scc_keep_visited_forall. exact OriginalGraph_gvalid0.
  Qed.

  Lemma tarjan_scc_preserves_child_parent_fa_from_after_set_fa
        (u a: V) (done: V -> Prop) (snap: @SCCSt V):
    Hoare (fun s => s = snap /\ low_tree_child_after_set_fa u a done s)
          (tarjan_scc g a)
          (fun _ s => fa s a = u /\ fa s a <> a).
  Proof.
    unfold Hoare.
    intros s1 r s2 [Heq Hset] Hrun.
    subst s1.
    unfold low_tree_child_after_set_fa in Hset.
    destruct Hset as
      (Hwfpre & Huvis & _Hustack & _Hdonevis & _Hfront & _Hsrc &
       _Hchild & _Hfa_child & _Hfa_not & Hfa_a & _Hord & _Hinj).
    unfold wf_scc_state_pre in Hwfpre.
    destruct Hwfpre as [_Hwf Hnot_a_vis].
    assert (Ha_neq_u: a <> u).
    { intro Ha_eq. subst a. apply Hnot_a_vis. exact Huvis. }
    pose proof (tarjan_scc_keep_root_fa a u) as Hkeep.
    unfold Hoare in Hkeep.
    specialize (Hkeep snap r s2 Hfa_a Hrun).
    split; [exact Hkeep |].
    intro Hloop.
    apply Ha_neq_u.
    rewrite Hkeep in Hloop.
    symmetry. exact Hloop.
  Qed.

  Definition low_tree_child_parent_low_fields
             (u a: V) (done: V -> Prop) (s: @SCCSt V): Prop :=
    low_frontier g u done s /\
    low_src g u done s /\
    children_low_valid g root u done s /\
    fa_child_of_u g u s /\
    fa_not_done_implies_eq_u u (done ∪ [a]) s.

  Lemma low_tree_child_parent_pending_from_fields
        (u a: V) (done: V -> Prop) (s: @SCCSt V):
    wf_scc_state g root s ->
    u ∈ visited s ->
    In u (stack s) ->
    done_visited done s ->
    low_tree_child_parent_low_fields u a done s ->
    stack_dfn_order s ->
    dfn_injective s ->
    dg_step g u a ->
    ~ done a ->
    a ∈ visited s ->
    fa s a = u ->
    fa s a <> a ->
    low_tree_child_parent_pending u a done s.
  Proof.
    intros Hwf Huvis Hustack Hdonevis Hfields Hord Hinj
           Hdg Hndone Hvis_a Hfa_a Hfa_neq_a.
    destruct Hfields as [Hfront [Hsrc [Hchild [Hfa_child Hfa_not]]]].
    unfold low_tree_child_parent_pending.
    split; [exact Hwf |].
    split; [exact Huvis |].
    split; [exact Hustack |].
    split; [exact Hdonevis |].
    split; [exact Hfront |].
    split; [exact Hsrc |].
    split; [exact Hchild |].
    split; [exact Hfa_child |].
    split; [exact Hfa_not |].
    split; [exact Hord |].
    split; [exact Hinj |].
    split; [exact Hdg |].
    split; [exact Hndone |].
    split; [exact Hvis_a |].
    split; [exact Hfa_a | exact Hfa_neq_a].
  Qed.

  Definition no_new_parent_to
             (parent root_child: V) (s0 s: @SCCSt V): Prop :=
    forall v,
      fa s v = parent ->
      v <> parent ->
      v <> root_child ->
      v ∈ visited s0.

  Lemma low_tree_child_frame_contract_continuation
        (W: V -> program (@SCCSt V) unit)
        (u a: V) (done: V -> Prop) (s0: @SCCSt V):
    low_tree_child_frame_contract W ->
    dg_step g u a ->
    ~ done a ->
    low_continuation_contract W u a done s0.
  Proof.
    intros Hframe Hdg Hndone.
    apply low_continuation_contract_from_tree_child_frame.
    apply Hframe; auto.
  Qed.

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
  Proof.
    intros HW Hdg Hndone.
    unfold process_edge, if_else, If.
    intro_state.
    apply Hoare_choice.
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with
        (P2 := fun s =>
                 s = s0 /\
                 low_iteration_inv g root u done s /\
                 stack_dfn_order s /\
                 dfn_injective s /\
                 ~ a ∈ visited s).
      { intros st [Hnot_vis Heq_st]. subst st.
        destruct H as [Heq [Hiter [Hord [Hinj [_ _]]]]].
        split; [exact Heq |].
        split; [exact Hiter |].
        split; [exact Hord |].
        split; [exact Hinj | exact Hnot_vis]. }
      apply HW; auto.
    - apply Hoare_assume_bind. simpl.
      apply Hoare_conseq_pre with
        (P2 := fun s =>
                 low_iteration_inv g root u done s /\
                 stack_dfn_order s /\
                 dfn_injective s /\
                 dg_step g u a /\
                 ~ done a /\
                 a ∈ visited s).
      { intros st [Hvis Heq_st]. subst st.
        destruct (classic (a ∈ visited s1)) as [Hvis' | Hnot_vis].
        2: { exfalso. apply Hvis. exact Hnot_vis. }
        destruct H as [_ [Hiter [Hord [Hinj [_ _]]]]].
        split; [exact Hiter |].
        split; [exact Hord |].
        split; [exact Hinj |].
        split; [exact Hdg |].
        split; [exact Hndone | exact Hvis']. }
      intro_state.
      apply Hoare_choice.
      + apply Hoare_assume_bind. simpl.
        apply Hoare_conseq_pre with
          (P2 := fun s =>
                   low_iteration_inv g root u done s /\
                   stack_dfn_order s /\
                   dfn_injective s /\
                   dg_step g u a /\
                   ~ done a /\
                   a ∈ visited s /\
                   In a (stack s)).
	        { intros st [Hstack Heq_st]. subst st.
	          destruct H1 as [Hiter [Hord [Hinj [Hdg' [Hndone' Hvis]]]]].
          split; [exact Hiter |].
          split; [exact Hord |].
          split; [exact Hinj |].
          split; [exact Hdg' |].
          split; [exact Hndone' |].
          split; [exact Hvis | exact Hstack]. }
        apply get_dfn_update_low_current_extends_low_iteration_stack.
      + eapply Hoare_conseq_pre.
        2: { apply low_iteration_extend_done_assume_nonstack. }
        intros st Heq_st. subst st. exact H1.
  Qed.

  Lemma process_edge_preserves_low_iteration_from_tree_child_frame
        (u a: V) (done: V -> Prop) (s0: @SCCSt V)
        (W: V -> program (@SCCSt V) unit):
    low_tree_child_frame_contract W ->
    dg_step g u a ->
    ~ done a ->
    Hoare (fun s => s = s0 /\ low_iteration_inv g root u done s /\
                     stack_dfn_order s /\ dfn_injective s /\
                     dg_step g u a /\ ~ done a)
          (process_edge u W a)
          (fun _ s => low_iteration_inv g root u (done ∪ [a]) s /\
                      stack_dfn_order s /\ dfn_injective s).
  Proof.
    intros Hframe Hdg Hndone.
    apply process_edge_preserves_low_iteration; auto.
    apply low_tree_child_frame_contract_continuation; auto.
  Qed.

  Lemma forset_preserves_low_iteration
        (u: V) (W: V -> program (@SCCSt V) unit):
    (forall a done s0,
       dg_step g u a ->
       ~ done a ->
       low_continuation_contract W u a done s0) ->
    Hoare (fun s => low_iteration_entry g root u s)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => low_iteration_done g root u s).
  Proof.
    intros HW.
    unfold low_iteration_entry, low_iteration_done.
    eapply Hoare_forset
      with (P := fun done s =>
                  low_iteration_inv g root u done s /\
                  stack_dfn_order s /\
                  dfn_injective s).
    - intros done1 done2 Hequiv s1 s2 Heq_s.
      subst s2.
      pose proof (low_iteration_inv_proper g root u) as Hproper.
      specialize (Hproper done1 done2 Hequiv s1 s1 eq_refl).
      destruct Hproper as [H12 H21].
      split; intros [Hiter [Hord Hinj]].
      + split; [apply H12; exact Hiter | split; [exact Hord | exact Hinj]].
      + split; [apply H21; exact Hiter | split; [exact Hord | exact Hinj]].
    - intros done a Hdone_sub Hdg Hnot_done.
      apply Hoare_normalize. intros s0 [Hiter [Hord Hinj]].
      eapply Hoare_conseq_pre.
      2: { apply process_edge_preserves_low_iteration; auto. }
      intros st Heq_st. subst st.
      split; [reflexivity |].
      split; [exact Hiter |].
      split; [exact Hord |].
      split; [exact Hinj |].
      split; [exact Hdg | exact Hnot_done].
  Qed.

  Lemma forset_preserves_low_iteration_from_tree_child_frame
        (u: V) (W: V -> program (@SCCSt V) unit):
    low_tree_child_frame_contract W ->
    Hoare (fun s => low_iteration_entry g root u s)
          (forset (fun v => dg_step g u v) (process_edge u W))
          (fun _ s => low_iteration_done g root u s).
  Proof.
    intros Hframe.
    apply forset_preserves_low_iteration.
    intros a done s0 Hdg Hndone.
    apply low_tree_child_frame_contract_continuation; auto.
  Qed.

  Lemma tarjan_scc_f_keep_low_valid_from_tree_child_frame
        (W: V -> program (@SCCSt V) unit) (u: V):
    low_tree_child_frame_contract W ->
    Hoare (fun s => low_pre g root u s /\
                    stack_dfn_order s /\
                    dfn_injective s)
          (tarjan_scc_f g W u)
          (fun _ s => low_valid_post g root u s /\
                      u ∈ visited s /\
                      stack_dfn_order s /\
                      dfn_injective s).
  Proof.
    intros Hframe.
    unfold tarjan_scc_f.
    eapply Hoare_bind.
    - apply preloop_establishes_low_iteration_entry.
    - simpl. intros _.
      eapply Hoare_bind.
      + apply forset_preserves_low_iteration_from_tree_child_frame.
        exact Hframe.
      + simpl. intros _.
        eapply Hoare_conseq_pre.
        2: { apply if_pop_preserves_low_valid_post. }
        intros st Hdone.
        split; [exact Hdone |].
        apply low_frontier_and_src_imply_low_valid.
        exact Hdone.
  Qed.

  Lemma tarjan_scc_f_tree_child_frame_from_parent_pending
        (W: V -> program (@SCCSt V) unit)
        (u a: V) (done: V -> Prop):
    low_tree_child_frame_contract W ->
    low_tree_child_pending_contract (tarjan_scc_f g W) ->
    dg_step g u a ->
    ~ done a ->
    Hoare (low_tree_child_after_set_fa u a done)
          (tarjan_scc_f g W a)
          (fun _ s => low_tree_child_after_recursive u a done s).
  Proof.
    intros Hframe Hparent Hdg Hndone.
    eapply Hoare_conseq_post.
    2: {
      apply Hoare_conj with
        (Q1 := fun _ s => low_tree_child_parent_pending u a done s)
        (Q2 := fun _ s => scc_low_valid_v g root s a).
      - apply Hparent; auto.
      - eapply Hoare_conseq
          with
            (P2 := fun s =>
                     low_pre g root a s /\
                     stack_dfn_order s /\
                     dfn_injective s)
            (Q2 := fun _ s =>
                     low_valid_post g root a s /\
                     a ∈ visited s /\
                     stack_dfn_order s /\
                     dfn_injective s).
        + intros st Hset.
          unfold low_tree_child_after_set_fa in Hset.
          destruct Hset as
            (Hwfpre & _Huvis & _Hustack & _Hdonevis & _Hfront & _Hsrc &
             _Hchild & _Hfa_child & _Hfa_not & _Hfa_a & Hord & Hinj).
          split; [exact Hwfpre | split; [exact Hord | exact Hinj]].
        + intros _ st Hpost.
          destruct Hpost as [[_Hwf Hvalid] [_Hvis [_Hord _Hinj]]].
          exact Hvalid.
        + apply tarjan_scc_f_keep_low_valid_from_tree_child_frame.
          exact Hframe. }
    intros _ st [Hpending Hvalid].
    unfold low_tree_child_after_recursive.
    split; [exact Hpending | exact Hvalid].
  Qed.

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
