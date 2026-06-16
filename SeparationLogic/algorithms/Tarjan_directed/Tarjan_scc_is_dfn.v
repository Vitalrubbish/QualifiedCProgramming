Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.EquivDec.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From Algorithms.Tarjan_directed Require Import SCC_basic Tarjan_scc Tarjan_scc_basics.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section IS_DFN.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}
          (root: V)
          (g_vvalid_root: original_vvalid g root).

(* ================================================================ *)
(* 1. dfn_inv — Basic dfn Invariant                                 *)
(* ================================================================ *)

Definition dfn_inv (s: @SCCSt V): Prop :=
  (forall v, v ∈ visited s -> dfn s v < timer s) /\
  (forall v, dfn s v = 0 <-> ~ v ∈ visited s) /\
  0 < timer s.

Lemma dfn_inv_init: dfn_inv initSt.
Proof.
  unfold dfn_inv, initSt. simpl. split; [| split].
  - intros v H. sets_unfold in H. destruct H.
  - intros v. split; intros; auto.
  - auto.
Qed.

Lemma set_fa_keep_dfn_inv (v p: V):
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (set_fa v p)
        (fun _ s => dfn_inv s).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. auto.
Qed.

Lemma update_low_keep_dfn_inv (u: V) (n: nat):
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (update_low u n)
        (fun _ s => dfn_inv s).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  { subst s. simpl. auto. }
  { destruct H1. subst s. auto. }
Qed.

Lemma pop_scc_keep_dfn_inv (u: V):
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (pop_scc u)
        (fun _ s => dfn_inv s).
Proof.
  unfold pop_scc. intro_state. hoare_auto_s.
  subst s. unfold pop_scc_state.
  destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
  simpl. auto.
Qed.

Lemma preloop_keep_dfn_inv (u: V):
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (preloop u)
        (fun _ s => dfn_inv s).
Proof.
  unfold dfn_inv.
  apply Hoare_conj with
    (Q1 := fun (_: unit) s => forall v, v ∈ visited s -> dfn s v < timer s)
    (Q2 := fun (_: unit) s => (forall v, dfn s v = 0 <-> ~ v ∈ visited s) /\ 0 < timer s).
  - intro_state. destruct H as [Hlt [_ _]].
    unfold preloop. unfold_op. hoare_auto_s.
    subst s. simpl.
    simpl in H1. sets_unfold in H1.
    destruct H1 as [Hvis0 | Heq].
    + apply Hlt in Hvis0.
      unfold equiv_decb. destruct (equiv_dec v u) as [Heq' | Hneq'].
      * lia.
      * lia.
    + subst v. unfold equiv_decb. destruct (equiv_dec u u) as [_ | c]; [lia | exfalso; apply c; reflexivity].
  - apply Hoare_conj with
      (Q1 := fun (_: unit) s => forall v, dfn s v = 0 <-> ~ v ∈ visited s)
      (Q2 := fun (_: unit) s => 0 < timer s).
    + intro_state. destruct H as [_ [Hiff Hpos]].
      unfold preloop. unfold_op. hoare_auto_s.
      subst s. simpl.
      unfold equiv_decb. destruct (equiv_dec v u) as [Heq | Hneq].
      * rewrite Heq. split.
        { intros Hdfn0. clear -Hdfn0 Hpos. lia. }
        { intros Hnvis. exfalso. apply Hnvis. sets_unfold. right; reflexivity. }
      * split.
        { intros Hdfn0. destruct (Hiff v) as [Hfw _]. apply Hfw in Hdfn0.
          sets_unfold. intros [Hvis0 | Heq'].
          { apply Hdfn0. exact Hvis0. }
          { exfalso. apply Hneq. symmetry. exact Heq'. } }
        { intros Hnvis. sets_unfold in Hnvis.
          assert (Hnvis0: ~ v ∈ visited s0). { intros Hc. apply Hnvis. left. exact Hc. }
          assert (Hneq': v <> u). { intros Hc. symmetry in Hc. apply Hnvis. right. exact Hc. }
          destruct (Hiff v) as [_ Hbw]. apply Hbw. exact Hnvis0. }
    + intro_state. destruct H as [_ [_ Hpos]].
      unfold preloop. unfold_op. hoare_auto_s.
      subst s. simpl. lia.
Qed.

Lemma get_low_update_low_keep_dfn_inv (u v: V):
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (lv <- get' (fun s => low s v);; update_low u lv)
        (fun _ s => dfn_inv s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
  apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
  { intros s1 Hs1. destruct Hs1. subst s1. simpl. auto. }
  apply (update_low_keep_dfn_inv u lv).
Qed.

Lemma get_dfn_update_low_keep_dfn_inv (u v: V):
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (dv <- get' (fun s => dfn s v);; update_low u dv)
        (fun _ s => dfn_inv s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
  apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
  { intros s1 Hs1. destruct Hs1. subst s1. simpl. auto. }
  apply (update_low_keep_dfn_inv u dv).
Qed.

Lemma process_edge_keep_dfn_inv (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_inv s) (W x) (fun _ s => dfn_inv s)) ->
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (process_edge u W v)
        (fun _ s => dfn_inv s).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state.
  apply Hoare_choice.
  - apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
    { intros s1 [Hnv Hs1]. subst s1. exact H. }
    hoare_bind (set_fa_keep_dfn_inv v u). simpl. clear a.
    eapply Hoare_bind. { apply HW. } simpl. intros _.
    apply get_low_update_low_keep_dfn_inv.
  - intro_state. hoare_auto_s.
    + apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
      { intros s1 Hs1. subst s1. exact H. }
      apply (update_low_keep_dfn_inv u (dfn s0 v)).
    + destruct H3 as [Heq Hnn]. subst s. subst s1. exact H.
Qed.

Lemma forset_process_edge_keep_dfn_inv (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_inv s) (W x) (fun _ s => dfn_inv s)) ->
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => dfn_inv s).
Proof.
  intros HW.
  unfold forset. hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
  eapply Hoare_bind with (R := fun (_: unit) s => dfn_inv s).
  { apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
    { intros s1 Hs1. subst s1. exact H. }
    apply (process_edge_keep_dfn_inv u a W). intros x. apply HW. }
  simpl. intros _. apply IH0.
Qed.

Theorem tarjan_scc_keep_dfn_inv (u: V):
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => dfn_inv s).
Proof.
  unfold tarjan_scc. hoare_fix_nolv_auto V.
  clear u. intros W IH u.
  unfold tarjan_scc_f.
  eapply Hoare_bind; [apply preloop_keep_dfn_inv | simpl; intros _].
  eapply Hoare_bind with (R := fun (_: unit) s => dfn_inv s).
  - apply forset_process_edge_keep_dfn_inv. intros x. apply IH.
  - simpl. intros _. intro_state. hoare_auto_s.
    + apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
      { intros s1 Hs1. subst s1. exact H. }
      apply pop_scc_keep_dfn_inv.
    + destruct H1. subst s. exact H.
Qed.

Theorem tarjan_scc_all_keep_dfn_inv:
  Hoare (fun s: @SCCSt V => dfn_inv s)
        (tarjan_scc_all g)
        (fun _ s => dfn_inv s).
Proof.
  unfold tarjan_scc_all.
  apply Hoare_forset with
    (P := fun (_: V -> Prop) (s: @SCCSt V) => dfn_inv s).
  - intros done1 done2 Hdone s1 s2 Heq. subst s2. reflexivity.
  - intros done a Hdone_sub Hvalid_a Hnot_done.
    unfold_op. intro_state. hoare_auto_s.
    + eapply Hoare_conseq_pre.
      2: apply (tarjan_scc_keep_dfn_inv a).
      intros s' Heq. subst s'. exact H.
    + destruct H1 as [Heq Hnn]. subst s. exact H.
Qed.

(* ================================================================ *)
(* 2. dfn_valid — Tree Edge dfn Monotonicity                        *)
(* ================================================================ *)

Definition dfn_valid (s: @SCCSt V) (root: V): Prop :=
  forall x y, dg_step (state_to_dfs_tree (V:=V) (E:=E) g s root) x y -> dfn s x < dfn s y.

(** [fa_visited s]: for every non-root vertex in the DFS tree
    ([fa v ≠ v]), its parent [fa v] is in the visited set. *)
Definition fa_visited (s: @SCCSt V): Prop :=
  forall v, fa s v <> v -> fa s v ∈ visited s.

Definition dfn_pre (u: V) (s: @SCCSt V) (root: V): Prop :=
  ~ u ∈ visited s /\ dfn_valid s root /\ dfn_inv s.

Definition dfn_post (s: @SCCSt V) (root: V): Prop :=
  dfn_valid s root /\ dfn_inv s.

Lemma fa_visited_init: fa_visited initSt.
Proof.
  unfold fa_visited, initSt. simpl. intros v Hneq.
  exfalso; apply Hneq; reflexivity.
Qed.

(** [set_fa_establishes_fa_visited]: setting [fa v := p] when p is
    visited establishes [fa_visited] (provided it held before). *)
Lemma set_fa_keep_fa_visited (v p: V):
  Hoare (fun s: @SCCSt V => p ∈ visited s /\ fa_visited s)
        (set_fa v p)
        (fun _ s => fa_visited s).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. unfold fa_visited.
  destruct H as [Hpvis Hfa].
  intros v0 Hneq. simpl. simpl in Hneq.
  unfold equiv_decb.
  destruct (equiv_dec v0 v) as [Heq | Hneq'].
  - exact Hpvis.
  - unfold equiv_decb in Hneq.
    destruct (equiv_dec v0 v) as [Heq2 | Hneq2].
    + exfalso. apply Hneq'. exact Heq2.
    + simpl in Hneq. apply Hfa. exact Hneq.
Qed.

Lemma preloop_keep_fa_visited (u: V):
  Hoare (fun s: @SCCSt V => fa_visited s)
        (preloop u)
        (fun _ s => fa_visited s).
Proof.
  unfold preloop, fa_visited. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl.
  simpl in H2. apply H in H2. sets_unfold. left. exact H2.
Qed.

Lemma update_low_keep_fa_visited (u: V) (n: nat):
  Hoare (fun s: @SCCSt V => fa_visited s)
        (update_low u n)
        (fun _ s => fa_visited s).
Proof.
  unfold update_low. intro_state. hoare_auto_s.
  - unfold set_low. intro_state. hoare_auto_s.
    subst s. simpl. unfold fa_visited.
    subst s1. simpl. exact H.
  - destruct H1. subst s. exact H.
Qed.

Lemma pop_scc_keep_fa_visited (u: V):
  Hoare (fun s: @SCCSt V => fa_visited s)
        (pop_scc u)
        (fun _ s => fa_visited s).
Proof.
  unfold pop_scc. intro_state. hoare_auto_s.
  subst s. unfold pop_scc_state.
  destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
  simpl. unfold fa_visited. auto.
Qed.

Lemma get_low_update_low_keep_fa_visited (u v: V):
  Hoare (fun s: @SCCSt V => fa_visited s)
        (lv <- get' (fun s => low s v);; update_low u lv)
        (fun _ s => fa_visited s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
  apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
  { intros s1 Hs1. destruct Hs1. subst s1. exact H. }
  apply (update_low_keep_fa_visited u lv).
Qed.

Lemma get_dfn_update_low_keep_fa_visited (u v: V):
  Hoare (fun s: @SCCSt V => fa_visited s)
        (dv <- get' (fun s => dfn s v);; update_low u dv)
        (fun _ s => fa_visited s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
  apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
  { intros s1 Hs1. destruct Hs1. subst s1. exact H. }
  apply (update_low_keep_fa_visited u dv).
Qed.

Lemma process_edge_keep_fa_visited (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => fa_visited s) (W x) (fun _ s => fa_visited s)) ->
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s)
        (process_edge u W v)
        (fun _ s => fa_visited s).
Proof.
  intros HW.
  unfold process_edge, if_else, If.
  intro_state. destruct H as [Huvis Hfa].
  apply Hoare_choice.
  - (* Tree-edge: ~ v ∈ visited *)
    apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s /\ fa_visited s).
    { intros s' [Hnv Hs']. subst s'. split; auto. }
    hoare_bind (set_fa_keep_fa_visited v u). simpl. clear a.
    eapply Hoare_bind. { apply HW. } simpl. intros _.
    apply get_low_update_low_keep_fa_visited.
  - (* Non-tree-edge: v ∈ visited *)
    intro_state. hoare_auto_s.
    + (* v ∈ stack: update low with dfn v *)
      eapply Hoare_conseq.
      * { intros s1 Heq. subst s1. exact Hfa. }
      * { intros b s1 Hfa'. exact Hfa'. }
      * apply (update_low_keep_fa_visited u (dfn s0 v)).
    + (* v ∉ stack: skip *)
      destruct H2 as [Heq _]. subst s. subst s1. exact Hfa.
Qed.

(** Combined version that preserves both [u ∈ visited] and [fa_visited]
    through [process_edge].  The [u ∈ visited] part is needed so that the
    forset induction can thread it through successive neighbour visits. *)
(** Rich version of [get_low_update_low_] that preserves both
    [u ∈ visited] and [fa_visited]. *)
Lemma get_low_update_low_keep_fa_visited_rich (u v: V):
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s)
        (lv <- get' (fun s => low s v);; update_low u lv)
        (fun _ s => u ∈ visited s /\ fa_visited s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
  apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s /\ fa_visited s).
  { intros s1 Hs1. destruct Hs1. subst s1. exact H. }
  apply Hoare_conj.
  - apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
    { intros s1 [Huvis1 Hfa1]. exact Huvis1. }
    apply (update_low_keep_visited u u lv).
  - apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
    { intros s1 [Huvis1 Hfa1]. exact Hfa1. }
    apply (update_low_keep_fa_visited u lv).
Qed.

(** Rich version of [process_edge_keep_fa_visited]: the HW hypothesis
    matches the shape of the fixpoint IH exactly — both [u ∈ visited]
    and [fa_visited] are preserved simultaneously. *)
Lemma process_edge_keep_fa_visited_rich (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s)
                  (W x)
                  (fun _ s => u ∈ visited s /\ fa_visited s)) ->
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s)
        (process_edge u W v)
        (fun _ s => u ∈ visited s /\ fa_visited s).
Proof.
  intros HW.
  unfold process_edge, if_else, If.
  intro_state. destruct H as [Huvis Hfa].
  apply Hoare_choice.
  - (* Tree-edge: ~ v ∈ visited *)
    apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s /\ fa_visited s).
    { intros s' [Hnv Hs']. subst s'. split; auto. }
    (* Compose set_fa v u ;; W v ;; get' low v ;; update_low u lv step by step *)
    assert (H_setfa : Hoare (fun s => u ∈ visited s /\ fa_visited s)
                            (set_fa v u)
                            (fun _ s => u ∈ visited s /\ fa_visited s)).
    { apply Hoare_conj.
      - eapply Hoare_conseq_pre. 2: apply (set_fa_keep_visited v u u).
        intros s [Huvis1 Hfa1]. exact Huvis1.
      - eapply Hoare_conseq_pre. 2: apply (set_fa_keep_fa_visited v u).
        intros s [Huvis1 Hfa1]. split; auto. }
    hoare_bind H_setfa. simpl. clear a.
    eapply Hoare_bind. { apply HW. } simpl. intros _.
    apply get_low_update_low_keep_fa_visited_rich.
  - (* Non-tree-edge: v ∈ visited *)
    intro_state. hoare_auto_s.
    + (* v ∈ stack: update_low u (dfn s0 v) *)
      apply (Hoare_conseq
        (fun s => s = s0) (fun s => u ∈ visited s /\ fa_visited s)
        (update_low u (dfn s0 v))
        (fun _ s => u ∈ visited s /\ fa_visited s)
        (fun _ s => u ∈ visited s /\ fa_visited s)).
      * intros s Heq. subst s. split; auto.
      * intros b s1 H. exact H.
      * apply Hoare_conj.
        { eapply Hoare_conseq_pre. 2: apply (update_low_keep_visited u u (dfn s0 v)).
          intros s1 [Huvis1 Hfa1]. exact Huvis1. }
        { eapply Hoare_conseq_pre. 2: apply (update_low_keep_fa_visited u (dfn s0 v)).
          intros s1 [Huvis1 Hfa1]. exact Hfa1. }
    + (* v ∉ stack: skip *)
      destruct H2 as [Heq _]. subst s. subst s1. split; auto.
Qed.

(** Combined version: preserves both [tracked \in visited /\ fa_visited]
    and [center \in visited] through [process_edge].  The callback [W] must
    preserve the full combined invariant [(tracked \in visited /\ fa_visited) /\ center \in visited].
    This is needed when the forset center differs from the tracked vertex. *)
Lemma process_edge_keep_combined (tracked center v: V) (W: V -> program (@SCCSt V) unit):
  (forall a, Hoare (fun s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)
                   (W a)
                   (fun _ s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)) ->
  Hoare (fun s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)
        (process_edge center W v)
        (fun _ s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s).
Proof.
  intros HW.
  unfold process_edge, if_else, If.
  intro_state. destruct H as [[Htvis Hfa] Hcvis].
  apply Hoare_choice.
  - (* Tree-edge: ~ v \in visited *)
    apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with
      (P2 := fun s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s).
    { intros s' [Hnv Hs']. subst s'. repeat split; auto. }
    (* set_fa v center *)
    assert (H_setfa : Hoare (fun s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)
                            (set_fa v center)
                            (fun _ s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)).
    { apply Hoare_conj.
      { apply Hoare_conj.
        { apply Hoare_conseq_pre with (P2 := fun s => tracked ∈ visited s).
          { intros s [[Htvis1 Hfa1] Hcvis1]. exact Htvis1. }
          apply (set_fa_keep_visited v tracked center). }
        { apply Hoare_conseq_pre with (P2 := fun s => center ∈ visited s /\ fa_visited s).
          { intros s [[Htvis1 Hfa1] Hcvis1]. split; auto. }
          apply (set_fa_keep_fa_visited v center). } }
      { apply Hoare_conseq_pre with (P2 := fun s => center ∈ visited s).
        { intros s [[Htvis1 Hfa1] Hcvis1]. exact Hcvis1. }
        apply (set_fa_keep_visited v center center). } }
    hoare_bind H_setfa. simpl. clear a.
    (* W v: recursive call *)
    eapply Hoare_bind. { apply HW. } simpl. intros _.
    (* get_low_update_low center v *)
    intro_state. destruct H as [[Htvis' Hfa'] Hcvis'].
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    apply Hoare_conj.
    { apply Hoare_conj.
      { apply Hoare_conseq_pre with (P2 := fun s => tracked ∈ visited s).
        { intros sx Hs1. destruct Hs1 as [Hseq _]. subst sx. exact Htvis'. }
        apply (update_low_keep_visited center tracked lv). }
      { apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
        { intros sx Hs1. destruct Hs1 as [Hseq _]. subst sx. exact Hfa'. }
        apply (update_low_keep_fa_visited center lv). } }
    { apply Hoare_conseq_pre with (P2 := fun s => center ∈ visited s).
      { intros sx Hs1. destruct Hs1 as [Hseq _]. subst sx. exact Hcvis'. }
      apply (update_low_keep_visited center center lv). }
  - (* Non-tree-edge: v \in visited *)
    intro_state. hoare_auto_s.
    + (* v \in stack: update_low center (dfn s0 v) *)
      apply (Hoare_conseq
        (fun s => s = s0) (fun s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)
        (update_low center (dfn s0 v))
        (fun _ s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)
        (fun _ s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)).
      { intros s Heq. subst s. repeat split; auto. }
      { intros b s1 H. exact H. }
      { apply Hoare_conj.
        { apply Hoare_conj.
          { apply Hoare_conseq_pre with (P2 := fun s => tracked ∈ visited s).
            { intros s1 [[Htvis1 Hfav1] Hcvis1]. exact Htvis1. }
            apply (update_low_keep_visited center tracked (dfn s0 v)). }
          { apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
            { intros s1 [[Htvis1 Hfav1] Hcvis1]. exact Hfav1. }
            apply (update_low_keep_fa_visited center (dfn s0 v)). } }
        { apply Hoare_conseq_pre with (P2 := fun s => center ∈ visited s).
          { intros s1 [[Htvis1 Hfav1] Hcvis1]. exact Hcvis1. }
          apply (update_low_keep_visited center center (dfn s0 v)). } }
    + (* v 
otin stack: skip *)
      destruct H2 as [Heq _]. subst s. subst s1. repeat split; auto.
Qed.

Lemma forset_process_edge_keep_combined (tracked center: V) (W: V -> program (@SCCSt V) unit):
  (forall a, Hoare (fun s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)
                   (W a)
                   (fun _ s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)) ->
  Hoare (fun s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s)
        (forset (fun w => dg_step g center w) (process_edge center W))
        (fun _ s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s).
Proof.
  intros HW.
  unfold forset. hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
  eapply Hoare_bind with
    (R := fun (_: unit) s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s).
  { apply Hoare_conseq_pre with
      (P2 := fun s => (tracked ∈ visited s /\ fa_visited s) /\ center ∈ visited s).
    { intros s1 Hs1. subst s1. exact H. }
    apply (process_edge_keep_combined tracked center a W).
    intros b. apply HW. }
  simpl. intros _. apply IH0.
Qed.

(** Rich version for the forset body: each [process_edge] preserves
    both [u ∈ visited] and [fa_visited].  The forset fixpoint invariant
    is [u ∈ visited s /\ fa_visited s]. *)
Lemma forset_process_edge_keep_fa_visited_rich (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s)
                  (W x)
                  (fun _ s => u ∈ visited s /\ fa_visited s)) ->
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => u ∈ visited s /\ fa_visited s).
Proof.
  intros HW.
  unfold forset. hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
  eapply Hoare_bind with (R := fun (_: unit) s => u ∈ visited s /\ fa_visited s).
  { apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s /\ fa_visited s).
    { intros s1 Hs1. subst s1. exact H. }
    apply (process_edge_keep_fa_visited_rich u a W). intros x. apply HW. }
  simpl. intros _. apply IH0.
Qed.

(** Core lemma: [tarjan_scc u] preserves both [u ∈ visited] and
    [fa_visited].  Proved by [Hoare_fix_logicv_conj], folding in the
    already-established [tarjan_scc_keep_visited] as an auxiliary
    invariant.  This is necessary because the inner [forset] iterates
    over neighbours of the current vertex [x], so its invariant talks
    about [x ∈ visited], whereas the outer fixed-point IH talks about
    the caller [u]; the auxiliary visited-preservation hypothesis
    supplies the missing [x ∈ visited] thread. *)
Lemma tarjan_scc_keep_fa_visited_rich (u: V):
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => u ∈ visited s /\ fa_visited s).
Proof.
  unfold tarjan_scc.
  apply (Hoare_fix_logicv_conj (tarjan_scc_f g)
           (fun (x: V) (_: unit) (s: SCCSt) => u ∈ visited s /\ fa_visited s)
           (fun (x: V) (_: unit) (_: unit) (s: SCCSt) => u ∈ visited s /\ fa_visited s)
           u tt
           (fun (x: V) (d: V) (s: SCCSt) => d ∈ visited s)
           (fun (x: V) (d: V) (_: unit) (s: SCCSt) => d ∈ visited s)).
  - (* Auxiliary property: [tarjan_scc] preserves arbitrary visitedness. *)
    intros x d. exact (tarjan_scc_keep_visited g x d).
  - (* Main induction step. *)
    intros W IHvis IHfa x.
    unfold tarjan_scc_f.
    intros _.
    apply (Hoare_bind (fun s => u ∈ visited s /\ fa_visited s)
                      (preloop x)
                      (fun (_: unit) s => (u ∈ visited s /\ fa_visited s) /\ x ∈ visited s)
                      (fun (_: unit) => forset (fun w => dg_step g x w) (process_edge x W);;
                                       If (fun s => low s x = dfn s x) (pop_scc x))
                      (fun (_: unit) s => u ∈ visited s /\ fa_visited s)).
    { (* preloop x: establish (u \in visited /\ fa_visited) /\ x \in visited *)
      apply Hoare_conj with
        (Q1 := fun _ s => u ∈ visited s /\ fa_visited s)
        (Q2 := fun _ s => x ∈ visited s).
      { apply Hoare_conj.
        { apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
          { intros s [Hvis1 Hfa1]; exact Hvis1. }
          apply (preloop_keep_visited x u). }
        { apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
          { intros s [Hvis1 Hfa1]; exact Hfa1. }
          apply (preloop_keep_fa_visited x). } }
      { apply Hoare_conseq_pre with (P2 := fun _ => True).
        { intros s _; exact I. }
        apply preloop_self_visited. } }
    { intros _. intro_state. destruct H as [[Huvis Hfa] Hxvis].
      apply Hoare_conseq_pre with
        (P2 := fun s => (u ∈ visited s /\ fa_visited s) /\ x ∈ visited s).
      { intros s1 Hs1. subst s1. repeat split; auto. }
      apply (Hoare_bind (fun s => (u ∈ visited s /\ fa_visited s) /\ x ∈ visited s)
                        (forset (fun w => dg_step g x w) (process_edge x W))
                        (fun (_: unit) s => (u ∈ visited s /\ fa_visited s) /\ x ∈ visited s)
                        (fun (_: unit) => If (fun s => low s x = dfn s x) (pop_scc x))
                        (fun (_: unit) s => u ∈ visited s /\ fa_visited s)).
      { (* forset: use combined lemma threading (u \in visited /\ fa_visited) /\ x \in visited *)
        apply (forset_process_edge_keep_combined u x W).
        intros a.
        (* Prove callback: Hoare ((u \in visited /\ fa_visited) /\ x \in visited) (W a)
                                 ((u \in visited /\ fa_visited) /\ x \in visited) *)
        apply Hoare_conj.
        { apply Hoare_conj.
          { (* u \in visited *)
            apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
            { intros s [[Huvis1 Hfa1] Hxvis1]. exact Huvis1. }
            apply (IHvis a u). }
          { (* fa_visited *)
            apply (Hoare_conseq
                    (fun s => (u ∈ visited s /\ fa_visited s) /\ x ∈ visited s)
                    (fun s => u ∈ visited s /\ fa_visited s)
                    (W a)
                    (fun _ s => fa_visited s)
                    (fun _ s => u ∈ visited s /\ fa_visited s)).
            { intros s [[Huvis1 Hfa1] Hxvis1]. split; [exact Huvis1 | exact Hfa1]. }
            { intros _ s [Huvis1 Hfa1]. exact Hfa1. }
            apply (IHfa a tt). } }
        { (* x \in visited *)
          apply Hoare_conseq_pre with (P2 := fun s => x ∈ visited s).
          { intros s [[Huvis1 Hfa1] Hxvis1]. exact Hxvis1. }
          apply (IHvis a x). } }
      { intros _.
        (* pop_scc / skip *)
        intro_state. hoare_auto_s.
        { (* pop_scc x: preserves both u \in visited and fa_visited *)
          apply Hoare_conj.
          { apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
            { intros s Hs. rewrite Hs. destruct H as [[Huvis1 Hfa1] Hxvis1]. exact Huvis1. }
            apply (pop_scc_keep_visited x u). }
          { apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
            { intros s Hs. rewrite Hs. destruct H as [[Huvis1 Hfa1] Hxvis1]. exact Hfa1. }
            apply pop_scc_keep_fa_visited. } }
        { (* skip *)
          destruct H1 as [Hs_eq _]. rewrite Hs_eq.
          destruct H as [[Huvis1 Hfa1] Hxvis1].
          split; [exact Huvis1 | exact Hfa1]. } } }
Qed.


(** Original theorem: proved via [Hoare_fix_logicv_conj] with [fa_visited]
    as the main property and [visited] as the auxiliary property.  This is
    structurally similar to [tarjan_scc_keep_fa_visited_rich] but with a
    simpler invariant (just [fa_visited] instead of [u ∈ visited ∧ fa_visited]),
    which avoids the tracking-vertex mismatch in the forset callbacks. *)
Theorem tarjan_scc_keep_fa_visited (u: V):
  Hoare (fun s: @SCCSt V => fa_visited s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => fa_visited s).
Proof.
  unfold tarjan_scc.
  apply (Hoare_fix_logicv_conj (tarjan_scc_f g)
           (fun (x: V) (_: unit) (s: SCCSt) => fa_visited s)
           (fun (x: V) (_: unit) (_: unit) (s: SCCSt) => fa_visited s)
           u tt
           (fun (x: V) (d: V) (s: SCCSt) => d ∈ visited s)
           (fun (x: V) (d: V) (_: unit) (s: SCCSt) => d ∈ visited s)).
  { (* Auxiliary: tarjan_scc preserves visitedness of any vertex *)
    intros x d. exact (tarjan_scc_keep_visited g x d). }
  { (* Main induction step *)
    intros W IHvis IHfa x.
    unfold tarjan_scc_f.
    intros _.
    apply (Hoare_bind (fun s => fa_visited s)
                      (preloop x)
                      (fun (_: unit) s => fa_visited s /\ x ∈ visited s)
                      (fun (_: unit) => forset (fun w => dg_step g x w) (process_edge x W);;
                                       If (fun s => low s x = dfn s x) (pop_scc x))
                      (fun (_: unit) s => fa_visited s)).
    { (* preloop x *)
      apply Hoare_conj.
      { apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
        { intros s Hfa. exact Hfa. }
        apply (preloop_keep_fa_visited x). }
      { apply Hoare_conseq_pre with (P2 := fun _ => True).
        { auto. }
        apply preloop_self_visited. } }
    { intros _. intro_state. destruct H as [Hfa Hxvis].
      apply Hoare_conseq_pre with
        (P2 := fun s => fa_visited s /\ x ∈ visited s).
      { intros s1 Hs1. subst s1. split; auto. }
      apply (Hoare_bind (fun s => fa_visited s /\ x ∈ visited s)
                        (forset (fun w => dg_step g x w) (process_edge x W))
                        (fun (_: unit) s => fa_visited s /\ x ∈ visited s)
                        (fun (_: unit) => If (fun s => low s x = dfn s x) (pop_scc x))
                        (fun (_: unit) s => fa_visited s)).
      { (* forset *)
        apply Hoare_conseq_pre with
          (P2 := fun s => x ∈ visited s /\ fa_visited s).
        { intros s1 [Hfa1 Hxvis1]. split; auto. }
        apply Hoare_conseq_post with
          (Q2 := fun (_: unit) s => x ∈ visited s /\ fa_visited s).
        { intros _ s [Hxvis1 Hfa1]. split; auto. }
        apply (forset_process_edge_keep_fa_visited_rich x W).
        intros a.
        apply Hoare_conj.
        { apply Hoare_conseq_pre with (P2 := fun s => x ∈ visited s).
          { intros s1 [Hxvis1 Hfa1]. exact Hxvis1. }
          apply (IHvis a x). }
        { apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
          { intros s1 [Hxvis1 Hfa1]. exact Hfa1. }
          apply (IHfa a tt). } }
      { intros _.
        intro_state. hoare_auto_s.
        { (* pop_scc x *)
          apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
          { intros s2 Hs2. rewrite Hs2. destruct H as [Hfa1 Hxvis1]. exact Hfa1. }
          apply pop_scc_keep_fa_visited. }
        { (* skip *)
          destruct H1 as [Hs2 _]. rewrite Hs2.
          destruct H as [Hfa1 Hxvis1]. exact Hfa1. } } } }
Qed.

(* ================================================================ *)
(* 2a. dfn_valid preservation through preloop                        *)
(* ================================================================ *)

Lemma preloop_preserves_dfn_valid (u: V):
  Hoare (fun s: @SCCSt V => ~ u ∈ visited s /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s)
        (preloop u)
        (fun _ s => u ∈ visited s /\ dfn_valid s root /\ dfn_inv s).
Admitted.

(* ================================================================ *)
(* 2b. dfn_valid preservation through process_edge                   *)
(* ================================================================ *)

Lemma process_edge_keep_dfn_valid (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_pre x s root) (W x) (fun _ s => dfn_post s root)) ->
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ dfn_valid s root /\ dfn_inv s)
        (process_edge u W v)
        (fun _ s => dfn_post s root).
Admitted.

(* ================================================================ *)
(* 2c. dfn_valid emergence through forset                            *)
(* ================================================================ *)

Lemma forset_establishes_dfn_valid (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_pre x s root) (W x) (fun _ s => dfn_post s root)) ->
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ dfn_valid s root /\ dfn_inv s)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => dfn_post s root).
Admitted.

(* ================================================================ *)
(* 2d. tarjan_scc keeps dfn_valid (Hoare_fix)                        *)
(* ================================================================ *)

Theorem tarjan_scc_keep_dfn_valid (u: V):
  Hoare (fun s: @SCCSt V => dfn_pre u s root)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => dfn_post s root).
Admitted.

(* ================================================================ *)
(* 2e. tarjan_scc_all establishes dfn_valid                          *)
(* ================================================================ *)

Theorem tarjan_scc_all_dfn_valid:
  Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s)
        (tarjan_scc_all g)
        (fun _ s => dfn_valid s root).
Admitted.

(* ================================================================ *)
(* 3. dfn_unique — Injectivity of dfn                                *)
(* ================================================================ *)

Lemma dfn_unique (s: @SCCSt V):
  dfn_inv s ->
  forall x y, dfn s x = dfn s y -> x = y \/ (~ x ∈ visited s /\ ~ y ∈ visited s).
Admitted.

End IS_DFN.
