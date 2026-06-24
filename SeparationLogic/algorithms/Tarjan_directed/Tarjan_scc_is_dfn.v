Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.Morphisms.
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

(** Lfix induction principle: if f W a satisfies Q a s0 under the
    hypothesis that W a does, then Lfix f a also satisfies Q a s0. *)
Theorem Hoare_normal_LFix {Σ A B: Type}:
  forall (Q: A -> Σ -> B -> Σ -> Prop)
         (f: (A -> StateRelMonad.M Σ B) -> (A -> StateRelMonad.M Σ B)),
    (forall (W: A -> StateRelMonad.M Σ B),
       (forall s0 a, Hoare (fun s => s = s0) (W a) (Q a s0)) ->
       (forall s0 a, Hoare (fun s => s = s0) (f W a) (Q a s0))) ->
    (forall s0 a, Hoare (fun s => s = s0) (Lfix f a) (Q a s0)).
Proof.
  intros.
  unfold Hoare.
  intros s1 b s2 ? ?.
  change (exists n, (s1, b, s2) ∈ Nat.iter n f ∅ a) in H1.
  destruct H1 as [n ?].
  revert s1 b s2 H0 H1.
  change (Hoare (fun s => s = s0) (Nat.iter n f ∅ a) (Q a s0)).
  revert s0 a.
  induction n.
  + unfold Hoare; simpl; sets_unfold; tauto.
  + simpl.
    apply H.
    apply IHn.
Qed.

(** Lfix induction with an invariant R closed under the recursive step. *)
Theorem Hoare_normal_LFix_closed {Σ A B: Type}:
  forall (R: Σ -> Prop)
         (Q: A -> Σ -> B -> Σ -> Prop)
         (f: (A -> StateRelMonad.M Σ B) -> (A -> StateRelMonad.M Σ B)),
    (forall (W: A -> StateRelMonad.M Σ B),
       (forall s0 a, R s0 -> Hoare (fun s => s = s0) (W a) (Q a s0)) ->
       (forall s0 a, R s0 -> Hoare (fun s => s = s0) (f W a) (Q a s0))) ->
    (forall s0 a, R s0 -> Hoare (fun s => s = s0) (Lfix f a) (Q a s0)).
Proof.
  intros R Q f H s0 a HR.
  unfold Hoare. intros s1 b s2 H0 H1.
  change (exists n, (s1, b, s2) ∈ Nat.iter n f ∅ a) in H1.
  destruct H1 as [n ?].
  revert s1 b s2 H0 H1.
  change (Hoare (fun s => s = s0) (Nat.iter n f ∅ a) (Q a s0)).
  revert s0 a HR.
  induction n.
  + unfold Hoare; simpl; sets_unfold; tauto.
  + simpl. apply H. apply IHn.
Qed.

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
(* 1a. dfn_injective — Injectivity of dfn for visited vertices      *)
(* ================================================================ *)

Definition dfn_injective (s: @SCCSt V): Prop :=
  forall x y, x <> y -> x ∈ visited s -> y ∈ visited s -> dfn s x <> dfn s y.

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
  ~ u ∈ visited s /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s.

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

Lemma pop_scc_keep_dfn_valid (u: V):
  Hoare (fun s: @SCCSt V => dfn_valid s root)
        (pop_scc u)
        (fun _ s => dfn_valid s root).
Proof.
  unfold pop_scc, dfn_valid. intro_state. hoare_auto_s.
  subst s.
  assert (Htree: state_to_dfs_tree g (pop_scc_state s0 u) root
                = state_to_dfs_tree g s0 root).
  { unfold pop_scc_state. destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
    reflexivity. }
  rewrite Htree in H2. apply H in H2.
  unfold pop_scc_state in *. destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
  simpl. exact H2.
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
Proof.
  apply Hoare_conj with (Q1 := fun _ s => u ∈ visited s) (Q2 := fun _ s => dfn_valid s root /\ dfn_inv s).
  { eapply Hoare_conseq_pre.
    { intros s Hpre. exact I. }
    apply preloop_self_visited. }
  { apply Hoare_conj with (Q1 := fun _ s => dfn_valid s root) (Q2 := fun _ s => dfn_inv s).
    { (* dfn_valid preservation *)
      intro_state. destruct H as [Hnuvis [Hvalid [Hinv Hfa]]].
      unfold preloop. unfold_op. hoare_auto_s. subst s. simpl.
      unfold dfn_valid. intros x y Hstep.
      unfold dg_step in Hstep.
      destruct Hstep as [e [Htree [Hfst_eq Hsnd_eq]]].
      unfold original_step in Htree. simpl in Htree.
      destruct Htree as [v [Hv [Hfa_ne' [Hfst_fa Hsnd_v]]]].
      cbn in Hv. sets_unfold in Hv.
      simpl in Hfst_fa.
      unfold state_to_dfs_tree in Hfst_eq, Hsnd_eq. simpl in Hfst_eq, Hsnd_eq.
      assert (Hvy: v = y). { rewrite <- Hsnd_v. exact Hsnd_eq. }
      rewrite Hvy in *. clear Hvy. simpl.
      destruct Hv as [Hyvis | Heqy].
      { (* Case 1: y was already visited before preloop *)
        assert (Hneqy: y <> u).
        { intros Heqy'. apply Hnuvis. rewrite <- Heqy'. exact Hyvis. }
        assert (Hneqx: x <> u).
        { intros Heqx. rewrite Heqx in *. rewrite Hfst_fa in Hfst_eq.
          apply Hnuvis. rewrite <- Hfst_eq. apply (Hfa y). exact Hfa_ne'. }
        unfold equiv_decb.
        destruct (equiv_dec x u) as [Heqx | _].
        { exfalso. apply Hneqx. exact Heqx. }
        destruct (equiv_dec y u) as [Heqy' | _].
        { exfalso. apply Hneqy. exact Heqy'. }
        simpl. unfold dfn_valid in Hvalid. apply Hvalid.
        unfold dg_step. exists e. split.
        { unfold original_step. simpl.
          exists y. split; [exact Hyvis | split; [exact Hfa_ne' | split; [exact Hfst_fa | exact Hsnd_v]]]. }
        { split; [exact Hfst_eq | exact Hsnd_eq]. } }
      { (* Case 2: y = u, new tree edge fa s0 u -> u *)
        rewrite Heqy in *. rewrite Hfst_fa in Hfst_eq. (* fa s0 y = x *)
        rewrite Hfst_eq in Hfa_ne'. (* now Hfa_ne': x <> y *)
        assert (Hfa_ne_orig: fa s0 y <> y). { rewrite Hfst_eq. exact Hfa_ne'. }
        assert (Hxvis: x ∈ visited s0).
        { apply (Hfa y) in Hfa_ne_orig. rewrite Hfst_eq in Hfa_ne_orig. exact Hfa_ne_orig. }
        destruct Hinv as [Hdfn_lt [Hdfn_zero Htimer_pos]].
        apply Hdfn_lt in Hxvis. (* dfn s0 x < timer s0 *)
        unfold equiv_decb.
        destruct (equiv_dec x y) as [Heqx | _].
        { exfalso. apply Hfa_ne'. exact Heqx. }
        destruct (equiv_dec y y) as [_ | Hneq].
        { simpl. exact Hxvis. }
        { exfalso. apply Hneq. reflexivity. } } }
    { (* dfn_inv preservation *)
      eapply Hoare_conseq_pre.
      { intros s Hpre. destruct Hpre as [_ [_ [Hinv _]]]. exact Hinv. }
      apply preloop_keep_dfn_inv. } }
Qed.

(* ================================================================ *)
(* 2b. dfn_valid preservation through process_edge                   *)
(* ================================================================ *)

(** [set_fa_preserves_dfn_pre_child]: [set_fa v u] when [v] is
    unvisited preserves all components of [dfn_pre v].  This bundles
    the facts needed to call the recursive hypothesis [W v] in the
    tree-edge branch of [process_edge]. *)

Lemma set_fa_preserves_dfn_pre_child (v u: V):
  Hoare (fun s: @SCCSt V => ~ v ∈ visited s /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s /\ u ∈ visited s)
        (set_fa v u)
        (fun _ s => dfn_pre v s root).
Proof.
  unfold set_fa, dfn_pre, dfn_valid, dfn_inv, fa_visited.
  intro_state. hoare_auto_s. subst s. simpl.
  destruct H as [Hnv [Hvalid [Hinv [Hfa Huvis]]]].
  repeat split.
  - exact Hnv.
  - intros x y Hstep. apply Hvalid.
    unfold dg_step in Hstep. destruct Hstep as [e [Htree [Hfst Hsnd]]].
    unfold original_step in Htree. simpl in Htree.
    destruct Htree as [w [Hwvis [Hwfa [Hwfst Hwsnd]]]].
    assert (Hwneq: w <> v). { intros Heq. rewrite Heq in Hwvis. apply Hnv. exact Hwvis. }
    unfold equiv_decb in Hwfa, Hwfst. destruct (equiv_dec w v) as [Heq | Hneq].
    { exfalso. rewrite Heq in Hwvis. apply Hnv. exact Hwvis. }
    exists e. split; [ | split]; auto.
    exists w. repeat split; auto.
  - intros v0 Hvis'. apply (proj1 Hinv v0). simpl in Hvis'. auto.
  - intros Hdfn0. simpl. apply (proj1 ((proj1 (proj2 Hinv)) v0)). auto.
  - intros Hnvis. simpl. apply (proj2 ((proj1 (proj2 Hinv)) v0)). simpl in Hnvis. auto.
  - simpl. apply (proj2 (proj2 Hinv)).
  - intros v0 Hneq. simpl. unfold equiv_decb.
    destruct (equiv_dec v0 v) as [Heq | Hneq'];
    [ rewrite Heq in *; simpl in Hneq; unfold equiv_decb in Hneq;
      destruct (equiv_dec v v) as [_ | Hc];
      [ exact Huvis | exfalso; apply Hc; reflexivity ]
    | simpl in Hneq; unfold equiv_decb in Hneq;
      destruct (equiv_dec v0 v) as [Heq | _];
      [ exfalso; apply Hneq'; exact Heq
      | apply Hfa; exact Hneq ] ].
Qed.

Lemma set_fa_preserves_dfn_pre_child_rich (v u: V):
  Hoare (fun s: @SCCSt V => dfn_pre v s root /\ u ∈ visited s)
        (set_fa v u)
        (fun _ s => dfn_pre v s root /\ u ∈ visited s).
Proof.
  apply Hoare_conj.
  - apply Hoare_conseq_pre with
      (P2 := fun s => ~ v ∈ visited s /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s /\ u ∈ visited s).
    + intros s [Hpre Huvis]. destruct Hpre as [Hnv [Hvalid [Hinv Hfa]]]. repeat split; auto.
      all: destruct Hinv as [Hlt [Hiff Hpos]];
           try (apply Hlt); try (apply (proj1 (Hiff v0)));
           try (apply (proj2 (Hiff v0))); try exact Hpos; auto.
    + apply set_fa_preserves_dfn_pre_child.
  - eapply Hoare_conseq_pre;
      [ intros s [Hpre Huvis]; exact Huvis
      | apply (set_fa_keep_visited v u u) ].
Qed.

Lemma set_fa_preserves_dfn_pre_child_full (v u: V):
  Hoare (fun s: @SCCSt V => dfn_pre v s root /\ u ∈ visited s /\ fa_visited s)
        (set_fa v u)
        (fun _ s => dfn_pre v s root /\ u ∈ visited s /\ fa_visited s).
Proof.
  unfold set_fa, dfn_pre, dfn_valid, dfn_inv, fa_visited.
  intro_state. hoare_auto_s. subst s. simpl.
  destruct H as [[Hnv [Hvalid [Hinv Hfa]]] [Huvis _]].
  split.
  - split; [| split; [| split]].
    + exact Hnv.
    + intros x y Hstep. apply Hvalid.
      unfold dg_step in Hstep. destruct Hstep as [e [Htree [Hfst Hsnd]]].
      unfold original_step in Htree. simpl in Htree.
      destruct Htree as [w [Hwvis [Hwfa [Hwfst Hwsnd]]]].
      assert (Hwneq: w <> v). { intros Heq. rewrite Heq in Hwvis. apply Hnv. exact Hwvis. }
      unfold equiv_decb in Hwfa, Hwfst. destruct (equiv_dec w v) as [Heq | Hneq].
      { exfalso. rewrite Heq in Hwvis. apply Hnv. exact Hwvis. }
      exists e. split; [ | split]; auto.
      exists w. repeat split; auto.
    + destruct Hinv as [Hlt [Hiff Hpos]].
      split; [| split].
      * intros v0 Hvis'. apply Hlt. simpl in Hvis'. auto.
      * intros v0. apply Hiff.
      * apply Hpos.
    + intros v0 Hneq. simpl. unfold equiv_decb.
      destruct (equiv_dec v0 v) as [Heq | Hneq'];
      [ rewrite Heq in *; simpl in Hneq; unfold equiv_decb in Hneq;
        destruct (equiv_dec v v) as [_ | Hc];
        [ exact Huvis | exfalso; apply Hc; reflexivity ]
      | simpl in Hneq; unfold equiv_decb in Hneq;
        destruct (equiv_dec v0 v) as [Heq | _];
        [ exfalso; apply Hneq'; exact Heq
        | apply Hfa; exact Hneq ] ].
  - split.
    + exact Huvis.
    + intros v0 Hneq. simpl. unfold equiv_decb.
      destruct (equiv_dec v0 v) as [Heq | Hneq'];
      [ rewrite Heq in *; simpl in Hneq; unfold equiv_decb in Hneq;
        destruct (equiv_dec v v) as [_ | Hc];
        [ exact Huvis | exfalso; apply Hc; reflexivity ]
      | simpl in Hneq; unfold equiv_decb in Hneq;
        destruct (equiv_dec v0 v) as [Heq | _];
        [ exfalso; apply Hneq'; exact Heq
        | apply Hfa; exact Hneq ] ].
Qed.

Lemma update_low_keep_dfn_valid (u: V) (n: nat):
  Hoare (fun s: @SCCSt V => dfn_valid s root)
        (update_low u n)
        (fun _ s => dfn_valid s root).
Proof.
  unfold update_low, dfn_valid. unfold_op. intro_state. hoare_auto_s.
  - subst s. simpl. auto.
  - match goal with
    | [ H: _ = s0 /\ _ |- _ ] => destruct H as [Hs _]; rewrite Hs in *; auto
    end.
Qed.

Lemma get_low_update_low_keep_dfn_valid (u v: V):
  Hoare (fun s: @SCCSt V => dfn_valid s root)
        (lv <- get' (fun s => low s v);; update_low u lv)
        (fun _ s => dfn_valid s root).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
  apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root).
  { intros s1 Hs1. destruct Hs1. subst s1. simpl. auto. }
  apply (update_low_keep_dfn_valid u lv).
Qed.

Lemma get_dfn_update_low_keep_dfn_valid (u v: V):
  Hoare (fun s: @SCCSt V => dfn_valid s root)
        (dv <- get' (fun s => dfn s v);; update_low u dv)
        (fun _ s => dfn_valid s root).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
  apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root).
  { intros s1 Hs1. destruct Hs1. subst s1. simpl. auto. }
  apply (update_low_keep_dfn_valid u dv).
Qed.

Lemma process_edge_keep_dfn_valid (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_pre x s root /\ u ∈ visited s) (W x)
                   (fun _ s => dfn_post s root /\ u ∈ visited s)) ->
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ dfn_valid s root /\ dfn_inv s /\ fa_visited s)
        (process_edge u W v)
        (fun _ s => dfn_post s root /\ u ∈ visited s).
Proof.
  intros HW.
  unfold process_edge, if_else, dfn_post.
  intro_state. destruct H as [Huvis [Hvalid [Hinv Hfa]]].
  apply Hoare_choice.
  - (* Tree edge: v not visited *)
    apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => dfn_pre v s root /\ u ∈ visited s).
    { intros s1 [Hnv Hs1]. subst s1. repeat split; auto.
      all: destruct Hinv as [Hlt [Hiff Hpos]];
           try (apply Hlt); try (apply (proj1 (Hiff v0)));
           try (apply (proj2 (Hiff v0))); try exact Hpos; auto. }
    eapply Hoare_bind.
    { apply (set_fa_preserves_dfn_pre_child_rich v u). }
    simpl. intros _.
    eapply Hoare_bind.
    { apply (HW v). }
    simpl. intros _.
    apply Hoare_conj.
    * apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root /\ dfn_inv s).
      { intros s1 [[Hvalid' Hinv'] _]. split; auto. }
      apply Hoare_conj.
      -- apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root);
           [ intros s1 [Hvalid' _]; exact Hvalid' | apply get_low_update_low_keep_dfn_valid ].
      -- apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s);
           [ intros s1 [_ Hinv']; exact Hinv' | apply get_low_update_low_keep_dfn_inv ].
    * apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s);
        [ intros s1 [_ Huvis']; exact Huvis' | apply (get_low_update_low_keep_visited u v u) ].
  - (* Non-tree edge: v visited *)
    intro_state. hoare_auto_s.
    + (* v in stack: update low with dfn v *)
      apply Hoare_conj.
      * apply Hoare_conj.
        -- apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root).
           ++ intros s1 Hs1. subst s1. exact Hvalid.
           ++ apply (update_low_keep_dfn_valid u (dfn s0 v)).
        -- apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
           ++ intros s1 Hs1. subst s1. exact Hinv.
           ++ apply (update_low_keep_dfn_inv u (dfn s0 v)).
      * apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
        -- intros s1 Hs1. subst s1. exact Huvis.
        -- apply (update_low_keep_visited u u (dfn s0 v)).
    + (* v not in stack: skip *)
      destruct H2 as [Heq _]. subst s. subst s1. repeat split; auto.
      all: destruct Hinv as [Hlt [Hiff Hpos]];
           try (apply Hlt); try (apply (proj1 (Hiff v0)));
           try (apply (proj2 (Hiff v0))); try exact Hpos; auto.
Qed.

Lemma process_edge_keep_dfn_valid_full (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_post s root /\ u ∈ visited s /\ fa_visited s) (W x)
                   (fun _ s => dfn_post s root /\ u ∈ visited s /\ fa_visited s)) ->
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s /\ dfn_valid s root /\ dfn_inv s)
        (process_edge u W v)
        (fun _ s => dfn_post s root /\ u ∈ visited s /\ fa_visited s).
Proof.
  intros HW.
  unfold process_edge, if_else, dfn_post.
  intro_state. destruct H as [Huvis [Hfa [Hvalid Hinv]]].
  apply Hoare_choice.
  - (* Tree edge: v not visited *)
    apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with
      (P2 := fun s => dfn_pre v s root /\ u ∈ visited s /\ fa_visited s).
    { intros s1 [Hnv Hs1]. subst s1. repeat split; auto.
      all: destruct Hinv as [Hlt [Hiff Hpos]];
           try (apply Hlt); try (apply (proj1 (Hiff v0)));
           try (apply (proj2 (Hiff v0))); try exact Hpos; auto. }
    eapply Hoare_bind.
    { apply (set_fa_preserves_dfn_pre_child_full v u). }
    simpl. intros _.
    eapply Hoare_bind.
    { assert (HWv_weaken : Hoare (fun s => dfn_pre v s root /\ u ∈ visited s /\ fa_visited s)
                               (W v)
                               (fun _ s => dfn_post s root /\ u ∈ visited s /\ fa_visited s)).
      { apply Hoare_conseq_pre with
          (P2 := fun s => dfn_post s root /\ u ∈ visited s /\ fa_visited s).
        - intros s1 Hs1. destruct Hs1 as [[Hpre [Hvalid' [Hinv' _]]] [Huvis1 Hfa']].
          destruct Hinv' as [Hlt [Hiff Hpos]].
          repeat split; auto.
          + intros Hdfn. apply (proj1 (Hiff v0)). exact Hdfn.
          + intros Hnvis. apply (proj2 (Hiff v0)). exact Hnvis.
        - apply (HW v). }
      exact HWv_weaken. }
    simpl. intros _.
    apply Hoare_conj with
      (Q1 := fun (_: unit) s => dfn_valid s root /\ dfn_inv s)
      (Q2 := fun (_: unit) s => u ∈ visited s /\ fa_visited s).
    { apply Hoare_conj with
        (Q1 := fun (_: unit) s => dfn_valid s root)
        (Q2 := fun (_: unit) s => dfn_inv s).
      - apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root).
        + intros s1 Hs1. apply Hs1.
        + apply get_low_update_low_keep_dfn_valid.
      - apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
        + intros s1 Hs1. apply Hs1.
        + apply get_low_update_low_keep_dfn_inv. }
    { apply Hoare_conj with
        (Q1 := fun (_: unit) s => u ∈ visited s)
        (Q2 := fun (_: unit) s => fa_visited s).
      - apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
        + intros s1 Hs1. apply Hs1.
        + apply (get_low_update_low_keep_visited u v u).
      - apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
        + intros s1 Hs1. apply Hs1.
        + apply (get_low_update_low_keep_fa_visited u v). }
  - (* Non-tree edge: v visited *)
    intro_state. hoare_auto_s.
    + (* v in stack: update low with dfn v *)
      apply Hoare_conj with
        (Q1 := fun (_: unit) s => dfn_valid s root /\ dfn_inv s)
        (Q2 := fun (_: unit) s => u ∈ visited s /\ fa_visited s).
      { apply Hoare_conj with
          (Q1 := fun (_: unit) s => dfn_valid s root)
          (Q2 := fun (_: unit) s => dfn_inv s).
        - apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root).
          + intros s1 Hs1. subst s1. exact Hvalid.
          + apply (update_low_keep_dfn_valid u (dfn s0 v)).
        - apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
          + intros s1 Hs1. subst s1. exact Hinv.
          + apply (update_low_keep_dfn_inv u (dfn s0 v)). }
      { apply Hoare_conj with
          (Q1 := fun (_: unit) s => u ∈ visited s)
          (Q2 := fun (_: unit) s => fa_visited s).
        - apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
          + intros s1 Hs1. subst s1. exact Huvis.
          + apply (update_low_keep_visited u u (dfn s0 v)).
        - apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
          + intros s1 Hs1. subst s1. exact Hfa.
          + apply (update_low_keep_fa_visited u (dfn s0 v)). }
    + (* v not in stack: skip *)
      destruct H2 as [Heq _]. subst s. subst s1. repeat split; auto.
      all: destruct Hinv as [Hlt [Hiff Hpos]];
           try (apply Hlt); try (apply (proj1 (Hiff v0)));
           try (apply (proj2 (Hiff v0))); try exact Hpos; auto.
Qed.

Lemma process_edge_keep_dfn_valid_pre (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_pre x s root /\ u ∈ visited s /\ fa_visited s) (W x)
                   (fun _ s => dfn_post s root /\ u ∈ visited s /\ fa_visited s)) ->
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s /\ dfn_valid s root /\ dfn_inv s)
        (process_edge u W v)
        (fun _ s => dfn_post s root /\ u ∈ visited s /\ fa_visited s).
Proof.
  intros HW.
  unfold process_edge, if_else, dfn_post.
  intro_state. destruct H as [Huvis [Hfa [Hvalid Hinv]]].
  apply Hoare_choice.
  - (* Tree edge: v not visited *)
    apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with
      (P2 := fun s => dfn_pre v s root /\ u ∈ visited s /\ fa_visited s).
    { intros s1 [Hnv Hs1]. subst s1. repeat split; auto.
      all: destruct Hinv as [Hlt [Hiff Hpos]];
           try (apply Hlt); try (apply (proj1 (Hiff v0)));
           try (apply (proj2 (Hiff v0))); try exact Hpos; auto. }
    eapply Hoare_bind.
    { apply (set_fa_preserves_dfn_pre_child_full v u). }
    simpl. intros _.
    eapply Hoare_bind.
    { apply (HW v). }
    simpl. intros _.
    apply Hoare_conj with
      (Q1 := fun (_: unit) s => dfn_valid s root /\ dfn_inv s)
      (Q2 := fun (_: unit) s => u ∈ visited s /\ fa_visited s).
    { apply Hoare_conj with
        (Q1 := fun (_: unit) s => dfn_valid s root)
        (Q2 := fun (_: unit) s => dfn_inv s).
      - apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root).
        + intros s1 Hs1. apply Hs1.
        + apply get_low_update_low_keep_dfn_valid.
      - apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
        + intros s1 Hs1. apply Hs1.
        + apply get_low_update_low_keep_dfn_inv. }
    { apply Hoare_conj with
        (Q1 := fun (_: unit) s => u ∈ visited s)
        (Q2 := fun (_: unit) s => fa_visited s).
      - apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
        + intros s1 Hs1. apply Hs1.
        + apply (get_low_update_low_keep_visited u v u).
      - apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
        + intros s1 Hs1. apply Hs1.
        + apply (get_low_update_low_keep_fa_visited u v). }
  - (* Non-tree edge: v visited *)
    intro_state. hoare_auto_s.
    + (* v in stack: update low with dfn v *)
      apply Hoare_conj with
        (Q1 := fun (_: unit) s => dfn_valid s root /\ dfn_inv s)
        (Q2 := fun (_: unit) s => u ∈ visited s /\ fa_visited s).
      { apply Hoare_conj with
          (Q1 := fun (_: unit) s => dfn_valid s root)
          (Q2 := fun (_: unit) s => dfn_inv s).
        - apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root).
          + intros s1 Hs1. subst s1. exact Hvalid.
          + apply (update_low_keep_dfn_valid u (dfn s0 v)).
        - apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
          + intros s1 Hs1. subst s1. exact Hinv.
          + apply (update_low_keep_dfn_inv u (dfn s0 v)). }
      { apply Hoare_conj with
          (Q1 := fun (_: unit) s => u ∈ visited s)
          (Q2 := fun (_: unit) s => fa_visited s).
        - apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
          + intros s1 Hs1. subst s1. exact Huvis.
          + apply (update_low_keep_visited u u (dfn s0 v)).
        - apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
          + intros s1 Hs1. subst s1. exact Hfa.
          + apply (update_low_keep_fa_visited u (dfn s0 v)). }
    + (* v not in stack: skip *)
      destruct H2 as [Heq _]. subst s. subst s1. repeat split; auto.
      all: destruct Hinv as [Hlt [Hiff Hpos]];
           try (apply Hlt); try (apply (proj1 (Hiff v0)));
           try (apply (proj2 (Hiff v0))); try exact Hpos; auto.
Qed.

Lemma forset_process_edge_keep_dfn_valid_pre (u: V) (W: V -> program (@SCCSt V) unit):
  (forall a, Hoare (fun s => dfn_pre a s root /\ u ∈ visited s /\ fa_visited s) (W a)
                   (fun _ s => dfn_post s root /\ u ∈ visited s /\ fa_visited s)) ->
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ fa_visited s /\ dfn_valid s root /\ dfn_inv s)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => dfn_post s root /\ u ∈ visited s /\ fa_visited s).
Proof.
  intros HW.
  unfold forset. hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
  - (* Goal 1: a ∈ todo, process_edge + recursion *)
    eapply Hoare_bind with
      (Q := fun (_: unit) s => u ∈ visited s /\ fa_visited s /\ dfn_valid s root /\ dfn_inv s).
    { (* process_edge u W a *)
      apply Hoare_conseq_post with
        (Q2 := fun _ s => dfn_post s root /\ u ∈ visited s /\ fa_visited s).
      { intros _ s [Hpost [Huvis' Hfa']].
        destruct Hpost as [Hvalid' Hinv'].
        destruct Hinv' as [Hlt [Hiff Hpos]].
        split; [exact Huvis' | split; [exact Hfa' | split; [exact Hvalid' |]]].
        split; [exact Hlt | split; [exact Hiff | exact Hpos]]. }
      apply Hoare_conseq_pre with
        (P2 := fun s => u ∈ visited s /\ fa_visited s /\ dfn_valid s root /\ dfn_inv s).
      { intros s1 Hs1. subst s1. exact H. }
      apply (process_edge_keep_dfn_valid_pre u a W). intros x. apply HW. }
    { intros _. apply IH0. }
  - (* Goal 2: todo == ∅ *)
    destruct H1 as [Huvis [Hfa [Hvalid Hinv]]].
    destruct Hinv as [Hlt [Hiff Hpos]].
    split.
    { split; [exact Hvalid | split; [exact Hlt | split; [exact Hiff | exact Hpos]]]. }
    { split; [exact Huvis | exact Hfa]. }
Qed.

Theorem tarjan_scc_keep_dfn_valid (u: V):
  Hoare (fun s: @SCCSt V => dfn_pre u s root)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => dfn_post s root).
Proof.
  (* First prove a richer version that also preserves fa_visited *)
  cut (Hoare (fun s: @SCCSt V => dfn_pre u s root)
             (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
             (fun _ s => dfn_post s root /\ fa_visited s)).
  { intros H. eapply Hoare_conseq_post; [| apply H]. intros _ s [Hpost _]. exact Hpost. }
  unfold tarjan_scc.
  apply (Hoare_fix_logicv_conj (tarjan_scc_f g)
           (fun (x: V) (_: unit) (s: SCCSt) => dfn_pre x s root)
           (fun (x: V) (_: unit) (_: unit) (s: SCCSt) => dfn_post s root /\ fa_visited s)
           u tt
           (fun (x: V) (d: V) (s: SCCSt) => d ∈ visited s)
           (fun (x: V) (d: V) (_: unit) (s: SCCSt) => d ∈ visited s)).
  { (* Auxiliary: tarjan_scc preserves visitedness of any vertex *)
    intros x d. exact (tarjan_scc_keep_visited g x d). }
  { (* Main induction step *)
    intros W IHvis IHdfn x.
    unfold tarjan_scc_f.
    intros _.
    (* Step 1: preloop x — establish x ∈ visited /\ fa_visited /\ dfn_post *)
    eapply Hoare_bind.
    { apply Hoare_conj with
        (Q1 := fun _ s => x ∈ visited s /\ dfn_valid s root /\ dfn_inv s)
        (Q2 := fun _ s => fa_visited s).
      - apply preloop_preserves_dfn_valid.
      - eapply Hoare_conseq_pre.
        2: apply preloop_keep_fa_visited.
        intros s Hpre. destruct Hpre as [_ [_ [_ Hfa]]]. exact Hfa. }
    simpl. intros _. intro_state.
    destruct H as [[Hxvis [Hvalid Hinv]] Hfa].
    (* Step 2: forset + if-else, target dfn_post /\ fa_visited *)
    eapply Hoare_bind with (Q := fun _ s => dfn_post s root /\ fa_visited s).
    { (* forset: apply lemma with pre/post adapted via Hoare_conseq *)
      apply (Hoare_conseq
        (fun s => s = s0)
        (fun s => x ∈ visited s /\ fa_visited s /\ dfn_valid s root /\ dfn_inv s)
        (forset (fun w => dg_step g x w) (process_edge x W))
        (fun _ s => dfn_post s root /\ fa_visited s)
        (fun _ s => dfn_post s root /\ x ∈ visited s /\ fa_visited s)).
      - (* P1 -> P2 *)
        intros s1 Heq. subst s1.
        destruct Hinv as [Hlt [Hiff Hpos]].
        split; [exact Hxvis | split; [exact Hfa | split; [exact Hvalid | split; [exact Hlt | split; [exact Hiff | exact Hpos]]]]].
      - (* Q2 -> Q1: drop x_vis *)
        intros _ s [Hpost [Hxvis' Hfa']]. split; [exact Hpost | exact Hfa'].
      - (* Hoare P2 f Q2: the forset lemma *)
        apply forset_process_edge_keep_dfn_valid_pre.
        intros a.
        (* Callback: Hoare (dfn_pre a /\ x_vis /\ fa_visited) (W a)
                           (dfn_post /\ x_vis /\ fa_visited) *)
        pose proof (IHdfn a tt) as Hdfn_a.
        pose proof (IHvis a x) as Hvis_a.
        (* Build dfn_post from IHdfn *)
        assert (Hdfn_post_a : Hoare (fun s => dfn_pre a s root /\ x ∈ visited s /\ fa_visited s)
                                    (W a)
                                    (fun _ s => dfn_post s root)).
        { eapply Hoare_conseq_post.
          2: { eapply Hoare_conseq_pre. 2: exact Hdfn_a. intros s [Hpre _]. exact Hpre. }
          intros _ s [Hpost _]. exact Hpost. }
        (* Build x_vis /\ fa_visited *)
        assert (Hxvis_fa_a : Hoare (fun s => dfn_pre a s root /\ x ∈ visited s /\ fa_visited s)
                                   (W a)
                                   (fun _ s => x ∈ visited s /\ fa_visited s)).
        { apply Hoare_conj with
            (Q1 := fun _ s => x ∈ visited s)
            (Q2 := fun _ s => fa_visited s).
          - eapply Hoare_conseq_pre. 2: exact Hvis_a. intros s [_ [Hxvis' _]]. exact Hxvis'.
          - eapply Hoare_conseq_post.
            2: { eapply Hoare_conseq_pre. 2: exact Hdfn_a. intros s [Hpre _]. exact Hpre. }
            intros _ s [_ Hfa']. exact Hfa'. }
        (* Combine: dfn_post /\ x_vis /\ fa_visited *)
        apply Hoare_conj with
          (Q1 := fun _ s => dfn_post s root)
          (Q2 := fun _ s => x ∈ visited s /\ fa_visited s).
        + exact Hdfn_post_a.
        + exact Hxvis_fa_a. }
    simpl. intros _.
    (* Step 3: If low x = dfn x then pop_scc x *)
    intro_state. hoare_auto_s.
    - (* pop_scc x: preserve dfn_post /\ fa_visited *)
      apply Hoare_conj with
        (Q1 := fun _ s => dfn_post s root)
        (Q2 := fun _ s => fa_visited s).
      + apply Hoare_conj with
          (Q1 := fun _ s => dfn_valid s root)
          (Q2 := fun _ s => dfn_inv s).
        * apply Hoare_conseq_pre with (P2 := fun s => dfn_valid s root).
          { intros sx Hsx. subst sx. destruct H as [[Hvalid' Hinv'] Hfa']. exact Hvalid'. }
          apply pop_scc_keep_dfn_valid.
        * apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
          { intros sx Hsx. subst sx. destruct H as [[Hvalid' Hinv'] Hfa']. exact Hinv'. }
          apply pop_scc_keep_dfn_inv.
      + apply Hoare_conseq_pre with (P2 := fun s => fa_visited s).
        { intros sx Hsx. subst sx. destruct H as [[Hvalid' Hinv'] Hfa']. exact Hfa'. }
        apply pop_scc_keep_fa_visited.
    - (* skip: preserve dfn_post /\ fa_visited *)
      destruct H1 as [Heq _]. subst s.
      destruct H as [[Hvalid' Hinv'] Hfa'].
      destruct Hinv' as [Hlt [Hiff Hpos]].
      split.
      { split; [exact Hvalid' | split; [exact Hlt | split; [exact Hiff | exact Hpos]]]. }
      { exact Hfa'. } }
Qed.

Theorem tarjan_scc_all_dfn_valid:
  Hoare (fun s: @SCCSt V => dfn_inv s /\ fa_visited s /\ dfn_valid s root)
        (tarjan_scc_all g)
        (fun _ s => dfn_valid s root).
Proof.
  unfold tarjan_scc_all.
  apply Hoare_conseq with
    (P2 := fun s => dfn_inv s /\ fa_visited s /\ dfn_valid s root)
    (Q2 := fun _ s => dfn_inv s /\ fa_visited s /\ dfn_valid s root).
  - (* P1 -> P2: trivial, same condition *)
    intros s H. exact H.
  - (* Q2 -> Q1: extract dfn_valid from the conjunction *)
    intros _ s [Hinv [Hfa Hvalid]]. exact Hvalid.
  - (* Hoare P2 forset Q2 — now postcondition matches *)
    apply Hoare_forset with
      (P := fun (_: V -> Prop) (s: @SCCSt V) => dfn_inv s /\ fa_visited s /\ dfn_valid s root).
    + (* ProperP *)
      intros done1 done2 Hdone s1 s2 Heq. subst s2. reflexivity.
    + (* Step case: for each vertex a, the body preserves the invariant *)
      intros done a Hdone_sub Huniv Hnot_done.
      unfold_op. intro_state. hoare_auto_s.
      * (* a ∉ visited s0 — execute tarjan_scc a *)
        apply Hoare_conj with
          (Q1 := fun _ s => dfn_inv s)
          (Q2 := fun _ s => fa_visited s /\ dfn_valid s root).
        -- (* Q1: dfn_inv via tarjan_scc_keep_dfn_inv *)
           eapply Hoare_conseq_pre.
           2: apply (tarjan_scc_keep_dfn_inv a).
           intros s' Heq. subst s'. destruct H as [Hinv _]. exact Hinv.
        -- (* Q2: fa_visited /\ dfn_valid *)
           apply Hoare_conj with
             (Q1 := fun _ s => fa_visited s)
             (Q2 := fun _ s => dfn_valid s root).
           ++ (* fa_visited via tarjan_scc_keep_fa_visited *)
              eapply Hoare_conseq_pre.
              2: apply (tarjan_scc_keep_fa_visited a).
              intros s' Heq. subst s'. destruct H as [_ [Hfa _]]. exact Hfa.
           ++ (* dfn_valid via tarjan_scc_keep_dfn_valid *)
              eapply Hoare_conseq_post.
              2: { eapply Hoare_conseq_pre.
                   2: apply (tarjan_scc_keep_dfn_valid a).
                   intros s' Heq. subst s'.
                   destruct H as [Hinv [Hfa Hvalid]].
                   split; [exact H1 | split; [exact Hvalid | split; [exact Hinv | exact Hfa]]]. }
              intros _ s [Hvalid _]. exact Hvalid.
      * (* a ∈ visited s0 — skip *)
        destruct H1 as [Heq _]. subst s. exact H.
Qed.

Lemma dfn_unique (s: @SCCSt V):
  dfn_inv s -> dfn_injective s ->
  forall x y, dfn s x = dfn s y -> x = y \/ (~ x ∈ visited s /\ ~ y ∈ visited s).
Proof.
  intros Hinv Hinj x y Heq.
  destruct Hinv as [Hlt [Hiff Hpos]].
  destruct (classic (x = y)) as [Hxy | Hxy].
  { left. exact Hxy. }
  right. split.
  - intro Hxv.
    destruct (classic (y ∈ visited s)) as [Hyv | Hnyv].
    + exfalso. apply (Hinj x y Hxy Hxv Hyv). exact Heq.
    + exfalso.
      assert (Hdfn_x_nonzero: dfn s x <> 0). {
        intro Hzero. apply (proj1 (Hiff x)) in Hzero. exact (Hzero Hxv). }
      assert (Hdfn_y_zero: dfn s y = 0). {
        apply (proj2 (Hiff y)). exact Hnyv. }
      apply Hdfn_x_nonzero. rewrite Heq. exact Hdfn_y_zero.
  - intro Hyv.
    destruct (classic (x ∈ visited s)) as [Hxv | Hnxv].
    + exfalso. apply (Hinj x y Hxy Hxv Hyv). exact Heq.
    + exfalso.
      assert (Hdfn_y_nonzero: dfn s y <> 0). {
        intro Hzero. apply (proj1 (Hiff y)) in Hzero. exact (Hzero Hyv). }
      assert (Hdfn_x_zero: dfn s x = 0). {
        apply (proj2 (Hiff x)). exact Hnxv. }
      apply Hdfn_y_nonzero. rewrite <- Heq. exact Hdfn_x_zero.
Qed.

(* ================================================================ *)
(* stack_dfn_order — Stack ordered by dfn (non-increasing top→bottom) *)
(* ================================================================ *)

(** The stack is ordered by discovery time: vertices closer to the top
    were discovered later, hence have larger dfn.  Formally, for any
    [x], [y] on the stack, if [x] appears before [y] (scanning from
    the top), then [dfn s y <= dfn s x]. *)
Definition stack_dfn_order (s: @SCCSt V) : Prop :=
  forall x y, In x (stack s) -> In y (stack s) ->
    (exists l1 l2, stack s = l1 ++ x :: l2 /\ In y l2) ->
    dfn s y <= dfn s x.

Lemma stack_dfn_order_init: stack_dfn_order initSt.
Proof.
  unfold stack_dfn_order, initSt. simpl.
  intros x y Hx Hy. destruct Hx.
Qed.

(* ---------------------------------------------------------------- *)
(* Stack-split decomposition lemmas                                  *)
(* ---------------------------------------------------------------- *)

Lemma stack_split_at_decomp (stk: list V) (u: V):
  In u stk ->
  forall popped rest,
    stack_split_at stk u = (popped, rest) ->
    exists prefix, stk = prefix ++ u :: rest.
Proof.
  induction stk as [| x xs IH] in u |- *; intros Hu_in popped rest Hsplit.
  { destruct Hu_in. }
  { simpl in Hsplit. destruct (equiv_decb x u) eqn:Heq_xu.
    - inversion Hsplit. subst popped rest. clear Hsplit.
      unfold equiv_decb in Heq_xu. destruct (equiv_dec x u) as [Heq | Hneq];
        [| discriminate Heq_xu].
      rewrite Heq. exists (@nil V). reflexivity.
    - destruct (stack_split_at xs u) as (popped', rest') eqn:Hsplit_inner.
      inversion Hsplit. subst popped rest. clear Hsplit.
      destruct Hu_in as [Hx_eq_u | Hu_in_xs].
      + exfalso. unfold equiv_decb in Heq_xu.
        destruct (equiv_dec x u) as [Heq' | Hneq]; [discriminate Heq_xu | apply Hneq; exact Hx_eq_u].
      + destruct (IH u Hu_in_xs popped' rest' Hsplit_inner) as (prefix & ->).
        exists (x :: prefix). reflexivity. }
Qed.

Lemma stack_split_at_rest_before (stk: list V) (u: V):
  In u stk ->
  forall popped rest,
    stack_split_at stk u = (popped, rest) ->
    forall x y, (exists l1 l2, rest = l1 ++ x :: l2 /\ In y l2) ->
    (exists l1 l2, stk = l1 ++ x :: l2 /\ In y l2).
Proof.
  intros Hu_in popped rest Hsplit x y [l1 [l2 [Hrest_eq Hy_in]]].
  destruct (stack_split_at_decomp stk u Hu_in popped rest Hsplit) as (prefix & Hstk_eq).
  exists (prefix ++ u :: l1). exists l2. split.
  { rewrite Hstk_eq, Hrest_eq. rewrite <- app_assoc. reflexivity. }
  { exact Hy_in. }
Qed.

(* ---------------------------------------------------------------- *)
(* Preservation lemmas                                               *)
(* ---------------------------------------------------------------- *)

Lemma preloop_preserves_stack_dfn_order (u: V):
  Hoare (fun s: @SCCSt V => stack_dfn_order s /\ dfn_inv s /\ stack_in_visited s /\ ~ u ∈ visited s)
        (preloop u)
        (fun _ s => stack_dfn_order s).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s. subst s. simpl.
  destruct H as [Horder [Hinv [Hsiv Hnu_vis]]]. destruct Hinv as [Hlt [Hiff Hpos]].
  unfold stack_dfn_order. simpl.
  intros x y Hx_in Hy_in [l1 [l2 [Hstk_eq Hy_in_l2]]].
  simpl in Hstk_eq.
  assert (Hnu_stack: ~ In u (stack s0)). { intro Hu_stk. apply Hsiv in Hu_stk. exact (Hnu_vis Hu_stk). }
  destruct Hx_in as [Hx_eq_u | Hx_in_s0].
  { (* Case 1: x = u (new head). RHS = timer s0. *)
    rewrite <- Hx_eq_u. simpl. unfold equiv_decb.
    destruct (equiv_dec x x) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
    destruct l1 as [| a l1'].
    { simpl in Hstk_eq. injection Hstk_eq as ->.
      destruct Hy_in as [Hy_eq_x | Hy_in_s0].
      { rewrite <- Hy_eq_x. simpl. unfold equiv_decb.
        destruct (equiv_dec x x) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
        reflexivity. }
      { assert (Hy_vis: y ∈ visited s0) by (apply Hsiv; exact Hy_in_s0).
        assert (Hy_lt: dfn s0 y < timer s0) by (apply Hlt; exact Hy_vis).
        unfold equiv_decb. destruct (equiv_dec y x) as [Hy_eq_x' | _].
        { rewrite Hy_eq_x' in Hy_vis. exfalso. apply Hnu_vis. exact Hy_vis. }
        { unfold equiv_decb. destruct (equiv_dec x x) as [_ | Hc]; [| exfalso; apply Hc; reflexivity]. lia. } } }
    { simpl in Hstk_eq. injection Hstk_eq as [= -> Hrest].
      exfalso. apply Hnu_stack. rewrite Hrest.
      rewrite List.in_app_iff. right. simpl. left. symmetry. exact Hx_eq_u. } }
  { (* Case 2: x ∈ stack s0. *)
    destruct l1 as [| a l1'].
    { simpl in Hstk_eq. injection Hstk_eq as [= -> _]. exfalso. apply Hnu_stack. exact Hx_in_s0. }
    { simpl in Hstk_eq. injection Hstk_eq as [= -> Hstk_eq'].
      assert (Hy_in_s0: In y (stack s0)). {
        destruct Hy_in as [Hy_eq_a | Hy_in_s0'].
        { rewrite <- Hy_eq_a. exfalso. apply Hnu_stack. rewrite Hstk_eq'.
          rewrite List.in_app_iff. right. simpl. right.
          rewrite <- Hy_eq_a in Hy_in_l2. exact Hy_in_l2. }
        { exact Hy_in_s0'. } }
      simpl. unfold equiv_decb.
      destruct (equiv_dec x a) as [Hx_eq_a' | _].
      { rewrite Hx_eq_a' in Hx_in_s0. exfalso. apply Hnu_stack. exact Hx_in_s0. }
      destruct (equiv_dec y a) as [Hy_eq_a' | _].
      { rewrite Hy_eq_a' in Hy_in_s0. exfalso. apply Hnu_stack. exact Hy_in_s0. }
      apply (Horder x y).
      { rewrite Hstk_eq'. rewrite List.in_app_iff. right. simpl. left. reflexivity. }
      { exact Hy_in_s0. }
      { exists l1'. exists l2. split; [exact Hstk_eq' | exact Hy_in_l2]. } } }
Qed.

Lemma pop_scc_preserves_stack_dfn_order (u: V):
  Hoare (fun s: @SCCSt V => stack_dfn_order s /\ In u (stack s))
        (pop_scc u)
        (fun _ s => stack_dfn_order s).
Proof.
  unfold pop_scc. intro_state. hoare_auto_s.
  subst s. unfold pop_scc_state.
  destruct (stack_split_at (stack s0) u) as (popped, rest) eqn:Hsplit. simpl.
  destruct H as [Horder Hu_in].
  unfold stack_dfn_order. simpl.
  intros x y Hx_in Hy_in [l1 [l2 [Hrest_eq Hy_in_l2]]].
  destruct (stack_split_at_decomp (stack s0) u Hu_in popped rest Hsplit) as (prefix & Hstk_eq).
  apply (Horder x y).
  - rewrite Hstk_eq, List.in_app_iff. right. simpl. right. exact Hx_in.
  - rewrite Hstk_eq, List.in_app_iff. right. simpl. right. exact Hy_in.
  - exists (prefix ++ u :: l1). exists l2. split.
    { rewrite Hstk_eq, Hrest_eq. rewrite <- app_assoc. reflexivity. }
    { exact Hy_in_l2. }
Qed.

(** [preloop_preserves_dfn_injective]: [preloop u] preserves
    [dfn_injective].  The new vertex [u] gets [dfn s u = timer s]
    (the largest dfn value so far, from [dfn_inv]), so its dfn
    is unique among visited vertices.  Previously visited vertices
    keep their dfn values. *)
Lemma preloop_preserves_dfn_injective (u: V):
  Hoare (fun s: @SCCSt V => dfn_injective s /\ dfn_inv s /\ ~ u ∈ visited s)
        (preloop u)
        (fun _ s => dfn_injective s).
Proof.
  intro_state. destruct H as [Hinj [Hinv Hnu_vis]].
  destruct Hinv as [Hlt [Hiff Hpos]].
  unfold preloop. unfold_op. hoare_auto_s. subst s. simpl.
  assert (Hdfn_u0: dfn s0 u = 0) by (apply (proj2 (Hiff u)); exact Hnu_vis).
  unfold dfn_injective. intros x y Hneq Hx_vis Hy_vis.
  sets_unfold in Hx_vis. sets_unfold in Hy_vis.
  destruct Hx_vis as [Hx_vis_s0 | Hx_eq_u]; destruct Hy_vis as [Hy_vis_s0 | Hy_eq_u].
  - (* both were already visited: dfn unchanged, use Hinj *)
    simpl. unfold equiv_decb.
    destruct (equiv_dec x u) as [Hx_eq_u' | Hx_ne_u']; [exfalso; apply Hnu_vis; rewrite <- Hx_eq_u'; exact Hx_vis_s0 |].
    destruct (equiv_dec y u) as [Hy_eq_u' | Hy_ne_u']; [exfalso; apply Hnu_vis; rewrite <- Hy_eq_u'; exact Hy_vis_s0 |].
    apply (Hinj x y Hneq Hx_vis_s0 Hy_vis_s0).
  - (* x visited, y = u *)
    subst y. simpl. unfold equiv_decb.
    assert (Hx_lt: dfn s0 x < timer s0) by (apply Hlt; exact Hx_vis_s0).
    rewrite Hdfn_u0.
    destruct (equiv_dec x u) as [Hx_eq_u2 | Hx_ne_u2]; simpl.
    { destruct (equiv_dec u u) as [_ | Hc]; simpl; [| exfalso; apply Hc; reflexivity].
      intro Heq. exfalso. apply Hnu_vis. rewrite <- Hx_eq_u2. exact Hx_vis_s0. }
    { destruct (equiv_dec u u) as [_ | Hc]; simpl; [| exfalso; apply Hc; reflexivity].
      intro Heq. rewrite Heq in Hx_lt. lia. }
  - (* x = u, y visited *)
    subst x. simpl. unfold equiv_decb.
    assert (Hy_lt: dfn s0 y < timer s0) by (apply Hlt; exact Hy_vis_s0).
    rewrite Hdfn_u0.
    destruct (equiv_dec u u) as [_ | Hc]; simpl; [| exfalso; apply Hc; reflexivity].
    destruct (equiv_dec y u) as [Hy_eq_u2 | Hy_ne_u2]; simpl.
    { intro Heq. exfalso. apply Hnu_vis. rewrite <- Hy_eq_u2. exact Hy_vis_s0. }
    { intro Heq. rewrite Heq in Hy_lt. lia. }
  - (* both x and y equal u → contradiction *)
    subst x. subst y. exfalso. apply Hneq. reflexivity.
Qed.

Lemma set_fa_keep_dfn_injective (v p: V):
  Hoare (fun s: @SCCSt V => dfn_injective s)
        (set_fa v p)
        (fun _ s => dfn_injective s).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. auto.
Qed.

Lemma update_low_keep_dfn_injective (u: V) (n: nat):
  Hoare (fun s: @SCCSt V => dfn_injective s)
        (update_low u n)
        (fun _ s => dfn_injective s).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  { subst s. simpl. auto. }
  { destruct H1. subst s. auto. }
Qed.

Lemma process_edge_keep_dfn_injective (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_injective s) (W x) (fun _ s => dfn_injective s)) ->
  Hoare (fun s: @SCCSt V => dfn_injective s)
        (process_edge u W v)
        (fun _ s => dfn_injective s).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state.
  apply Hoare_choice.
  - apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => dfn_injective s).
    { intros sx [Hnv Hsx]. subst sx. exact H. }
    hoare_bind (set_fa_keep_dfn_injective v u). simpl. clear a.
    eapply Hoare_bind. { apply HW. } simpl. intros _.
    intro_state.
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    apply Hoare_conseq_pre with (P2 := fun s => dfn_injective s).
    { intros sx Hsx. destruct Hsx. subst sx. simpl. auto. }
    apply (update_low_keep_dfn_injective u lv).
  - intro_state. hoare_auto_s.
    + apply Hoare_conseq_pre with (P2 := fun s => dfn_injective s).
      { intros sx Hsx. subst sx. exact H. }
      apply (update_low_keep_dfn_injective u (dfn s0 v)).
    + destruct H3 as [Heq Hnn]. subst s. subst s1. exact H.
Qed.

Lemma forset_process_edge_keep_dfn_injective (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_injective s) (W x) (fun _ s => dfn_injective s)) ->
  Hoare (fun s: @SCCSt V => dfn_injective s)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => dfn_injective s).
Proof.
  intros HW.
  unfold forset. hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
  eapply Hoare_bind with (R := fun (_: unit) s => dfn_injective s).
  { apply Hoare_conseq_pre with (P2 := fun s => dfn_injective s).
    { intros s1 Hs1. subst s1. exact H. }
    apply (process_edge_keep_dfn_injective u a W). intros x. apply HW. }
  simpl. intros _. apply IH0.
Qed.

(** Combined lemma: [process_edge] preserves [dfn_injective /\ dfn_inv].
    The callback [W] is required to preserve the combined invariant under the
    stronger precondition [dfn_injective /\ dfn_inv /\ ~x ∈ visited], which
    matches the IH we obtain from [Hoare_normal_LFix] for the outer
    [tarjan_scc] fixpoint. *)
Lemma process_edge_keep_dfn_injective_inv (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_injective s /\ dfn_inv s /\ ~ x ∈ visited s)
                   (W x)
                   (fun _ s => dfn_injective s /\ dfn_inv s)) ->
  Hoare (fun s: @SCCSt V => dfn_injective s /\ dfn_inv s)
        (process_edge u W v)
        (fun _ s => dfn_injective s /\ dfn_inv s).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state. destruct H as [Hinj Hinv].
  apply Hoare_choice.
  - (* Tree-edge: ~ v ∈ visited *)
    apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => dfn_injective s /\ dfn_inv s /\ ~ v ∈ visited s).
    { intros s' [Hnv Hs']. subst s'. split; [| split]; auto. }
    (* set_fa v u: preserves dfn_injective, dfn_inv, and ~v ∈ visited *)
    assert (H_setfa_inj : Hoare (fun s => dfn_injective s /\ dfn_inv s /\ ~ v ∈ visited s)
                                (set_fa v u) (fun _ s => dfn_injective s)).
    { eapply Hoare_conseq_pre. 2: apply (set_fa_keep_dfn_injective v u).
      intros s [Hinj1 [Hinv1 Hnv1]]. exact Hinj1. }
    assert (H_setfa_inv : Hoare (fun s => dfn_injective s /\ dfn_inv s /\ ~ v ∈ visited s)
                                (set_fa v u) (fun _ s => dfn_inv s)).
    { eapply Hoare_conseq_pre. 2: apply (set_fa_keep_dfn_inv v u).
      intros s [Hinj1 [Hinv1 Hnv1]]. exact Hinv1. }
    assert (H_setfa_nv_base : Hoare (fun s => ~ v ∈ visited s) (set_fa v u) (fun _ s => ~ v ∈ visited s)).
    { unfold set_fa. intro_state. hoare_auto_s. subst s. simpl. auto. }
    assert (H_setfa_nv : Hoare (fun s => dfn_injective s /\ dfn_inv s /\ ~ v ∈ visited s)
                                (set_fa v u) (fun _ s => ~ v ∈ visited s)).
    { eapply Hoare_conseq_pre. 2: exact H_setfa_nv_base.
      intros s [_ [_ Hnv]]. exact Hnv. }
    assert (H_setfa : Hoare (fun s => dfn_injective s /\ dfn_inv s /\ ~ v ∈ visited s)
                            (set_fa v u)
                            (fun _ s => dfn_injective s /\ dfn_inv s /\ ~ v ∈ visited s)).
    { apply Hoare_conj with (Q1 := fun _ s => dfn_injective s) (Q2 := fun _ s => dfn_inv s /\ ~ v ∈ visited s).
      { exact H_setfa_inj. }
      { apply Hoare_conj with (Q1 := fun _ s => dfn_inv s) (Q2 := fun _ s => ~ v ∈ visited s).
        { exact H_setfa_inv. }
        { exact H_setfa_nv. } } }
    hoare_bind H_setfa. simpl. clear a.
    (* W v: the precondition (dfn_injective /\ dfn_inv /\ ~v ∈ visited) matches HW *)
    eapply Hoare_bind.
    { apply (HW v). }
    simpl. intros _.
    (* get_low_update_low: preserve dfn_injective /\ dfn_inv *)
    apply Hoare_conj.
    { intro_state. eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
      apply Hoare_conseq_pre with (P2 := fun s => dfn_injective s).
      { intros s' Hs'. destruct Hs'. subst s'. destruct H as [Hinj' Hinv']. exact Hinj'. }
      apply (update_low_keep_dfn_injective u lv). }
    { intro_state. eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
      apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
      { intros s' Hs'. destruct Hs'. subst s'. destruct H as [Hinj' Hinv']. exact Hinv'. }
      apply (update_low_keep_dfn_inv u lv). }
  - (* Non-tree-edge: v ∈ visited *)
    intro_state. hoare_auto_s.
    + (* v ∈ stack: update_low u (dfn s0 v) *)
      apply Hoare_conj.
      { apply Hoare_conseq_pre with (P2 := fun s => dfn_injective s).
        { intros s' Hs'. subst s'. exact Hinj. }
        apply (update_low_keep_dfn_injective u (dfn s0 v)). }
      { apply Hoare_conseq_pre with (P2 := fun s => dfn_inv s).
        { intros s' Hs'. subst s'. exact Hinv. }
        apply (update_low_keep_dfn_inv u (dfn s0 v)). }
    + (* skip *)
      destruct H2 as [Heq _]. subst s. subst s1. split; auto.
Qed.

Lemma forset_process_edge_keep_dfn_injective_inv (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => dfn_injective s /\ dfn_inv s /\ ~ x ∈ visited s)
                   (W x)
                   (fun _ s => dfn_injective s /\ dfn_inv s)) ->
  Hoare (fun s: @SCCSt V => dfn_injective s /\ dfn_inv s)
        (forset (fun v => dg_step g u v) (process_edge u W))
        (fun _ s => dfn_injective s /\ dfn_inv s).
Proof.
  intros HW.
  unfold forset. hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
  eapply Hoare_bind with (R := fun (_: unit) s => dfn_injective s /\ dfn_inv s).
  { apply Hoare_conseq_pre with (P2 := fun s => dfn_injective s /\ dfn_inv s).
    { intros s1 Hs1. subst s1. exact H. }
    apply (process_edge_keep_dfn_injective_inv u a W). intros x. apply HW. }
  simpl. intros _. apply IH0.
Qed.

(** Helper: convert [Hoare_normal_LFix_closed] IH (which is parameterised by
    the initial state [s0] and requires [R s0]) into a standard Hoare triple
    with an explicit precondition. *)
Lemma normal_LFix_closed_IH_to_standard (W: V -> program (@SCCSt V) unit)
  (R: SCCSt -> Prop)
  (Q: V -> SCCSt -> unit -> SCCSt -> Prop)
  (H_ih: forall s0 a, R s0 -> Hoare (fun s => s = s0) (W a) (Q a s0))
  (P: V -> SCCSt -> Prop)
  (Q_std: unit -> SCCSt -> Prop)
  (H_imp: forall a s0 s', R s0 -> P a s0 -> Q a s0 tt s' -> Q_std tt s'):
  forall a, Hoare (fun s => R s /\ P a s) (W a) (fun _ s' => Q_std tt s').
Proof.
  intros a.
  unfold Hoare. sets_unfold.
  intros s1 b s2 [HR HP] Hprog.
  specialize (H_ih s1 a HR).
  unfold Hoare in H_ih. sets_unfold in H_ih.
  apply H_ih in Hprog; [| reflexivity].
  destruct b.
  eapply H_imp; eauto.
Qed.

Theorem tarjan_scc_keep_dfn_injective (u: V):
  Hoare (fun s: @SCCSt V => dfn_injective s /\ dfn_inv s /\ ~ u ∈ visited s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => dfn_injective s).
Proof.
  (* First prove a richer version with dfn_inv in the postcondition *)
  cut (Hoare (fun s: @SCCSt V => dfn_injective s /\ dfn_inv s /\ ~ u ∈ visited s)
             (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
             (fun _ s => dfn_injective s /\ dfn_inv s)).
  { intros H. eapply Hoare_conseq_post; [| apply H]. intros _ s [Hinj _]. exact Hinj. }
  (* Prove the richer version using hoare_fix_nolv_auto *)
  unfold tarjan_scc. hoare_fix_nolv_auto V.
  clear u. intros W IH u.
  unfold tarjan_scc_f.
  (* IH: forall a, Hoare (dfn_injective /\ dfn_inv /\ ~a ∈ visited) (W a)
                          (dfn_injective /\ dfn_inv) *)
  (* Step 1: preloop u *)
  eapply Hoare_bind.
  { apply Hoare_conj.
    - eapply Hoare_conseq_pre. 2: apply preloop_preserves_dfn_injective.
      intros s [Hinj [Hinv Hnv]]. split; [exact Hinj | split; [exact Hinv | exact Hnv]].
    - eapply Hoare_conseq_pre. 2: apply preloop_keep_dfn_inv.
      intros s [Hinj [Hinv Hnv]]. exact Hinv. }
  simpl. intros _. intro_state.
  destruct H as [Hinj_mid Hinv_mid].
  (* Step 2: forset *)
  eapply Hoare_bind with (R := fun _ s => dfn_injective s /\ dfn_inv s).
  { apply Hoare_conseq_pre with (P2 := fun s => dfn_injective s /\ dfn_inv s).
    { intros s1 Hs1. subst s1. split; [exact Hinj_mid | exact Hinv_mid]. }
    apply (forset_process_edge_keep_dfn_injective_inv u W).
    intros a. apply IH. }
  simpl. intros _. intro_state.
  destruct H as [Hinj_mid2 Hinv_mid2].
  (* Step 3: If low u = dfn u then pop_scc u *)
  hoare_auto_s.
  - (* pop_scc u *)
    apply Hoare_conj.
    + (* dfn_injective: pop_scc only modifies stack, not dfn or visited *)
      unfold pop_scc. intro_state. hoare_auto_s.
      subst s2. subst s.
      unfold pop_scc_state.
      destruct (stack_split_at (stack s1) u) as [popped rest] eqn:?.
      simpl. exact Hinj_mid2.
    + eapply Hoare_conseq_pre. 2: apply pop_scc_keep_dfn_inv.
      intros s Hs. rewrite Hs. exact Hinv_mid2.
  - (* skip *)
    destruct H as [Heq _]. rewrite Heq.
    split; [exact Hinj_mid2 | exact Hinv_mid2].
Qed.

Theorem tarjan_scc_all_keep_dfn_injective:
  Hoare (fun s: @SCCSt V => dfn_injective s /\ dfn_inv s)
        (tarjan_scc_all g)
        (fun _ s => dfn_injective s).
Proof.
  unfold tarjan_scc_all.
  apply Hoare_conseq with
    (P2 := fun s => dfn_injective s /\ dfn_inv s)
    (Q2 := fun _ s => dfn_injective s /\ dfn_inv s).
  - intros s H. exact H.
  - intros _ s [Hinj Hinv]. exact Hinj.
  - apply Hoare_forset with
      (P := fun (_: V -> Prop) (s: @SCCSt V) => dfn_injective s /\ dfn_inv s).
    + intros done1 done2 Hdone s1 s2 Heq. subst s2. reflexivity.
    + intros done a Hdone_sub Huniv Hnot_done.
      unfold_op. intro_state. hoare_auto_s.
      * (* a ∉ visited s0 — execute tarjan_scc a *)
        apply Hoare_conj with
          (Q1 := fun _ s => dfn_injective s)
          (Q2 := fun _ s => dfn_inv s).
        -- (* dfn_injective via tarjan_scc_keep_dfn_injective *)
           eapply Hoare_conseq_pre.
           2: apply (tarjan_scc_keep_dfn_injective a).
           intros s' Heq. subst s'. destruct H as [Hinj Hinv].
           split; [exact Hinj | split; [exact Hinv | exact H1]].
        -- (* dfn_inv via tarjan_scc_keep_dfn_inv *)
           eapply Hoare_conseq_pre.
           2: apply (tarjan_scc_keep_dfn_inv a).
           intros s' Heq. subst s'. destruct H as [_ Hinv]. exact Hinv.
      * (* a ∈ visited s0 — skip *)
        destruct H1 as [Heq _]. subst s. exact H.
Qed.

(** [preloop_after_visited_dfn_lt]: If [u] is already visited and we then
    execute [preloop v], the dfn of [u] is strictly smaller than the newly
    assigned dfn of [v].  This captures the timer/dfn monotonicity:
    when [preloop v] runs the timer is already larger than the timer value
    that was assigned to [u]. *)
Lemma preloop_after_visited_dfn_lt (u v: V):
  Hoare (fun s: @SCCSt V => u ∈ visited s /\ ~ v ∈ visited s /\ dfn_inv s)
        (preloop v)
        (fun _ s => dfn s u < dfn s v).
Proof.
  intro_state. destruct H as [Hu_vis [Hv_nvis Hinv]].
  destruct Hinv as [Hlt Hiff Hpos].
  unfold preloop. unfold_op. hoare_auto_s. subst s. simpl.
  unfold equiv_decb.
  destruct (equiv_dec u v) as [Heq | Hneq].
  - exfalso. rewrite Heq in Hu_vis. apply Hv_nvis. exact Hu_vis.
  - destruct (equiv_dec v v) as [Heqvv | Hneqq];
      [simpl; apply Hlt; exact Hu_vis | exfalso; apply Hneqq; reflexivity].
Qed.

(** [stack_dfn_order_strict]: With [dfn_injective] and
    [stack_in_visited], two distinct stack vertices at different
    positions have strictly different dfn values: if [x] is above
    [y] then [dfn s y < dfn s x]. *)
Lemma stack_dfn_order_strict (s: @SCCSt V):
  stack_in_visited s -> stack_dfn_order s -> dfn_injective s ->
  forall x y, In x (stack s) -> In y (stack s) ->
    (exists l1 l2, stack s = l1 ++ x :: l2 /\ In y l2) ->
    x <> y -> dfn s y < dfn s x.
Proof.
  intros Hsiv Hord Hinj x y Hx_stk Hy_stk Habove Hneq.
  assert (Hle: dfn s y <= dfn s x) by (apply (Hord x y Hx_stk Hy_stk Habove)).
  assert (Hneq_dfns: dfn s x <> dfn s y).
  { apply (Hinj x y Hneq); apply Hsiv; assumption. }
  lia.
Qed.

(** [fa_parent_dfn_lt]: If [u] is the DFS parent of [v]
    (i.e. [fa s v = u /\ fa s v ≠ v]), [v] is visited, and the
    original graph has the edge [u → v], then [dfn s u < dfn s v].
    This follows directly from the tree-edge characterization and
    [dfn_valid]. *)
Lemma fa_parent_dfn_lt (s: @SCCSt V) (u v: V):
  fa s v = u -> fa s v <> v -> dg_step g u v -> v ∈ visited s ->
  dfn_valid s root -> dfn s u < dfn s v.
Proof.
  intros Hfa_eq Hfa_ne Hdg Hvvis Hvalid.
  eapply Hvalid.
  eapply tree_step_char_backward with (s := s) (x := u) (y := v); eauto.
Qed.

(** [tarjan_scc_keep_in_stack_below]: [tarjan_scc g u] preserves
    [In w (stack s)] for any vertex [w] that is on the stack and
    visited (hence has [dfn s w < timer s]).  After [preloop u],
    [dfn s u] becomes the old timer, so [dfn s w < dfn s u] and
    [pop_scc u] (if called) does not remove [w] because [w] lies
    below [u] on the stack. *)
Lemma preloop_keep_in_stack (u w: V):
  Hoare (fun s: @SCCSt V => In w (stack s))
        (preloop u)
        (fun _ s => In w (stack s)).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl. auto.
Qed.

Lemma set_fa_keep_in_stack (v p w: V):
  Hoare (fun s: @SCCSt V => In w (stack s))
        (set_fa v p)
        (fun _ s => In w (stack s)).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. auto.
Qed.

Lemma pop_scc_keep_in_stack_below (u w: V):
  Hoare (fun s: @SCCSt V => In w (stack s) /\
          (forall popped rest, stack_split_at (stack s) u = (popped, rest) -> In w rest))
        (pop_scc u)
        (fun _ s => In w (stack s)).
Proof.
  unfold pop_scc. intro_state. hoare_auto_s.
  destruct H as [Hin Hrest].
  subst s. unfold pop_scc_state.
  destruct (stack_split_at (stack s0) u) as [popped rest] eqn:Hsplit.
  simpl. apply Hrest with (popped := popped) (rest := rest).
  reflexivity.
Qed.

Lemma update_low_keep_in_stack (u w: V) (n: nat):
  Hoare (fun s: @SCCSt V => In w (stack s))
        (update_low u n)
        (fun _ s => In w (stack s)).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  - subst s. simpl. exact H.
  - destruct H1 as [Heq _]. subst s. exact H.
Qed.

Lemma get_low_update_low_keep_in_stack (u v w: V):
  Hoare (fun s: @SCCSt V => In w (stack s))
        (lv <- get' (fun s => low s v);; update_low u lv)
        (fun _ s => In w (stack s)).
Proof.
  intro_state. eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
  apply Hoare_conseq_pre with (P2 := fun s => In w (stack s)).
  { intros s' Hs'. destruct Hs'. subst s'. exact H. }
  apply (update_low_keep_in_stack u w lv).
Qed.

Lemma process_edge_keep_in_stack (u v w: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => In w (stack s)) (W x) (fun _ s => In w (stack s))) ->
  Hoare (fun s: @SCCSt V => In w (stack s))
        (process_edge u W v)
        (fun _ s => In w (stack s)).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state.
  apply Hoare_choice.
  - apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => In w (stack s)).
    { intros s' [Hnv Hs']. subst s'. exact H. }
    hoare_bind (set_fa_keep_in_stack v u w). simpl. clear a.
    eapply Hoare_bind. { apply HW. } simpl. intros _.
    apply get_low_update_low_keep_in_stack.
  - intro_state. hoare_auto_s.
    + apply Hoare_conseq_pre with (P2 := fun s => In w (stack s)).
      { intros s' Hs'. subst s'. exact H. }
      apply (update_low_keep_in_stack u w (dfn s0 v)).
    + destruct H3 as [Heq Hnn]. subst s. rewrite H1. exact H.
Qed.

Lemma forset_process_edge_keep_in_stack (u w: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => In w (stack s)) (W x) (fun _ s => In w (stack s))) ->
  Hoare (fun s: @SCCSt V => In w (stack s))
        (forset (fun v => dg_step g u v) (process_edge u W))
        (fun _ s => In w (stack s)).
Proof.
  intros HW.
  unfold forset. hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
  eapply Hoare_bind with (R := fun (_: unit) s => In w (stack s)).
  { apply Hoare_conseq_pre with (P2 := fun s => In w (stack s)).
    { intros s1 Hs1. subst s1. exact H. }
    apply (process_edge_keep_in_stack u a w W). intros x. apply HW. }
  simpl. intros _. apply IH0.
Qed.

Lemma tarjan_scc_keep_in_stack_below (u w: V):
  Hoare (fun s: @SCCSt V => In w (stack s) /\ ~ u ∈ visited s /\
          dfn_inv s /\ stack_in_visited s /\ stack_dfn_order s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => In w (stack s)).
Proof.
  (* TODO: Full proof via [hoare_fix_nolv_auto] with
     process_edge_keep_in_stack composed from set_fa_keep_in_stack
     and IH.  The critical sub-lemma is that after preloop u,
     u is on top and w is below u, so pop_scc u (if called) removes
     only vertices above w.  Admitted pending stack_dfn_order
     integration. *)
Admitted.

Lemma set_fa_keep_stack_dfn_order (v p: V):
  Hoare (fun s: @SCCSt V => stack_dfn_order s)
        (set_fa v p)
        (fun _ s => stack_dfn_order s).
Proof.
  unfold set_fa. intro_state. hoare_auto_s. subst s. simpl. exact H.
Qed.

Lemma set_low_keep_stack_dfn_order (v: V) (n: nat):
  Hoare (fun s: @SCCSt V => stack_dfn_order s)
        (set_low v n)
        (fun _ s => stack_dfn_order s).
Proof.
  unfold set_low. intro_state. hoare_auto_s. subst s. simpl. exact H.
Qed.

Lemma incr_timer_keep_stack_dfn_order:
  Hoare (fun s: @SCCSt V => stack_dfn_order s)
        (incr_timer)
        (fun _ s => stack_dfn_order s).
Proof.
  unfold incr_timer. intro_state. hoare_auto_s. subst s. simpl. exact H.
Qed.

Lemma update_low_keep_stack_dfn_order (u: V) (n: nat):
  Hoare (fun s: @SCCSt V => stack_dfn_order s)
        (update_low u n)
        (fun _ s => stack_dfn_order s).
Proof.
  unfold update_low. intro_state. hoare_auto_s.
  - unfold set_low. intro_state. hoare_auto_s. subst s1 s. simpl. exact H.
  - destruct H1 as [Heq _]. subst s. exact H.
Qed.

(* ================================================================ *)
(* 6. settled_closed — Forward-reachability closure for settled     *)
(*    vertices (those no longer on the stack).                      *)
(* ================================================================ *)

(** [settled_closed s]: every vertex that has been visited but is no
    longer on the stack has all its forward-reachable vertices also
    visited.  This is the Tarjan analogue of Kosaraju's
    [ReachRevClosed] — it guarantees that completed SCCs cannot reach
    unvisited vertices, blocking cross-subtree "old→new" pathologies. *)
Definition settled_closed (s: @SCCSt V): Prop :=
  forall v w, v ∈ visited s -> ~ In v (stack s) -> dg_reachable g v w -> w ∈ visited s.

Lemma settled_closed_init: settled_closed initSt.
Proof.
  unfold settled_closed, initSt. simpl.
  intros v w Hvis Hnstk Hreach. sets_unfold in Hvis. destruct Hvis.
Qed.

(** Primitive operations that do not change [visited] or [stack]
    trivially preserve [settled_closed]. *)

Lemma set_dfn_keep_settled_closed (v: V) (n: nat):
  Hoare (fun s: @SCCSt V => settled_closed s)
        (set_dfn v n)
        (fun _ s => settled_closed s).
Proof.
  unfold set_dfn. intro_state. hoare_auto_s.
  subst s. simpl. exact H.
Qed.

Lemma set_low_keep_settled_closed (v: V) (n: nat):
  Hoare (fun s: @SCCSt V => settled_closed s)
        (set_low v n)
        (fun _ s => settled_closed s).
Proof.
  unfold set_low. intro_state. hoare_auto_s.
  subst s. simpl. exact H.
Qed.

Lemma set_fa_keep_settled_closed (v p: V):
  Hoare (fun s: @SCCSt V => settled_closed s)
        (set_fa v p)
        (fun _ s => settled_closed s).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. exact H.
Qed.

Lemma incr_timer_keep_settled_closed:
  Hoare (fun s: @SCCSt V => settled_closed s)
        incr_timer
        (fun _ s => settled_closed s).
Proof.
  unfold incr_timer. intro_state. hoare_auto_s.
  subst s. simpl. exact H.
Qed.

Lemma update_low_keep_settled_closed (u: V) (n: nat):
  Hoare (fun s: @SCCSt V => settled_closed s)
        (update_low u n)
        (fun _ s => settled_closed s).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  - subst s. simpl. exact H.
  - destruct H1 as [Heq _]. subst s. exact H.
Qed.

(** [visit v] adds [v] to [visited] but [v] is already on the stack
    (pushed before [visit] in [preloop]), so the antecedent
    [~ In v (stack s)] is false for the new vertex. *)

Lemma visit_keep_settled_closed (v: V):
  Hoare (fun s: @SCCSt V => settled_closed s /\ In v (stack s))
        (visit v)
        (fun _ s => settled_closed s).
Proof.
  unfold visit. intro_state. hoare_auto_s.
  destruct H as [Hsc Hinstk].
  subst s. simpl.
  unfold settled_closed.
  intros x y Hxvis Hxnstk Hreach.
  simpl in Hxvis.
  sets_unfold in Hxvis.
  destruct Hxvis as [Hxvis0 | Hxeq].
  - (* x was already visited in s0 *)
    assert (Hxnstk0: ~ In x (stack s0)).
    { intro Hc. apply Hxnstk. simpl. exact Hc. }
    unfold settled_closed in Hsc.
    apply Hsc with (v := x) (w := y) in Hxvis0; [| exact Hxnstk0 | exact Hreach].
    simpl. sets_unfold. left. exact Hxvis0.
  - (* x = v, but x is on the stack — contradiction *)
    subst x. exfalso. apply Hxnstk. simpl. exact Hinstk.
Qed.

Lemma push_stack_keep_settled_closed (v: V):
  Hoare (fun s: @SCCSt V => settled_closed s)
        (push_stack v)
        (fun _ s => settled_closed s).
Proof.
  unfold push_stack. intro_state. hoare_auto_s.
  subst s. simpl.
  unfold settled_closed.
  intros x y Hxvis Hxnstk Hreach.
  (* visited unchanged by push_stack, so Hxvis: x ∈ visited s0 *)
  simpl in Hxvis.
  (* stack updated to v :: stack s0; Hxnstk: ~ In x (v :: stack s0) *)
  simpl in Hxnstk.
  (* Hxnstk: ~ (x = v \/ In x (stack s0)) *)
  (* So x ≠ v and x ∉ stack s0 *)
  assert (Hxnstk0: ~ In x (stack s0)).
  { intro Hc. apply Hxnstk. right. exact Hc. }
  unfold settled_closed in H.
  apply H with (v := x) (w := y) in Hxvis; [| exact Hxnstk0 | exact Hreach].
  simpl. exact Hxvis.
Qed.

Lemma preloop_keep_settled_closed (u: V):
  Hoare (fun s: @SCCSt V => settled_closed s)
        (preloop u)
        (fun _ s => settled_closed s).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl.
  (* After preloop, settled_closed must hold.
     The key: push_stack adds u to stack, then visit adds u to visited.
     Since u is on the stack, the settled_closed guard (~In u (stack)) is false for u.
     For other vertices, settled_closed is preserved. *)
  unfold settled_closed.
  intros x y Hxvis Hxnstk Hreach.
  (* visited after preloop: visited s0 ∪ {u} *)
  simpl in Hxvis. sets_unfold in Hxvis.
  destruct Hxvis as [Hxvis0 | Hxeq].
  - (* x was already visited in s0 *)
    simpl in Hxnstk.
    (* stack after preloop: u :: stack s0 *)
    (* If x is NOT on the new stack, then x ∉ stack s0 (and x ≠ u) *)
    assert (Hxnstk0: ~ In x (stack s0)).
    { intro Hc. apply Hxnstk. simpl. right. exact Hc. }
    unfold settled_closed in H.
    apply H with (v := x) (w := y) in Hxvis0; [| exact Hxnstk0 | exact Hreach].
    simpl. sets_unfold. left. exact Hxvis0.
  - (* x = u: but u is on top of the stack, contradicting Hxnstk *)
    subst x. exfalso. apply Hxnstk. simpl. left. reflexivity.
Qed.

(** Composition helpers for [process_edge] and beyond. *)

Lemma get_low_update_low_keep_settled_closed (u v: V):
  Hoare (fun s: @SCCSt V => settled_closed s)
        (lv <- get' (fun s => low s v);; update_low u lv)
        (fun _ s => settled_closed s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
  apply Hoare_conseq_pre with (P2 := fun s => settled_closed s).
  { intros s1 Hs1. destruct Hs1. subst s1. simpl. auto. }
  apply (update_low_keep_settled_closed u lv).
Qed.

Lemma get_dfn_update_low_keep_settled_closed (u v: V):
  Hoare (fun s: @SCCSt V => settled_closed s)
        (dv <- get' (fun s => dfn s v);; update_low u dv)
        (fun _ s => settled_closed s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
  apply Hoare_conseq_pre with (P2 := fun s => settled_closed s).
  { intros s1 Hs1. destruct Hs1. subst s1. simpl. auto. }
  apply (update_low_keep_settled_closed u dv).
Qed.

Lemma process_edge_keep_settled_closed (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => settled_closed s) (W x) (fun _ s => settled_closed s)) ->
  Hoare (fun s: @SCCSt V => settled_closed s)
        (process_edge u W v)
        (fun _ s => settled_closed s).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state.
  apply Hoare_choice.
  - apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => settled_closed s).
    { intros s1 [Hnv Hs1]. subst s1. exact H. }
    hoare_bind (set_fa_keep_settled_closed v u). simpl. clear a.
    eapply Hoare_bind. { apply HW. } simpl. intros _.
    apply get_low_update_low_keep_settled_closed.
  - intro_state. hoare_auto_s.
    + apply Hoare_conseq_pre with (P2 := fun s => settled_closed s).
      { intros s1 Hs1. subst s1. exact H. }
      apply (update_low_keep_settled_closed u (dfn s0 v)).
    + destruct H3 as [Heq Hnn]. subst s. subst s1. exact H.
Qed.

Lemma forset_process_edge_keep_settled_closed (u: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s => settled_closed s) (W x) (fun _ s => settled_closed s)) ->
  Hoare (fun s: @SCCSt V => settled_closed s)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => settled_closed s).
Proof.
  intros HW.
  unfold forset. hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
  eapply Hoare_bind with (R := fun (_: unit) s => settled_closed s).
  { apply Hoare_conseq_pre with (P2 := fun s => settled_closed s).
    { intros s1 Hs1. subst s1. exact H. }
    apply (process_edge_keep_settled_closed u a W). intros x. apply HW. }
  simpl. intros _. apply IH0.
Qed.

(* ================================================================ *)
(* 7. wf_scc_state — Composite global invariant                      *)
(* ================================================================ *)

(** [wf_scc_state s] packages four Layer-2 invariants into a
    single predicate: stack_in_visited, dfn_inv, dfn_valid, fa_visited.
    Note: [settled_closed] is deliberately excluded — its preservation
    at [pop_scc] requires low-link correctness (Layer 3). *)

Definition wf_scc_state (s: @SCCSt V): Prop :=
  stack_in_visited s /\ dfn_inv s /\ dfn_valid s root /\
  fa_visited s.

(** [wf_scc_state_pre u s]: the global invariants hold, but vertex [u]
    is not yet visited.  This is the state right before [preloop u]
    and right after [set_fa u p] (when [u] has been assigned a parent
    [p] but not yet visited).  In the latter case [dfn_valid s root]
    is still globally meaningful because the pending tree edge
    [p → u] does not yet need to satisfy the dfn order (it will after
    [preloop u]). *)

Definition wf_scc_state_pre (u: V) (s: @SCCSt V): Prop :=
  wf_scc_state s /\ ~ u ∈ visited s.

Lemma pop_scc_preserves_wf_scc_state (u: V):
  Hoare (fun s: @SCCSt V => wf_scc_state s)
        (pop_scc u)
        (fun _ s => wf_scc_state s).
Proof.
  unfold wf_scc_state.
  apply Hoare_conj with (Q1 := fun _ s => stack_in_visited s).
  { eapply Hoare_conseq_pre.
    2: apply (pop_scc_keep_stack_in_visited u).
    intros s [Hsiv _]. exact Hsiv. }
  apply Hoare_conj with (Q1 := fun _ s => dfn_inv s).
  { eapply Hoare_conseq_pre.
    2: apply (pop_scc_keep_dfn_inv u).
    intros s [_ [Hinv _]]. exact Hinv. }
  apply Hoare_conj with (Q1 := fun _ s => dfn_valid s root).
  { eapply Hoare_conseq_pre.
    2: apply (pop_scc_keep_dfn_valid u).
    intros s [_ [_ [Hvalid _]]]. exact Hvalid. }
  { eapply Hoare_conseq_pre.
    2: apply (pop_scc_keep_fa_visited u).
    intros s [_ [_ [_ Hfa]]]. exact Hfa. }
Qed.

Lemma preloop_preserves_wf_scc_state (u: V):
  Hoare (fun s: @SCCSt V => wf_scc_state_pre u s)
        (preloop u)
        (fun _ s => wf_scc_state s).
Proof.
  unfold wf_scc_state_pre, wf_scc_state.
  apply Hoare_conj with (Q1 := fun _ s => stack_in_visited s).
  { eapply Hoare_conseq_pre. 2: apply (preloop_keep_stack_in_visited u).
    intros s [[Hsiv _] _]. exact Hsiv. }
  apply Hoare_conj with (Q1 := fun _ s => dfn_inv s).
  { eapply Hoare_conseq_pre. 2: apply (preloop_keep_dfn_inv u).
    intros s [[_ [Hinv _]] _]. exact Hinv. }
  apply Hoare_conj with (Q1 := fun _ s => dfn_valid s root).
  { eapply Hoare_conseq_post.
    2: { eapply Hoare_conseq_pre.
         2: apply preloop_preserves_dfn_valid.
         intros s [[_ [Hinv [Hvalid Hfa]]] Hnv].
         split; [exact Hnv | split; [exact Hvalid | split; [exact Hinv | exact Hfa]]]. }
    intros _ s [Huvis [Hvalid Hinv]]. exact Hvalid. }
  { eapply Hoare_conseq_pre. 2: apply (preloop_keep_fa_visited u).
    intros s [[_ [_ [_ Hfa]]] _]. exact Hfa. }
Qed.

Lemma set_fa_preserves_wf_scc_state_pre (v u: V):
  Hoare (fun s: @SCCSt V => wf_scc_state s /\ u ∈ visited s /\ ~ v ∈ visited s)
        (set_fa v u)
        (fun _ s => wf_scc_state_pre v s /\ u ∈ visited s).
Proof.
  apply Hoare_conj with (Q1 := fun _ s => wf_scc_state_pre v s) (Q2 := fun _ s => u ∈ visited s).
  { unfold wf_scc_state_pre.
    apply Hoare_conj with (Q1 := fun _ s => wf_scc_state s) (Q2 := fun _ s => ~ v ∈ visited s).
    - (* wf_scc_state *)
      unfold wf_scc_state.
      apply Hoare_conj with (Q1 := fun _ s => stack_in_visited s)
        (Q2 := fun _ s => dfn_inv s /\ dfn_valid s root /\ fa_visited s).
      { eapply Hoare_conseq_pre. 2: apply (set_fa_keep_stack_in_visited v u).
        intros s [[Hsiv _] _]. exact Hsiv. }
      apply Hoare_conj with (Q1 := fun _ s => dfn_inv s)
        (Q2 := fun _ s => dfn_valid s root /\ fa_visited s).
      { eapply Hoare_conseq_pre. 2: apply (set_fa_keep_dfn_inv v u).
        intros s [[_ [Hinv _]] _]. exact Hinv. }
      apply Hoare_conj with (Q1 := fun _ s => dfn_valid s root)
        (Q2 := fun _ s => fa_visited s).
      { eapply Hoare_conseq_post.
        2: { eapply Hoare_conseq_pre.
             2: apply (set_fa_preserves_dfn_pre_child v u).
             intro s. intros [Hwfs Huvis_nv].
             destruct Hwfs as [Hsiv [Hinv [Hvalid Hfa]]].
             destruct Huvis_nv as [Huvis Hnv].
             split; [exact Hnv | split; [exact Hvalid | split; [exact Hinv | split; [exact Hfa | exact Huvis]]]]. }
        intros _ s [Hnv [Hvalid [Hinv Hfa]]]. exact Hvalid. }
      { eapply Hoare_conseq_pre. 2: apply (set_fa_keep_fa_visited v u).
        intros s [[_ [_ [_ Hfa]]] [Huvis Hnv]]. split; auto. }
    - (* ~ v ∈ visited *)
      unfold set_fa. intro_state. hoare_auto_s. subst s. simpl.
      destruct H as [[_ [_ [_ _]]] [_ Hnv]]. exact Hnv. }
  { eapply Hoare_conseq_pre. 2: apply (set_fa_keep_visited v u u).
    intros s [[_ [_ [_ _]]] [Huvis _]]. exact Huvis. }
Qed.

Lemma set_low_preserves_wf_scc_state (u: V) (n: nat):
  Hoare (fun s: @SCCSt V => wf_scc_state s)
        (set_low u n)
        (fun _ s => wf_scc_state s).
Proof.
  unfold wf_scc_state.
  apply Hoare_conj with (Q1 := fun _ s => stack_in_visited s).
  { unfold set_low. intro_state. hoare_auto_s. subst s. simpl.
    destruct H as [Hsiv _]. exact Hsiv. }
  apply Hoare_conj with (Q1 := fun _ s => dfn_inv s).
  { unfold set_low. intro_state. hoare_auto_s. subst s. simpl.
    destruct H as [_ [Hinv _]]. exact Hinv. }
  apply Hoare_conj with (Q1 := fun _ s => dfn_valid s root).
  { unfold set_low. intro_state. hoare_auto_s. subst s. simpl.
    destruct H as [_ [_ [Hvalid _]]]. exact Hvalid. }
  { unfold set_low. intro_state. hoare_auto_s. subst s. simpl.
    destruct H as [_ [_ [_ Hfa]]]. exact Hfa. }
Qed.

Lemma update_low_preserves_wf_scc_state (u: V) (n: nat):
  Hoare (fun s: @SCCSt V => wf_scc_state s /\ u ∈ visited s)
        (update_low u n)
        (fun _ s => wf_scc_state s).
Proof.
  unfold wf_scc_state.
  apply Hoare_conj with (Q1 := fun _ s => stack_in_visited s).
  { unfold update_low. unfold_op. intro_state. hoare_auto_s.
    { subst s. simpl. destruct H as [[Hsiv _] _]. exact Hsiv. }
    { destruct H1 as [Heq _]. subst s. destruct H as [[Hsiv _] _]. exact Hsiv. } }
  apply Hoare_conj with (Q1 := fun _ s => dfn_inv s).
  { eapply Hoare_conseq_pre. 2: apply (update_low_keep_dfn_inv u n).
    intros s [[_ [Hinv _]] _]. exact Hinv. }
  apply Hoare_conj with (Q1 := fun _ s => dfn_valid s root).
  { eapply Hoare_conseq_pre. 2: apply (update_low_keep_dfn_valid u n).
    intros s [[_ [_ [Hvalid _]]] _]. exact Hvalid. }
  { eapply Hoare_conseq_pre. 2: apply (update_low_keep_fa_visited u n).
    intros s [[_ [_ [_ Hfa]]] _]. exact Hfa. }
Qed.

End IS_DFN.
