Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic Syntax.
From GraphLib.examples Require Import tarjan.
From Algorithms.Tarjan_directed Require Import SCC_basic Tarjan_scc.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

(* ================================================================ *)
(* Tactic Definitions                                                *)
(* ================================================================ *)

Ltac unfold_op :=
  unfold visit, set_dfn, set_low, set_fa, incr_timer,
         push_stack, update_low, pop_scc.

Ltac my_destruct H := destruct H as [? [? ?]].

Tactic Notation "hoare_bind''" uconstr(H) :=
  eapply Hoare_bind; [ | intros; eapply H]; intros.

Section BASICS.

  Context {V E: Type}
          `{EqDec V eq}
          (g: OriginalGraphType V E)
          `{OriginalGraph_gvalid g}.

(* ================================================================ *)
(* Invariant Definitions                                             *)
(* ================================================================ *)

Definition visited_mono (s1 s2: @SCCSt V): Prop :=
  forall v, v ∈ visited s1 -> v ∈ visited s2.

Definition dfn_persist (s1 s2: @SCCSt V): Prop :=
  forall v, v ∈ visited s1 -> dfn s1 v = dfn s2 v.

Definition low_nonincreasing (s1 s2: @SCCSt V): Prop :=
  forall v, v ∈ visited s1 -> low s2 v <= low s1 v.

Definition fa_persist (s1 s2: @SCCSt V): Prop :=
  forall v, v ∈ visited s1 -> fa s1 v = fa s2 v.

Definition stack_in_visited (s: @SCCSt V): Prop :=
  forall v, In v (stack s) -> v ∈ visited s.

Definition sccs_mono (s1 s2: @SCCSt V): Prop :=
  forall scc, In scc (sccs s1) -> In scc (sccs s2).

Definition timer_mono (s1 s2: @SCCSt V): Prop :=
  timer s1 <= timer s2.

Definition basics_invariant (s1 s2: @SCCSt V): Prop :=
  visited_mono s1 s2 /\
  dfn_persist s1 s2 /\
  low_nonincreasing s1 s2 /\
  fa_persist s1 s2 /\
  timer_mono s1 s2 /\
  stack_in_visited s2 /\
  sccs_mono s1 s2.

(* ================================================================ *)
(* Primitive Operation Lemmas                                        *)
(* ================================================================ *)

Lemma visit_keep_visited (v w: V):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (visit v)
        (fun _ s => w ∈ visited s).
Proof.
  unfold visit. intro_state. hoare_auto_s.
  subst s. simpl. sets_unfold. tauto.
Qed.

Lemma set_dfn_keep_visited (v w: V) (n: nat):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (set_dfn v n)
        (fun _ s => w ∈ visited s).
Proof.
  unfold set_dfn. intro_state. hoare_auto_s.
  subst s. simpl. sets_unfold. tauto.
Qed.

Lemma set_dfn_new_dfn (v: V) (n: nat):
  Hoare (fun s: @SCCSt V => ~ v ∈ visited s)
        (set_dfn v n)
        (fun _ s => dfn s v = n).
Proof.
  unfold set_dfn. intro_state. hoare_auto_s.
  subst s. simpl.
  unfold equiv_decb. destruct (equiv_dec v v) as [Heq|Hneq];
    simpl; [reflexivity | exfalso; apply Hneq; reflexivity].
Qed.

Lemma set_dfn_keep_other_dfn (v w: V) (n: nat) (dfnw: nat):
  Hoare (fun s: @SCCSt V => v <> w /\ dfn s w = dfnw)
        (set_dfn v n)
        (fun _ s => dfn s w = dfnw).
Proof.
  unfold set_dfn. intro_state. hoare_auto_s.
  subst s. simpl.
  destruct H as [Hneq Hdfn].
  unfold equiv_decb. destruct (equiv_dec w v) as [Heq|Hneq']; simpl.
  - exfalso; apply Hneq; symmetry; exact Heq.
  - exact Hdfn.
Qed.

Lemma set_low_keep_visited (v w: V) (n: nat):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (set_low v n)
        (fun _ s => w ∈ visited s).
Proof.
  unfold set_low. intro_state. hoare_auto_s.
  subst s. simpl. sets_unfold. tauto.
Qed.

Lemma set_low_new_low (v: V) (n: nat):
  Hoare (fun s: @SCCSt V => True)
        (set_low v n)
        (fun _ s => low s v = n).
Proof.
  unfold set_low. intro_state. hoare_auto_s.
  subst s. simpl.
  unfold equiv_decb. destruct (equiv_dec v v) as [Heq|Hneq];
    simpl; [reflexivity | exfalso; apply Hneq; reflexivity].
Qed.

Lemma set_low_keep_other_low (v w: V) (n: nat) (loww: nat):
  Hoare (fun s: @SCCSt V => v <> w /\ low s w = loww)
        (set_low v n)
        (fun _ s => low s w = loww).
Proof.
  unfold set_low. intro_state. hoare_auto_s.
  subst s. simpl.
  destruct H as [Hneq Hlow].
  unfold equiv_decb. destruct (equiv_dec w v) as [Heq|Hneq']; simpl.
  - exfalso; apply Hneq; symmetry; exact Heq.
  - exact Hlow.
Qed.

Lemma set_fa_keep_visited (v w: V) (p: V):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (set_fa v p)
        (fun _ s => w ∈ visited s).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. sets_unfold. tauto.
Qed.

Lemma set_fa_new_fa (v: V) (p: V):
  Hoare (fun s: @SCCSt V => True)
        (set_fa v p)
        (fun _ s => fa s v = p).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl.
  unfold equiv_decb. destruct (equiv_dec v v) as [Heq|Hneq];
    simpl; [reflexivity | exfalso; apply Hneq; reflexivity].
Qed.

Lemma set_fa_keep_other_fa (v w: V) (p: V) (faw: V):
  Hoare (fun s: @SCCSt V => v <> w /\ fa s w = faw)
        (set_fa v p)
        (fun _ s => fa s w = faw).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl.
  destruct H as [Hneq Hfa].
  unfold equiv_decb. destruct (equiv_dec w v) as [Heq|Hneq']; simpl.
  - exfalso; apply Hneq; symmetry; exact Heq.
  - exact Hfa.
Qed.

Lemma incr_timer_keep_visited (w: V):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        incr_timer
        (fun _ s => w ∈ visited s).
Proof.
  unfold incr_timer. intro_state. hoare_auto_s.
  subst s. simpl. sets_unfold. tauto.
Qed.

Lemma push_stack_keep_visited (v w: V):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (push_stack v)
        (fun _ s => w ∈ visited s).
Proof.
  unfold push_stack. intro_state. hoare_auto_s.
  subst s. simpl. sets_unfold. tauto.
Qed.

Lemma push_stack_in_stack (v: V):
  Hoare (fun s: @SCCSt V => True)
        (push_stack v)
        (fun _ s => In v (stack s)).
Proof.
  unfold push_stack. intro_state. hoare_auto_s.
  subst s. simpl. left; reflexivity.
Qed.

Lemma update_low_keep_visited (u w: V) (n: nat):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (update_low u n)
        (fun _ s => w ∈ visited s).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  { subst s. simpl. sets_unfold. tauto. }
  { destruct H1. subst s. sets_unfold. tauto. }
Qed.

Lemma update_low_nonincreasing (u: V) (n: nat) (old_low: nat):
  Hoare (fun s: @SCCSt V => low s u = old_low)
        (update_low u n)
        (fun _ s => low s u <= old_low).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  { subst s. simpl.
    unfold equiv_decb. destruct (equiv_dec u u) as [Heq|Hneq]; simpl.
    - lia.
    - exfalso; apply Hneq; reflexivity. }
  { destruct H. subst s. lia. }
Qed.

Lemma update_low_keep_dfn (u w: V) (n: nat) (dfnw: nat):
  Hoare (fun s: @SCCSt V => dfn s w = dfnw)
        (update_low u n)
        (fun _ s => dfn s w = dfnw).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  { subst s. simpl. auto. }
  { destruct H. subst s. auto. }
Qed.

Lemma set_fa_keep_dfn (v w: V) (p: V) (dfnw: nat):
  Hoare (fun s: @SCCSt V => dfn s w = dfnw)
        (set_fa v p)
        (fun _ s => dfn s w = dfnw).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. auto.
Qed.

Lemma set_fa_keep_low (v w: V) (p: V) (loww: nat):
  Hoare (fun s: @SCCSt V => low s w = loww)
        (set_fa v p)
        (fun _ s => low s w = loww).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. auto.
Qed.

Lemma pop_scc_keep_visited (u w: V):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (pop_scc u)
        (fun _ s => w ∈ visited s).
Proof.
  unfold pop_scc. intro_state. hoare_auto_s.
  subst s. unfold pop_scc_state.
  destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
  simpl. auto.
Qed.

Lemma pop_scc_keep_dfn (u w: V) (dfnw: nat):
  Hoare (fun s: @SCCSt V => dfn s w = dfnw)
        (pop_scc u)
        (fun _ s => dfn s w = dfnw).
Proof.
  unfold pop_scc. intro_state. hoare_auto_s.
  subst s. unfold pop_scc_state.
  destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
  simpl. auto.
Qed.

Lemma pop_scc_keep_low (u w: V) (loww: nat):
  Hoare (fun s: @SCCSt V => low s w = loww)
        (pop_scc u)
        (fun _ s => low s w = loww).
Proof.
  unfold pop_scc. intro_state. hoare_auto_s.
  subst s. unfold pop_scc_state.
  destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
  simpl. auto.
Qed.

Lemma pop_scc_keep_fa (u w: V) (faw: V):
  Hoare (fun s: @SCCSt V => fa s w = faw)
        (pop_scc u)
        (fun _ s => fa s w = faw).
Proof.
  unfold pop_scc. intro_state. hoare_auto_s.
  subst s. unfold pop_scc_state.
  destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
  simpl. auto.
Qed.

(* ================================================================ *)
(* Composite Operation Lemmas — preloop                              *)
(* ================================================================ *)

Lemma preloop_keep_visited (u w: V):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (preloop u)
        (fun _ s => w ∈ visited s).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl. sets_unfold. tauto.
Qed.

Lemma preloop_self_visited (u: V):
  Hoare (fun s: @SCCSt V => True)
        (preloop u)
        (fun _ s => u ∈ visited s).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl. sets_unfold. right; reflexivity.
Qed.

Lemma preloop_in_stack (u: V):
  Hoare (fun s: @SCCSt V => True)
        (preloop u)
        (fun _ s => In u (stack s)).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl. left; reflexivity.
Qed.

Lemma preloop_dfn_set (u: V) (t: nat):
  Hoare (fun s: @SCCSt V => timer s = t)
        (preloop u)
        (fun _ s => dfn s u = t).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl.
  unfold equiv_decb. destruct (equiv_dec u u) as [Heq|Hneq];
    simpl; [reflexivity | exfalso; apply Hneq; reflexivity].
Qed.

Lemma preloop_low_set (u: V) (t: nat):
  Hoare (fun s: @SCCSt V => timer s = t)
        (preloop u)
        (fun _ s => low s u = t).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl.
  unfold equiv_decb. destruct (equiv_dec u u) as [Heq|Hneq];
    simpl; [reflexivity | exfalso; apply Hneq; reflexivity].
Qed.

Lemma preloop_keep_dfn (u v: V) (dfnv: nat):
  Hoare (fun s: @SCCSt V => u <> v /\ v ∈ visited s /\ dfn s v = dfnv)
        (preloop u)
        (fun _ s => u <> v /\ v ∈ visited s /\ dfn s v = dfnv).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl.
  destruct H as [Hneq [Hvis Hdfn]].
  split; [exact Hneq | split].
  { sets_unfold. left; exact Hvis. }
  { unfold equiv_decb. destruct (equiv_dec v u) as [Heq|Hneq']; simpl.
    - exfalso; apply Hneq; symmetry; exact Heq.
    - exact Hdfn. }
Qed.

Lemma preloop_keep_low (u v: V) (lowv: nat):
  Hoare (fun s: @SCCSt V => u <> v /\ v ∈ visited s /\ low s v = lowv)
        (preloop u)
        (fun _ s => u <> v /\ v ∈ visited s /\ low s v = lowv).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl.
  destruct H as [Hneq Hrest]. destruct Hrest as [Hvis Hlow].
  split; [exact Hneq | split].
  { sets_unfold. left; exact Hvis. }
  { unfold equiv_decb. destruct (equiv_dec v u) as [Heq|Hneq']; simpl.
    - exfalso; apply Hneq; symmetry; exact Heq.
    - exact Hlow. }
Qed.

Lemma preloop_keep_fa (u v: V) (fav: V):
  Hoare (fun s: @SCCSt V => u <> v /\ v ∈ visited s /\ fa s v = fav)
        (preloop u)
        (fun _ s => u <> v /\ v ∈ visited s /\ fa s v = fav).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. simpl.
  destruct H as [Hneq [Hvis Hfa]].
  split; [exact Hneq | split].
  { sets_unfold. left; exact Hvis. }
  { unfold equiv_decb. destruct (equiv_dec v u) as [Heq|Hneq']; simpl.
    - exfalso; apply Hneq; symmetry; exact Heq.
    - exact Hfa. }
Qed.

(* ================================================================ *)
(* Composite Operation Lemmas — process_edge helpers                 *)
(* ================================================================ *)

Lemma get_low_update_low_keep_visited (u v w: V):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (lv <- get' (fun s => low s v);; update_low u lv)
        (fun _ s => w ∈ visited s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
  apply Hoare_conseq_pre with (P2 := fun s => w ∈ visited s).
  { intros s1 Hs1. destruct Hs1. subst s1. simpl. auto. }
  apply (update_low_keep_visited u w lv).
Qed.

Lemma get_dfn_update_low_keep_visited (u v w: V):
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (dv <- get' (fun s => dfn s v);; update_low u dv)
        (fun _ s => w ∈ visited s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
  apply Hoare_conseq_pre with (P2 := fun s => w ∈ visited s).
  { intros s1 Hs1. destruct Hs1. subst s1. simpl. auto. }
  apply (update_low_keep_visited u w dv).
Qed.

(* ================================================================ *)
(* Composite Operation Lemmas — process_edge                         *)
(* ================================================================ *)

Lemma process_edge_keep_visited (u v w: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s: @SCCSt V => w ∈ visited s) (W x) (fun _ s => w ∈ visited s)) ->
  Hoare (fun s: @SCCSt V => w ∈ visited s)
        (process_edge u W v)
        (fun _ s => w ∈ visited s).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state.
  apply Hoare_choice.
  - (* Tree edge *)
    apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => w ∈ visited s).
    { intros s1 [Hnv Hs1]. subst s1. exact H. }
    hoare_bind (set_fa_keep_visited v w u). simpl. clear a.
    eapply Hoare_bind. { apply HW. } simpl. intros _.
    apply get_low_update_low_keep_visited.
  - (* Non-tree edge *)
    intro_state. hoare_auto_s.
    + apply Hoare_conseq_pre with (P2 := fun s => w ∈ visited s).
      { intros s1 Hs1. subst s1. simpl. apply H. }
      apply (update_low_keep_visited u w (dfn s0 v)).
    + destruct H3. subst s. subst s1. exact H.
Qed.

(* ================================================================ *)
(* Composite Operation Lemmas — process_edge_fa                      *)
(* ================================================================ *)

(** [set_fa_keep_not_visited]: [set_fa] does not change [visited],
    so vertices that were not visited stay not visited. *)
Lemma set_fa_keep_not_visited (v w p: V):
  Hoare (fun s: @SCCSt V => ~ v ∈ visited s)
        (set_fa w p)
        (fun _ s => ~ v ∈ visited s).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. auto.
Qed.

(** [update_low_keep_fa]: [update_low] only changes [low], so [fa]
    values are unchanged. *)
Lemma update_low_keep_fa (u w: V) (n: nat) (faw: V):
  Hoare (fun s: @SCCSt V => fa s w = faw)
        (update_low u n)
        (fun _ s => fa s w = faw).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  { subst s. simpl. auto. }
  { destruct H. subst s. auto. }
Qed.

(** [update_low_keep_visited_fa]: combined lemma preserving both
    [visited] and [fa] through [update_low]. *)
Lemma update_low_keep_visited_fa (u w: V) (n: nat) (faw: V):
  Hoare (fun s: @SCCSt V => w ∈ visited s /\ fa s w = faw)
        (update_low u n)
        (fun _ s => w ∈ visited s /\ fa s w = faw).
Proof.
  apply Hoare_conj.
  - eapply Hoare_conseq_pre.
    2: apply (update_low_keep_visited u w n).
    intros s [Hvis Hfa]; exact Hvis.
  - eapply Hoare_conseq_pre.
    2: apply (update_low_keep_fa u w n faw).
    intros s [Hvis Hfa]; exact Hfa.
Qed.

(** [process_edge_keep_fa]: the operations in process_edge only touch
    fa of the newly-discovered vertex v (via set_fa). For any already-
    visited vertex w, its fa value is unchanged. *)

Lemma process_edge_keep_fa (u v w: V) (W: V -> program (@SCCSt V) unit) (faw: V):
  (forall x, Hoare (fun s: @SCCSt V => x <> w /\ w ∈ visited s /\ fa s w = faw)
                  (W x)
                  (fun _ s => w ∈ visited s /\ fa s w = faw)) ->
  Hoare (fun s: @SCCSt V => w ∈ visited s /\ fa s w = faw)
        (process_edge u W v)
        (fun _ s => w ∈ visited s /\ fa s w = faw).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state. destruct H as [Hvis Hfa].
  apply Hoare_choice.
  - (* Tree edge: v not visited *)
    apply Hoare_assume_bind. simpl.
    eapply Hoare_bind.
    { apply Hoare_conj.
      - eapply Hoare_conseq_pre.
        2: apply (set_fa_keep_not_visited v v u).
        intros s1 [Hnv' Hs1]; subst s1; exact Hnv'.
      - apply Hoare_conj.
        + eapply Hoare_conseq_pre.
          2: apply (set_fa_keep_visited v w u).
          intros s1 [Hnv' Hs1]; subst s1; exact Hvis.
        + eapply Hoare_conseq_pre.
          2: apply (set_fa_keep_other_fa v w u faw).
          intros s1 [Hnv' Hs1]; subst s1; split; [| exact Hfa].
          intro Heq; subst v; apply Hnv'; exact Hvis. }
    simpl. intros _.
    eapply Hoare_bind.
    { apply Hoare_conseq_pre with
        (P2 := fun s => v <> w /\ w ∈ visited s /\ fa s w = faw).
      - intros s' Hpre. destruct Hpre as [Hnv'' Hrest]. destruct Hrest as [Hvis'' Hfa''].
        split; [| split]; auto.
        intro Heq; subst v; apply Hnv''; exact Hvis''.
      - apply HW. }
    simpl. intros _.
    intro_state. destruct H as [Hvis1 Hfa1].
    eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
    apply Hoare_conj.
    + eapply Hoare_conseq_pre.
      2: apply (update_low_keep_visited u w lv).
      intros s' Hs'. destruct Hs'. subst s'. exact Hvis1.
    + eapply Hoare_conseq_pre.
      2: apply (update_low_keep_fa u w lv faw).
      intros s' Hs'. destruct Hs'. subst s'. exact Hfa1.
  - (* Non-tree edge: v already visited, if in stack update_low *)
    intro_state; hoare_auto_s;
    [ apply Hoare_conseq_pre with
        (P2 := fun s => w ∈ visited s /\ fa s w = fa s0 w);
        [ intros s' Hs'; destruct Hs'; split; auto
        | apply (update_low_keep_visited_fa u w (dfn s0 v) (fa s0 w)) ]
    | repeat (match goal with
             | [ H: ?s = ?t /\ _ |- _ ] => destruct H; subst
             | [ H: _ /\ _ |- _ ] => destruct H
             end); split; auto ].
Qed.

(* ================================================================ *)
(* Composite Operation Lemmas — process_edge (dfn/low variants)      *)
(* ================================================================ *)

(** [update_low_keep_other_low]: when [u <> w], updating low of [u]
    does not change the low value of [w]. *)
Lemma update_low_keep_other_low (u w: V) (n: nat) (loww: nat):
  Hoare (fun s: @SCCSt V => u <> w /\ low s w = loww)
        (update_low u n)
        (fun _ s => low s w = loww).
Proof.
  unfold update_low. unfold_op. intro_state. destruct H as [Hneq Hlow]. hoare_auto_s.
  - rewrite H1. simpl. unfold equiv_decb. destruct (equiv_dec w u) as [Heq|Hneq'].
    { exfalso; apply Hneq; symmetry; exact Heq. } reflexivity.
  - destruct H. subst s. reflexivity.
Qed.

(** [update_low_keep_other_dfn]: updating low of [u] does not
    change the dfn value of any vertex.  (Trivial: [update_low]
    only touches the [low] field.) *)
Lemma update_low_keep_other_dfn (u w: V) (n: nat) (dfnw: nat):
  Hoare (fun s: @SCCSt V => u <> w /\ dfn s w = dfnw)
        (update_low u n)
        (fun _ s => dfn s w = dfnw).
Proof.
  unfold update_low. unfold_op. intro_state. destruct H as [Hneq Hdfn]. hoare_auto_s.
  - rewrite H1. simpl. auto.
  - destruct H. subst s. auto.
Qed.

(** [set_fa_keep_nv_visited_dfn]: [set_fa] does not change [visited]
    nor [dfn], so it preserves [~ v ∈ visited] together with
    [w ∈ visited] and [dfn w = dfnw]. *)
Lemma set_fa_keep_nv_visited_dfn (v w u: V) (dfnw: nat):
  Hoare (fun s: @SCCSt V => ~ v ∈ visited s /\ w ∈ visited s /\ dfn s w = dfnw)
        (set_fa v u)
        (fun _ s => ~ v ∈ visited s /\ w ∈ visited s /\ dfn s w = dfnw).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl.
  destruct H as [Hnv [Hvis Hdfn]].
  repeat split; auto.
Qed.

(** [set_fa_keep_nv_visited_low]: same as above, but for [low]
    instead of [dfn]. *)
Lemma set_fa_keep_nv_visited_low (v w u: V) (loww: nat):
  Hoare (fun s: @SCCSt V => ~ v ∈ visited s /\ w ∈ visited s /\ low s w = loww)
        (set_fa v u)
        (fun _ s => ~ v ∈ visited s /\ w ∈ visited s /\ low s w = loww).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl.
  destruct H as [Hnv [Hvis Hlow]].
  repeat split; auto.
Qed.

(** Combined lemmas: package two properties into one Hoare triple. *)

Lemma set_fa_keep_visited_dfn (v w u: V) (dfnw: nat):
  Hoare (fun s: @SCCSt V => w ∈ visited s /\ dfn s w = dfnw)
        (set_fa v u)
        (fun _ s => w ∈ visited s /\ dfn s w = dfnw).
Proof.
  apply Hoare_conj with (Q1 := fun (_: unit) s => w ∈ visited s)
                        (Q2 := fun (_: unit) s => dfn s w = dfnw).
  - eapply Hoare_conseq_pre.
    2: apply (set_fa_keep_visited v w u).
    intros s [Hvis _]. exact Hvis.
  - eapply Hoare_conseq_pre.
    2: apply (set_fa_keep_dfn v w u dfnw).
    intros s [_ Hdfn]. exact Hdfn.
Qed.

Lemma set_fa_keep_visited_low (v w u: V) (loww: nat):
  Hoare (fun s: @SCCSt V => w ∈ visited s /\ low s w = loww)
        (set_fa v u)
        (fun _ s => w ∈ visited s /\ low s w = loww).
Proof.
  apply Hoare_conj with (Q1 := fun (_: unit) s => w ∈ visited s)
                        (Q2 := fun (_: unit) s => low s w = loww).
  - eapply Hoare_conseq_pre.
    2: apply (set_fa_keep_visited v w u).
    intros s [Hvis _]. exact Hvis.
  - eapply Hoare_conseq_pre.
    2: apply (set_fa_keep_low v w u loww).
    intros s [_ Hlow]. exact Hlow.
Qed.

Lemma update_low_keep_visited_dfn (u w: V) (n dfnw: nat):
  Hoare (fun s: @SCCSt V => w ∈ visited s /\ dfn s w = dfnw)
        (update_low u n)
        (fun _ s => w ∈ visited s /\ dfn s w = dfnw).
Proof.
  apply Hoare_conj with (Q1 := fun (_: unit) s => w ∈ visited s)
                        (Q2 := fun (_: unit) s => dfn s w = dfnw).
  - eapply Hoare_conseq_pre.
    2: apply (update_low_keep_visited u w n).
    intros s [Hvis _]. exact Hvis.
  - eapply Hoare_conseq_pre.
    2: apply (update_low_keep_dfn u w n dfnw).
    intros s [_ Hdfn]. exact Hdfn.
Qed.

Lemma get_low_update_low_keep_visited_dfn (u v w: V) (dfnw: nat):
  Hoare (fun s: @SCCSt V => w ∈ visited s /\ dfn s w = dfnw)
        (lv <- get' (fun s => low s v);; update_low u lv)
        (fun _ s => w ∈ visited s /\ dfn s w = dfnw).
Proof.
  unfold update_low. unfold_op. intro_state. destruct H as [Hvis Hdfn]. hoare_auto_s.
  - rewrite H1. simpl. split; auto.
  - destruct H. subst s. split; auto.
Qed.

Lemma get_dfn_update_low_keep_visited_dfn (u v w: V) (dfnw: nat):
  Hoare (fun s: @SCCSt V => w ∈ visited s /\ dfn s w = dfnw)
        (dv <- get' (fun s => dfn s v);; update_low u dv)
        (fun _ s => w ∈ visited s /\ dfn s w = dfnw).
Proof.
  unfold update_low. unfold_op. intro_state. destruct H as [Hvis Hdfn]. hoare_auto_s.
  - rewrite H1. simpl. split; auto.
  - destruct H. subst s. split; auto.
Qed.

(** [process_edge_keep_dfn]: the dfn-preserving variant for both
    the tree-edge and non-tree-edge cases. *)

Lemma process_edge_keep_dfn (u v w: V) (W: V -> program (@SCCSt V) unit) (dfnw: nat):
  (forall x, Hoare (fun s: @SCCSt V => x <> w /\ w ∈ visited s /\ dfn s w = dfnw)
                  (W x)
                  (fun _ s => w ∈ visited s /\ dfn s w = dfnw)) ->
  Hoare (fun s: @SCCSt V => u <> w /\ w ∈ visited s /\ dfn s w = dfnw)
        (process_edge u W v)
        (fun _ s => w ∈ visited s /\ dfn s w = dfnw).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state. destruct H as [Hneq [Hvis Hdfn]].
  apply Hoare_choice.
  apply Hoare_assume_bind. simpl.
  eapply Hoare_bind.
  apply Hoare_conseq_pre with (P2 := fun s => ~ v ∈ visited s /\ w ∈ visited s /\ dfn s w = dfnw).
  { intros s1 [Hnv' Hs1]. subst s1. repeat split; auto. }
  apply (set_fa_keep_nv_visited_dfn v w u dfnw).
  simpl. intros _.
  eapply Hoare_bind.
  apply Hoare_conseq_pre with (P2 := fun s => v <> w /\ w ∈ visited s /\ dfn s w = dfnw).
  { intros s1 [Hnv' [Hvis1 Hdfn1]].
    split; [| split]; auto.
    intro Heq. subst v. apply Hnv'. exact Hvis1. }
  apply HW.
  simpl. intros _.
  apply (get_low_update_low_keep_visited_dfn u v w dfnw).
  intro_state. hoare_auto_s.
  apply Hoare_conseq_pre with (P2 := fun s => w ∈ visited s /\ dfn s w = dfn s0 w).
  { intros s' ->. split; auto. }
  apply (update_low_keep_visited_dfn u w (dfn s0 v) (dfn s0 w)).
  destruct H2. subst s. subst s1. split; auto.
Qed.

(** [process_edge_keep_low]: the low-preserving variant.  The key
    difference from the dfn version is that [update_low] *can*
    change [low u], so we need [u <> w] to guarantee [low w] is
    untouched. *)

Lemma process_edge_keep_low (u v w: V) (W: V -> program (@SCCSt V) unit) (loww: nat):
  (forall x, Hoare (fun s: @SCCSt V => x <> w /\ w ∈ visited s /\ low s w = loww)
                  (W x)
                  (fun _ s => w ∈ visited s /\ low s w = loww)) ->
  Hoare (fun s: @SCCSt V => u <> w /\ w ∈ visited s /\ low s w = loww)
        (process_edge u W v)
        (fun _ s => w ∈ visited s /\ low s w = loww).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state. destruct H as [Hneq Hrest]. destruct Hrest as [Hvis Hlow].
  apply Hoare_choice.
  apply Hoare_assume_bind. simpl.
  eapply Hoare_bind.
  apply Hoare_conseq_pre with (P2 := fun s => ~ v ∈ visited s /\ w ∈ visited s /\ low s w = loww).
  { intros s1 [Hnv' Hs1]. subst s1. repeat split; auto. }
  apply (set_fa_keep_nv_visited_low v w u loww).
  simpl. intros _.
  eapply Hoare_bind.
  apply Hoare_conseq_pre with (P2 := fun s => v <> w /\ w ∈ visited s /\ low s w = loww).
  { intros s1 [Hnv' [Hvis1 Hlow1]].
    split; [| split]; auto.
    intro Heq. subst v. apply Hnv'. exact Hvis1. }
  apply HW.
  simpl. intros _.
  apply Hoare_conj.
  { eapply Hoare_conseq_pre.
    2: apply (get_low_update_low_keep_visited u v w).
    intros s1 [Hvis1 Hlow1]. exact Hvis1. }
  eapply Hoare_conseq_pre.
  { intros s1 [Hvis1 Hlow1]. exact Hlow1. }
  intro_state. eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
  apply Hoare_conseq_pre with (P2 := fun s => u <> w /\ low s w = loww).
  { intros s2 Hs2. destruct Hs2. subst s2. simpl. auto. }
  apply (update_low_keep_other_low u w lv loww).
  intro_state. hoare_auto_s.
  apply Hoare_conseq_pre with (P2 := fun s => w ∈ visited s /\ low s w = low s0 w).
  { intros s' ->. split; auto. }
  apply Hoare_conj.
  { eapply Hoare_conseq_pre.
    2: apply (update_low_keep_visited u w (dfn s0 v)).
    intros s' [Hvis' Hlow']. exact Hvis'. }
  apply Hoare_conseq_pre with (P2 := fun s => u <> w /\ low s w = low s0 w).
  { intros s' [Hvis' Hlow']. split; auto. }
  apply (update_low_keep_other_low u w (dfn s0 v) (low s0 w)).
  destruct H2. subst s. subst s1. split; auto.
Qed.

(* ================================================================ *)
(* Forall variants — visited preservation helpers                    *)
(* ================================================================ *)

(** These lemmas lift the pointwise [visited] preservation results
    to forall-quantified versions.  Since the constituent operations
    (set_fa, update_low, preloop, pop_scc) never remove vertices
    from [visited], the forall versions are straightforward. *)

Lemma set_fa_keep_visited_forall (v p: V) (done: V -> Prop):
  Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s)
        (set_fa v p)
        (fun _ s => forall w, done w -> w ∈ visited s).
Proof.
  unfold set_fa. intro_state. hoare_auto_s.
  subst s. simpl. auto.
Qed.

Lemma update_low_keep_visited_forall (u: V) (n: nat) (done: V -> Prop):
  Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s)
        (update_low u n)
        (fun _ s => forall w, done w -> w ∈ visited s).
Proof.
  unfold update_low. unfold_op. intro_state. hoare_auto_s.
  - subst s. simpl. auto.
  - destruct H1. subst s. auto.
Qed.

Lemma get_low_update_low_keep_visited_forall (u v: V) (done: V -> Prop):
  Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s)
        (lv <- get' (fun s => low s v);; update_low u lv)
        (fun _ s => forall w, done w -> w ∈ visited s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros lv.
  apply Hoare_conseq_pre with (P2 := fun s => forall w, done w -> w ∈ visited s).
  { intros s1 Hs1. destruct Hs1. subst s1. auto. }
  apply (update_low_keep_visited_forall u lv done).
Qed.

Lemma get_dfn_update_low_keep_visited_forall (u v: V) (done: V -> Prop):
  Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s)
        (dv <- get' (fun s => dfn s v);; update_low u dv)
        (fun _ s => forall w, done w -> w ∈ visited s).
Proof.
  intro_state.
  eapply Hoare_bind. { eapply Hoare_get'. } simpl. intros dv.
  apply Hoare_conseq_pre with (P2 := fun s => forall w, done w -> w ∈ visited s).
  { intros s1 Hs1. destruct Hs1. subst s1. auto. }
  apply (update_low_keep_visited_forall u dv done).
Qed.

Lemma preloop_keep_visited_forall (u: V) (done: V -> Prop):
  Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s)
        (preloop u)
        (fun _ s => forall w, done w -> w ∈ visited s).
Proof.
  unfold preloop. unfold_op. intro_state. hoare_auto_s.
  subst s. cbv. sets_unfold. firstorder.
Qed.

Lemma pop_scc_keep_visited_forall (u: V) (done: V -> Prop):
  Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s)
        (pop_scc u)
        (fun _ s => forall w, done w -> w ∈ visited s).
Proof.
  unfold pop_scc. intro_state. hoare_auto_s.
  subst s. unfold pop_scc_state.
  destruct (stack_split_at (stack s0) u) as [popped rest] eqn:?.
  simpl. auto.
Qed.

Lemma process_edge_keep_visited_forall (u v: V) (W: V -> program (@SCCSt V) unit) (done: V -> Prop):
  (forall x, Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s) (W x) (fun _ s => forall w, done w -> w ∈ visited s)) ->
  Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s)
        (process_edge u W v)
        (fun _ s => forall w, done w -> w ∈ visited s).
Proof.
  intros HW.
  unfold process_edge, if_else.
  intro_state.
  apply Hoare_choice.
  - (* Tree edge *)
    apply Hoare_assume_bind. simpl.
    apply Hoare_conseq_pre with (P2 := fun s => forall w, done w -> w ∈ visited s).
    { intros s1 [Hnv Heq]. subst s1. exact H. }
    hoare_bind (set_fa_keep_visited_forall v u done). simpl. clear a.
    eapply Hoare_bind. { apply HW. } simpl. intros _.
    apply get_low_update_low_keep_visited_forall.
  - (* Non-tree edge: assume (~~v∈visited);; If (In v stack) ... *)
    intro_state. hoare_auto_s.
    + (* In v (stack s) branch: get' dfn v;; update_low u *)
      apply Hoare_conseq_pre with (P2 := fun s => forall w, done w -> w ∈ visited s).
      { intros s1 Hs1. subst s1. exact H. }
      apply (update_low_keep_visited_forall u (dfn s0 v) done).
    + (* ~ In v (stack s) branch: skip — postcondition weakening *)
      destruct H3 as [-> Hnin]. subst s1. apply H; auto.
Qed.

Lemma forset_process_edge_keep_visited_forall (u: V) (W: V -> program (@SCCSt V) unit) (done: V -> Prop):
  (forall x, Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s) (W x) (fun _ s => forall w, done w -> w ∈ visited s)) ->
  Hoare (fun s: @SCCSt V => forall w, done w -> w ∈ visited s)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => forall w, done w -> w ∈ visited s).
Proof.
  intros HW.
  unfold forset. hoare_fix_nolv_auto (V -> Prop).
  simpl. intros W0 IH0 todo.
  unfold forset_f. hoare_auto_s. intro_state. hoare_auto_s.
  - eapply Hoare_bind with (R := fun _ s => forall w, done w -> w ∈ visited s).
    { apply Hoare_conseq_pre with (P2 := fun s => forall w, done w -> w ∈ visited s).
      - intros s1 Hs1. subst s1. exact H.
      - apply process_edge_keep_visited_forall. intros x. apply HW. }
    simpl. intros _. apply IH0.
Qed.

(* ================================================================ *)
(* Core Hoare Fixpoint Theorems — tarjan_scc                         *)
(* ================================================================ *)
(* Helper: forset inner fixpoint lemmas                               *)
(* ================================================================ *)

(** [forset_process_edge_keep_visited]: the inner forset fixpoint
    preserves [visited]. *)
Lemma forset_process_edge_keep_visited (u v: V) (W: V -> program (@SCCSt V) unit):
  (forall x, Hoare (fun s: @SCCSt V => v ∈ visited s) (W x) (fun _ s => v ∈ visited s)) ->
  Hoare (fun s: @SCCSt V => v ∈ visited s)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => v ∈ visited s).
Proof.
  intros HW.
  unfold forset.
  hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f.
  hoare_auto_s.
  intro_state.
  hoare_auto_s.
  - eapply Hoare_bind with (R := fun (_: unit) s => v ∈ visited s).
    { apply Hoare_conseq_pre with (P2 := fun s => v ∈ visited s).
      - intros s1 Hs1. subst s1. exact H.
      - apply (process_edge_keep_visited u a v W). intros x. apply HW. }
    simpl. intros _. apply IH0.
Qed.

Lemma forset_process_edge_keep_dfn (u v: V) (W: V -> program (@SCCSt V) unit) (dfnv: nat):
  (forall x, Hoare (fun s: @SCCSt V => x <> v /\ v ∈ visited s /\ dfn s v = dfnv) (W x) (fun _ s => v ∈ visited s /\ dfn s v = dfnv)) ->
  Hoare (fun s: @SCCSt V => u <> v /\ v ∈ visited s /\ dfn s v = dfnv)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => v ∈ visited s /\ dfn s v = dfnv).
Proof.
  intros HW.
  unfold forset.
  hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f.
  hoare_auto_s.
  intro_state.
  destruct H as [Hneq Hrest]. destruct Hrest as [Hvis Hdfn].
  hoare_auto_s.
  - eapply Hoare_bind with (R := fun (_: unit) s => v ∈ visited s /\ dfn s v = dfn s0 v).
    { apply Hoare_conseq_pre with (P2 := fun s => u <> v /\ v ∈ visited s /\ dfn s v = dfn s0 v).
      - intros s1 Hs1. subst s1. repeat split; auto.
      - apply (process_edge_keep_dfn u a v W (dfn s0 v)). intros x. apply HW. }
    simpl. intros _.
    apply Hoare_conseq_pre with (P2 := fun s => u <> v /\ v ∈ visited s /\ dfn s v = dfn s0 v).
    { intros s' [Hvis' Hdfn']. split; [exact Hneq | split; auto]. }
    apply IH0.
  - my_destruct H1; split; auto.
Qed.

Lemma forset_process_edge_keep_low (u v: V) (W: V -> program (@SCCSt V) unit) (lowv: nat):
  (forall x, Hoare (fun s: @SCCSt V => x <> v /\ v ∈ visited s /\ low s v = lowv) (W x) (fun _ s => v ∈ visited s /\ low s v = lowv)) ->
  Hoare (fun s: @SCCSt V => u <> v /\ v ∈ visited s /\ low s v = lowv)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => v ∈ visited s /\ low s v = lowv).
Proof.
  intros HW.
  unfold forset.
  hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f.
  hoare_auto_s.
  intro_state.
  destruct H as [Hneq Hrest]. destruct Hrest as [Hvis Hlow].
  hoare_auto_s.
  - eapply Hoare_bind with (R := fun (_: unit) s => v ∈ visited s /\ low s v = low s0 v).
    { apply Hoare_conseq_pre with (P2 := fun s => u <> v /\ v ∈ visited s /\ low s v = low s0 v).
      - intros s1 Hs1. subst s1. repeat split; auto.
      - apply (process_edge_keep_low u a v W (low s0 v)). intros x. apply HW. }
    simpl. intros _.
    apply Hoare_conseq_pre with (P2 := fun s => u <> v /\ v ∈ visited s /\ low s v = low s0 v).
    { intros s' [Hvis' Hlow']. split; [exact Hneq | split; auto]. }
    apply IH0.
  - my_destruct H1; split; auto.
Qed.

Lemma forset_process_edge_keep_fa (u v: V) (W: V -> program (@SCCSt V) unit) (fav: V):
  (forall x, Hoare (fun s: @SCCSt V => x <> v /\ v ∈ visited s /\ fa s v = fav) (W x) (fun _ s => v ∈ visited s /\ fa s v = fav)) ->
  Hoare (fun s: @SCCSt V => v ∈ visited s /\ fa s v = fav)
        (forset (fun w => dg_step g u w) (process_edge u W))
        (fun _ s => v ∈ visited s /\ fa s v = fav).
Proof.
  intros HW.
  unfold forset.
  hoare_fix_nolv_auto (V -> Prop).
  simpl; intros W0 IH0 todo.
  unfold forset_f.
  hoare_auto_s.
  intro_state.
  destruct H as [Hvis Hfa].
  hoare_auto_s.
  - eapply Hoare_bind with (R := fun (_: unit) s => v ∈ visited s /\ fa s v = fa s0 v).
    { apply Hoare_conseq_pre with (P2 := fun s => v ∈ visited s /\ fa s v = fa s0 v).
      - intros s1 Hs1. rewrite Hs1. split; auto.
      - apply (process_edge_keep_fa u a v W (fa s0 v)). intros x. apply HW. }
    simpl. intros _.
    apply Hoare_conseq_pre with (P2 := fun s => v ∈ visited s /\ fa s v = fa s0 v).
    { intros s' [Hvis' Hfa']. split; auto. }
    apply IH0.
Qed.

(* ================================================================ *)
(* Core Hoare Fixpoint Theorems — tarjan_scc                         *)
(* ================================================================ *)

Theorem tarjan_scc_keep_visited (u v: V):
  Hoare (fun s: @SCCSt V => v ∈ visited s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => v ∈ visited s).
Proof.
  unfold tarjan_scc.
  hoare_fix_nolv_auto V.
  clear u. intros W IH u.
  unfold tarjan_scc_f.
  hoare_bind preloop_keep_visited; simpl; clear a.
  eapply Hoare_bind with (R := fun (_: unit) s => v ∈ visited s).
  - apply forset_process_edge_keep_visited. intros x. apply IH.
  - simpl. intros _. intro_state. hoare_auto_s.
    + apply Hoare_conseq_pre with (P2 := fun s => v ∈ visited s).
      { intros s1 Hs1. subst s1. exact H. }
      apply pop_scc_keep_visited.
    + destruct H1. subst s. exact H.
Qed.

Theorem tarjan_scc_keep_dfn (u v: V) (dfnv: nat):
  Hoare (fun s: @SCCSt V => u <> v /\ v ∈ visited s /\ dfn s v = dfnv)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => v ∈ visited s /\ dfn s v = dfnv).
Proof.
  unfold tarjan_scc.
  hoare_fix_nolv_auto V.
  clear u. intros W IH u.
  unfold tarjan_scc_f.
  eapply Hoare_bind; [apply (preloop_keep_dfn u v dfnv) | simpl; intros].
  eapply Hoare_bind with
    (R := fun (_: unit) s => v ∈ visited s /\ dfn s v = dfnv).
  - apply forset_process_edge_keep_dfn. intros x. apply IH.
  - simpl. intros _. intro_state. hoare_auto_s.
    + apply Hoare_conj.
      * apply Hoare_conseq_pre with (P2 := fun s => v ∈ visited s).
        { intros s1 Hs1. subst s1. destruct H; tauto. }
        apply (pop_scc_keep_visited u v).
      * apply Hoare_conseq_pre with (P2 := fun s => dfn s v = dfnv).
        { intros s1 Hs1. subst s1. destruct H; tauto. }
        apply (pop_scc_keep_dfn u v dfnv).
    + destruct H1. subst s. destruct H; split; auto.
Qed.

Theorem tarjan_scc_keep_low (u v: V) (lowv: nat):
  Hoare (fun s: @SCCSt V => u <> v /\ v ∈ visited s /\ low s v = lowv)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => v ∈ visited s /\ low s v = lowv).
Proof.
  unfold tarjan_scc.
  hoare_fix_nolv_auto V.
  clear u. intros W IH u.
  unfold tarjan_scc_f.
  eapply Hoare_bind; [apply (preloop_keep_low u v lowv) | simpl; intros].
  eapply Hoare_bind with
    (R := fun (_: unit) s => v ∈ visited s /\ low s v = lowv).
  - apply forset_process_edge_keep_low. intros x. apply IH.
  - simpl. intros _. intro_state. hoare_auto_s.
    + apply Hoare_conj.
      * apply Hoare_conseq_pre with (P2 := fun s => v ∈ visited s).
        { intros s1 Hs1. subst s1. destruct H; tauto. }
        apply (pop_scc_keep_visited u v).
      * apply Hoare_conseq_pre with (P2 := fun s => low s v = lowv).
        { intros s1 Hs1. subst s1. destruct H; tauto. }
        apply (pop_scc_keep_low u v lowv).
    + destruct H1. subst s. destruct H; split; auto.
Qed.

Theorem tarjan_scc_keep_fa (u v: V) (fav: V):
  Hoare (fun s: @SCCSt V => u <> v /\ v ∈ visited s /\ fa s v = fav)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => v ∈ visited s /\ fa s v = fav).
Proof.
  unfold tarjan_scc.
  hoare_fix_nolv_auto V.
  clear u. intros W IH u.
  unfold tarjan_scc_f.
  eapply Hoare_bind; [apply (preloop_keep_fa u v fav) | simpl; intros].
  eapply Hoare_bind with
    (R := fun (_: unit) s => v ∈ visited s /\ fa s v = fav).
  - apply Hoare_conseq_pre with (P2 := fun s => v ∈ visited s /\ fa s v = fav).
    { intros s' [Hneq' [Hvis' Hfa']]. split; auto. }
    apply forset_process_edge_keep_fa. intros x. apply IH.
  - simpl. intros _. intro_state. hoare_auto_s.
    + apply Hoare_conj.
      * apply Hoare_conseq_pre with (P2 := fun s => v ∈ visited s).
        { intros s1 Hs1. subst s1. destruct H; tauto. }
        apply (pop_scc_keep_visited u v).
      * apply Hoare_conseq_pre with (P2 := fun s => fa s v = fav).
        { intros s1 Hs1. subst s1. destruct H; tauto. }
        apply (pop_scc_keep_fa u v fav).
    + destruct H1. subst s. destruct H; split; auto.
Qed.

(* ================================================================ *)
(* Self-visitation and forall-preservation theorems                  *)
(* ================================================================ *)

(** [tarjan_scc_self_visited]: after calling [tarjan_scc u], vertex
    [u] is guaranteed to be in the [visited] set.  This is proved
    by expanding the fixpoint one step with [tarjan_scc_unfold],
    then using [preloop_self_visited] followed by preservation
    through [forset] and [pop_scc]. *)

Theorem tarjan_scc_self_visited (u: V):
  Hoare (fun s: @SCCSt V => True)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => u ∈ visited s).
Proof.
  rewrite (tarjan_scc_unfold g u).
  unfold tarjan_scc_f.
  eapply Hoare_bind.
  { apply Hoare_conseq_pre with (P2 := fun s => True). auto.
    apply preloop_self_visited. }
  simpl. intros _.
  eapply Hoare_bind with (R := fun _ s => u ∈ visited s).
  + apply forset_process_edge_keep_visited with (v := u).
    intros x. apply (tarjan_scc_keep_visited x u).
  + simpl. intros _. intro_state. hoare_auto_s.
    * apply Hoare_conseq_pre with (P2 := fun s => u ∈ visited s).
      { intros s1 Hs1. subst s1. exact H. }
      apply pop_scc_keep_visited.
    * destruct H1 as [Heq _]. subst s. exact H.
Qed.

(** [tarjan_scc_keep_visited_forall]: the forall version of
    [tarjan_scc_keep_visited].  Uses fixpoint induction directly,
    since the forall-precondition is a valid parameter for
    [Hoare_fix]. *)

Theorem tarjan_scc_keep_visited_forall (u: V) (done: V -> Prop):
  Hoare (fun s: @SCCSt V => forall v, done v -> v ∈ visited s)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => forall v, done v -> v ∈ visited s).
Proof.
  unfold tarjan_scc.
  hoare_fix_nolv_auto V.
  clear u. intros W IH u.
  unfold tarjan_scc_f.
  eapply Hoare_bind. { apply preloop_keep_visited_forall. }
  simpl. intros _.
  eapply Hoare_bind with (R := fun _ s => forall v, done v -> v ∈ visited s).
  - apply forset_process_edge_keep_visited_forall. intros x. apply IH.
  - simpl. intros _. intro_state. hoare_auto_s.
    + apply Hoare_conseq_pre with (P2 := fun s => forall v, done v -> v ∈ visited s).
      { intros s1 Hs1. subst s1. exact H. }
      apply pop_scc_keep_visited_forall.
    + destruct H1 as [-> Hneq]. apply H; auto.
Qed.

(** Derived theorems: dfn/low order is preserved across the
    recursive call.  These are obtained by combining the dfn-
    and low-preserving fixpoint theorems via [Hoare_conj].

    Note: the explicit [dfnx] and [lowy] parameters are required
    because [tarjan_scc_keep_dfn] and [tarjan_scc_keep_low] each
    need the exact pre-state value to match.  The caller should
    supply these from the current state via [get'] or by binding
    the state variable through [intro_state]. *)

Theorem tarjan_scc_keep_dfn_low_order (u x y: V) (dfnx lowy: nat):
  Hoare (fun s: @SCCSt V =>
           u <> x /\ u <> y /\ x ∈ visited s /\ y ∈ visited s
           /\ dfn s x = dfnx /\ low s y = lowy /\ dfnx < lowy)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => dfn s x < low s y).
Proof.
  intro_state.
  destruct H as [Hux [Huy [Hxvis [Hyvis [Hdfneq [Hloweq Hlt]]]]]].
  eapply Hoare_conseq_post.
  2:
  { eapply Hoare_conj.
    - eapply Hoare_conseq_pre with (P2 := fun s => u <> x /\ x ∈ visited s /\ dfn s x = dfnx).
      2: apply (tarjan_scc_keep_dfn u x dfnx).
      intros s Hpre; destruct Hpre; repeat split; auto.
    - eapply Hoare_conseq_pre with (P2 := fun s => u <> y /\ y ∈ visited s /\ low s y = lowy).
      2: apply (tarjan_scc_keep_low u y lowy).
      intros s Hpre; destruct Hpre; repeat split; auto.
  }
  simpl. intros _ s [[_ Hdfn_pres] [_ Hlow_pres]].
  rewrite Hdfn_pres, Hlow_pres. auto.
Qed.

Theorem tarjan_scc_keep_dfn_low_order' (u x y: V) (dfnx lowy: nat):
  Hoare (fun s: @SCCSt V =>
           u <> x /\ u <> y /\ x ∈ visited s /\ y ∈ visited s
           /\ dfn s x = dfnx /\ low s y = lowy /\ ~ dfnx < lowy)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => ~ dfn s x < low s y).
Proof.
  intro_state.
  destruct H as [Hux [Huy [Hxvis [Hyvis [Hdfneq [Hloweq Hnlt]]]]]].
  eapply Hoare_conseq_post.
  2:
  { eapply Hoare_conj.
    - eapply Hoare_conseq_pre with (P2 := fun s => u <> x /\ x ∈ visited s /\ dfn s x = dfnx).
      2: apply (tarjan_scc_keep_dfn u x dfnx).
      intros s Hpre; destruct Hpre; repeat split; auto.
    - eapply Hoare_conseq_pre with (P2 := fun s => u <> y /\ y ∈ visited s /\ low s y = lowy).
      2: apply (tarjan_scc_keep_low u y lowy).
      intros s Hpre; destruct Hpre; repeat split; auto.
  }
  simpl. intros _ s [[_ Hdfn_pres] [_ Hlow_pres]].
  rewrite Hdfn_pres, Hlow_pres. auto.
Qed.

(** prod-wrapped versions for convenience in later files. *)

Theorem tarjan_scc_keep_dfn_prod (u: V) (p: V * nat):
  Hoare (fun s: @SCCSt V => u <> fst p /\ fst p ∈ visited s /\ dfn s (fst p) = snd p)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => fst p ∈ visited s /\ dfn s (fst p) = snd p).
Proof.
  destruct p as [x n]; simpl.
  apply tarjan_scc_keep_dfn.
Qed.

Theorem tarjan_scc_keep_low_prod (u: V) (p: V * nat):
  Hoare (fun s: @SCCSt V => u <> fst p /\ fst p ∈ visited s /\ low s (fst p) = snd p)
        (tarjan_scc (V:=V) (E:=E) (equiv0:=equiv0) (H0:=H0) g u)
        (fun _ s => fst p ∈ visited s /\ low s (fst p) = snd p).
Proof.
  destruct p as [x n]; simpl.
  apply tarjan_scc_keep_low.
Qed.

(* ================================================================ *)
(* Outer Loop Theorems — tarjan_scc_all                              *)
(* ================================================================ *)

Theorem tarjan_scc_all_keep_visited (v: V):
  Hoare (fun s: @SCCSt V => v ∈ visited s)
        (tarjan_scc_all g)
        (fun _ s => v ∈ visited s).
Proof.
  unfold tarjan_scc_all.
  apply Hoare_forset with
    (P := fun (_: V -> Prop) (s: @SCCSt V) => v ∈ visited s).
  - (* ProperP: P is Proper w.r.t. set equivalence *)
    intros done1 done2 Hdone s1 s2 Heq. subst s2. reflexivity.
  - intros done a Hdone_sub Hvalid_a Hnot_done.
    unfold_op. intro_state. hoare_auto_s.
    + (* a ∉ visited: execute tarjan_scc a *)
      eapply Hoare_conseq_pre.
      2: apply (tarjan_scc_keep_visited a v).
      intros s' Heq. subst s'. exact H.
    + (* a already visited: skip *)
      match goal with
      | [ Hconj: _ /\ _ |- _ ] =>
          destruct Hconj; subst; exact H
      end.
Qed.

Theorem tarjan_scc_all_visited_all:
  Hoare (fun s: @SCCSt V => True)
        (tarjan_scc_all g)
        (fun _ s => forall v, original_vvalid g v -> v ∈ visited s).
Proof.
  unfold tarjan_scc_all.
  apply Hoare_conseq_pre with (P1 := fun s => True)
    (P2 := fun s => forall v, ∅ v -> v ∈ visited s).
  - (* Premise: True -> (forall v, ∅ v -> v ∈ visited s) *)
    intros s _. intros v Hv. sets_unfold in Hv. destruct Hv.
  - (* Main goal: Hoare (forall v, ∅ v -> ...) (forset ...) (forall v, vvalid v -> ...) *)
    apply Hoare_forset with
      (P := fun (done: V -> Prop) (s: @SCCSt V) =>
              forall v, done v -> v ∈ visited s)
      (universe := original_vvalid g).
    + (* ProperP *)
      unfold Proper, respectful. intros done1 done2 Hdone s1 s2 Heq. subst s2.
      cbv in Hdone.
      split; intros H v Hv.
      * apply H. specialize (Hdone v) as [_ H21]; apply H21; exact Hv.
      * apply H. specialize (Hdone v) as [H12 _]; apply H12; exact Hv.
    + intros done a Hdone_sub Hvalid_a Hnot_done.
      intro_state. hoare_auto_s.
      * (* a ∉ visited: execute tarjan_scc a *)
        apply Hoare_conseq_post with (Q2 := fun _ s => a ∈ visited s /\ forall v, done v -> v ∈ visited s).
        -- (* postcondition weakening *)
           simpl. intros _ s [Ha_vis Hdone_vis].
           intros v. sets_unfold.
           intros [Hin_done | Hin_a].
           ++ apply Hdone_vis; auto.
           ++ subst v; exact Ha_vis.
        -- (* Hoare triple with stronger postcondition *)
           apply Hoare_conj with (Q1 := fun _ s => a ∈ visited s)
             (Q2 := fun _ s => forall v, done v -> v ∈ visited s).
           ++ apply Hoare_conseq_pre with (P2 := fun s => True).
              { auto. }
              apply tarjan_scc_self_visited.
           ++ apply Hoare_conseq_pre with (P2 := fun s => forall v, done v -> v ∈ visited s).
              { intros s' Heq. subst s'. exact H. }
              apply tarjan_scc_keep_visited_forall.
      * (* a already visited: skip *)
        destruct H1 as [Heq Hnn]. subst s.
        apply NNPP in Hnn.
        sets_unfold in H2. destruct H2 as [Hin_done | Hin_a].
        -- apply H; auto.
        -- subst; exact Hnn.
Qed.

End BASICS.
 