Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Relations.Relations.
Require Import SetsClass.SetsClass.
Require Import GraphLib.graph_basic.
Require Import GraphLib.Syntax.
Require Import GraphLib.examples.tarjan.

Local Open Scope sets.

Section SCC_DEFS.
  Context {V E: Type} (g: OriginalGraphType V E)
          (Hgvalid: OriginalGraphProp V E g)
          (finite_vertices: forall v, original_vvalid g v -> In v (original_listV g)).

  (* ================================================================ *)
  (* Section 0: dg_step / dg_reachable — Directed graph primitives   *)
  (* ================================================================ *)

  (** [dg_step g x y] holds when there is a directed edge from x to y
      in the original graph.  Unlike the undirected [step] from
      [reachable_basic], this relation is NOT symmetric. *)
  Definition dg_step (g: OriginalGraphType V E) (x y: V): Prop :=
    exists e, original_step g e /\
              original_step_fst g e = x /\
              original_step_snd g e = y.

  (** [dg_reachable g x y] is the reflexive-transitive closure of
      [dg_step g x y], i.e. there is a (possibly empty) directed path
      from x to y. *)
  Definition dg_reachable (g: OriginalGraphType V E) (x y: V): Prop :=
    @Coq.Relations.Relation_Operators.clos_refl_trans V (dg_step g) x y.

  Lemma dg_reachable_refl : forall x,
    original_vvalid g x -> dg_reachable g x x.
  Proof.
    intros. apply Coq.Relations.Relation_Operators.rt_refl.
  Qed.

  (** Unconditional reflexivity — [clos_refl_trans] is reflexive
      for all vertices, even invalid ones.  Useful in inductions
      where validity information is not available. *)
  Lemma dg_reachable_refl' : forall x, dg_reachable g x x.
  Proof.
    intros. apply Coq.Relations.Relation_Operators.rt_refl.
  Qed.

  Lemma dg_reachable_trans : forall x y z,
    dg_reachable g x y -> dg_reachable g y z -> dg_reachable g x z.
  Proof.
    intros x y z H1 H2.
    eapply Coq.Relations.Relation_Operators.rt_trans; eauto.
  Qed.

  Lemma dg_reachable_step : forall x y,
    dg_step g x y -> dg_reachable g x y.
  Proof.
    intros x y Hstep.
    apply Coq.Relations.Relation_Operators.rt_step. exact Hstep.
  Qed.

  Lemma dg_step_vvalid : forall x y,
    dg_step g x y -> original_vvalid g x /\ original_vvalid g y.
  Proof.
    intros x y [e [Hstep [Hfst Hsnd]]].
    destruct Hgvalid as [Hfst_valid Hsnd_valid Hfinite].
    split; [rewrite <- Hfst | rewrite <- Hsnd];
    [apply Hfst_valid | apply Hsnd_valid]; exact Hstep.
  Qed.

  Lemma dg_reachable_vvalid : forall x y,
    x <> y -> dg_reachable g x y -> original_vvalid g x /\ original_vvalid g y.
  Proof.
    intros x y Hneq Hreach.
    generalize dependent y.
    intro y. intro Hneq'. intro Hreach'.
    induction Hreach'.
    - apply dg_step_vvalid. auto.
    - exfalso. apply Hneq'. reflexivity.
    - destruct (classic (x = y)).
      + subst x. apply IHHreach'2. auto.
      + destruct (classic (y = z)).
        * subst z. apply IHHreach'1. auto.
        * assert (Hv1: original_vvalid g x /\ original_vvalid g y)
            by (apply IHHreach'1; auto).
          assert (Hv2: original_vvalid g y /\ original_vvalid g z)
            by (apply IHHreach'2; auto).
          split; tauto.
  Qed.

  Lemma dg_step_reachable_reachable : forall x y z,
    dg_step g x y -> dg_reachable g y z -> dg_reachable g x z.
  Proof.
    intros x y z Hstep Hreach.
    apply dg_reachable_step in Hstep.
    eapply dg_reachable_trans; eauto.
  Qed.

  Lemma dg_reachable_step_reachable : forall x y z,
    dg_reachable g x y -> dg_step g y z -> dg_reachable g x z.
  Proof.
    intros x y z Hreach Hstep.
    apply dg_reachable_step in Hstep.
    eapply dg_reachable_trans; eauto.
  Qed.

  (* ================================================================ *)
  (* Section 1: mutually_reachable — Mutual reachability              *)
  (* ================================================================ *)

  (** Two vertices are mutually reachable if there is a directed path
      in both directions.  This is an equivalence relation on the set
      of valid vertices. *)
  Definition mutually_reachable (g: OriginalGraphType V E) (u v: V) : Prop :=
    dg_reachable g u v /\ dg_reachable g v u.

  Lemma mutually_reachable_refl : forall u,
    original_vvalid g u -> mutually_reachable g u u.
  Proof.
    intros u Hu. split; apply dg_reachable_refl; auto.
  Qed.

  Lemma mutually_reachable_sym : forall u v,
    mutually_reachable g u v -> mutually_reachable g v u.
  Proof.
    intros u v [Huv Hvu]. split; assumption.
  Qed.

  Lemma mutually_reachable_trans : forall u v w,
    mutually_reachable g u v -> mutually_reachable g v w -> mutually_reachable g u w.
  Proof.
    intros u v w [Huv Hvu] [Hvw Hwv].
    split; [eapply dg_reachable_trans; eauto | eapply dg_reachable_trans; eauto].
  Qed.

  Lemma mutually_reachable_vvalid_l : forall u v,
    u <> v -> mutually_reachable g u v -> original_vvalid g u.
  Proof.
    intros u v Hneq [Huv _].
    apply (dg_reachable_vvalid u v Hneq) in Huv. destruct Huv. auto.
  Qed.

  Lemma mutually_reachable_vvalid_r : forall u v,
    u <> v -> mutually_reachable g u v -> original_vvalid g v.
  Proof.
    intros u v Hneq [_ Hvu].
    apply (dg_reachable_vvalid v u) in Hvu; [destruct Hvu; auto |].
    intro Heq. apply Hneq. symmetry. exact Heq.
  Qed.

  Lemma dg_reachable_mutually_reachable : forall u v,
    dg_reachable g u v -> dg_reachable g v u -> mutually_reachable g u v.
  Proof.
    intros u v Huv Hvu. split; assumption.
  Qed.

  (* ================================================================ *)
  (* Section 2: is_SCC — SCC predicate                                *)
  (* ================================================================ *)

  (** [is_SCC g s] holds when [s] is a strongly connected component
      of [g].  Three conditions:
      - Non-emptiness: [s] contains at least one valid vertex.
      - Internal MR: any two vertices in [s] are mutually reachable.
      - Maximality: any vertex mutually reachable with a member of [s]
        is also in [s]. *)
  Definition is_SCC (g: OriginalGraphType V E) (s: V -> Prop) : Prop :=
    (exists v, s v /\ original_vvalid g v) /\
    (forall u v, s u -> s v -> mutually_reachable g u v) /\
    (forall u v, s u -> original_vvalid g v -> mutually_reachable g u v -> s v).

  Lemma is_SCC_vvalid : forall s u,
    is_SCC g s -> s u -> original_vvalid g u.
  Proof.
    intros s u [Hex [Hmr Hmax]] Hsu.
    destruct Hex as [v [Hsv Hvv]].
    destruct (classic (u = v)).
    - subst. auto.
    - apply Hmr with u v in Hsu; [| assumption].
      apply mutually_reachable_vvalid_l with v; auto.
  Qed.

  Lemma is_SCC_closed_under_mr : forall s u v,
    is_SCC g s -> s u -> mutually_reachable g u v -> s v.
  Proof.
    intros s u v Hiscc Hsu Hmr_uv.
    pose proof Hiscc as [_ [_ Hmax]].
    destruct (classic (u = v)).
    - subst. auto.
    - apply Hmax with u; auto.
      apply mutually_reachable_vvalid_r with u; auto.
  Qed.

  Lemma is_SCC_mutually_reachable_in : forall s u v,
    is_SCC g s -> s u -> mutually_reachable g u v ->
    s v /\ mutually_reachable g u v.
  Proof.
    intros s u v Hiscc Hsu Hmr.
    split; [eapply is_SCC_closed_under_mr; eauto | auto].
  Qed.

  Lemma is_SCC_maximal : forall s1 s2,
    is_SCC g s1 -> is_SCC g s2 ->
    (forall v, s1 v -> s2 v) -> (forall v, s2 v -> s1 v).
  Proof.
    intros s1 s2 Hiscc1 Hiscc2 Hincl v Hs2v.
    destruct Hiscc1 as [[u0 [Hs1u0 Hvu0]] [Hmr1 Hmax1]].
    assert (Hs2u0: s2 u0) by (apply Hincl; auto).
    destruct Hiscc2 as [_ [Hmr2 _]].
    apply Hmr2 with v u0 in Hs2v; [| exact Hs2u0].
    apply (Hmax1 u0 v Hs1u0).
    - destruct (classic (v = u0)).
      + subst v. exact Hvu0.
      + apply (mutually_reachable_vvalid_l v u0 H Hs2v).
    - apply mutually_reachable_sym. exact Hs2v.
  Qed.

  Lemma is_SCC_extensional : forall s1 s2,
    is_SCC g s1 -> is_SCC g s2 ->
    (forall v, s1 v <-> s2 v) -> (forall v, s1 v = s2 v).
  Proof.
    intros s1 s2 Hiscc1 Hiscc2 Hequiv v.
    destruct (Hequiv v) as [H12 H21].
    apply propositional_extensionality.
    split; assumption.
  Qed.

  Lemma mutually_reachable_is_SCC : forall u,
    original_vvalid g u -> is_SCC g (fun v => mutually_reachable g u v).
  Proof.
    intros u Hu.
    split; [| split].
    - exists u. split.
      + apply mutually_reachable_refl. auto.
      + auto.
    - intros v w Hmr_uv Hmr_uw.
      apply mutually_reachable_sym in Hmr_uv.
      eapply mutually_reachable_trans; eauto.
    - intros v w Hmr_uv Hvw Hmr_uw.
      eapply mutually_reachable_trans; [exact Hmr_uv | exact Hmr_uw].
  Qed.

  (* ================================================================ *)
  (* Section 3: scc_partition — SCC partition                         *)
  (* ================================================================ *)

  (** [scc_partition g sccs] holds when [sccs] is a valid SCC
      partition of [g]:
      - Coverage: every valid vertex belongs to some SCC in [sccs].
      - Correctness: every element of [sccs] is an SCC.
      - Disjointness: two different SCCs share no vertices. *)
  Definition scc_partition (g: OriginalGraphType V E) (sccs: list (V -> Prop)) : Prop :=
    (forall v, original_vvalid g v -> exists s, In s sccs /\ s v) /\
    (forall s, In s sccs -> is_SCC g s) /\
    (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v ->
      (forall w, s1 w = s2 w)).

  Lemma scc_partition_disjoint : forall sccs s1 s2,
    scc_partition g sccs -> In s1 sccs -> In s2 sccs -> s1 <> s2 ->
    forall v, ~ (s1 v /\ s2 v).
  Proof.
    intros sccs s1 s2 [Hcov [Hcorr Hdisj]] Hin1 Hin2 Hneq v [Hs1v Hs2v].
    apply Hneq. apply functional_extensionality.
    apply (Hdisj s1 s2 v Hin1 Hin2 Hs1v Hs2v).
  Qed.

  Lemma mutually_reachable_same_SCC : forall u v sccs,
    original_vvalid g u -> scc_partition g sccs -> mutually_reachable g u v ->
    exists s, In s sccs /\ s u /\ s v.
  Proof.
    intros u v sccs Hu [Hcov [Hcorr Hdisj]] Hmr.
    destruct (Hcov u Hu) as [s [Hin Hsu]].
    exists s. split; [auto | split; auto].
    eapply is_SCC_closed_under_mr; eauto.
  Qed.

  Lemma scc_partition_unique_SCC : forall u sccs,
    original_vvalid g u -> scc_partition g sccs ->
    exists! s, In s sccs /\ s u.
  Proof.
    intros u sccs Hu [Hcov [Hcorr Hdisj]].
    destruct (Hcov u Hu) as [s [Hin Hsu]].
    exists s. split; [split; assumption |].
    intros s' [Hin' Hs'u].
    apply functional_extensionality.
    apply (Hdisj s s' u Hin Hin' Hsu Hs'u).
  Qed.

  (* Helper: construct scc_of v = { w | mutually_reachable v w } for all
     valid vertices, collecting distinct ones into a list. *)
  Theorem scc_partition_exists :
    exists sccs, scc_partition g sccs.
  Proof.
    set (scc_of := fun (v: V) => fun w => mutually_reachable g v w).
    assert (H_scc_of_SCC: forall v, original_vvalid g v -> is_SCC g (scc_of v)).
    { intros v Hv. unfold scc_of. apply mutually_reachable_is_SCC. auto. }

    set (l := original_listV g).
    pose (build_sccs :=
      (fix build_sccs (xs: list V) (acc: list (V -> Prop)) : list (V -> Prop) :=
        match xs with
        | nil => acc
        | x :: xs' =>
            if excluded_middle_informative
                 (original_vvalid g x /\ ~ exists s, In s acc /\ s x)
            then build_sccs xs' (scc_of x :: acc)
            else build_sccs xs' acc
        end)).
    exists (build_sccs l nil).

    (* Helper: build_sccs preserves all elements of acc *)
    assert (Hpreserve: forall xs acc s,
      In s acc -> In s (build_sccs xs acc)).
    { induction xs as [|x xs IH]; intros acc s Hin; simpl.
      - exact Hin.
      - destruct (excluded_middle_informative _).
        + apply IH. simpl. right. exact Hin.
        + apply IH. exact Hin. }

    (* Helper: if v is covered by acc, it's covered by the result *)
    assert (Hcov_aux: forall xs acc v,
      original_vvalid g v ->
      (exists s, In s acc /\ s v) ->
      exists s, In s (build_sccs xs acc) /\ s v).
    { induction xs as [|x xs IH]; intros acc v Hv Hex; simpl.
      - destruct Hex as [s [Hin Hs_v]]. exists s; auto.
      - destruct (excluded_middle_informative _) as [[_ _] | _].
        + destruct Hex as [s [Hin Hs_v]].
          apply (IH (scc_of x :: acc) v Hv).
          exists s. split; [| exact Hs_v].
          simpl. right. exact Hin.
        + apply (IH acc v Hv Hex). }

    (* Coverage: every valid vertex in xs is covered by build_sccs xs acc *)
    assert (Hcov: forall xs acc v,
      original_vvalid g v -> In v xs ->
      exists s, In s (build_sccs xs acc) /\ s v).
    { induction xs as [|x xs IH]; intros acc v Hv Hin; simpl in Hin.
      - inversion Hin.
      - destruct Hin as [Heq | Hin_tail].
        + subst x. simpl.
          destruct (excluded_middle_informative _) as [[Hvx Hnot] | Hskip].
          * (* add scc_of v: it will be in the result via Hcov_aux *)
            apply (Hcov_aux xs (scc_of v :: acc) v Hv).
            exists (scc_of v). split.
            -- constructor 1. reflexivity.
            -- unfold scc_of. apply mutually_reachable_refl. auto.
          * (* v skipped: acc already covers v *)
            destruct (classic (exists s, In s acc /\ s v)) as [Hex | Hnex].
            -- destruct Hex as [s [Hin_acc Hs_v]].
               exists s. split; [apply (Hpreserve xs acc s Hin_acc) | auto].
            -- exfalso. apply Hskip. split; [exact Hv | exact Hnex].
        + (* v in tail *)
          simpl.
          destruct (excluded_middle_informative _) as [[Hvx Hnot] | Hskip].
          * (* x is new — search in recursive call with expanded acc *)
            apply (IH (scc_of x :: acc) v Hv Hin_tail).
          * (* x skipped — search in recursive call with same acc *)
            apply (IH acc v Hv Hin_tail). }

    (* Correctness helper: all SCCs in build_sccs are valid *)
    assert (Hcorr: forall xs acc,
      (forall s, In s acc -> is_SCC g s) ->
      (forall s, In s (build_sccs xs acc) -> is_SCC g s)).
    { induction xs as [|x xs IH]; intros acc Hacc s Hin; simpl in Hin.
      - apply Hacc. auto.
      - destruct (excluded_middle_informative _).
        + (* then: scc_of x added to acc *)
          apply (IH (scc_of x :: acc)); auto.
          intros s0 [Heq' | Hin_acc].
          -- subst s0. apply H_scc_of_SCC. destruct a as [Hvx _]. auto.
          -- apply Hacc. auto.
        + (* else: acc unchanged *)
          apply (IH acc); auto. }

    (* Disjointness helper *)
    assert (Hdisj: forall xs acc s1 s2 v,
      (forall s, In s acc -> is_SCC g s) ->
      (forall s1 s2 v, In s1 acc -> In s2 acc -> s1 v -> s2 v -> forall w, s1 w = s2 w) ->
      In s1 (build_sccs xs acc) -> In s2 (build_sccs xs acc) ->
      s1 v -> s2 v -> forall w, s1 w = s2 w).
    { induction xs as [|x xs IH]; intros acc s1 s2 v Hacc_corr Hacc_disj Hin1 Hin2 Hs1v Hs2v; simpl in Hin1, Hin2.
      - eapply Hacc_disj; eauto.
      - destruct (excluded_middle_informative _) as [[Hvx Hnot] | Hskip].
        + (* then: scc_of x added to acc *)
          apply (IH (scc_of x :: acc) s1 s2 v); auto.
          * (* Hacc_corr for extended acc *)
            intros s [Heq | Hin_acc].
            -- subst s. apply H_scc_of_SCC. exact Hvx.
            -- apply Hacc_corr. exact Hin_acc.
          * (* Hacc_disj for extended acc *)
            intros s0 s3 v0 [Heq0 | Hin_a1] [Heq3 | Hin_a2] Hs0v Hsv0.
            -- (* s0 = s3 = scc_of x *) subst s0 s3. reflexivity.
            -- (* s0 = scc_of x, s3 in acc *)
              subst s0. pose proof (Hacc_corr _ Hin_a2) as Hiscc3.
              apply (is_SCC_extensional (scc_of x) s3); [| |].
              { apply H_scc_of_SCC. exact Hvx. }
              { exact Hiscc3. }
              { intro v'. split.
                - (* (scc_of x) v' -> s3 v' *)
                  intros Hxv'. unfold scc_of in Hxv', Hs0v.
                  assert (Hmr: mutually_reachable g v0 v').
                  { apply mutually_reachable_sym in Hs0v.
                    eapply mutually_reachable_trans; eauto. }
                  eapply (is_SCC_closed_under_mr s3 v0 v'); eauto.
                - (* s3 v' -> (scc_of x) v' *)
                  intros Hsv'. unfold scc_of.
                  destruct Hiscc3 as [_ [Hmr_scc _]].
                  pose proof (Hmr_scc v0 v' Hsv0 Hsv') as Hmr_v0v'.
                  (* Hmr_v0v': mutually_reachable g v0 v' *)
                  destruct Hs0v as [Hxv0 Hv0x].
                  (* Hs0v: mutually_reachable g x v0 *)
                  destruct Hmr_v0v' as [Hv0v' Hv'v0].
                  split.
                  + eapply dg_reachable_trans; [exact Hxv0 | exact Hv0v'].
                  + eapply dg_reachable_trans; [exact Hv'v0 | exact Hv0x]. }
            -- (* s0 in acc, s3 = scc_of x *)
              subst s3. pose proof (Hacc_corr _ Hin_a1) as Hiscc0.
              apply (is_SCC_extensional s0 (scc_of x)); [| |].
              { exact Hiscc0. }
              { apply H_scc_of_SCC. exact Hvx. }
              { intro v'. split.
                - (* s0 v' -> (scc_of x) v' *)
                  intros Hsv'. unfold scc_of.
                  destruct Hiscc0 as [_ [Hmr_scc _]].
                  pose proof (Hmr_scc v0 v' Hs0v Hsv') as Hmr_v0v'.
                  (* Hmr_v0v': mutually_reachable g v0 v' *)
                  destruct Hsv0 as [Hxv0 Hv0x].
                  (* Hsv0: mutually_reachable g x v0 *)
                  destruct Hmr_v0v' as [Hv0v' Hv'v0].
                  split.
                  + eapply dg_reachable_trans; [exact Hxv0 | exact Hv0v'].
                  + eapply dg_reachable_trans; [exact Hv'v0 | exact Hv0x].
                - (* (scc_of x) v' -> s0 v' *)
                  intros Hxv'. unfold scc_of in Hxv', Hsv0.
                  assert (Hmr: mutually_reachable g v0 v').
                  { apply mutually_reachable_sym in Hsv0.
                    eapply mutually_reachable_trans; eauto. }
                  eapply (is_SCC_closed_under_mr s0 v0 v'); eauto. }
            -- (* s0 in acc, s3 in acc *)
              eapply Hacc_disj; eauto.
        + (* else: acc unchanged *)
          apply (IH acc s1 s2 v); auto. }

    (* Assemble the final result *)
    unfold scc_partition. split; [| split].
    - intros v Hv. apply (Hcov l nil v Hv). apply finite_vertices. auto.
    - intros s Hin. apply (Hcorr l nil). { intros s0 Hin0. inversion Hin0. } auto.
    - intros s1 s2 v Hin1 Hin2 Hs1v Hs2v w.
      apply (Hdisj l nil s1 s2 v).
      + intros s0 Hin0. inversion Hin0.
      + intros s0 s3 v0 Hin0 _. inversion Hin0.
      + auto.
      + auto.
      + auto.
      + auto.
  Qed.

  (* ================================================================ *)
  (* Section 4: condensation — Condensation graph DAG                 *)
  (* ================================================================ *)

  (** [condensation_edge sccs s1 s2]: there is a directed edge from
      SCC [s1] to a different SCC [s2] in the condensation graph. *)
  Definition condensation_edge (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
    In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
    exists u v, s1 u /\ s2 v /\ dg_step g u v.

  (** [condensation_path] is the transitive closure of
      [condensation_edge].  Defined as an inductive predicate because
      the condensation graph's vertex type ([V -> Prop]) is not a
      [Graph] instance. *)
  Inductive condensation_path (sccs: list (V -> Prop)) :
    (V -> Prop) -> (V -> Prop) -> Prop :=
    | cp_edge : forall s1 s2,
        condensation_edge sccs s1 s2 ->
        condensation_path sccs s1 s2
    | cp_trans : forall s1 s2 s3,
        condensation_path sccs s1 s2 ->
        condensation_path sccs s2 s3 ->
        condensation_path sccs s1 s3.

  (** [condensation_reachable sccs s1 s2]: SCC [s2] is reachable from
      SCC [s1] in the condensation graph (including the zero-step
      case). *)
  Definition condensation_reachable (sccs: list (V -> Prop))
    (s1 s2: V -> Prop) : Prop :=
    s1 = s2 \/ condensation_path sccs s1 s2.

  (** Every original directed edge is either internal to an SCC or
      connects two different SCCs (producing a condensation edge). *)
  Lemma dg_step_SCC_classify : forall sccs u v,
    scc_partition g sccs -> dg_step g u v ->
    (exists s, In s sccs /\ s u /\ s v)
    \/
    (exists s1 s2,
      In s1 sccs /\ In s2 sccs /\ s1 u /\ s2 v /\
      condensation_edge sccs s1 s2).
  Proof.
    intros sccs u v Hpart Hstep.
    destruct Hpart as [Hcov [Hcorr Hdisj]].
    (* u and v are valid by dg_step_vvalid *)
    pose proof Hstep as Hstep_copy.
    apply dg_step_vvalid in Hstep as [Hu Hv].
    destruct Hstep_copy as [e [Hstep' [Hfst Hsnd]]].
    (* Get the SCC containing u *)
    destruct (Hcov u Hu) as [su [Hin_u Hsu_u]].
    (* Get the SCC containing v *)
    destruct (Hcov v Hv) as [sv [Hin_v Hsv_v]].
    (* Check if su and sv are the same *)
    destruct (classic (forall w, su w = sv w)) as [Heq_sccs | Hneq_sccs].
    - left. exists su. split; [auto | split; auto].
      rewrite (Heq_sccs v). auto.
    - right. exists su, sv.
      assert (Hedge: condensation_edge sccs su sv).
      { repeat split; auto.
        - intro Heq. apply Hneq_sccs. subst sv. reflexivity.
        - exists u, v. split; [auto | split; [auto |]].
          exists e. split; [exact Hstep' | split]; assumption. }
      split; [auto | split; [auto | split; [auto | split; [auto | auto]]]].
  Qed.

  (** Bridge: a condensation_path implies original-graph reachability
      between representative vertices. *)
  Lemma condensation_path_to_dg_reachable : forall sccs s1 s2 u v,
    scc_partition g sccs ->
    condensation_path sccs s1 s2 ->
    s1 u -> s2 v ->
    dg_reachable g u v.
  Proof.
    intros sccs s1 s2 u v Hpart Hpath.
    assert (path_member: forall sccs' a b, condensation_path sccs' a b -> In b sccs').
    { intros sccs' a0 b0 Hcp. induction Hcp.
      - destruct H as [_ [? _]]. auto.
      - auto. }
    revert u v.
    induction Hpath as [sa sb Hedge | sa sb sc Hpath1 IH1 Hpath2 IH2]; intros u v Hsu Hsv.
    - (* cp_edge *)
      destruct Hedge as [Hin_a [Hin_b [Hneq [x [y [Hsax [Hsby Hstep]]]]]]].
      destruct Hpart as [Hcov [Hcorr Hdisj]].
      destruct (Hcorr sa Hin_a) as [_ [Hmr_a _]].
      destruct (Hcorr sb Hin_b) as [_ [Hmr_b _]].
      destruct (Hmr_a u x Hsu Hsax) as [Hux _].
      destruct (Hmr_b y v Hsby Hsv) as [Hyv _].
      apply dg_reachable_step in Hstep.
      eapply dg_reachable_trans; [exact Hux |].
      eapply dg_reachable_trans; [exact Hstep | exact Hyv].
    - (* cp_trans *)
      destruct Hpart as [Hcov [Hcorr Hdisj]].
      destruct (Hcorr sb (path_member sccs sa sb Hpath1)) as [[w [Hsbw _]] _].
      pose proof (IH1 u w Hsu Hsbw) as Huw.
      pose proof (IH2 w v Hsbw Hsv) as Hwv.
      eapply dg_reachable_trans; [exact Huw | exact Hwv].
  Qed.

  (** A condensation edge implies one-way reachability in the original
      graph but NOT mutual reachability. *)
  Lemma condensation_edge_oneway : forall sccs s1 s2 u v,
    scc_partition g sccs ->
    condensation_edge sccs s1 s2 ->
    s1 u -> s2 v ->
    dg_reachable g u v /\ ~ mutually_reachable g u v.
  Proof.
    intros sccs s1 s2 u v Hpart Hedge Hsu Hsv.
    destruct Hedge as [Hin1 [Hin2 [Hneq [x [y [Hs1x [Hs2y Hstep]]]]]]].
    destruct Hpart as [Hcov [Hcorr Hdisj]].
    split.
    - destruct (Hcorr s1 Hin1) as [_ [Hmr1 _]].
      destruct (Hcorr s2 Hin2) as [_ [Hmr2 _]].
      destruct (Hmr1 u x Hsu Hs1x) as [Hux _].
      destruct (Hmr2 y v Hs2y Hsv) as [Hyv _].
      apply dg_reachable_step in Hstep.
      eapply dg_reachable_trans; [exact Hux |].
      eapply dg_reachable_trans; [exact Hstep | exact Hyv].
    - intros [Huv Hvu].
      destruct (Hcorr s1 Hin1) as [_ [_ Hmax1]].
      assert (Hvv: original_vvalid g v).
      { destruct (classic (u = v)).
        - subst. eapply is_SCC_vvalid; eauto.
        - eapply mutually_reachable_vvalid_r with (u := u); eauto. split; auto. }
      assert (Hs1v: s1 v) by (apply Hmax1 with u; auto; split; auto).
      apply Hneq. apply functional_extensionality.
      apply (Hdisj s1 s2 v Hin1 Hin2 Hs1v Hsv).
  Qed.

  (** The condensation of an SCC partition is acyclic — there is no
      condensation edge whose target can reach back to its source. *)
  Theorem condensation_is_acyclic : forall sccs,
    scc_partition g sccs ->
    forall s1 s2,
      condensation_edge sccs s1 s2 ->
      ~ condensation_reachable sccs s2 s1.
  Proof.
    intros sccs Hpart s1 s2 Hedge Hreach.
    destruct Hedge as [Hin1 [Hin2 [Hneq [u [v [Hs1u [Hs2v Hstep]]]]]]].
    destruct Hreach as [Heq | Hpath].
    - apply Hneq. symmetry. exact Heq.
    - pose proof (condensation_path_to_dg_reachable sccs s2 s1 v u Hpart Hpath Hs2v Hs1u) as Hvu.
      pose proof (condensation_edge_oneway sccs s1 s2 u v Hpart
        (conj Hin1 (conj Hin2 (conj Hneq (ex_intro (fun u0 => _) u
          (ex_intro (fun v0 => _) v (conj Hs1u (conj Hs2v Hstep)))))))
        Hs1u Hs2v) as [Huv' Hnot_mr].
      apply Hnot_mr.
      split; [apply dg_reachable_step; exact Hstep | exact Hvu].
  Qed.

  (** Equivalent formulation: the condensation graph has no directed
      cycle involving at least one condensation edge. *)
  Theorem condensation_no_cycle : forall sccs,
    scc_partition g sccs ->
    ~ exists s1 s2,
      condensation_edge sccs s1 s2 /\
      condensation_path sccs s2 s1.
  Proof.
    intros sccs Hpart [s1 [s2 [Hedge Hpath]]].
    apply (condensation_is_acyclic sccs Hpart s1 s2 Hedge).
    right. exact Hpath.
  Qed.

  (* ================================================================ *)
  (* Section 5: reverse_graph — Graph reversal & SCC invariance       *)
  (* ================================================================ *)

  (** [reverse_graph g] swaps the direction of every edge in [g].
      All other fields ([original_vvalid], [original_step],
      [original_listV]) remain unchanged. *)
  Definition reverse_graph (g: OriginalGraphType V E) : OriginalGraphType V E :=
    {|
      original_vvalid   := g.(original_vvalid);
      original_step     := g.(original_step);
      original_step_fst := g.(original_step_snd);
      original_step_snd := g.(original_step_fst);
      original_listV    := g.(original_listV);
    |}.

  (** The reversal of a valid [OriginalGraph] is still valid. *)
  Lemma reverse_graph_gvalid :
    @OriginalGraphProp V E (reverse_graph g).
  Proof.
    destruct Hgvalid as [Hfst_valid Hsnd_valid Hfinite].
    constructor; simpl; intros; auto.
    (* Goal 1: fst_valid for reverse_graph — uses Hsnd_valid since fst←snd swap *)
    (* Goal 2: snd_valid for reverse_graph — uses Hfst_valid since snd←fst swap *)
    (* Goal 3: finite_vertices — unchanged *)
  Qed.

  (** Reversal swaps the direction of [dg_step]. *)
  Lemma dg_step_reverse : forall u v,
    dg_step (reverse_graph g) u v <-> dg_step g v u.
  Proof.
    intros u v. split.
    - intros [e [Hstep [Hfst Hsnd]]].
      exists e. split; [exact Hstep |].
      simpl in Hfst, Hsnd.
      (* In reverse_graph, fst = original_snd, snd = original_fst *)
      split; assumption.
    - intros [e [Hstep [Hfst Hsnd]]].
      exists e. split; [exact Hstep |].
      simpl.
      split; assumption.
  Qed.

  (** Reversal swaps the direction of [dg_reachable]. *)
  Lemma dg_reachable_reverse : forall u v,
    dg_reachable (reverse_graph g) u v <-> dg_reachable g v u.
  Proof.
    intros u v. split.
    - intro H. generalize dependent v. intro t. intro H0. induction H0.
      + apply Coq.Relations.Relation_Operators.rt_step.
        apply (proj1 (dg_step_reverse x y)). exact H.
      + apply Coq.Relations.Relation_Operators.rt_refl.
      + eapply Coq.Relations.Relation_Operators.rt_trans;
          [exact IHclos_refl_trans2 | exact IHclos_refl_trans1].
    - intro H. generalize dependent v. intro t. intro H0. induction H0.
      + apply Coq.Relations.Relation_Operators.rt_step.
        apply (proj2 (dg_step_reverse y x)). exact H.
      + apply Coq.Relations.Relation_Operators.rt_refl.
      + eapply Coq.Relations.Relation_Operators.rt_trans;
          [exact IHclos_refl_trans2 | exact IHclos_refl_trans1].
  Qed.

  (** Mutual reachability is invariant under graph reversal. *)
  Lemma mutually_reachable_reverse : forall u v,
    mutually_reachable g u v <-> mutually_reachable (reverse_graph g) u v.
  Proof.
    intros u v.
    unfold mutually_reachable.
    split; intros [Huv Hvu];
      split; apply dg_reachable_reverse; auto.
  Qed.

  (** Whether a set is an SCC is invariant under graph reversal. *)
  Corollary is_SCC_reverse : forall s,
    is_SCC g s <-> is_SCC (reverse_graph g) s.
  Proof.
    intro s. unfold is_SCC. split.
    - intros [Hne [Hmr Hmax]]. simpl. split; [| split].
      + destruct Hne as [v [Hsv Hvv]]. exists v. split; auto.
      + intros u v0 Hsu Hsv0. apply mutually_reachable_reverse. apply Hmr; auto.
      + intros u v0 Hsu Hvv0 Hmr_uv.
        apply Hmax with u; auto.
        apply mutually_reachable_reverse. auto.
    - intros [Hne [Hmr Hmax]]. simpl. split; [| split].
      + destruct Hne as [v [Hsv Hvv]]. exists v. split; auto.
      + intros u v0 Hsu Hsv0. apply mutually_reachable_reverse. apply Hmr; auto.
      + intros u v0 Hsu Hvv0 Hmr_uv.
        apply Hmax with u; auto.
        apply mutually_reachable_reverse. auto.
  Qed.

  (** Whether a list is an SCC partition is invariant under graph
      reversal. *)
  Corollary scc_partition_reverse : forall sccs,
    scc_partition g sccs <-> scc_partition (reverse_graph g) sccs.
  Proof.
    intro sccs. unfold scc_partition. split.
    - intros [Hcov [Hcorr Hdisj]]. simpl. split; [| split].
      + intros v Hvv. apply Hcov. simpl in Hvv. exact Hvv.
      + intros s Hin. apply is_SCC_reverse. apply Hcorr. auto.
      + intros s1 s2 v Hin1 Hin2 Hs1v Hs2v.
        exact (Hdisj s1 s2 v Hin1 Hin2 Hs1v Hs2v).
    - intros [Hcov [Hcorr Hdisj]]. simpl. split; [| split].
      + intros v Hvv. apply Hcov. simpl in Hvv. exact Hvv.
      + intros s Hin. apply is_SCC_reverse. apply Hcorr. auto.
      + intros s1 s2 v Hin1 Hin2 Hs1v Hs2v.
        exact (Hdisj s1 s2 v Hin1 Hin2 Hs1v Hs2v).
  Qed.

End SCC_DEFS.
