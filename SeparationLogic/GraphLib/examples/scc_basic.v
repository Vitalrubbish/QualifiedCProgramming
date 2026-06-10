Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import Lia.

Local Open Scope sets_scope.

(* ================================================================ *)
(* 1. Directed Graph Type                                           *)
(* ================================================================ *)

(** DirectedGraphType: concrete representation of a directed graph.
    Edges have a fixed direction from source to target.
    Contrast with tarjan.v's OriginalGraphType which has undirected semantics. *)
Record DirectedGraphType {V E: Type} := {
  dg_vvalid   : V -> Prop;
  dg_evalid   : E -> Prop;
  dg_source   : E -> V;
  dg_target   : E -> V;
  dg_listV    : list V;
}.

Arguments DirectedGraphType _ _ : clear implicits.

(** DirectedGraphProp: well-formedness conditions for a directed graph *)
Record DirectedGraphProp {V E: Type} (dg: DirectedGraphType V E) : Prop := {
  dg_source_valid : forall e, dg_evalid dg e -> dg_vvalid dg (dg_source dg e);
  dg_target_valid : forall e, dg_evalid dg e -> dg_vvalid dg (dg_target dg e);
  dg_finite_v     : forall v, dg_vvalid dg v -> In v (dg_listV dg);
}.

Arguments DirectedGraphProp _ _ : clear implicits.

(** dg_step_aux: a directed edge e goes strictly from x to y.
    Unlike OriginalGraphType's step_aux which allows either direction,
    dg_step_aux enforces x = source(e) and y = target(e). *)
Record dg_step_aux {V E: Type} (dg: DirectedGraphType V E) (e: E) (x y: V) : Prop := {
  dg_vx  : dg_vvalid dg x;
  dg_vy  : dg_vvalid dg y;
  dg_ve  : dg_evalid dg e;
  dg_dir : dg_source dg e = x /\ dg_target dg e = y;
}.

(* ================================================================ *)
(* 2. Type Class Instances for DirectedGraphType                    *)
(* ================================================================ *)

#[export] Instance DirectedGraph_graph {V E: Type} :
  Graph (DirectedGraphType V E) V E := {|
  graph_basic.vvalid := dg_vvalid;
  graph_basic.evalid := dg_evalid;
  graph_basic.step_aux := dg_step_aux;
|}.

#[export] Instance DirectedGraph_gvalid {V E: Type} :
  GValid (DirectedGraphType V E) :=
  @DirectedGraphProp V E.

#[export] Instance DirectedGraph_stepvalid {V E: Type} :
  StepValid (DirectedGraphType V E) V E.
Proof.
  split; intros; destruct H; auto.
Qed.

#[export] Instance DirectedGraph_noemptyedge {V E: Type} :
  NoEmptyEdge (DirectedGraphType V E) V E.
Proof.
  split; intros.
  exists (g.(dg_source V E) e), (g.(dg_target V E) e).
  repeat split; auto.
  apply dg_source_valid; auto.
  apply dg_target_valid; auto.
Qed.

#[export] Instance DirectedGraph_stepunique {V E: Type} :
  StepUniqueDirected (DirectedGraphType V E) V E.
Proof.
  split; intros.
  destruct H0, H1.
  destruct dg_dir0, dg_dir1.
  subst; auto.
Qed.

#[export] Instance Directed_finitegraph {V E: Type} :
  FiniteGraph (DirectedGraphType V E) V E.
Proof.
  refine {|graph_basic.listV := dg_listV; |}.
  intros; apply dg_finite_v; auto.
Defined.

(* ================================================================ *)
(* 3. Mutually Reachable and SCC                                    *)
(*    Definitions are generic: work for any Graph G V E instance.  *)
(* ================================================================ *)

Section SCC_DEFS.

Context {G: Type} {V: Type} {E: Type}.
Context {g: G}.
Context {pg: Graph G V E} {gv: GValid G} {stepvalid: StepValid G V E}.

(** mutually_reachable: u and v are in the same strongly connected component *)
Definition mutually_reachable (u v: V) : Prop :=
  reachable g u v /\ reachable g v u.

(** Equivalence relation properties of mutually_reachable *)

Lemma mutually_reachable_refl : forall u,
  vvalid g u -> mutually_reachable u u.
Proof.
  intros u Hu.
  unfold mutually_reachable, reachable.
  split; reflexivity.
Qed.

Lemma mutually_reachable_sym : forall u v,
  mutually_reachable u v -> mutually_reachable v u.
Proof.
  unfold mutually_reachable; tauto.
Qed.

Lemma mutually_reachable_trans : forall u v w,
  mutually_reachable u v -> mutually_reachable v w -> mutually_reachable u w.
Proof.
  intros u v w [Huv Hvu] [Hvw Hwv].
  unfold mutually_reachable.
  split; unfold reachable in *.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.

(** is_SCC: s is a strongly connected component iff:
    - s is non-empty and contains at least one valid vertex
    - all vertices in s are mutually reachable
    - s is maximal with respect to mutual reachability *)
Definition is_SCC (s: V -> Prop) : Prop :=
  (exists v, s v /\ vvalid g v) /\
  (forall u v, s u -> s v -> mutually_reachable u v) /\
  (forall u v, s u -> vvalid g v -> mutually_reachable u v -> s v).

(** Every vertex in an SCC is valid.
    Derived from non-emptiness (valid witness) + internal mutual reachability. *)
Lemma is_SCC_vvalid : forall s u,
  is_SCC s -> s u -> vvalid g u.
Proof.
  intros s u [Hnonempty [Hinternal Hmaximal]] Hsu.
  destruct Hnonempty as [w [Hsw Hvw]].
  destruct (classic (u = w)).
  - subst; auto.
  - apply Hinternal with u w in Hsu; [|exact Hsw].
    unfold mutually_reachable in Hsu.
    destruct Hsu as [Huw _].
    apply reachable_vvalid with (x := u) (y := w) in Huw; auto.
    destruct Huw; auto.
Qed.

Lemma is_SCC_closed_under_mr : forall s u v,
  is_SCC s -> s u -> mutually_reachable u v -> s v.
Proof.
  intros s u v Hscc Hsu Hmr.
  destruct Hscc as [Hnonempty [Hinternal Hmaximal]].
  destruct (classic (u = v)) as [Heq|Hneq].
  - subst; exact Hsu.
  - assert (Hvv : vvalid g v).
    { unfold mutually_reachable in Hmr; destruct Hmr as [Huv _].
      apply reachable_vvalid with (x := u) (y := v) in Huv; auto.
      destruct Huv; auto. }
    apply Hmaximal with u; auto.
Qed.

(** Maximality: if s1 is a subset of s2 and both are SCCs, then s1 = s2 (extensionally) *)
Lemma is_SCC_maximal : forall s1 s2,
  is_SCC s1 -> is_SCC s2 ->
  (forall v, s1 v -> s2 v) -> (forall v, s2 v -> s1 v).
Proof.
  intros s1 s2 Hscc1 Hscc2 Hsubset v Hsv.
  destruct Hscc1 as [Hnonempty1 [Hinternal1 Hmaximal1]].
  destruct Hnonempty1 as [u [Hsu Hvu]].
  assert (Hsu2 : s2 u) by (apply Hsubset; auto).
  assert (Hmr : mutually_reachable u v) by
    (destruct Hscc2 as [_ [Hinternal2 _]]; eapply Hinternal2; eauto).
  assert (Hvv : vvalid g v) by (eapply is_SCC_vvalid; eauto).
  apply Hmaximal1 with u; auto.
Qed.

(** A singleton vertex is an SCC if it is only mutually reachable with itself *)
Lemma singleton_is_SCC : forall v,
  vvalid g v -> (forall u, vvalid g u -> mutually_reachable v u -> u = v) ->
  is_SCC (fun w => w = v).
Proof.
  intros v Hv Hunique.
  split.
  - exists v; split; auto.
  - split.
    + intros u w Hu Hw.
      subst u; subst w.
      apply mutually_reachable_refl; auto.
    + intros u w Hu Hvw Hmr.
      subst u.
      apply Hunique; auto.
Qed.

(* ================================================================ *)
(* 4. SCC Partition                                                 *)
(* ================================================================ *)

(** scc_partition: sccs is a valid SCC partition of g iff:
    - Cover: every valid vertex belongs to some SCC in sccs
    - SCC: every element of sccs is an SCC
    - Disjoint: distinct SCCs in sccs are disjoint *)
Definition scc_partition (sccs: list (V -> Prop)) : Prop :=
  (forall v, vvalid g v -> exists s, In s sccs /\ s v) /\
  (forall s, In s sccs -> is_SCC s) /\
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2).

(** If u and v are mutually reachable, they belong to the same SCC in any partition *)
Lemma mutually_reachable_same_SCC : forall u v sccs,
  vvalid g u -> scc_partition sccs -> mutually_reachable u v ->
  exists s, In s sccs /\ s u /\ s v.
Proof.
  intros u v sccs Hvu Hpart Hmr.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  destruct (Hcover u Hvu) as [su [Hin_su Hsu]].
  exists su; split; [auto|split; auto].
  apply (is_SCC_closed_under_mr su u v); [apply Hsccs; auto|auto|auto].
Qed.

(** Uniqueness of SCC partition up to extensional equivalence *)
Lemma scc_partition_unique : forall sccs1 sccs2,
  scc_partition sccs1 -> scc_partition sccs2 ->
  (forall s1, In s1 sccs1 -> exists s2, In s2 sccs2 /\
    forall v, s1 v <-> s2 v) /\
  (forall s2, In s2 sccs2 -> exists s1, In s1 sccs1 /\
    forall v, s2 v <-> s1 v).
Proof.
  intros sccs1 sccs2 Hpart1 Hpart2.
  destruct Hpart1 as [Hcover1 [Hsccs1 Hdisjoint1]].
  destruct Hpart2 as [Hcover2 [Hsccs2 Hdisjoint2]].
  split.
  - intros s1 Hin1.
    pose proof Hsccs1 _ Hin1 as Hscc1.
    destruct Hscc1 as [Hnonempty1 [Hinternal1 Hmaximal1]].
    destruct Hnonempty1 as [v [Hsv Hvv]].
    destruct (Hcover2 v Hvv) as [s2 [Hin2 Hsv2]].
    exists s2; split; auto.
    intro v0; split.
    + intros Hsv0.
      assert (Hmr : mutually_reachable v v0) by (apply Hinternal1; auto).
      apply (is_SCC_closed_under_mr s2 v v0); [apply Hsccs2; auto | auto | auto].
    + intros Hsv0'.
      assert (Hmr : mutually_reachable v v0) by
        (destruct (Hsccs2 _ Hin2) as [_ [Hinternal2 _]]; apply Hinternal2; auto).
      apply (is_SCC_closed_under_mr s1 v v0); [apply Hsccs1; auto | auto | auto].
  - intros s2 Hin2.
    pose proof Hsccs2 _ Hin2 as Hscc2.
    destruct Hscc2 as [Hnonempty2 [Hinternal2 Hmaximal2]].
    destruct Hnonempty2 as [v [Hsv Hvv]].
    destruct (Hcover1 v Hvv) as [s1 [Hin1 Hsv1]].
    exists s1; split; auto.
    intro v0; split.
    + intros Hsv0'.
      assert (Hmr : mutually_reachable v v0) by
        (apply Hinternal2; auto).
      apply (is_SCC_closed_under_mr s1 v v0); [apply Hsccs1; auto | auto | auto].
    + intros Hsv0.
      assert (Hmr : mutually_reachable v v0) by
        (destruct (Hsccs1 _ Hin1) as [_ [Hinternal1 _]]; apply Hinternal1; auto).
      apply (is_SCC_closed_under_mr s2 v v0); [apply Hsccs2; auto | auto | auto].
Qed.

(* ================================================================ *)
(* 5. Existence of SCC Partition (classical construction)           *)
(*    Requires FiniteGraph in addition to the base context.         *)
(* ================================================================ *)

Context {finitegraph: FiniteGraph G V E}.
Context {Hgvalid: gvalid g}.

(** Equivalence class of a vertex under mutually_reachable *)
Definition equiv_class (v: V) : V -> Prop :=
  fun w => vvalid g w /\ mutually_reachable v w.

(** equiv_class v is an SCC when v is valid *)
Lemma equiv_class_is_SCC : forall v,
  vvalid g v -> is_SCC (equiv_class v).
Proof.
  intros v Hv.
  split.
  - exists v; split.
    + unfold equiv_class; split; auto.
      apply mutually_reachable_refl; auto.
    + auto.
  - split.
    + intros u w [Hvu Hmru] [Hvw Hmrw].
      apply mutually_reachable_trans with v; auto.
      apply mutually_reachable_sym; auto.
    + intros u w [Hvu Hmru] Hvw Hmruw.
      unfold equiv_class.
      split; auto.
      apply mutually_reachable_trans with u; auto.
Qed.

(** Helper lemma: build a partition for a given list of vertices by induction *)
Lemma build_scc_partition_aux : forall (vertices: list V),
  exists sccs,
    (forall v, vvalid g v -> In v vertices -> exists s, In s sccs /\ s v) /\
    (forall s, In s sccs -> is_SCC s) /\
    (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2).
Proof.
  induction vertices as [|a rest IH].
  - exists nil; simpl; split; [|split].
    + intros v Hv Hin. inversion Hin.
    + intros s Hin. inversion Hin.
    + intros s1 s2 v Hin1 Hin2. inversion Hin1.
  - destruct IH as [sccs_rest [Hcover_rest [Hsccs_rest Hdisjoint_rest]]].
    destruct (classic (exists s, In s sccs_rest /\ s a)).
    + (* a is already covered by an existing SCC: use sccs_rest as-is *)
      exists sccs_rest; split; [|split]; auto.
      intros v Hv Hin.
      destruct Hin as [Hva|Hrest'].
      * subst v. destruct H as [s [Hin_s Hsa]].
        exists s; split; auto.
      * apply Hcover_rest; auto.
    + (* a is not covered by any existing SCC *)
      destruct (classic (vvalid g a)).
      * (* a is valid: create new SCC equiv_class a *)
        exists (equiv_class a :: sccs_rest).
        split; [|split].
        -- intros v Hv Hin.
           destruct Hin as [Hva|Hrest'].
           ++ subst v.
              exists (equiv_class a); split; [left; reflexivity|].
              unfold equiv_class; split; auto.
              apply mutually_reachable_refl; auto.
           ++ destruct (Hcover_rest v Hv Hrest') as [s [Hin_s Hsv]].
              exists s; split; auto. right; auto.
        -- intros s Hin.
           destruct Hin as [Hin|Hin].
           ++ subst s. apply equiv_class_is_SCC; auto.
           ++ apply Hsccs_rest; auto.
        -- intros s1 s2 v Hind Hind' Hv1 Hv2.
           apply in_inv in Hind; apply in_inv in Hind'.
           destruct Hind as [Heq1|Hin1]; destruct Hind' as [Heq2|Hin2].
           ++ (* Case 1: s1 = equiv_class a, s2 = equiv_class a *)
              subst s1; subst s2; auto.
           ++ (* Case 2: s1 = equiv_class a, In s2 sccs_rest *)
              subst s1; exfalso; apply H.
              { unfold equiv_class in Hv1; destruct Hv1 as [_ Hmr0].
                assert (Hscc_s2 : is_SCC s2) by (apply Hsccs_rest; auto).
                assert (Hs2a : s2 a).
                { assert (Hvv_v : vvalid g v) by (eapply is_SCC_vvalid; eauto).
                  apply (is_SCC_closed_under_mr s2 v a); auto.
                  apply mutually_reachable_sym; auto. }
                exists s2; split; auto. }
           ++ (* Case 3: In s1 sccs_rest, s2 = equiv_class a *)
              subst s2; exfalso; apply H.
              { unfold equiv_class in Hv2; destruct Hv2 as [_ Hmr0].
                assert (Hscc_s1 : is_SCC s1) by (apply Hsccs_rest; auto).
                assert (Hs1a : s1 a).
                { assert (Hvv_v : vvalid g v) by (eapply is_SCC_vvalid; eauto).
                  apply (is_SCC_closed_under_mr s1 v a); auto.
                  apply mutually_reachable_sym; auto. }
                exists s1; split; auto. }
           ++ (* Case 4: In s1 sccs_rest, In s2 sccs_rest *)
              eapply Hdisjoint_rest; eauto.
      * (* a is not valid: skip, no new SCC needed *)
        exists sccs_rest; split; [|split]; auto.
        intros v Hv Hin.
        destruct Hin as [Hva|Hrest'].
        -- subst v. exfalso; auto.
        -- apply Hcover_rest; auto.
Qed.

(** Helper: every valid vertex is in listV g *)
Lemma listV_contains_valid (v : V) : vvalid g v -> In v (listV g).
Proof.
  intro Hv.
  apply (finite_vertices g Hgvalid v).
  auto.
Qed.

Theorem scc_partition_exists : exists sccs, scc_partition sccs.
Proof.
  destruct (build_scc_partition_aux (listV g)) as [sccs [Hcover [Hsccs Hdisjoint]]].
  exists sccs.
  split; [|split].
  - intros v Hv. apply (Hcover v Hv). apply listV_contains_valid; auto.
  - apply Hsccs.
  - apply Hdisjoint.
Qed.

(* ================================================================ *)
(* 6. Condensation (DAG property of SCCs)                           *)
(* ================================================================ *)

(** An edge in the condensation graph: from SCC s1 to different SCC s2
    if there is an edge from some vertex in s1 to some vertex in s2 *)
Definition condensation_edge (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ step g u v.

(** condensation_reachable: the transitive closure of condensation_edge.
    Represents paths in the condensation DAG. *)
Inductive condensation_reachable (sccs: list (V -> Prop)) : (V -> Prop) -> (V -> Prop) -> Prop :=
| cr_edge : forall s1 s2,
    condensation_edge sccs s1 s2 ->
    condensation_reachable sccs s1 s2
| cr_trans : forall s1 s2 s3,
    condensation_reachable sccs s1 s2 ->
    condensation_reachable sccs s2 s3 ->
    condensation_reachable sccs s1 s3.

(** Helper: every SCC on a condensation_reachable path is in the partition *)
Lemma condensation_reachable_In : forall sccs s1 s2,
  condensation_reachable sccs s1 s2 ->
  In s1 sccs /\ In s2 sccs.
Proof.
  intros sccs s1 s2 Hcr.
  induction Hcr as [s1' s2' Hedge | s1' s2' s3' Hcr1 IHcr1 Hcr2 IHcr2].
  - destruct Hedge as [Hin1 [Hin2 _]]; split; auto.
  - destruct IHcr1 as [Hin1 _].
    destruct IHcr2 as [_ Hin2].
    split; auto.
Qed.

(** Key lemma: condensation-level reachability implies vertex-level reachability.
    If there is a condensation path from s1 to s2 (via condensation edges),
    and s1 ≠ s2, then there exist vertices u in s1 and v in s2 that are
    reachable in g. *)
Lemma condensation_reachable_implies_reachable : forall sccs s1 s2,
  scc_partition sccs ->
  condensation_reachable sccs s1 s2 ->
  s1 <> s2 ->
  exists u v, s1 u /\ s2 v /\ reachable g u v.
Proof.
  intros sccs s1 s2 Hpart Hcr Hneq.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  induction Hcr as [s1 s2 Hedge | s1 s2 s3 Hcr1 IH1 Hcr2 IH2].
  - (* Base case: single condensation edge *)
    destruct Hedge as [_ [_ [_ [u [v [Hu [Hv Hstep]]]]]]].
    exists u, v.
    split; [|split]; auto.
    apply step_rt; auto.
  - (* Transitive case: chain s1 -> s2 -> s3 *)
    destruct (classic (s1 = s2)) as [Heq12|Hneq12].
    + (* s1 = s2: the path is effectively s1(=s2) -> s3 *)
      subst s2. apply IH2; auto.
    + destruct (classic (s2 = s3)) as [Heq23|Hneq23].
      * (* s2 = s3: the path is effectively s1 -> s2(=s3) *)
        subst s3. apply IH1; auto.
      * (* s1, s2, s3 are all distinct (as functions) *)
        destruct (IH1 Hneq12) as [u1 [v2 [Hu1 [Hv2 Hreach12]]]].
        destruct (IH2 Hneq23) as [u2 [v3 [Hu2 [Hv3 Hreach23]]]].
        (* v2 and u2 are both in s2. We need to know s2 is an SCC. *)
        apply condensation_reachable_In in Hcr1 as [_ Hin2].
        apply Hsccs in Hin2; destruct Hin2 as [_ [Hinternal2 _]].
        assert (Hmr2 : mutually_reachable v2 u2) by (apply Hinternal2; auto).
        (* Chain: u1 -> v2 -> u2 -> v3 *)
        exists u1, v3.
        split; [|split]; auto.
        unfold reachable in *.
        etransitivity; [apply Hreach12|].
        destruct Hmr2 as [Hv2u2 _].
        etransitivity; [apply Hv2u2|].
        apply Hreach23.
Qed.

(** No cycle between two different SCCs.
    This is the key property: if there were a path from s1 to s2 AND
    a path from s2 back to s1 at the vertex level, then s1 = s2 by SCC
    maximality. This is a direct vertex-level statement that doesn't
    require condensation_reachable. *)
Theorem no_cycle_between_different_SCCs : forall sccs,
  scc_partition sccs ->
  ~ exists s1 s2, In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
    (exists u1 v1, s1 u1 /\ s2 v1 /\ reachable g u1 v1) /\
    (exists u2 v2, s2 u2 /\ s1 v2 /\ reachable g u2 v2).
Proof.
  intros sccs Hpart.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  unfold not; intros Hcycle.
  destruct Hcycle as [s1 [s2 [Hin1 [Hin2 [Hneq [Hforward Hback]]]]]].

  destruct Hforward as [u1 [v1 [Hsu1 [Hsv1 Hreach_fwd]]]].
  destruct Hback as [u2 [v2 [Hsu2 [Hsv2 Hreach_bwd]]]].

  pose proof Hsccs _ Hin1 as Hscc1_full.
  pose proof Hsccs _ Hin2 as Hscc2_full.

  destruct Hscc1_full as [_ [Hinternal1 _]].
  destruct Hscc2_full as [_ [Hinternal2 _]].

  (* v1 and u2 are both in s2, so they are mutually reachable *)
  assert (Hmr_s2 : mutually_reachable v1 u2) by
    (apply Hinternal2; auto).
  (* v2 and u1 are both in s1, so they are mutually reachable *)
  assert (Hmr_s1 : mutually_reachable v2 u1) by
    (apply Hinternal1; auto).

  (* By transitivity, u1 and u2 are mutually reachable *)
  assert (Hmr_u1u2 : mutually_reachable u1 u2).
  { unfold mutually_reachable.
    split; unfold reachable in *.
    - etransitivity; [apply Hreach_fwd|].
      destruct Hmr_s2. exact H.
    - etransitivity; [apply Hreach_bwd|].
      destruct Hmr_s1. exact H. }

  (* u2 must be in s1 by maximality of s1 *)
  assert (Hs1u2 : s1 u2).
  { apply (is_SCC_closed_under_mr s1 u1 u2 (Hsccs _ Hin1)); auto. }

  (* Contradiction: s1 u2 and s2 u2 but s1 <> s2 *)
  apply Hneq.
  eapply Hdisjoint with (v := u2); eauto.
Qed.

(** condensation_is_acyclic: The condensation graph is acyclic.
    If there is a condensation edge from s1 to s2, then there is
    no condensation path from s2 back to s1. This captures the
    essential DAG property at the condensation level. *)
Theorem condensation_is_acyclic : forall sccs s1 s2,
  scc_partition sccs ->
  condensation_edge sccs s1 s2 ->
  ~ condensation_reachable sccs s2 s1.
Proof.
  intros sccs s1 s2 Hpart Hedge Hback.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  destruct Hedge as [Hin1 [Hin2 [Hneq [u [v [Hu [Hv Hstep]]]]]]].
  (* Forward: step from u (in s1) to v (in s2) implies reachable *)
  assert (Hfwd : reachable g u v) by (apply step_rt; auto).
  (* Backward: condensation_reachable from s2 to s1 implies vertex-level reachability *)
  assert (Hneq_sym : s2 <> s1) by (intro Heq; apply Hneq; symmetry; auto).
  destruct (condensation_reachable_implies_reachable sccs s2 s1
    (conj Hcover (conj Hsccs Hdisjoint)) Hback Hneq_sym)
    as [u' [v' [Hu' [Hv' Hback_reach]]]].
  (* v (in s2) and u' (in s2) are mutually reachable *)
  pose proof (Hsccs _ Hin2) as Hscc2_full.
  destruct Hscc2_full as [_ [Hinternal2 _]].
  assert (Hmr2 : mutually_reachable v u') by (apply Hinternal2; auto).
  (* v' (in s1) and u (in s1) are mutually reachable *)
  pose proof (Hsccs _ Hin1) as Hscc1_full.
  destruct Hscc1_full as [_ [Hinternal1 _]].
  assert (Hmr1 : mutually_reachable v' u) by (apply Hinternal1; auto).
  (* Chain: u -> v -> u' -> v' -> u gives mutually_reachable u u' *)
  assert (Hcycle : mutually_reachable u u').
  { unfold mutually_reachable.
    split; unfold reachable in *.
    - etransitivity; [apply Hfwd|].
      destruct Hmr2 as [Hvu' _]. exact Hvu'.
    - etransitivity; [apply Hback_reach|].
      destruct Hmr1 as [Hv'u _]. exact Hv'u. }
  (* u' must be in s1 by SCC maximality of s1 *)
  assert (Hu'_in_s1 : s1 u').
  { exact (is_SCC_closed_under_mr s1 u u' (Hsccs _ Hin1) Hu Hcycle). }
  (* Contradiction: s1 u' and s2 u' but s1 <> s2 *)
  apply Hneq.
  eapply Hdisjoint with (v := u'); eauto.
Qed.

End SCC_DEFS.

(* ================================================================ *)
(* 7. Graph Reversal (for Kosaraju's algorithm)                     *)
(* ================================================================ *)

(** Reverse a directed graph: swap source and target of every edge *)
Definition reverse_directed_graph {V E: Type}
  (dg: DirectedGraphType V E) : DirectedGraphType V E :=
  {| dg_vvalid := dg_vvalid dg;
     dg_evalid := dg_evalid dg;
     dg_source := dg_target dg;
     dg_target := dg_source dg;
     dg_listV  := dg_listV dg |}.

(** Key lemma: step_aux in the reverse graph is equivalent to step_aux in the
    original graph with endpoints swapped. *)
Lemma step_aux_reverse_equiv : forall {V E: Type} (dg: DirectedGraphType V E) e x y,
  dg_step_aux (reverse_directed_graph dg) e x y <-> dg_step_aux dg e y x.
Proof.
  intros V E dg e x y.
  split; intros H; destruct H as [Hvx Hvy Hve [Hsrc Htgt]];
    constructor; simpl; auto.
Qed.

(** step in the reverse graph is equivalent to step in reverse direction *)
Lemma step_reverse_equiv : forall {V E: Type} (dg: DirectedGraphType V E) x y,
  step (reverse_directed_graph dg) x y <-> step dg y x.
Proof.
  intros V E dg x y.
  unfold step.
  split; intros [e H]; exists e.
  - apply step_aux_reverse_equiv; exact H.
  - apply step_aux_reverse_equiv; exact H.
Qed.

(** reachable in the reverse graph is reachable in reverse direction *)
Lemma reachable_reverse_equiv : forall {V E: Type} (dg: DirectedGraphType V E) x y,
  reachable (reverse_directed_graph dg) x y <-> reachable dg y x.
Proof.
  intros V E dg x y.
  unfold reachable.
  split; intros H.
  - induction_1n H.
    + reflexivity.
    + transitivity_n1 x0; auto.
      apply step_reverse_equiv; auto.
  - induction_1n H.
    + reflexivity.
    + transitivity_n1 y0; auto.
      apply step_reverse_equiv; auto.
Qed.

(** Note: Type Class instances for the reversed graph are NOT needed.
    Since reverse_directed_graph dg has type DirectedGraphType V E, the existing
    instances (DirectedGraph_graph, DirectedGraph_gvalid, DirectedGraph_stepvalid,
    etc.) already apply. The lemmas below prove the key properties that downstream
    algorithms (Kosaraju) need. *)

(** Reversal lemmas *)

Lemma reverse_reverse_id : forall {V E: Type} (dg: DirectedGraphType V E),
  reverse_directed_graph (reverse_directed_graph dg) = dg.
Proof.
  intros; unfold reverse_directed_graph.
  destruct dg; simpl; reflexivity.
Qed.

Lemma reverse_preserves_valid : forall {V E: Type} (dg: DirectedGraphType V E),
  @DirectedGraphProp V E dg -> @DirectedGraphProp V E (reverse_directed_graph dg).
Proof.
  intros V E dg Hvalid.
  destruct Hvalid.
  split; simpl; auto.
Qed.

(** mutually_reachable is invariant under graph reversal.
    Crucial for Kosaraju: connects "SCC in reverse graph" with "SCC in original graph" *)
Lemma mutually_reachable_reverse : forall {V E: Type} (dg: DirectedGraphType V E)
  (u v: V),
  (mutually_reachable (g := dg) u v <-> mutually_reachable (g := reverse_directed_graph dg) u v).
Proof.
  intros V E dg u v.
  unfold mutually_reachable.
  split; intros [Huv Hvu]; split.
  - apply reachable_reverse_equiv; auto.
  - apply reachable_reverse_equiv; auto.
  - apply reachable_reverse_equiv; auto.
  - apply reachable_reverse_equiv; auto.
Qed.

(** Corollary: SCC membership is invariant under graph reversal *)
Corollary is_SCC_reverse : forall {V E: Type} (dg: DirectedGraphType V E) s,
  is_SCC (g := dg) s <-> is_SCC (g := reverse_directed_graph dg) s.
Proof.
  intros V E dg s.
  unfold is_SCC.
  split; intros [Hnonempty [Hinternal Hmaximal]].
  - split; [|split].
    + exact Hnonempty.
    + intros u v Hsu Hsv.
      apply (mutually_reachable_reverse dg u v).
      apply Hinternal; auto.
    + intros u v Hsu Hvv Hmr.
      apply (mutually_reachable_reverse dg u v) in Hmr.
      apply Hmaximal with u; auto.
  - split; [|split].
    + exact Hnonempty.
    + intros u v Hsu Hsv.
      apply (mutually_reachable_reverse dg u v).
      apply Hinternal; auto.
    + intros u v Hsu Hvv Hmr.
      apply (mutually_reachable_reverse dg u v) in Hmr.
      apply Hmaximal with u; auto.
Qed.

(** Corollary: SCC partition is invariant under graph reversal *)
Corollary scc_partition_reverse : forall {V E: Type} (dg: DirectedGraphType V E) sccs,
  scc_partition (g := dg) sccs <-> scc_partition (g := reverse_directed_graph dg) sccs.
Proof.
  intros V E dg sccs.
  unfold scc_partition.
  split; intros [Hcover [Hsccs Hdisjoint]].
  - split; [|split].
    + intros v Hv. apply Hcover; auto.
    + intros s Hin. apply (is_SCC_reverse dg s); auto.
    + intros s1 s2 v Hin1 Hin2 H1v H2v. eapply Hdisjoint; eauto.
  - split; [|split].
    + intros v Hv. apply Hcover; auto.
    + intros s Hin. apply (is_SCC_reverse dg s); auto.
    + intros s1 s2 v Hin1 Hin2 H1v H2v. eapply Hdisjoint; eauto.
Qed.
