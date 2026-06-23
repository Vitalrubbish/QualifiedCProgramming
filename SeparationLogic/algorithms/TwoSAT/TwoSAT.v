Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
Require Import Recdef.
Require Import GraphLib.graph_basic.
Require Import GraphLib.Syntax.
Require Import GraphLib.examples.tarjan.
Require Import Algorithms.Tarjan_directed.SCC_basic.
Import ListNotations.

Local Open Scope Z_scope.

(* ================================================================ *)
(* Section 1: 2-SAT Syntax                                          *)
(* ================================================================ *)

Definition literal : Type := (Z * bool)%type.

Definition negate (l : literal) : literal :=
  (fst l, negb (snd l)).

Lemma negate_involutive : forall l, negate (negate l) = l.
Proof.
  destruct l as [v b]; unfold negate; simpl.
  rewrite Bool.negb_involutive; auto.
Qed.

Lemma negate_injective : forall l1 l2, negate l1 = negate l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  apply (f_equal negate) in H; rewrite !negate_involutive in H; auto.
Qed.

Definition clause : Type := literal * literal.
Definition formula : Type := list clause.
Definition assignment : Type := Z -> bool.

Definition eval_literal (a : assignment) (l : literal) : bool :=
  let (v, sign) := l in
  if sign then a v else negb (a v).

Lemma eval_negate : forall a l,
  eval_literal a (negate l) = negb (eval_literal a l).
Proof.
  intros a [v b]; unfold eval_literal, negate; simpl.
  destruct b; simpl; auto.
  symmetry; apply Bool.negb_involutive.
Qed.

Definition satisfies (a : assignment) (f : formula) : Prop :=
  forall c, In c f ->
    eval_literal a (fst c) = true \/ eval_literal a (snd c) = true.

Definition satisfiable (f : formula) : Prop := exists a, satisfies a f.

(* ================================================================ *)
(* Section 2: Validity Constraints                                   *)
(* ================================================================ *)

Definition valid_literal (numVars : Z) (l : literal) : Prop :=
  let (v, _) := l in 1 <= v <= numVars.

Lemma valid_literal_negate : forall numVars l,
  valid_literal numVars l -> valid_literal numVars (negate l).
Proof.
  intros numVars [v b] H; unfold valid_literal in *; simpl in *.
  unfold negate; simpl; auto.
Qed.

Definition valid_clause (numVars : Z) (c : clause) : Prop :=
  valid_literal numVars (fst c) /\ valid_literal numVars (snd c).

Definition valid_formula (numVars : Z) (f : formula) : Prop :=
  forall c, In c f -> valid_clause numVars c.

(* ================================================================ *)
(* Section 3: Implication Graph Construction                         *)
(* ================================================================ *)

Fixpoint literal_list_aux (n : nat) (base : Z) : list literal :=
  match n with
  | O => nil
  | S n' => (base, true) :: (base, false) :: literal_list_aux n' (base + 1)
  end.

Definition literal_list (numVars : Z) : list literal :=
  literal_list_aux (Z.to_nat numVars) 1.

Lemma literal_list_aux_in : forall n (base : Z) (v : Z) (b : bool),
  (exists (k : nat), (k < n)%nat /\ v = base + Z.of_nat k) -> In (v, b) (literal_list_aux n base).
Proof.
  induction n.
  - simpl; intros base v b H; destruct H as [k [Hlt _]]; exfalso; lia.
  - simpl; intros base v b H; destruct H as [k [Hlt Heq]].
    destruct k as [| k'].
    + destruct b; [left | right; left]; simpl; f_equal; lia.
    + destruct b; [right; right | right; right]; apply IHn; exists k'; split; [lia | rewrite Heq; lia | lia | rewrite Heq; lia].
Qed.

Lemma literal_list_complete : forall numVars l,
  valid_literal numVars l -> In l (literal_list numVars).
Proof.
  intros numVars [v b] [Hlow Hhigh].
  unfold literal_list.
  apply literal_list_aux_in with (base := 1).
  exists (Z.to_nat (v - 1)).
  split.
  - apply Z2Nat.inj_lt; lia.
  - rewrite Z2Nat.id by lia; lia.
Qed.

Definition nth_clause (f : formula) (i : Z) : clause :=
  nth (Z.to_nat i) f ((0, false), (0, false)).

Definition implication_graph (f : formula) (numVars : Z)
  : OriginalGraphType literal Z :=
  {|
    original_vvalid := fun (l : literal) => valid_literal numVars l;
    original_step := fun (e : Z) => 0 <= e < 2 * Zlength f;
    original_step_fst := fun (e : Z) =>
      let i := e / 2 in
      let c := nth_clause f i in
      if Z.even e then negate (fst c) else negate (snd c);
    original_step_snd := fun (e : Z) =>
      let i := e / 2 in
      let c := nth_clause f i in
      if Z.even e then snd c else fst c;
    original_listV := literal_list numVars;
  |}.

Lemma nth_clause_in : forall f i, 0 <= i < Zlength f ->
  In (nth_clause f i) f.
Proof.
  intros f i Hrange.
  unfold nth_clause.
  apply nth_In.
  rewrite (Zlength_correct f) in Hrange.
  lia.
Qed.

Lemma implication_graph_gvalid : forall f numVars,
  valid_formula numVars f ->
  OriginalGraphProp literal Z (implication_graph f numVars).
Proof.
  intros f numVars Hvalid.
  set (g := implication_graph f numVars).
  constructor; unfold g; simpl; intros.
  - unfold valid_literal.
    destruct (Z.even e) eqn: Heven;
      [ apply valid_literal_negate | apply valid_literal_negate ];
      unfold Z.mul in H; destruct H as [He1 He2];
      assert (Hdiv : 0 <= e / 2 < Zlength f)
        by (split; [apply Z.div_pos; [exact He1 | lia] |
                    apply Z.div_lt_upper_bound; [lia | exact He2]]);
      destruct (Hvalid _ (nth_clause_in f (e / 2) Hdiv)) as [Hl1 Hl2];
      auto.
  - unfold valid_literal.
    destruct (Z.even e) eqn: Heven;
      unfold Z.mul in H; destruct H as [He1 He2].
    + assert (Hdiv : 0 <= e / 2 < Zlength f)
        by (split; [apply Z.div_pos; [exact He1 | lia] |
                    apply Z.div_lt_upper_bound; [lia | exact He2]]);
      destruct (Hvalid _ (nth_clause_in f (e / 2) Hdiv)) as [_ Hl2]; auto.
    + assert (Hdiv : 0 <= e / 2 < Zlength f)
        by (split; [apply Z.div_pos; [exact He1 | lia] |
                    apply Z.div_lt_upper_bound; [lia | exact He2]]);
      destruct (Hvalid _ (nth_clause_in f (e / 2) Hdiv)) as [Hl1 _]; auto.
  - apply literal_list_complete; auto.
Qed.

Lemma dg_step_implication : forall f numVars c,
  In c f ->
  dg_step (implication_graph f numVars) (negate (fst c)) (snd c) /\
  dg_step (implication_graph f numVars) (negate (snd c)) (fst c).
Proof.
  intros f numVars [l1 l2] Hc.
  set (g := implication_graph f numVars).
  assert (Hpos: exists i : Z, 0 <= i < Zlength f /\
    nth (Z.to_nat i) f ((0,false),(0,false)) = (l1, l2)).
  { apply In_nth with (d := ((0,false),(0,false))) in Hc.
    destruct Hc as [i [Hrange Hnth]].
    exists (Z.of_nat i); split.
    - split.
      + apply (Nat2Z.is_nonneg i).
      + apply Nat2Z.inj_lt in Hrange.
        rewrite Zlength_correct.
        assumption.
    - rewrite Nat2Z.id; auto. }
  destruct Hpos as [i [Hrange Hnth]].
  unfold g, implication_graph; simpl.
  pose (e1 := 2 * i).
  pose (e2 := 2 * i + 1).
  assert (Hstep1: original_step g e1).
  { unfold original_step, e1.
    rewrite Zlength_correct in Hrange.
    split; [lia |].
    rewrite Zlength_correct; lia. }
  assert (Hstep2: original_step g e2).
  { unfold original_step, e2.
    rewrite Zlength_correct in Hrange.
    split; [lia |].
    rewrite Zlength_correct; lia. }
  split.
  - unfold dg_step.
    exists e1; split; [exact Hstep1 |].
    unfold original_step_fst, original_step_snd, e1, nth_clause.
    assert (Hdiv : (2*i)/2 = i).
    { symmetry; apply Z.div_unique with (r := 0); [lia | ring]. }
    rewrite Hdiv.
    assert (Heven : Z.even (2*i) = true) by (rewrite Z.even_mul, Z.even_2; auto).
    rewrite Heven; rewrite Hnth; auto.
  - unfold dg_step.
    exists e2; split; [exact Hstep2 |].
    unfold original_step_fst, original_step_snd, e2, nth_clause.
    assert (Hdiv : (2*i+1)/2 = i).
    { rewrite Z.mul_comm.
      rewrite Z.div_add_l by lia.
      rewrite Z.div_small; [ring | lia]. }
    rewrite Hdiv.
    assert (Heven : Z.even (2*i+1) = false) by
      (rewrite Z.even_add, Z.even_mul, Z.even_2; simpl; auto).
    rewrite Heven; rewrite Hnth; auto.
Qed.

(* ================================================================ *)
(* Section 4: Forward Direction                                      *)
(* ================================================================ *)

Lemma eval_preserved_along_step : forall f numVars a,
  satisfies a f ->
  forall l1 l2,
  dg_step (implication_graph f numVars) l1 l2 ->
  eval_literal a l1 = true -> eval_literal a l2 = true.
Proof.
  intros f numVars a Hsat l1 l2 Hstep Heval.
  set (g := implication_graph f numVars) in *.
  destruct Hstep as [e [Hstep [Hfst Hsnd]]].
  unfold g in Hfst, Hsnd, Hstep.
  cbv zeta in Hfst, Hsnd, Hstep.
  simpl in Hfst, Hsnd.
  rename Hstep into Hrange.
  destruct Hrange as [He1 He2].
  set (i := e / 2).
  set (c := nth_clause f i).
  assert (Hi_range : 0 <= i < Zlength f).
  { unfold i; split.
    - apply Z.div_pos; [exact He1 | apply Z.lt_0_2].
    - apply Z.div_lt_upper_bound; [apply Z.lt_0_2 | exact He2]. }
  revert Hfst Hsnd.
  destruct (Z.even e) eqn: Heven;
    intros Hfst Hsnd;
    simpl in Hfst, Hsnd.
  - (* Z.even e = true *)
    unfold c, i in Hfst, Hsnd.
    rewrite <- Hfst in Heval; rewrite <- Hsnd.
    rewrite eval_negate in Heval.
    destruct (Hsat (nth_clause f (e/2)) (nth_clause_in f i Hi_range))
      as [Hc1 | Hc2].
    + rewrite Hc1 in Heval; simpl in Heval; discriminate.
    + exact Hc2.
  - (* Z.even e = false *)
    unfold c, i in Hfst, Hsnd.
    rewrite <- Hfst in Heval; rewrite <- Hsnd.
    rewrite eval_negate in Heval.
    destruct (Hsat (nth_clause f (e/2)) (nth_clause_in f i Hi_range))
      as [Hc1 | Hc2].
    + exact Hc1.
    + rewrite Hc2 in Heval; simpl in Heval; discriminate.
Qed.

Lemma eval_preserved_along_path : forall f numVars a,
  satisfies a f ->
  forall l1 l2,
  dg_reachable (implication_graph f numVars) l1 l2 ->
  eval_literal a l1 = true -> eval_literal a l2 = true.
Proof.
  intros f numVars a Hsat l1 l2 Hreach Heval.
  induction Hreach.
  - apply (eval_preserved_along_step f numVars a Hsat x y H Heval).
  - exact Heval.
  - apply IHHreach2; apply IHHreach1; exact Heval.
Qed.

Definition no_conflict (g : OriginalGraphType literal Z) (numVars : Z) : Prop :=
  forall v, 1 <= v <= numVars ->
    ~ mutually_reachable g (v, true) (v, false).

Lemma forward : forall f numVars,
  valid_formula numVars f ->
  satisfiable f -> no_conflict (implication_graph f numVars) numVars.
Proof.
  intros f numVars Hvalid [a Hsat] v Hv Hmr.
  set (g := implication_graph f numVars) in *.
  destruct Hmr as [Hftb Hbtf].
  destruct (classic (a v = true)) as [Hav | Hav].
  - assert (Heval: eval_literal a (v, true) = true)
      by (unfold eval_literal; simpl; rewrite Hav; auto).
    apply eval_preserved_along_path with (f := f) (numVars := numVars) (a := a)
      (l1 := (v, true)) (l2 := (v, false)) in Heval.
    + unfold eval_literal in Heval; simpl in Heval.
      rewrite Hav in Heval; simpl in Heval.
      discriminate.
    + exact Hsat.
    + unfold g; exact Hftb.
  - apply Bool.not_true_is_false in Hav.
    assert (Heval: eval_literal a (v, false) = true)
      by (unfold eval_literal; simpl; rewrite Hav; auto).
    apply eval_preserved_along_path with (f := f) (numVars := numVars) (a := a)
      (l1 := (v, false)) (l2 := (v, true)) in Heval.
    + unfold eval_literal in Heval; simpl in Heval.
      rewrite Hav in Heval; simpl in Heval.
      discriminate.
    + exact Hsat.
    + unfold g; exact Hbtf.
Qed.

(* ================================================================ *)
(* Section 5: Backward Direction                                     *)
(* ================================================================ *)

Section BACKWARD.

Variables (f : formula) (numVars : Z).
Hypothesis (Hvalid : valid_formula numVars f).

Let g : OriginalGraphType literal Z := implication_graph f numVars.
Let Hgvalid : OriginalGraphProp literal Z g :=
  implication_graph_gvalid f numVars Hvalid.
Let Hfinite : forall v : literal, original_vvalid g v -> In v (original_listV g) :=
  literal_list_complete numVars.

Let Hsccp : exists sccs, scc_partition g sccs :=
  scc_partition_exists g Hgvalid Hfinite.


End BACKWARD.

(* ================================================================ *)
(* Section 6: Main Theorem                                          *)
(* ================================================================ *)

Theorem two_sat_characterization :
  forall f numVars, valid_formula numVars f ->
  (satisfiable f <-> no_conflict (implication_graph f numVars) numVars).
Proof.
  intros f numVars Hvalid.
  split.
  - apply forward; auto.
  - admit.
Admitted.
